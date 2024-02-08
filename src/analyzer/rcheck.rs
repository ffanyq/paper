use std::borrow::BorrowMut;
use std::cell::RefCell;
use std::cmp::min;
use std::hash::Hash;
use std::rc::Rc;

use crate::analyzer::node::PointSet;

/*
1.首先进行初次的别名分析，构建每个阶段的node的对应的别名集合，
2.同时根据分析的每个阶段的每个线程所涉及的锁语句和赋值语句，按顺序构建ThreadBlock,
3.
*/
use super::node::{FuncMap, Node, ReturnResults};


use rustc_hash::FxHashMap;
use rustc_hash::FxHashSet;
use rustc_middle::mir::visit::{
    MutatingUseContext, NonMutatingUseContext, NonUseContext, PlaceContext, Visitor,
};
use rustc_middle::mir::{
    BasicBlocks, Local, Location, StatementKind, TerminatorKind, UnwindAction,
};
use rustc_middle::ty::{self, Ty, TyKind};
use rustc_middle::{
    mir::{BasicBlock, Operand, Place, ProjectionElem, Rvalue, Terminator},
    ty::TyCtxt,
};

use rustc_span::def_id::DefId;

use rustc_span::{Span};
use std::collections::{HashMap, HashSet, VecDeque};

#[derive(Eq, PartialEq, Clone, Debug)]
pub enum DefUse {
    Def,
    Use,
    Drop,
}

pub fn categorize(context: PlaceContext) -> Option<DefUse> {
    match context {
        ///////////////////////////////////////////////////////////////////////////
        // DEFS

        PlaceContext::MutatingUse(MutatingUseContext::Store) |

        // We let Call define the result in both the success and
        // unwind cases. This is not really correct, however it
        // does not seem to be observable due to the way that we
        // generate MIR. To do things properly, we would apply
        // the def in call only to the input from the success
        // path and not the unwind path. -nmatsakis
        PlaceContext::MutatingUse(MutatingUseContext::Call) |
        PlaceContext::MutatingUse(MutatingUseContext::AsmOutput) |
        PlaceContext::MutatingUse(MutatingUseContext::Yield) |

        // Storage live and storage dead aren't proper defines, but we can ignore
        // values that come before them.
        PlaceContext::NonUse(NonUseContext::StorageLive) |
        PlaceContext::NonUse(NonUseContext::StorageDead) => Some(DefUse::Def),

        ///////////////////////////////////////////////////////////////////////////
        // REGULAR USES
        //
        // These are uses that occur *outside* of a drop. For the
        // purposes of NLL, these are special in that **all** the
        // lifetimes appearing in the variable must be live for each regular use.

        PlaceContext::NonMutatingUse(NonMutatingUseContext::Projection) |
        PlaceContext::MutatingUse(MutatingUseContext::Projection) |

        // Borrows only consider their local used at the point of the borrow.
        // This won't affect the results since we use this analysis for generators
        // and we only care about the result at suspension points. Borrows cannot
        // cross suspension points so this behavior is unproblematic.
        PlaceContext::MutatingUse(MutatingUseContext::Borrow) |
        PlaceContext::NonMutatingUse(NonMutatingUseContext::SharedBorrow) |
        PlaceContext::NonMutatingUse(NonMutatingUseContext::FakeBorrow) |
        PlaceContext::NonMutatingUse(NonMutatingUseContext::PlaceMention)|

        PlaceContext::MutatingUse(MutatingUseContext::AddressOf) |
        PlaceContext::NonMutatingUse(NonMutatingUseContext::AddressOf) |
        PlaceContext::NonMutatingUse(NonMutatingUseContext::Inspect) |
        PlaceContext::NonMutatingUse(NonMutatingUseContext::Copy) |
        PlaceContext::NonMutatingUse(NonMutatingUseContext::Move) |
        PlaceContext::NonUse(NonUseContext::AscribeUserTy(_)) |
        PlaceContext::MutatingUse(MutatingUseContext::Retag) =>
            Some(DefUse::Use),

        ///////////////////////////////////////////////////////////////////////////
        // DROP USES
        //
        // These are uses that occur in a DROP (a MIR drop, not a
        // call to `std::mem::drop()`). For the purposes of NLL,
        // uses in drop are special because `#[may_dangle]`
        // attributes can affect whether lifetimes must be live.

        PlaceContext::MutatingUse(MutatingUseContext::Drop) =>
            Some(DefUse::Drop),

        // Debug info is neither def nor use.
        PlaceContext::NonUse(NonUseContext::VarDebugInfo) => None,

        PlaceContext::MutatingUse(MutatingUseContext::Deinit | MutatingUseContext::SetDiscriminant) => {
            None
        }
    }
}

struct AllLocalUsesVisitor<'tcx> {
    for_local: Local,
    bs: BasicBlocks<'tcx>,
}

impl<'tcx> Visitor<'tcx> for AllLocalUsesVisitor<'tcx> {
    fn visit_local(&mut self, local: Local, context: PlaceContext, location: Location) {
        //println!("local: {:?}", local);
        //if local == self.for_local {
        // if let Some(DefUse::Use) = categorize(context) {
        //     self.uses.insert(location);
        // }
        // let span = self.bs[location.block]
        //     .terminator
        //     .clone()
        //     .unwrap()
        //     .source_info
        //     .span;

        let a = location.statement_index;
        if a == self.bs[location.block].statements.len() {
            return;
        }
        println!(
            "local:      {:?}, categorize:     {:?}, location:     {:?},  span : {:?}",
            local,
            categorize(context),
            location,
            self.bs[location.block].statements[a]
                .clone()
                .source_info
                .span
        );

        //}
    }
}

#[derive(Debug, Clone)]
pub struct AssignStms<'tcx> {
    pub left: Place<'tcx>,
    pub right: Place<'tcx>,
    pub alias: Vec<Vec<usize>>,
    pub lock: Vec<usize>,
    pub atype: usize,
    pub span: Span,
}
impl<'tcx> AssignStms<'tcx> {
    pub fn new(left: Place<'tcx>, right: Place<'tcx>, atype: usize, span: Span) -> Self {
        AssignStms {
            left,
            right,
            alias: Vec::<Vec<usize>>::new(),
            atype,
            lock: Vec::<usize>::new(),
            span,
        }
    }
}

#[derive(Debug, Clone)]
pub struct BlockNode<'tcx> {
    pub index: usize,
    pub is_cleanup: bool,
    pub next: FxHashSet<usize>,
    pub assignment: Vec<AssignStms<'tcx>>,
    pub calls: Vec<Terminator<'tcx>>,
    pub sub_blocks: Vec<usize>,
    pub const_value: Vec<(usize, usize)>,
    pub switch_stmts: Vec<Terminator<'tcx>>,
    pub thread_id: usize,
    pub is_current: bool,
}

impl<'tcx> BlockNode<'tcx> {
    pub fn new(index: usize, is_cleanup: bool, t_id: usize) -> Self {
        BlockNode {
            index,
            is_cleanup,
            next: FxHashSet::<usize>::default(),
            assignment: Vec::<AssignStms>::new(),
            calls: Vec::<Terminator<'tcx>>::new(),
            sub_blocks: Vec::<usize>::new(),
            const_value: Vec::<(usize, usize)>::new(),
            switch_stmts: Vec::<Terminator<'tcx>>::new(),
            thread_id: t_id,
            is_current: false,
        }
    }

    pub fn push(&mut self, index: usize) {
        self.next.insert(index);
    }
}

pub struct RCheck<'tcx> {
    pub def_id: DefId,
    pub tcx: TyCtxt<'tcx>,
    pub blocks: Vec<BlockNode<'tcx>>,
    pub count: usize,
    //pub alias: Alias,                   //Union Find Set
    pub constant_bool: FxHashMap<usize, usize>,
    pub father_block: Vec<usize>,
    pub nodes: Vec<Node>,                   //Saving the alias set.
    pub thread_node: HashMap<usize, usize>, //The start node index of every thread.
    pub thread_set: HashSet<usize>,         //Saving the thread set during analysis.
    pub return_results: ReturnResults,
}

impl<'tcx> RCheck<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, defid: DefId) -> Self {
        let body = tcx.optimized_mir(defid);
        let arg_size = body.arg_count;
        RCheck {
            def_id: defid,
            tcx,
            blocks: Vec::new(),
            constant_bool: FxHashMap::default(),
            count: 0,
            //alias: Alias::new(0),
            father_block: Vec::new(),
            nodes: Vec::new(),
            thread_node: HashMap::new(),
            thread_set: HashSet::new(),
            return_results: ReturnResults::new(arg_size + 1),
        }
    }
    pub fn analysis(&mut self) {
        if self.tcx.is_mir_available(self.def_id) {
            let body = self.tcx.optimized_mir(self.def_id);
            let locals = &body.local_decls;
            let param_env = self.tcx.param_env(self.def_id);
            //let mut nodes: Vec<Node> =  Vec::new();
            //let count = 0;

            // for l in locals {
            //     println!("locals:   {:?}", l);
            // }

            //self.alias = Alias::new(locals.len());
            for ld in 0..locals.len() {
                let node = Node::new(ld, ld);
                self.nodes.push(node);
            }
            //let mut move_set: FxHashSet<usize> = FxHashSet::default();
            let basicblocks = &body.basic_blocks;
            let current_thread: usize = 0;

            //? Tracing the LockGuard
            // for (local, local_decl) in locals.iter_enumerated() {
            //     if let ty::TyKind::Adt(adt_def, substs) = local_decl.ty.kind() {
            //         let path = self.tcx.def_path_str_with_args(adt_def.did(), &*substs);
            //         if !path.starts_with("std::sync::MutexGuard") {
            //             println!();
            //             let mut visitor = AllLocalUsesVisitor {
            //                 for_local: local,
            //                 bs: basicblocks.clone(),
            //             };
            //             visitor.visit_body(body);
            //             println!("path:   {:?}", path);
            //             println!("{:?}, {:?}", local, local_decl.ty);
            //         }
            //     }

            // }
            // println!();

            // ? local visitor
            // let mut visitor = AllLocalUsesVisitor {
            //     for_local: Local::from_u32(2),
            //     bs: basicblocks.clone(),
            // };
            // visitor.visit_body(body);

            // // ? Rvalue Enum
            // for i in 0..basicblocks.len() {
            //      let iter = BasicBlock::from(i);
            //     // let terminator = basicblocks[iter].terminator.clone();
            //     // if let TerminatorKind::Call { func, args, destination, target, unwind, call_source, fn_span } = terminator.clone().unwrap().kind {
            //     //     println!("func : {:?}, args : {:?}, destination : {:?}, target : {:?}, call_source: {:?}", func, args, destination, target,call_source);
            //     // }
            //     // println!("{:?}",terminator);
            //     for statement in &basicblocks[iter].statements {
            //         println!("{:?}", statement.clone().source_info.span);
            //         if let StatementKind::Assign(ref assign) = statement.kind {
            //             let right = assign.1.clone();
            //             match right {
            //                 Rvalue::Use(ref x) => {
            //                     match x {
            //                         Operand::Copy(c) => {
            //                             println!("copy: {:?}", c);
            //                         },
            //                         Operand::Move(c) => {
            //                             println!("move: {:?}", c);
            //                         },
            //                         Operand::Constant(c) => {
            //                             println!( "try_to_scalar_int: {:?}",c.const_.try_eval_scalar_int(self.tcx, param_env));
            //                             println!( "try_to_scalar: {:?}",c.const_.try_eval_scalar(self.tcx, param_env));
            //                             println!( "try_eval_bits: {:?}",c.const_.try_eval_bits(self.tcx, param_env));
            //                             println!( "try_eval_target_usize: {:?}",c.const_.try_eval_target_usize(self.tcx, param_env));

            //                         },
            //                     }
            //                 },
            //                 _ => {}
            //             }
            //             println!();
            //             //println!("  right : {:?}", mem::discriminant(&right));
            //         }
            //     }

            // println!("  BasicBlock: {:?}", iter);
            // println!("  {:?}", basicblocks[iter].terminator);
            // println!("  kind:    {:?}", basicblocks[iter].terminator.clone().unwrap().kind.name());
            // match terminator {
            //     Some(t) => {
            //         match t.kind {
            //             TerminatorKind::Call { func, args, destination, target, unwind, call_source, fn_span } => {
            //                 println!("call name : {:?}", func.ty(local_decls, tcx));
            //             },

            //             _ => {}
            //         }
            //     },
            //     None => todo!(),
            // }

            for i in 0..basicblocks.len() {
                self.father_block.push(i);
                let iter = BasicBlock::from(i);
                let terminator = basicblocks[iter].terminator.clone();
                println!("terminator : {:?}", terminator);
                let mut current_node =
                    BlockNode::new(i, basicblocks[iter].is_cleanup, current_thread);
                for statement in &basicblocks[iter].statements {
                    println!("      statement: {:?}, span: {:?}", statement, statement.source_info.span);
                    let span = statement.source_info.span.clone();
                    if let StatementKind::Assign(ref assign) = statement.kind {
                        let left_local = assign.0.local.as_usize();
                        let left = assign.0.clone();

                        match assign.1 {
                            Rvalue::Use(ref x) => match x {
                                Operand::Copy(ref p) => {
                                    let right = p.clone();
                                    let assgin = AssignStms::new(left, right, 0, span);
                                    current_node.assignment.push(assgin);
                                }
                                Operand::Move(ref p) => {
                                    let right = p.clone();
                                    let assgin = AssignStms::new(left, right, 1, span);
                                    current_node.assignment.push(assgin);
                                }
                                Operand::Constant(ref constant) => {
                                    if let Some(right) =
                                        constant.const_.try_eval_scalar(self.tcx, param_env)
                                    {
                                        if let Ok(scalar) = right.try_to_int() {
                                            if let Ok(ans) = scalar.try_to_u64() {
                                                current_node
                                                    .const_value
                                                    .push((left_local, ans as usize));
                                            }
                                        }
                                    };
                                }
                            },
                            Rvalue::Ref(_, _, ref p) => {
                                let right = p.clone();
                                let assgin = AssignStms::new(left, right, 0, span);
                                current_node.assignment.push(assgin);
                            }
                            Rvalue::AddressOf(_, ref p) => {
                                let right = p.clone();
                                let assgin = AssignStms::new(left, right, 0, span);
                                current_node.assignment.push(assgin);
                            }
                            Rvalue::Cast(_, ref x, _) => match x {
                                Operand::Copy(ref p) => {
                                    let right = p.clone();
                                    let assgin = AssignStms::new(left, right, 0, span);
                                    current_node.assignment.push(assgin);
                                }
                                Operand::Move(ref p) => {
                                    let right = p.clone();
                                    let assgin = AssignStms::new(left, right, 1, span);
                                    current_node.assignment.push(assgin);
                                }
                                Operand::Constant(_) => {}
                            },
                            Rvalue::ShallowInitBox(ref x, _) => {
                                if self.nodes[left_local].sons.contains_key(&0) == false {
                                    let mut node = Node::new(left_local, self.nodes.len());
                                    let mut node1 = Node::new(left_local, self.nodes.len() + 1);
                                    let mut node2 = Node::new(left_local, self.nodes.len() + 2);
                                    node.sons.insert(0, node1.local);
                                    node.field_info.push(0);
                                    node1.sons.insert(0, node2.local);
                                    node1.field_info.push(0);
                                    node1.field_info.push(0);
                                    node2.field_info.push(0);
                                    node2.field_info.push(0);
                                    node2.field_info.push(0);
                                    self.nodes[left_local].sons.insert(0, node.local);
                                    self.nodes.push(node);
                                    self.nodes.push(node1);
                                    self.nodes.push(node2);
                                }
                                match x {
                                    Operand::Copy(ref p) => {
                                        let right = p.clone();
                                        let assgin = AssignStms::new(left, right, 2, span);
                                        current_node.assignment.push(assgin);
                                    }
                                    Operand::Move(ref p) => {
                                        let right = p.clone();
                                        let assgin = AssignStms::new(left, right, 2, span);
                                        current_node.assignment.push(assgin);
                                    }
                                    Operand::Constant(_) => {}
                                }
                            }
                            Rvalue::Discriminant(ref p) => {
                                let right = p.clone();
                                let assgin = AssignStms::new(left, right, 3, span);
                                current_node.assignment.push(assgin);
                            }
                            Rvalue::Aggregate(_, ref x) => {
                                for each_x in x {
                                    match each_x {
                                        Operand::Copy(ref p) => {
                                            let right = p.clone();
                                            let assgin = AssignStms::new(left, right, 0, span);
                                            current_node.assignment.push(assgin);
                                        }
                                        Operand::Move(ref p) => {
                                            let right = p.clone();
                                            let assgin = AssignStms::new(left, right, 0, span);
                                            current_node.assignment.push(assgin);
                                        }
                                        Operand::Constant(_) => {}
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                }

                //handle terminator statements
                match terminator.as_ref().unwrap().kind {
                    TerminatorKind::Goto { ref target } => {
                        current_node.push(target.as_usize());
                    }
                    TerminatorKind::SwitchInt {
                        discr: _,
                        ref targets,
                    } => {
                        current_node.switch_stmts.push(terminator.clone().unwrap());
                        for (_, ref target) in targets.iter() {
                            current_node.push(target.as_usize());
                        }
                        current_node.push(targets.otherwise().as_usize());
                    }
                    TerminatorKind::Return => {}

                    TerminatorKind::Unreachable => {}
                    TerminatorKind::Drop {
                        place: _,
                        ref target,
                        ref unwind,
                        replace:_,
                    } => {
                        current_node.push(target.as_usize());
                        if let UnwindAction::Cleanup(bb) = unwind {
                            current_node.push(bb.index());
                        }
                    }
                    TerminatorKind::Call {
                        func: _,
                        args: _,
                        destination: _,
                        ref target,
                        fn_span: _,
                        unwind,
                        call_source:_,
                    } => {
                        if let Some(tt) = target {
                            current_node.push(tt.as_usize());
                        }
                        if let UnwindAction::Cleanup(bb) = unwind {
                            current_node.push(bb.as_usize());
                        }
                        current_node.calls.push(terminator.clone().unwrap());
                    }
                    TerminatorKind::Assert {
                        cond: _,
                        expected: _,
                        msg: _,
                        ref target,
                        unwind,
                    } => {
                        current_node.push(target.as_usize());
                        if let UnwindAction::Cleanup(bb) = unwind {
                            current_node.push(bb.as_usize());
                        }
                    }
                    TerminatorKind::Yield {
                        value: _,
                        ref resume,
                        resume_arg: _,
                        ref drop,
                    } => {
                        current_node.push(resume.as_usize());
                        if let Some(target) = drop {
                            current_node.push(target.as_usize());
                        }
                    }
                    TerminatorKind::FalseEdge {
                        ref real_target,
                        imaginary_target: _,
                    } => {
                        current_node.push(real_target.as_usize());
                    }
                    TerminatorKind::FalseUnwind {
                        ref real_target,
                        unwind: _,
                    } => {
                        current_node.push(real_target.as_usize());
                    }
                    TerminatorKind::InlineAsm {
                        template: _,
                        operands: _,
                        options: _,
                        line_spans: _,
                        ref destination,
                        unwind,
                    } => {
                        if let Some(target) = destination {
                            current_node.push(target.as_usize());
                        }
                        if let UnwindAction::Cleanup(bb) = unwind {
                            current_node.push(bb.as_usize());
                        }
                    }
                    TerminatorKind::UnwindResume => {}
                    TerminatorKind::UnwindTerminate(_) => {}
                    TerminatorKind::CoroutineDrop => {}
                }
                self.blocks.push(current_node);
            }
        }
    }

    pub fn debuginfo(&self) {
        // println!("Assignments: ");
        // for i in &self.blocks {
        //     for j in i.assignment.clone() {
        //         let l = j.left;
        //         let r = j.right;
        //         println!(
        //             "{:?}, {:?},span: {:?}",
        //             l,
        //             r,
        //             j.span
        //         );
        //     }
        // }

        // println!("Blocks:");
        // for i in &self.blocks {
        //     println!("{:?}", i);
        // }

        println!("Nodes:");
        for i in &self.nodes {
            println!("{:?}", i);
        }

        // println!("Fatherblocks:");
        // println!("{:?}", &self.father_block);
    }

    pub fn tarjan(
        &mut self,
        index: usize,
        stack: &mut Vec<usize>,
        instack: &mut FxHashSet<usize>,
        dfn: &mut Vec<usize>,
        low: &mut Vec<usize>,
    ) {
        dfn[index] = self.count;
        low[index] = self.count;
        self.count += 1;
        instack.insert(index);
        stack.push(index);
        let out_set = self.blocks[index].next.clone();
        for i in out_set {
            let target = i;
            if dfn[target] == 0 {
                self.tarjan(target, stack, instack, dfn, low);
                low[index] = min(low[index], low[target]);
            } else {
                if instack.contains(&target) {
                    low[index] = min(low[index], dfn[target]);
                }
            }
        }
        // generate SCC
        if dfn[index] == low[index] {
            loop {
                let top = stack.pop().unwrap();
                self.father_block[top] = index;
                instack.remove(&top);
                if index == top {
                    break;
                }
                let top_node = self.blocks[top].next.clone();
                for i in top_node {
                    self.blocks[index].next.insert(i);
                }
                self.blocks[index].sub_blocks.push(top);
                for i in self.blocks[top].sub_blocks.clone() {
                    self.blocks[index].sub_blocks.push(i);
                }
            }
            self.blocks[index].sub_blocks.reverse();
            //remove the out nodes which is in the current SCC
            let mut remove_list = Vec::new();
            for i in self.blocks[index].next.iter() {
                if self.father_block[*i] == index {
                    remove_list.push(*i);
                }
            }
            for i in remove_list {
                self.blocks[index].next.remove(&i);
            }
        }
    }

    // handle SCC
    pub fn solve_scc(&mut self) {
        let mut stack = Vec::<usize>::new();
        let mut instack = FxHashSet::<usize>::default();
        let mut dfn = vec![0 as usize; self.blocks.len()];
        let mut low = vec![0 as usize; self.blocks.len()];
        self.tarjan(0, &mut stack, &mut instack, &mut dfn, &mut low);
    }

    pub fn alias_intra(
        &mut self,
        bb_index: usize,
        move_set: &mut FxHashSet<usize>,
        flow_sensitive: bool,
    ) {
        for stmt in self.blocks[bb_index].const_value.clone() {
            self.constant_bool.insert(stmt.0, stmt.1);
        }
        let current_block = self.blocks[bb_index].clone();

        for i in current_block.assignment {
            let l_node_ref =
                self.handle_projection(false, i.left.local.as_usize(), i.left.clone());
            let r_node_ref =
                self.handle_projection(true, i.right.local.as_usize(), i.right.clone());

            //println!("stm: {:?}, l_p: {:?}, r_p: {:?}", i, l_node_ref, r_node_ref);

            // match stms
            if i.atype == 3 {
                if r_node_ref.len() > 1 {
                    panic!("match statement r_node_ref's size is bigger than one!");
                }
                let mut v = PointSet::new();
                v.add_object(r_node_ref[0]);

                for node in l_node_ref {
                    v.add_node(node);
                    self.nodes[node].point_to.inner = Rc::clone(&v.inner);
                }
                //self.nodes[l_node_ref].point_to = Rc::new(RefCell::new(vec![r _node_ref]));
                continue;
            }

            //Box::new
            if i.atype == 2 {
                let _ = l_node_ref.clone()
                    .into_iter()
                    .map(|l| self.nodes[l].sons.get(&0).unwrap() + 2);
                //l_node_ref = self.nodes[l_node_ref].sons.get(&0).unwrap() + 2;
            }

            self.merge_alias(
                move_set,
                l_node_ref,
                r_node_ref,
                flow_sensitive,
            );

            //self.debuginfo();
        }
    }

    pub fn alias_inter(
        &mut self,
        bb_index: usize,
        move_set: &mut FxHashSet<usize>,
        func_map: &mut FuncMap,
        flow_sensitive: bool,
    ) {
        let current_block = self.blocks[bb_index].clone();
        for call in current_block.calls {
            if let TerminatorKind::Call {
                ref func,
                ref args,
                ref destination,
                target: _,
                fn_span: _,
                unwind: _,
                call_source: _,
            } = call.kind
            {
                if let Operand::Constant(ref constant) = func {
                    let mut merge_vec = Vec::new();

                    //新建一个临时的return节点，用于后面的merge
                    let ret_node = Node::new(self.nodes.len(),self.nodes.len());
                    let ret_index = ret_node.index;
                    merge_vec.push(ret_index);
                    self.nodes.push(ret_node);
                    

                    for arg in args {
                        match arg {
                            Operand::Copy(ref p) => {
                                merge_vec.push(p.local.as_usize());
                            }
                            Operand::Move(ref p) => {
                                merge_vec.push(p.local.as_usize());
                            }
                            Operand::Constant(_) => {
                                merge_vec.push(0);
                            }
                        }
                    }
                    //if let TyKind::FnDef(ref target_id, _) = constant.literal.ty().kind() {
                    if let TyKind::FnDef(ref target_id, _) = constant.const_.ty().kind() {
                        if self.tcx.is_mir_available(*target_id) {
                            // todo, 函数图，考虑递归如何处理
                            if func_map.map.contains_key(&target_id.index.as_usize()) {
                                let rr_nodes = func_map.map.get(&target_id.index.as_usize()).unwrap();
                                self.inter_merge((*rr_nodes).nodes.clone(), merge_vec, flow_sensitive);
                                self.merge_alias(move_set, vec![destination.local.as_usize()], vec![ret_index], flow_sensitive);
                            } else {
                                if func_map.set.contains(&target_id.index.as_usize()) {
                                    continue;
                                }
                                println!("@@@@@@@@@@@");
                                self.debuginfo();
                                println!("@@@@@@@@@@@");
                                func_map.set.insert(target_id.index.as_usize());
                                //let func_body = self.tcx.optimized_mir(*target_id);
                                let mut rchecker = RCheck::new(self.tcx, *target_id);
                                rchecker.analysis();
                                rchecker.check(0, self.tcx, func_map);
                                let rr_nodes = rchecker.return_results.clone();
                                self.inter_merge(rr_nodes.clone().nodes, merge_vec, flow_sensitive);
                                self.merge_alias(move_set, vec![destination.local.as_usize()], vec![ret_index], flow_sensitive);
                                println!("###########");
                                self.debuginfo();
                                println!("###########");
                                func_map
                                    .map
                                    .insert(target_id.index.as_usize(), rr_nodes);
                            }
                        } else {
                            // ?todo
                            // let mut right_set = Vec::new();
                            // for right_local in &merge_vec {
                            //     right_set.push(*right_local);
                            // }

                            // if right_set.len() == 1 {
                            //     self.merge_alias(move_set, vec![destination.local.as_usize()], right_set[0], flow_sensitive);
                            // }
                        }
                    }
                }
            }
        }
    }

    //处理projection，将a = *b, a = b.f 等复杂assignment统一转换成a = b的形式
    //返回一个Vec<usize>
    pub fn handle_projection(
        &mut self,
        is_right: bool,
        local: usize,
        place: Place<'tcx>,
    ) -> Vec<usize> {
        //let mut init_local = local;
        let mut current_local = VecDeque::new();
        current_local.push_back(local);

        //let mut ret_vec = Vec::new();
        for projection in place.projection {
            match projection {
                ProjectionElem::Deref => {
                    let mut ret_set: Vec<usize> = Vec::new();
                    while !current_local.is_empty() {
                        let current = current_local.pop_back().unwrap();

                        let point_set = &self.nodes[current].point_to;

                        let iter = point_set.inner.borrow().objects.clone();
                        for object in iter {
                            if self.nodes[object].deref == None {
                                let mut node = Node::new(self.nodes.len(), self.nodes.len());
                                node.kind = 1;
                                self.nodes[object].deref = Some(node.index);
                                self.nodes.push(node);
                            }
                            ret_set.push(self.nodes[object].deref.unwrap());
                        }
                    }
                    current_local.extend(ret_set);
                }

                ProjectionElem::Field(field, ty) => {
                    let mut ret_set: Vec<usize> = Vec::new();
                    while !current_local.is_empty() {
                        let current = current_local.pop_back().unwrap();
                        let index = field.as_usize();

                        let point_set = &self.nodes[current].point_to;
                        let iter = point_set.inner.borrow().objects.clone();

                        for object in iter {
                            if !self.nodes[object].sons.contains_key(&index) {
                                let mut node = Node::new(self.nodes.len(), self.nodes.len());
                                node.kind = kind(ty);
                                // !下面两行不知道做啥的
                                node.field_info = self.nodes[object].field_info.clone();
                                node.field_info.push(index);

                                node.father = object;
                                node.son_index = Some(index);
                                self.nodes[object].sons.insert(index, node.local);
                                self.nodes.push(node);
                            }
                            ret_set.push(*self.nodes[object].sons.get(&index).unwrap());
                        }
                    }
                    current_local.extend(ret_set);
                }
                _ => {}
            }
        }
        return current_local.into_iter().collect();
    }

    pub fn base_assign(&mut self, mut left: Vec<usize>, right: Vec<usize>, flow_sensitive: bool) {
        if flow_sensitive {
            self.multi_union_set(right.clone());
            for l_node in left {
                (*self.nodes[l_node].point_to.inner).borrow_mut().nodes.remove(&l_node);
                (*self.nodes[right[0]].point_to.inner).borrow_mut().nodes.insert(l_node);
                self.nodes[l_node].point_to.inner = Rc::clone(&self.nodes[right[0]].point_to.inner);
            }
        } else {
            left.extend(right);
            self.multi_union_set(left);
        }
    }

    pub fn merge_alias(
        &mut self,
        move_set: &mut FxHashSet<usize>,
        left_ssa: Vec<usize>,
        right_ssa: Vec<usize>,
        flow_sensitive: bool,
    ) {
        self.base_assign(left_ssa.clone(), right_ssa.clone(), flow_sensitive);

        //同步修改子节点的指向情况
        for r_node in right_ssa {
            for l_node in &left_ssa {
                let son_num = std::cmp::max(self.nodes[r_node].sons.len(), self.nodes[*l_node].sons.len());

                for son_index in 0..son_num {
                    if !self.nodes[*l_node].sons.contains_key(&son_index) {
                        let mut node = Node::new(self.nodes.len(), self.nodes.len());
                        node.father = node.index;
                        node.son_index = Some(son_index);
                        self.nodes[*l_node].sons.insert(son_index, node.index);
                        self.nodes.push(node);               
                    }
                    if !self.nodes[r_node].sons.contains_key(&son_index) {
                        let mut node = Node::new(self.nodes.len(), self.nodes.len());
                        node.father = node.index;
                        node.son_index = Some(son_index);
                        self.nodes[r_node].sons.insert(son_index, node.index);
                        self.nodes.push(node);                
                    }
                    let l_son = *self.nodes[*l_node].sons.get(&son_index).unwrap();
                    let r_son = *self.nodes[r_node].sons.get(&son_index).unwrap();
                    self.base_assign(vec![l_son], vec![r_son], flow_sensitive)
                }
            }
        }
    }

    pub fn inter_merge(&mut self, return_nodes: Vec<Node>, arg_vec: Vec<usize>, flow_sensitive: bool) {
        if return_nodes.len() != arg_vec.len() {
            panic!("return_nodes.len() != arg_vec.len() !");
        }
        //补齐域节点
        for index in 0..arg_vec.len() {
            for son_index in 0..return_nodes[index].sons.len() {
                if !self.nodes[arg_vec[index]].sons.contains_key(&son_index) {
                    let mut node = Node::new(
                        self.nodes.len(),
                        self.nodes.len(),
                    );
                    node.father = index;
                    node.son_index = Some(son_index);
                    self.nodes[index]
                        .sons
                        .insert(son_index, node.index);
                    self.nodes.push(node);
                }
            }
        }

        let mut return_map: HashMap<usize, Node>  = HashMap::new();
        for r_node in return_nodes.clone() {
            return_map.insert(r_node.index, r_node);
        }
        println!("return_map:");
        for i in return_map.clone() {
            println!("{:?}", i);
        }
        let mut align_map: HashMap<usize, Node> = HashMap::new();

        
        //对齐index
        for (_,  r_node) in return_map.clone() {
            let father_node = r_node.father;
            let son_node = r_node.son_index;
            let mut t_node = r_node.clone();
        
            //对齐merge_nodes和return_result的每个Node的index
            if let Some(s) = son_node {
                t_node.index = *self.nodes[arg_vec[father_node]].sons.get(&s).unwrap();
                // r_node.borrow_mut().index =
                //     *self.nodes[arg_vec[father_node]].sons.get(&s).unwrap();
                //     // *self.nodes[father_node].sons.get(&s).unwrap();
            }
            else {
                t_node.index = self.nodes[arg_vec[father_node]].index;
                // r_node.borrow_mut().index =
                //      self.nodes[arg_vec[father_node]].index;
            }
            //让merge_vec与point_vec的各项index对齐
            
            let merge_set = t_node.point_to.inner.clone();

            let align_set: HashSet<usize> = merge_set.borrow().clone().objects;
            let ret_set: HashSet<usize> = align_set.iter().map(|x| {
                if let  Some(f) = return_map.get(x) {
                    let f_index = f.father;
                    let s_index = return_map.get(x).unwrap().son_index;
                    if let Some(s) = s_index {
                        *self.nodes[arg_vec[f_index]].sons.get(&s).unwrap()
                        
                    }
                    else {
                        self.nodes[arg_vec[f_index]].index
                    }
                }
                else {
                    *x
                }
            }).collect();
            let mut trans_set = HashSet::new();
            for i in ret_set {
                let v = &self.nodes[i].point_to.inner;
                trans_set.extend(v.borrow().clone().objects);
            }
            //println!("we are here!!!!!!!!");
            (*t_node.point_to.inner).borrow_mut().objects = trans_set.clone();
        
            align_map.insert(t_node.index, t_node);
        }
        return_map = align_map.clone();
        
        //转换object的指针

        //识别节点别名
        let mut alias_map: HashMap<usize, Vec<usize>> = HashMap::new();
        for (i, n1) in return_map.clone() {
            for (j, n2) in return_map.clone() {
                if i == j || !Rc::ptr_eq(&n1.point_to.inner, &n2.point_to.inner) {
                    continue;
                }
                if alias_map.contains_key(&i) {
                    let mut v = alias_map.get(&i).unwrap().clone();
                    v.push(j);
                    alias_map.insert(i, v);
                } else {
                    alias_map.insert(i, vec![j]);
                }
            }
        }
        println!("return_map:");
        for i in return_map.clone() {
            println!("{:?}", i);
        }
        
        let mut used_map:HashSet<usize> = HashSet::new();
        //合并节点
        for (m_index, m_node) in return_map {
            if used_map.contains(&m_index) {continue;}

            let extend_v = m_node.point_to.inner.borrow().clone().objects;
            if extend_v.is_empty() {
                //Objects为空说明是流敏感，需要指向一个新的Obeject, 用于代表当前上下文的Object

                let node = Node::new(
                    self.nodes.len(),
                    self.nodes.len(),
                );
                if let Some(v) = alias_map.get(&m_index) {
                    let mut alias_vec = v.clone();
                    alias_vec.push(m_index);
                    let mut new_set = PointSet::new();
                    println!("alias_vec: {:?}", alias_vec);
                    new_set.add_object(node.index);
                    for alias in alias_vec {
                        new_set.add_node(alias);
                        (*self.nodes[alias].point_to.inner).borrow_mut().nodes.remove(&alias);
                        self.nodes[alias].point_to.inner = Rc::clone(&new_set.inner);
                        used_map.insert(alias);
                    }
                }
                self.nodes.push(node);
                
                

            }
            else {
                if let Some(v) = alias_map.get(&m_index) {
                    let mut alias_vec = v.clone();
                    alias_vec.push(m_index);
                    println!("alias_vec: {:?}", alias_vec);
                    for alias in alias_vec.clone() {
                        used_map.insert(alias);
                    }
                    self.multi_union_set(alias_vec);

                }
                let mut point_vec = self.nodes[m_index].point_to.inner.borrow().clone().objects;
                //extend_v.remove(&m_index);
                if flow_sensitive {
                    point_vec = extend_v.clone();
                }
                else {
                    point_vec.extend(extend_v);
                }
                (*self.nodes[m_index].point_to.inner).borrow_mut().objects = point_vec.clone();

            }

        }

    }


    // pub fn alias_analysis(&mut self, bb_index: usize, func_map: &mut FuncMap) {
    //     let current_block = self.blocks[self.father_block[bb_index]].clone();
    //     let mut move_set = FxHashSet::default();
    //     self.alias_intra(self.father_block[bb_index], &mut move_set);
    //     self.alias_inter(self.father_block[bb_index], &mut move_set, func_map);
    //     if current_block.sub_blocks.len() > 0 {
    //         for i in current_block.sub_blocks.clone() {
    //             self.alias_intra(i, &mut move_set);
    //             self.alias_inter(i, &mut move_set, func_map);
    //         }
    //     }
    // }

    // pub fn union_set(&mut self, a: usize, b: usize) {
    //     //In the same alais set, return.
    //     if Rc::ptr_eq(&self.nodes[a].point_to, &self.nodes[b].point_to) {
    //         return;
    //     }
    //     //In the different set, merging them.
    //     let temp_set = self.nodes[a].point_to.borrow().clone();
    //     for i in temp_set {
    //         (*self.nodes[b].point_to).borrow_mut().push(i);
    //     }
    //     self.nodes[a].point_to = Rc::clone(&self.nodes[b].point_to);
    // }

    pub fn multi_union_set(&mut self, node_list: Vec<usize>) {
        let mut v: HashSet<usize> = HashSet::new();
        let mut n: HashSet<usize> = HashSet::new();
        for i in node_list.clone() {
            let point_set = self.nodes[i].point_to.inner.borrow().objects.clone();
            let node_set = self.nodes[i].point_to.inner.borrow().nodes.clone();
            v.extend(point_set);
            n.extend(node_set);
        }
        let mut point_set = PointSet::new();
        point_set.init_objects(v);
        point_set.init_nodes(n.clone());
        for i in n {
            self.nodes[i].point_to.inner = Rc::clone(&point_set.inner); 
        }
    }

    //将当前路径合并，实际合并的是return_result;  ！！！！上下文敏感！！！！
    pub fn merge_path(&mut self) {
        println!("-------------merge_path  start-----------");
        let arg_size = self.return_results.arg_size;
        //println!("--------arg_size: {:?}--------", arg_size);
        //let mut merge_nodes = Vec::<Node>::new();
        let mut merge_nodes: HashMap<usize, Node> = HashMap::new();
        //let mut merge_set = HashSet::<usize>::new();
        for index in 0..arg_size {
            //merge_nodes.push(self.nodes[index].clone());
            merge_nodes.insert(index, self.nodes[index].clone());
        }
        for (_, node) in merge_nodes.clone() {
            for (_son_index, son_local) in node.sons {
                merge_nodes.insert(son_local, self.nodes[son_local].clone());
                //merge_nodes.push(self.nodes[son_local].clone());
            }
        }
        //消除所有的局部变量
        for (_, node) in merge_nodes.clone() {
            let point_set = node.point_to.inner;
            let iter = (*point_set.borrow()).clone().objects;
            for object in iter {
                if !merge_nodes.contains_key(&object) {
                    (*point_set).borrow_mut().objects.remove(&object);
                }
            }

        }

        //首条路径
        if self.return_results.nodes.len() < arg_size {
            let mut temp_nodes = Vec::<Node>::new();
            for v in merge_nodes.values() {
                temp_nodes.push(v.clone());
            }
            self.return_results.nodes = temp_nodes;
            return;
        }

        //补齐域节点
        for index in 0..arg_size {
            for son_index in 0..merge_nodes.clone().get(&index).unwrap().sons.len() {
                if !self.return_results.nodes[index]
                    .sons
                    .contains_key(&son_index)
                {
                    let mut node = Node::new(
                        self.return_results.nodes.len(),
                        self.return_results.nodes.len(),
                    );
                    node.father = index;
                    node.son_index = Some(son_index);
                    self.return_results.nodes[index]
                        .sons
                        .insert(son_index, node.index);
                    self.return_results.nodes.push(node);
                }
            }
        }
        for (_, mut m_node) in merge_nodes.clone() {
            let father_node = m_node.father;
            let son_node = m_node.son_index;

            if !m_node.sons.is_empty() {
                //对齐merge_nodes和return_result的每个Node的index
                if let Some(s) = son_node {
                    m_node.borrow_mut().index =
                        *self.return_results.nodes[father_node].sons.get(&s).unwrap();
                }
                //让merge_vec与point_vec的各项index对齐
                //let mut point_vec = *self.return_results.nodes[father_node].point_to.borrow_mut();
                let merge_set = m_node.point_to.inner;
                let align_set = merge_set.borrow().clone().objects;

                let _ = align_set.iter().map(|x|{
                    let f_index = merge_nodes.get(x).unwrap().father;
                    let s_index = merge_nodes.get(x).unwrap().son_index;
                    if let Some(s) = s_index {
                        *self.return_results.nodes[f_index].sons.get(&s).unwrap()
                    }
                    else {
                        *x
                    }
                });
                
            }
        }

        //识别每个节点的别名
        let mut alias_map: HashMap<usize, Vec<usize>> = HashMap::new();
        for (i, n1) in merge_nodes.clone() {
            for (j, n2) in merge_nodes.clone() {
                if i == j || !Rc::ptr_eq(&n1.point_to.inner, &n2.point_to.inner) {
                    continue;
                }
                if alias_map.contains_key(&i) {
                    let mut v = alias_map.get(&i).unwrap().clone();
                    v.push(j);
                    alias_map.insert(i, v);
                } else {
                    alias_map.insert(i, vec![j]);
                }
            }
        }

        for (m_index, m_node) in merge_nodes.clone() {
            //有别名先合并
            if alias_map.contains_key(&m_index) {
                let node_list = alias_map.get(&m_index).unwrap();
                //self.multi_union_set(*v);
                let mut v: HashSet<usize> = HashSet::new();
                let mut n: HashSet<usize> = HashSet::new();
                for i in node_list.clone() {
                    let point_set = self.return_results.nodes[i].point_to.inner.borrow().objects.clone();
                    let node_set = self.return_results.nodes[i].point_to.inner.borrow().nodes.clone();
                    v.extend(point_set);
                    n.extend(node_set);
                }
                let mut point_set = PointSet::new();
                point_set.init_objects(v);

                for i in n {
                    self.return_results.nodes[i].point_to.inner = Rc::clone(&point_set.inner); 
                }
            }
            //合并每个节点
            let mut point_vec = self.return_results.nodes[m_index].point_to.inner.borrow().clone().objects;
            let extend_v = m_node.point_to.inner.borrow().clone().objects;
            point_vec.extend(extend_v);
            // let mut ref_point = self.return_results.nodes[m_index].point_to.inner;
            // let mut t = (*ref_point).borrow_mut();
            (*self.return_results.nodes[m_index].point_to.inner).borrow_mut().objects = point_vec.clone();

        }

    }
    // the core function of the safedrop.
    pub fn check(&mut self, bb_index: usize, tcx: TyCtxt<'tcx>, func_map: &mut FuncMap) {
        // !todo visit times
        // self.visit_times += 1;
        // if self.visit_times > 10000{
        //     return;
        // }
        let current_block = self.blocks[self.father_block[bb_index]].clone();
        let mut move_set = FxHashSet::default();
        let flow_sensitive = true;

        self.alias_intra(bb_index, &mut move_set, flow_sensitive);
        //self.debuginfo();
        self.alias_inter(bb_index, &mut move_set, func_map, flow_sensitive);

        if current_block.sub_blocks.len() > 0 {
            for i in current_block.sub_blocks.clone() {
                self.alias_intra(i, &mut move_set, flow_sensitive);
                self.alias_inter(i, &mut move_set, func_map, flow_sensitive);
            }
        }
        //println!("enter line:180");

        //finish the analysis for a path
        if current_block.next.len() == 0 {
            // merge the result.
            //let results_nodes = self.nodes.clone();
            self.merge_path();
            for r in self.return_results.nodes.clone() {
                println!("{:?}", r);
            }
           // println!("return_vec: {:?}", self.return_results);
            println!("-----------------merge_path end-------------------");

            //println!("@@@@@@@@@@@@@@@@@@@    {:?}    @@@@@@@@@@@@@@@@@", bb_index);
            // println!("current block: {:?}", current_block);
        }

        //return;
        //search for the next block to visit.
        let mut loop_flag = true;
        let mut ans_bool = 0;
        let mut s_target = 0;
        let mut discr_target = 0;
        let mut s_targets = None;
        //handle the SwitchInt statement.
        if current_block.switch_stmts.is_empty() == false && current_block.sub_blocks.is_empty() {
            if let TerminatorKind::SwitchInt {
                ref discr,
                ref targets,
            } = current_block.switch_stmts[0].clone().kind
            {
                if let Some(p) = discr.place() {
                    //  先不处理handle_projection的问题
                    let place = p.as_local().unwrap().as_usize();
                    //let place = self.handle_projection(false, p.local.as_usize(), tcx, p.clone());

                    if let Some(const_bool) = self.constant_bool.get(&self.nodes[place].alias[0]) {
                        loop_flag = false;
                        ans_bool = *const_bool;
                    }
                    if self.nodes[place].alias[0] != place {
                        discr_target = self.nodes[place].alias[0];
                        s_targets = Some(targets.clone());
                    }
                } else {
                    loop {
                        if let None = discr.constant() {
                            break;
                        }
                        let temp = discr.constant().unwrap().const_;
                        if let None = temp.try_to_scalar() {
                            break;
                        }
                        if let Err(_tmp) = temp.try_to_scalar().clone().unwrap().try_to_int() {
                            break;
                        }
                        let param_env = tcx.param_env(self.def_id);
                        if let Some(const_bool) = temp.try_eval_target_usize(tcx, param_env) {
                            loop_flag = false;
                            ans_bool = const_bool as usize;
                            break;
                        }
                        if let Some(const_bool) = temp.try_to_bool() {
                            loop_flag = false;
                            ans_bool = const_bool as usize;
                        }
                        break;
                    }
                }
                if !loop_flag {
                    for iter in targets.iter() {
                        if iter.0 as usize == ans_bool as usize {
                            s_target = iter.1.as_usize();
                            break;
                        }
                    }
                    if s_target == 0 {
                        let all_target = targets.all_targets();
                        if ans_bool as usize >= all_target.len() {
                            s_target = all_target[all_target.len() - 1].as_usize();
                        } else {
                            s_target = all_target[ans_bool as usize].as_usize();
                        }
                    }
                }
            }
        }
        // println!("enter line:260");
        // only one path
        if current_block.next.len() == 1 {
            for next_index in current_block.next {
                self.check(next_index, tcx, func_map);
            }
        } else {
            // fixed path since a constant switchInt value
            if loop_flag == false {
                self.check(s_target, tcx, func_map);
            } else {
                // Other cases in switchInt terminators
                if let Some(targets) = s_targets {
                    for iter in targets.iter() {
                        // if self.visit_times > 10000{
                        //     continue;
                        // }
                        let next_index = iter.1.as_usize();
                        let backup_nodes = self.nodes.clone();
                        let constant_record = self.constant_bool.clone();
                        self.constant_bool.insert(discr_target, iter.0 as usize);
                        self.check(next_index, tcx, func_map);
                        self.nodes = backup_nodes;
                        self.constant_bool = constant_record;
                    }
                    let all_targets = targets.all_targets();
                    let next_index = all_targets[all_targets.len() - 1].as_usize();
                    let backup_nodes = self.nodes.clone();
                    let constant_record = self.constant_bool.clone();
                    self.constant_bool.insert(discr_target, 99999 as usize);
                    self.check(next_index, tcx, func_map);
                    self.nodes = backup_nodes;
                    self.constant_bool = constant_record;
                } else {
                    //println!("enter line:297, current_block.next {:?}", &current_block.clone().next);
                    for i in current_block.clone().next {
                        //println!("enter line:298, current_block.next {:?}", &current_block.clone().next);
                        //println!("enter line:299, i = {:?}", i);
                        // if self.visit_times > 10000{
                        //     continue;
                        // }
                        let next_index = i;
                        let backup_nodes = self.nodes.clone();
                        let constant_record = self.constant_bool.clone();
                        self.check(next_index, tcx, func_map);
                        self.nodes = backup_nodes;
                        self.constant_bool = constant_record;
                    }
                }
            }
        }
        //self.debuginfo();
    }
}
pub fn kind<'tcx>(current_ty: Ty<'tcx>) -> usize {
    match current_ty.kind() {
        ty::RawPtr(..) => 1,
        ty::Ref(..) => 4,
        ty::Tuple(..) => 2,
        ty::Adt(ref adt_def, _) => {
            return 0;
            // if is_corner_adt(format!("{:?}", adt_def)){
            //     return 3;
            // }
            // else{
            //     return 0;
            // }
        }
        _ => 0,
    }
}
