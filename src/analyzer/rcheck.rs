use std::marker::PhantomData;
use std::rc;

/*
1.首先进行初次的别名分析，构建每个阶段的node的对应的别名集合，
2.同时根据分析的每个阶段的每个线程所涉及的锁语句和赋值语句，按顺序构建ThreadBlock,
3.


*/
use super::node::{FuncMap, Node, ValuableNode, ReturnAssign, ReturnResults};
use rustc_hash::FxHashSet;
use rustc_middle::ty::TyKind;
use rustc_middle::{
    mir::{BasicBlock, Operand, Place, ProjectionElem, Rvalue, Statement, Terminator},
    ty::TyCtxt,
};
use rustc_span::{def_id::LocalDefId, Span};

//Valuable Statements, composed of lock/unlock stms or assignment stms.
#[derive(Debug, Clone)]
pub enum Stms {
    Assignment,
    LockStms,
}

#[derive(Debug, Clone)]
pub struct AssignStms<'tcx> {
    pub left: Place<'tcx>,
    pub right: Place<'tcx>,
    //pub atype: usize,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct LockStms {
    //lock-true, unlock-false.
    pub atype: bool,
    pub lock_id: usize,
}
#[derive(Debug, Clone)]
pub struct ThreadBlock {
    pub order: usize,
    pub thread_id: usize,
    pub inner_nodes: Vec<usize>,
    pub statements: Vec<Stms>,
}
impl ThreadBlock {
    pub fn new(order: usize, id: usize) -> Self {
        ThreadBlock {
            order,
            thread_id: id,
            inner_nodes: Vec::new(),
            statements: Vec::new(),
        }
    }
}

pub struct RCheck<'tcx> {
    pub def_id: LocalDefId,
    pub tcx: TyCtxt<'tcx>,
    pub stage_nodes: Vec<Vec<Node>>,
    pub valuables: Vec<ValuableNode>,
    pub thread_blocks: Vec<ThreadBlock>,
    pub nodes: Vec<Node>,
    pub return_results: ReturnResults,
}

impl<'tcx> RCheck<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> Self {
        let body = tcx.optimized_mir(def_id);
        let arg_size = &body.arg_count;
        RCheck {
            def_id,
            tcx,
            stage_nodes: Vec::new(),
            valuables: Vec::new(),
            thread_blocks: Vec::new(),
            nodes: Vec::new(),
            return_results: ReturnResults::new(arg_size),
        }
    }
    pub fn analysis(&mut self) {
        if self.tcx.is_mir_available(self.def_id) {
            let body = self.tcx.optimized_mir(self.def_id);
            let locals = &body.local_decls;
            //let mut nodes: Vec<Node> =  Vec::new();
            for ld in 0..locals.len() {
                let mut node = Node::new(ld, ld);
                self.nodes.push(node);
            }

            let mut move_set = FxHashSet::default();
            let basicblocks = &body.basic_blocks;
            for i in 0..basicblocks.len() {
                let iter = BasicBlock::from(i);
                let terminator = basicblocks[iter].terminator.clone();
                println!("  BasicBlock: {:?}", iter);
                for statement in &basicblocks[iter].statements {
                    println!("      statement: {:?}", statement);

                    if let Statement::Assign(ref assign) = statement.kind {
                        let left_local = assign.0.local.as_usize();
                        let left = assign.0.clone();

                        match *assign.1 {
                            Rvalue::Use(ref x) => match x {
                                Operand::Copy(ref p) => {
                                    let right = p.clone();
                                    self.alias_intra(left, right, 0, &mut move_set);
                                }
                                Operand::Move(ref p) => {
                                    let right = p.clone();
                                    self.alias_intra(left, right, 1, &mut move_set);
                                }
                                Operand::Constant(ref constant) => {
                                    todo!();
                                }
                            },
                            Rvalue::Ref(_, _, ref p) => {
                                let right = p.clone();
                                self.alias_intra(left, right, 1, &mut move_set);
                            }
                            Rvalue::AddressOf(_, ref p) => {
                                let right = p.clone();
                                self.alias_intra(left, right, 1, &mut move_set);
                            }
                            Rvalue::Cast(_, ref x, _) => match x {
                                Operand::Copy(ref p) => {
                                    let right = p.clone();
                                    self.alias_intra(left, right, 0, &mut move_set);
                                }
                                Operand::Move(ref p) => {
                                    let right = p.clone();
                                    self.alias_intra(left, right, 1, &mut move_set);
                                }
                                Operand::Constant(_) => todo!(),
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
                                        self.alias_intra(left, right, 2, &mut move_set);
                                    }
                                    Operand::Move(ref p) => {
                                        let right = p.clone();
                                        self.alias_intra(left, right, 2, &mut move_set);
                                    }
                                    Operand::Constant(_) => {}
                                }
                            }
                            Rvalue::Discriminant(ref p) => {
                                let right = p.clone();
                                self.alias_intra(left, right, 3, &mut move_set);
                            }
                            Rvalue::Aggregate(_, ref x) => {
                                for each_x in x {
                                    match each_x {
                                        Operand::Copy(ref p) => {
                                            let right = p.clone();
                                            self.alias_intra(left, right, 0, &mut move_set);
                                        }
                                        Operand::Move(ref p) => {
                                            let right = p.clone();
                                            self.alias_intra(left, right, 0, &mut move_set);
                                        }
                                        Operand::Constant(_) => todo!(),
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                }

                //handle terminator statements
                match terminator.kind {
                    Terminator::Goto { ref target } => {}
                }
            }
        }
    }
    pub fn alias_intra(
        &mut self,
        left: Place<'tcx>,
        right: Place<'tcx>,
        atype: usize,
        move_set: &mut FxHashSet<usize>,
    ) {
        let mut l_node_ref = self.handle_projection(false, left.local.as_usize(), left.clone());
        let r_node_ref = self.handle_projection(true, right.local.as_usize(), right.clone());

        if atype == 3 {
            self.nodes[l_node_ref].alias[0] = r_node_ref;
            return;
        }

        if atype == 2 {
            l_node_ref = *self.nodes[l_node_ref].sons.get(&0).unwrap() + 2;
        }

        merge_alias(move_set, l_node_ref, r_node_ref, &mut self.nodes);
    }

    pub fn alias_inter(
        &mut self,
        call: Terminator<'tcx>,
        move_set: &mut FxHashSet<usize>,
        func_map: &mut FuncMap,
    ) {
        if let Terminator::Call {
            ref func,
            ref args,
            ref destination,
            target: _,
            cleanup: _,
            from_hir_call: _,
            fn_span: _,
        } = call
        {
            if let Operand::Constant(ref constant) = func {
                let left_local = self.handle_projection(
                    false,
                    destination.local.as_usize(),
                    destination.clone(),
                );
                let mut merge_vec = Vec::new();
                merge_vec.push(left_local);

                for arg in args {
                    match arg {
                        Operand::Copy(ref p) => {
                            let right_local =
                                self.handle_projection(true, p.local.as_usize(), p.clone());
                            merge_vec.push(right_local);
                        }
                        Operand::Move(ref p) => {
                            let right_local =
                                self.handle_projection(true, p.local.as_usize(), p.clone());
                            merge_vec.push(right_local);
                        }
                        Operand::Constant(_) => {
                            merge_vec.push(0);
                        }
                    }
                    if let TyKind::FnDef(ref target_id, _) = constant.literal.ty().kind() {
                        if self.tcx.is_mir_available(*target_id) {
                            if func_map.map.contains_key(&target_id.index.as_usize()) {
                                let assignments =
                                    func_map.map.get(&target_id.index.as_usize()).unwrap();
                                for assign in assignments.assignments.iter() {
                                    if !assign.valuable() {
                                        continue;
                                    }
                                    self.merge(move_set, &mut self.nodes, assign, &merge_vec);
                                }
                            } else {
                                if func_map.set.contains(&target_id.index.as_usize()) {
                                    continue;
                                }
                                func_map.set.insert(target_id.index.as_usize());
                                let func_body = self.tcx.optimized_mir(*target_id);
                                let mut rchecker = RCheck::new(self.tcx, *target_id);
                                rchecker.analysis();
                                let return_result = rchecker.return_results.clone();
                                for assign in return_result.assignments.iter() {
                                    inter_merge(move_set, &mut self.nodes, assign, &merge_vec);
                                }

                                func_map.map.insert(target_id.index.as_usize(), return_result);
                            }
                        }
                        else {
                            let mut right_set = Vec::new();
                            for right_local in &merge_vec {
                                right_set.push(*right_local);
                            }

                            if right_set.len() == 1 {
                                inter_merge(move_set, left_local, right_set[0], &mut self.nodes);
                            }
                        }
                    }
                }
            }
        }
    }

    pub fn handle_projection(&mut self, is_right: bool, local: usize, place: Place<'tcx>) -> usize {
        let mut init_local = local;
        let mut current_local = local;
        for projection in place.projection {
            match projection {
                ProjectionElem::Deref => {
                    if current_local == self.nodes[current_local].alias[0]
                        && self.nodes[current_local].is_ref() == false
                    {
                        let mut node = Node::new(self.nodes.len(), self.nodes.len());
                        self.nodes[current_local].alias[0] = self.nodes.len();
                        self.nodes.push(node);
                    }
                    current_local = self.nodes[current_local].alias[0];
                    init_local = self.nodes[current_local].index;
                }
                ProjectionElem::Field(field, ty) => {
                    let index = field.as_usize();
                    if is_right && self.nodes[current_local].alias[0] != current_local {
                        current_local = self.nodes[current_local].alias[0];
                        init_local = self.nodes[current_local].index;
                    }
                    if self.nodes[current_local].sons.contains_key(&index) == false {
                        let mut node = Node::new(init_local, self.nodes.len());
                        node.field_info = self.nodes[current_local].field_info.clone();
                        node.field_info.push(index);
                        self.nodes[current_local].sons.insert(index, node.local);
                        self.nodes.push(node);
                    }
                    current_local = *self.nodes[current_local].sons.get(&index).unwrap();
                }
                _ => {}
            }
        }
        return current_local;
    }
}
pub fn merge_alias(
    move_set: &mut FxHashSet<usize>,
    left_ssa: usize,
    right_ssa: usize,
    nodes: &mut Vec<Node>,
) {
    if nodes[left_ssa].index == nodes[right_ssa].index {
        return;
    }
    if move_set.contains(&left_ssa) {
        let mut alias_clone = nodes[right_ssa].alias.clone();
        nodes[left_ssa].alias.append(&mut alias_clone);
    } else {
        move_set.insert(left_ssa);
        nodes[left_ssa].alias = nodes[right_ssa].alias.clone();
    }
    for son in nodes[right_ssa].sons.clone().into_iter() {
        if nodes[left_ssa].sons.contains_key(&son.0) == false {
            let mut node = Node::new(nodes[left_ssa].index, nodes.len());
            node.kind = nodes[son.1].kind;
            node.alive = nodes[left_ssa].alive;
            node.field_info = nodes[left_ssa].field_info.clone();
            node.field_info.push(son.0);
            nodes[left_ssa].sons.insert(son.0, node.local);
            nodes.push(node);
        }
        let l_son = *(nodes[left_ssa].sons.get(&son.0).unwrap());
        merge_alias(move_set, l_son, son.1, nodes);
    }
}
//inter-procedure instruction to merge alias.
pub fn inter_merge(
    move_set: &mut FxHashSet<usize>,
    nodes: &mut Vec<Node>,
    assign: &ReturnAssign,
    arg_vec: &Vec<usize>,
) {
    if assign.left_index >= arg_vec.len() {
        println!("vector warning!");
        return;
    }
    if assign.right_index >= arg_vec.len() {
        println!("vector warning!");
        return;
    }
    let left_init = arg_vec[assign.left_index];
    let mut right_init = arg_vec[assign.right_index];
    let mut left_ssa = left_init;
    let mut right_ssa = right_init;
    for index in assign.left.iter() {
        if nodes[left_ssa].sons.contains_key(&index) == false {
            let mut node = Node::new(left_init, nodes.len());

            node.field_info = nodes[left_ssa].field_info.clone();
            node.field_info.push(*index);
            nodes[left_ssa].sons.insert(*index, node.local);
            nodes.push(node);
        }
        left_ssa = *nodes[left_ssa].sons.get(&index).unwrap();
    }
    for index in assign.right.iter() {
        if nodes[right_ssa].alias[0] != right_ssa {
            right_ssa = nodes[right_ssa].alias[0];
            right_init = nodes[right_ssa].index;
        }
        if nodes[right_ssa].sons.contains_key(&index) == false {
            let mut node = Node::new(right_init, nodes.len());
            node.field_info = nodes[right_ssa].field_info.clone();
            node.field_info.push(*index);
            nodes[right_ssa].sons.insert(*index, node.local);
            nodes.push(node);
        }
        right_ssa = *nodes[right_ssa].sons.get(&index).unwrap();
    }
    merge_alias(move_set, left_ssa, right_ssa, nodes);
}
