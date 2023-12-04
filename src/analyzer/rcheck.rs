use std::marker::PhantomData;

/*
1.首先进行初次的别名分析，构建每个阶段的node的对应的别名集合，
2.同时根据分析的每个阶段的每个线程所涉及的锁语句和赋值语句，按顺序构建ThreadBlock,
3.


*/
use super::node::{Node, ValuableNode};
use rustc_middle::{mir::{Place, BasicBlock}, ty::TyCtxt};
use rustc_span::{Span, def_id::LocalDefId};


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
    pub fn new(order: usize, id: usize) -> Self{
        ThreadBlock { order, thread_id: id, inner_nodes: Vec::new(), statements: Vec::new() }
    }
}


pub struct RCheck<'tcx>{
    tcx: TyCtxt<'tcx>,
    stage_nodes: Vec<Vec<Node>>,
    valuables: Vec<ValuableNode>,
    thread_blocks: Vec<ThreadBlock>,

}

impl<'tcx> RCheck<'tcx> {
    pub fn new(def_id: LocalDefId, tcx: TyCtxt<'tcx>) {
        if tcx.is_mir_available(def_id) {
            let body = tcx.optimized_mir(def_id);
            
            let basicblocks = &body.basic_blocks;
            for i in 0..basicblocks.len() {
                let iter = BasicBlock::from(i);
                println!("  BasicBlock: {:?}", iter);
                for statement in &basicblocks[iter].statements {
                    println!("      statement: {:?}", statement);
                }
            }
        }
    }
}
