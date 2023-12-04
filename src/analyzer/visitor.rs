extern crate rustc_span;
use rustc_middle::mir::visit::{PlaceContext, Visitor};
use rustc_middle::mir::{
    Body, HasLocalDecls, Local, LocalDecl, LocalKind, Location, Operand, Rvalue, Statement,
    StatementKind, Terminator, TerminatorKind,
};
use rustc_middle::ty::{self, EarlyBinder, Instance, ParamEnv, TyCtxt, TyKind};
use rustc_span::def_id::LocalDefId;
use std::collections::HashSet;
pub struct TestVistor<'tcx> {
    tcx: TyCtxt<'tcx>,
    id: LocalDefId,
}
impl<'tcx> TestVistor<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, id: LocalDefId) -> Self {
        TestVistor { tcx: tcx, id: id }
    }
    pub fn analysis(&self) {
        let body = self.tcx.optimized_mir(self.id);
        let mut visitor = MyVisitor::new(self.tcx, body);
        visitor.visit_body(body);
    }
}
pub struct MyVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
}
impl<'a, 'tcx> HasLocalDecls<'tcx> for MyVisitor<'a, 'tcx> {
    fn local_decls(&self) -> &rustc_middle::mir::LocalDecls<'tcx> {
        self.body.local_decls()
    }
}
impl<'a, 'tcx> MyVisitor<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, body: &'a Body<'tcx>) -> Self {
        MyVisitor { tcx, body }
    }
}
impl<'a, 'tcx> Visitor<'tcx> for MyVisitor<'a, 'tcx> {
    // fn visit_statement(&mut self, statement: &Statement<'tcx>, _location: Location) {
    //     match &statement.kind {
    //         StatementKind::Assign(box (place, rvalue)) => {
    //             let ty = rvalue.ty(self, self.tcx);
    //             if ty.is_unsafe_ptr() {
    //                 println!("this is a unsafe ptr!, {:?}", statement.source_info.span);
    //             }
    //         }
    //         _ => {}
    //     }
    //     self.super_statement(statement, _location);
    // }

    fn visit_basic_block_data(&mut self,block:rustc_middle::mir::BasicBlock,data: &rustc_middle::mir::BasicBlockData<'tcx>,) {
        println!("index: {:?}, stms: {:?}", block, data);

        self.super_basic_block_data(block, data);
    }
}
