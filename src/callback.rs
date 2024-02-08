extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;


use crate::analyzer::node::FuncMap;
use crate::analyzer::rcheck::RCheck;
use rustc_interface::interface;
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::LocalDefId;

pub struct RLockCallback;

impl rustc_driver::Callbacks for RLockCallback {
    fn after_analysis<'tcx>(
        &mut self,
        compiler: &rustc_interface::interface::Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> rustc_driver::Compilation {
        compiler.sess.parse_sess.dcx.abort_if_errors();
        queries.global_ctxt().unwrap().enter(|tcx| {
            self.pointer_test(compiler, tcx);
        });
        compiler.sess.parse_sess.dcx.abort_if_errors();
        rustc_driver::Compilation::Stop
    }
}

impl RLockCallback {
    fn pointer_test<'tcx>(&mut self, _compiler: &interface::Compiler, tcx: TyCtxt<'tcx>) {
        //let crate_name = tcx.crate_name(LOCAL_CRATE).to_string();
        //println!("{:?}", crate_name);
        let ids = tcx.mir_keys(());

        let fn_ids: Vec<LocalDefId> = ids
            .clone()
            .into_iter()
            .filter(|id| {
                let hir = tcx.hir();
                hir.body_owner_kind(*id).is_fn_or_closure()
            })
            .collect();

        let (entry_id, _) = if let Some((entry_def, x)) = tcx.entry_fn(()) {
            (entry_def, x)
        } else {
            let msg = "this tool only analysis on programs with a main function";
            panic!("{}", msg);
        };
        let mut r = RCheck::new(tcx, entry_id);
        r.analysis();
        
        r.solve_scc();
        let mut func_map = FuncMap::new();
        r.check(0, tcx, &mut func_map);
        r.debuginfo();
    }
}
