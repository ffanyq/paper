extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;

use crate::analyzer::callgraph::*;
use crate::analyzer::rcheck::RCheck;
use crate::analyzer::visitor;
use crate::analyzer::visitor::*;
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_interface::interface;
use rustc_middle::mir::mono::MonoItem;
use rustc_middle::ty::{Instance, ParamEnv, TyCtxt};
use rustc_span::def_id::LocalDefId;

pub struct RLockCallback;

impl rustc_driver::Callbacks for RLockCallback {
    fn after_analysis<'tcx>(
        &mut self,
        compiler: &rustc_interface::interface::Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> rustc_driver::Compilation {

        compiler.sess.abort_if_errors();
        queries.global_ctxt().unwrap().enter(|tcx| {
            self.pointer_test(compiler, tcx);
        });
        compiler.sess.abort_if_errors();
        rustc_driver::Compilation::Stop
    }
}

impl RLockCallback {
    fn call_graph_test<'tcx>(&mut self, _compiler: &interface::Compiler, tcx: TyCtxt<'tcx>) {
        // Skip crates by names (white or black list).
        //let crate_name = tcx.crate_name(LOCAL_CRATE).to_string();

        if tcx.sess.opts.unstable_opts.no_codegen || !tcx.sess.opts.output_types.should_codegen() {
            return;
        }

        let cgus = tcx.collect_and_partition_mono_items(()).1;
        let instances: Vec<Instance<'tcx>> = cgus
            .iter()
            .flat_map(|cgu| {
                cgu.items().iter().filter_map(|(mono_item, _)| {
                    if let MonoItem::Fn(instance) = mono_item {
                        Some(*instance)
                    } else {
                        None
                    }
                })
            })
            .collect();

        let mut callgraph = CallGraph::new();
        let param_env = ParamEnv::reveal_all();
        callgraph.analyze(instances.clone(), tcx, param_env);

        callgraph.dot();
    }

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

        for i in fn_ids {
            println!("{:?}", i);
            RCheck::new(i, tcx);

            //let visitor = visitor::TestVistor::new(tcx, i);
            //visitor.analysis();
        }
    }
}
