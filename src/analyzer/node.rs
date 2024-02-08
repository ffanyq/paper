use std::{cell::RefCell, collections::HashSet, rc::Rc};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_span::Span;
// #[derive(Debug, Clone)]
// pub struct ObjectNode {
//     pub node_list: Vec<usize>,
//     pub deref: i64,
//     pub filed: FxHashMap<usize, usize>,
// }
// impl ObjectNode {
//     pub fn new() -> Self {
//         ObjectNode { node_list: Vec::new(), deref: -1, filed: FxHashMap::default() }
//     }
// }
#[derive(Debug, Clone)]
pub struct PointInner {
    pub nodes: HashSet<usize>,
    pub objects: HashSet<usize>,
}

#[derive(Debug, Clone)]
pub struct PointSet {
    pub inner: Rc<RefCell<PointInner>>
}

impl PointSet {
    pub fn new() -> Self{
        let inner = PointInner {nodes: HashSet::new(), objects: HashSet::new()};
        PointSet {
            inner: Rc::new(RefCell::new(inner)), 
        }
    }

    pub fn add_node(&mut self, index: usize) {
        //let mut t = self.inner.borrow_mut();
        (*self.inner).borrow_mut().nodes.insert(index);
    }

    pub fn add_object(&mut self, index: usize) {
        //let mut t = *self.inner.borrow_mut();
        (*self.inner).borrow_mut().objects.insert(index);
    }

    pub fn init_objects(&mut self, v: HashSet<usize>) {
        //let mut t = *self.inner.borrow_mut();
        (*self.inner).borrow_mut().objects = v;
    }

    pub fn init_nodes(&mut self, n: HashSet<usize>) {
        //let mut t = *self.inner.borrow_mut();
        (*self.inner).borrow_mut().nodes = n;
    }


}
// impl PointSet {
//     pub fn new() {

//     }

// }
#[derive(Debug, Clone)]
pub struct Node {
    pub index: usize,
    pub local: usize,
    pub point_to: PointSet,
    pub deref: Option<usize>,
    pub alias: Vec<usize>,
    pub father: usize,
    pub son_index: Option<usize>,
    pub kind: usize,
    pub sons: FxHashMap<usize, usize>,
    pub field_info: Vec<usize>,
}

impl Node {
    pub fn new(index: usize, local: usize) -> Self {
        let mut temp = Vec::new();
        temp.push(local);
        let mut point_set = PointSet::new();
        point_set.add_node(index);
        point_set.add_object(index);
        Node {
            index,
            local,
            father: local,
            son_index: None,
            deref: None,
            point_to: point_set,
            alias: temp,
            kind: 0,
            sons: FxHashMap::default(),
            field_info: Vec::new(),
        }
    }
    pub fn is_tuple(&self) -> bool {
        return self.kind == 2;
    }

    pub fn is_ptr(&self) -> bool {
        return self.kind == 1 || self.kind == 4;
    }

    pub fn is_ref(&self) -> bool {
        return self.kind == 4;
    }
}
#[derive(Debug, Clone)]
pub struct ValuableNode {
    pub thread_id: usize,
    pub local: usize,
    pub is_rvalue: bool,
    pub order_index: usize,
    pub lock_set: Vec<usize>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct ReturnAssign {
    pub left_index: usize,
    pub left: Vec<usize>,
    pub right_index: usize,
    pub right: Vec<usize>,
    pub atype: usize,
}

impl ReturnAssign {
    pub fn new(left_index: usize, right_index: usize, atype: usize) -> Self {
        let left = Vec::new();
        let right = Vec::new();

        ReturnAssign {
            left_index,
            left,
            right_index,
            right,
            atype,
        }
    }
}

#[derive(Debug,Clone)]
pub struct ReturnResults {
    pub arg_size: usize,
    pub nodes: Vec<Node>,
    //pub assignments: Vec<ReturnAssign>,
}

impl ReturnResults {
    pub fn new(arg_size: usize) -> Self {
        //let assignments: Vec<ReturnAssign> = Vec::new();
        ReturnResults {
            arg_size,
            nodes: Vec::<Node>::new(),
        }
    }
}

//struct to cache the results for analyzed functions.
#[derive(Clone)]
pub struct FuncMap {
    pub map: FxHashMap<usize, ReturnResults>,
    pub set: FxHashSet<usize>,
}

impl FuncMap {
    pub fn new() -> FuncMap {
        FuncMap {
            map: FxHashMap::default(),
            set: FxHashSet::default(),
        }
    }
}
