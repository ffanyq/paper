use rustc_hash::{FxHashMap, FxHashSet};
use rustc_span::Span;
pub struct Node {
    pub index: usize,
    pub local: usize,
    pub alias: Vec<usize>,
    pub sons: FxHashMap<usize, usize>,
    pub field_info: Vec<usize>,
}

impl Node {
    pub fn new(index: usize, local: usize) {
        let mut temp = Vec::new();
        temp.push(local);
        Node {
            index,
            local,
            alias: temp,
            sons: FxHashMap::default(),
            field_info: Vec::new(),
        };
    }
}

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

#[derive(Clone)]
pub struct ReturnResults {
    pub arg_size: usize,
    pub assignments: Vec<ReturnAssign>,
}

impl ReturnResults {
    pub fn new(arg_size: usize) -> Self {
        let assignments: Vec<ReturnAssign> = Vec::new();
        ReturnResults {
            arg_size,
            assignments,
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
