use rustc_hash::FxHashMap;
use rustc_span::Span;
pub struct Node{
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
        Node {index, local, alias: temp, sons: FxHashMap::default(), field_info: Vec::new()};
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