terminator : Some(Terminator { source_info: SourceInfo { span: alias.rs:31:17: 31:32 (#0), scope: scope[8] }, kind: _11 = foo(move _12, move _13, _7) -> [return: bb1, unwind continue] })
      statement: _1 = const 1_i32, span: alias.rs:17:17: 17:18 (#0)
      statement: _2 = const 2_i32, span: alias.rs:18:17: 18:18 (#0)
      statement: _3 = const 3_i32, span: alias.rs:19:17: 19:18 (#0)
      statement: _4 = const 5_i32, span: alias.rs:20:17: 20:18 (#0)
      statement: _5 = &raw const _1, span: C:\Users\12398\.rustup\toolchains\nightly-x86_64-pc-windows-msvc\lib/rustlib/src/rust\library\core\src\ptr\mod.rs:2055:5: 2055:22 (#5)
      statement: _6 = &raw const _2, span: C:\Users\12398\.rustup\toolchains\nightly-x86_64-pc-windows-msvc\lib/rustlib/src/rust\library\core\src\ptr\mod.rs:2055:5: 2055:22 (#6)
      statement: _7 = &raw const _3, span: C:\Users\12398\.rustup\toolchains\nightly-x86_64-pc-windows-msvc\lib/rustlib/src/rust\library\core\src\ptr\mod.rs:2055:5: 2055:22 (#7)
      statement: _8 = &raw const _4, span: C:\Users\12398\.rustup\toolchains\nightly-x86_64-pc-windows-msvc\lib/rustlib/src/rust\library\core\src\ptr\mod.rs:2055:5: 2055:22 (#8)
      statement: _9 = _8, span: alias.rs:27:10: 27:12 (#0)
      statement: _5 = move _9, span: alias.rs:27:5: 27:12 (#0)
      statement: _10 = _5, span: alias.rs:28:10: 28:12 (#0)
      statement: _6 = move _10, span: alias.rs:28:5: 28:12 (#0)
      statement: _8 = _7, span: alias.rs:29:5: 29:12 (#0)
      statement: _12 = _5, span: alias.rs:31:21: 31:23 (#0)
      statement: _13 = _6, span: alias.rs:31:25: 31:27 (#0)
terminator : Some(Terminator { source_info: SourceInfo { span: alias.rs:34:2: 34:2 (#0), scope: scope[0] }, kind: return })
@@@@@@@@@@@
Nodes:
Node { index: 0, local: 0, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {0}, objects: {0} } } }, deref: None, alias: [0], father: 0, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 1, local: 1, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {1}, objects: {1} } } }, deref: None, alias: [1], father: 1, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 2, local: 2, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {2}, objects: {2} } } }, deref: None, alias: [2], father: 2, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 3, local: 3, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {3, 7, 8}, objects: {3} } } }, deref: None, alias: [3], father: 3, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 4, local: 4, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {4, 9, 10, 6, 5, 13, 12}, objects: {4} } } }, deref: None, alias: [4], father: 4, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 5, local: 5, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {4, 9, 10, 6, 5, 13, 12}, objects: {4} } } }, deref: None, alias: [5], father: 5, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 6, local: 6, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {4, 9, 10, 6, 5, 13, 12}, objects: {4} } } }, deref: None, alias: [6], father: 6, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 7, local: 7, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {3, 7, 8}, objects: {3} } } }, deref: None, alias: [7], father: 7, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 8, local: 8, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {3, 7, 8}, objects: {3} } } }, deref: None, alias: [8], father: 8, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 9, local: 9, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {4, 9, 10, 6, 5, 13, 12}, objects: {4} } } }, deref: None, alias: [9], father: 9, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 10, local: 10, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {4, 9, 10, 6, 5, 13, 12}, objects: {4} } } }, deref: None, alias: [10], father: 10, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 11, local: 11, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {11}, objects: {11} } } }, deref: None, alias: [11], father: 11, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 12, local: 12, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {4, 9, 10, 6, 5, 13, 12}, objects: {4} } } }, deref: None, alias: [12], father: 12, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 13, local: 13, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {4, 9, 10, 6, 5, 13, 12}, objects: {4} } } }, deref: None, alias: [13], father: 13, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 14, local: 14, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {14}, objects: {14} } } }, deref: None, alias: [14], father: 14, son_index: None, kind: 0, sons: {}, field_info: [] }
@@@@@@@@@@@
terminator : Some(Terminator { source_info: SourceInfo { span: alias.rs:14:2: 14:2 (#0), scope: scope[0] }, kind: return })
      statement: _4 = const 4_i32, span: alias.rs:6:18: 6:19 (#0)
      statement: _5 = _2, span: alias.rs:9:9: 9:10 (#0)
      statement: _1 = move _5, span: alias.rs:9:5: 9:10 (#0)
      statement: _2 = _3, span: alias.rs:10:5: 10:10 (#0)
      statement: _6 = &raw const _4, span: C:\Users\12398\.rustup\toolchains\nightly-x86_64-pc-windows-msvc\lib/rustlib/src/rust\library\core\src\ptr\mod.rs:2055:5: 2055:22 (#4)
      statement: _1 = move _6, span: alias.rs:11:5: 11:20 (#0)
      statement: _0 = _1, span: alias.rs:13:5: 13:6 (#0)
-------------merge_path  start-----------
Node { index: 0, local: 0, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {0, 4, 1, 6}, objects: {} } } }, deref: None, alias: [0], father: 0, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 2, local: 2, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {3, 2}, objects: {3} } } }, deref: None, alias: [2], father: 2, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 1, local: 1, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {0, 4, 1, 6}, objects: {} } } }, deref: None, alias: [1], father: 1, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 3, local: 3, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {3, 2}, objects: {3} } } }, deref: None, alias: [3], father: 3, son_index: None, kind: 0, sons: {}, field_info: [] }
-----------------merge_path end-------------------
return_map:
(0, Node { index: 0, local: 0, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {0, 4, 1, 6}, objects: {} } } }, deref: None, alias: [0], father: 0, son_index: None, kind: 0, sons: {}, field_info: [] })
(1, Node { index: 1, local: 1, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {0, 4, 1, 6}, objects: {} } } }, deref: None, alias: [1], father: 1, son_index: None, kind: 0, sons: {}, field_info: [] })
(2, Node { index: 2, local: 2, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {3, 2}, objects: {3} } } }, deref: None, alias: [2], father: 2, son_index: None, kind: 0, sons: {}, field_info: [] })
(3, Node { index: 3, local: 3, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {3, 2}, objects: {3} } } }, deref: None, alias: [3], father: 3, son_index: None, kind: 0, sons: {}, field_info: [] })
return_map:
(14, Node { index: 14, local: 0, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {0, 4, 1, 6}, objects: {} } } }, deref: None, alias: [0], father: 0, son_index: None, kind: 0, sons: {}, field_info: [] })
(12, Node { index: 12, local: 1, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {0, 4, 1, 6}, objects: {} } } }, deref: None, alias: [1], father: 1, son_index: None, kind: 0, sons: {}, field_info: [] })
(7, Node { index: 7, local: 3, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {3, 2}, objects: {3} } } }, deref: None, alias: [3], father: 3, son_index: None, kind: 0, sons: {}, field_info: [] })
(13, Node { index: 13, local: 2, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {3, 2}, objects: {3} } } }, deref: None, alias: [2], father: 2, son_index: None, kind: 0, sons: {}, field_info: [] })
alias_vec: [12, 14]
alias_vec: [13, 7]
###########
Nodes:
Node { index: 0, local: 0, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {0}, objects: {0} } } }, deref: None, alias: [0], father: 0, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 1, local: 1, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {1}, objects: {1} } } }, deref: None, alias: [1], father: 1, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 2, local: 2, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {2}, objects: {2} } } }, deref: None, alias: [2], father: 2, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 3, local: 3, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {10, 9, 6, 4, 3, 7, 5, 13, 8}, objects: {3} } } }, deref: None, alias: [3], father: 3, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 4, local: 4, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {10, 9, 6, 4, 3, 7, 5, 13, 8}, objects: {3} } } }, deref: None, alias: [4], father: 4, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 5, local: 5, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {10, 9, 6, 4, 3, 7, 5, 13, 8}, objects: {3} } } }, deref: None, alias: [5], father: 5, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 6, local: 6, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {10, 9, 6, 4, 3, 7, 5, 13, 8}, objects: {3} } } }, deref: None, alias: [6], father: 6, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 7, local: 7, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {10, 9, 6, 4, 3, 7, 5, 13, 8}, objects: {3} } } }, deref: None, alias: [7], father: 7, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 8, local: 8, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {10, 9, 6, 4, 3, 7, 5, 13, 8}, objects: {3} } } }, deref: None, alias: [8], father: 8, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 9, local: 9, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {10, 9, 6, 4, 3, 7, 5, 13, 8}, objects: {3} } } }, deref: None, alias: [9], father: 9, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 10, local: 10, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {10, 9, 6, 4, 3, 7, 5, 13, 8}, objects: {3} } } }, deref: None, alias: [10], father: 10, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 11, local: 11, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {12, 14, 11}, objects: {15} } } }, deref: None, alias: [11], father: 11, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 12, local: 12, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {12, 14, 11}, objects: {15} } } }, deref: None, alias: [12], father: 12, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 13, local: 13, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {10, 9, 6, 4, 3, 7, 5, 13, 8}, objects: {3} } } }, deref: None, alias: [13], father: 13, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 14, local: 14, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {12, 14, 11}, objects: {15} } } }, deref: None, alias: [14], father: 14, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 15, local: 15, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {15}, objects: {15} } } }, deref: None, alias: [15], father: 15, son_index: None, kind: 0, sons: {}, field_info: [] }
###########
-------------merge_path  start-----------
Node { index: 0, local: 0, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {0}, objects: {0} } } }, deref: None, alias: [0], father: 0, son_index: None, kind: 0, sons: {}, field_info: [] }
-----------------merge_path end-------------------
Nodes:
Node { index: 0, local: 0, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {0}, objects: {0} } } }, deref: None, alias: [0], father: 0, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 1, local: 1, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {1}, objects: {1} } } }, deref: None, alias: [1], father: 1, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 2, local: 2, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {2}, objects: {2} } } }, deref: None, alias: [2], father: 2, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 3, local: 3, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {10, 9, 6, 4, 3, 7, 5, 13, 8}, objects: {3} } } }, deref: None, alias: [3], father: 3, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 4, local: 4, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {10, 9, 6, 4, 3, 7, 5, 13, 8}, objects: {3} } } }, deref: None, alias: [4], father: 4, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 5, local: 5, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {10, 9, 6, 4, 3, 7, 5, 13, 8}, objects: {3} } } }, deref: None, alias: [5], father: 5, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 6, local: 6, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {10, 9, 6, 4, 3, 7, 5, 13, 8}, objects: {3} } } }, deref: None, alias: [6], father: 6, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 7, local: 7, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {10, 9, 6, 4, 3, 7, 5, 13, 8}, objects: {3} } } }, deref: None, alias: [7], father: 7, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 8, local: 8, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {10, 9, 6, 4, 3, 7, 5, 13, 8}, objects: {3} } } }, deref: None, alias: [8], father: 8, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 9, local: 9, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {10, 9, 6, 4, 3, 7, 5, 13, 8}, objects: {3} } } }, deref: None, alias: [9], father: 9, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 10, local: 10, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {10, 9, 6, 4, 3, 7, 5, 13, 8}, objects: {3} } } }, deref: None, alias: [10], father: 10, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 11, local: 11, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {12, 14, 11}, objects: {15} } } }, deref: None, alias: [11], father: 11, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 12, local: 12, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {12, 14, 11}, objects: {15} } } }, deref: None, alias: [12], father: 12, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 13, local: 13, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {10, 9, 6, 4, 3, 7, 5, 13, 8}, objects: {3} } } }, deref: None, alias: [13], father: 13, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 14, local: 14, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {12, 14, 11}, objects: {15} } } }, deref: None, alias: [14], father: 14, son_index: None, kind: 0, sons: {}, field_info: [] }
Node { index: 15, local: 15, point_to: PointSet { inner: RefCell { value: PointInner { nodes: {15}, objects: {15} } } }, deref: None, alias: [15], father: 15, son_index: None, kind: 0, sons: {}, field_info: [] }
