DefId(0:7 ~ toy[c0d3]::foo)
  BasicBlock: bb0
DefId(0:8 ~ toy[c0d3]::main)
  BasicBlock: bb0
      statement: _33 = const false
      statement: _32 = const false
  BasicBlock: bb1
      statement: _2 = const 0_i32
  BasicBlock: bb2
  BasicBlock: bb3
      statement: _6 = &_3
  BasicBlock: bb4
      statement: _8 = {closure@toy.rs:12:28: 12:35} { clone: move _5 }
  BasicBlock: bb5
      statement: _33 = const true
      statement: _10 = &_3
  BasicBlock: bb6
      statement: _12 = {closure@toy.rs:22:28: 22:35} { clone2: move _9 }
  BasicBlock: bb7
      statement: _32 = const true
      statement: _33 = const false
      statement: _15 = move _7
  BasicBlock: bb8
  BasicBlock: bb9
      statement: _32 = const false
      statement: _18 = move _11
  BasicBlock: bb10
  BasicBlock: bb11
      statement: _31 = const _
      statement: _21 = _31 as &[&str] (PointerCoercion(Unsize))
      statement: _30 = &_3
  BasicBlock: bb12
  BasicBlock: bb13
  BasicBlock: bb14
      statement: _26 = &_27
  BasicBlock: bb15
      statement: _24 = [move _25]
      statement: _23 = &_24
      statement: _22 = _23 as &[core::fmt::rt::Argument<'_>] (PointerCoercion(Unsize))
  BasicBlock: bb16
  BasicBlock: bb17
  BasicBlock: bb18
      statement: _32 = const false
      statement: _33 = const false
  BasicBlock: bb19
  BasicBlock: bb20
  BasicBlock: bb21
  BasicBlock: bb22
  BasicBlock: bb23
  BasicBlock: bb24
  BasicBlock: bb25
  BasicBlock: bb26
DefId(0:9 ~ toy[c0d3]::main::{closure#0})
  BasicBlock: bb0
      statement: _5 = &(_1.0: std::sync::Arc<std::sync::Mutex<i32>>)
  BasicBlock: bb1
  BasicBlock: bb2
  BasicBlock: bb3
      statement: _8 = &mut _2
  BasicBlock: bb4
      statement: _6 = &raw mut (*_7)
  BasicBlock: bb5
      statement: _16 = _6 as *const () (PtrToPtr)
      statement: _17 = _16 as usize (Transmute)
      statement: _18 = AlignOf(i32)
      statement: _19 = Sub(_18, const 1_usize)
      statement: _20 = BitAnd(_17, _19)
      statement: _21 = Eq(_20, const 0_usize)
  BasicBlock: bb6
      statement: _10 = _6 as *const () (PtrToPtr)
      statement: _11 = _10 as usize (Transmute)
      statement: _12 = AlignOf(i32)
      statement: _13 = Sub(_12, const 1_usize)
      statement: _14 = BitAnd(_11, _13)
      statement: _15 = Eq(_14, const 0_usize)
  BasicBlock: bb7
  BasicBlock: bb8
  BasicBlock: bb9
  BasicBlock: bb10
  BasicBlock: bb11
      statement: (*_6) = move (_9.0: i32)
  BasicBlock: bb12
      statement: _9 = CheckedAdd((*_6), const 1_i32)
DefId(0:10 ~ toy[c0d3]::main::{closure#1})
  BasicBlock: bb0
      statement: _5 = &(_1.0: std::sync::Arc<std::sync::Mutex<i32>>)
  BasicBlock: bb1
  BasicBlock: bb2
  BasicBlock: bb3
      statement: _8 = &mut _2
  BasicBlock: bb4
      statement: _6 = &raw mut (*_7)
  BasicBlock: bb5
      statement: _16 = _6 as *const () (PtrToPtr)
      statement: _17 = _16 as usize (Transmute)
      statement: _18 = AlignOf(i32)
      statement: _19 = Sub(_18, const 1_usize)
      statement: _20 = BitAnd(_17, _19)
      statement: _21 = Eq(_20, const 0_usize)
  BasicBlock: bb6
      statement: _10 = _6 as *const () (PtrToPtr)
      statement: _11 = _10 as usize (Transmute)
      statement: _12 = AlignOf(i32)
      statement: _13 = Sub(_12, const 1_usize)
      statement: _14 = BitAnd(_11, _13)
      statement: _15 = Eq(_14, const 0_usize)
  BasicBlock: bb7
  BasicBlock: bb8
  BasicBlock: bb9
  BasicBlock: bb10
  BasicBlock: bb11
      statement: (*_6) = move (_9.0: i32)
  BasicBlock: bb12
      statement: _9 = CheckedAdd((*_6), const 1_i32)
