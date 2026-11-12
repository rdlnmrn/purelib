module

-- Public operations retain the original IO action and mutable-reference carriers.
public import Init.System.IO

/-!
# Mutable IO references

These native adapters retain the original reference cells and IO results.
Allocation consumes its initial value, reading borrows the cell, and modification
retains the original exclusive take, update and set ordering.
-/

namespace Purelib.System.IO

/-- Allocate an original mutable reference containing the supplied value.

The returned cell has the original `IO.Ref` carrier. Its native allocation
consumes the value and returns the cell in a successful IO result.
-/
@[extern c inline "lean_io_result_mk_ok(lean_st_mk_ref(#2))"]
public opaque mkRef {Alpha : Type} (value : Alpha) : IO (_root_.IO.Ref Alpha)

namespace Ref

/-- Read the current value of an original mutable reference.

The native read borrows the original cell and retains the returned value.
Aliases continue to refer to the same cell, while retained values remain
independent snapshots of its earlier contents.
-/
@[extern c inline "lean_io_result_mk_ok(lean_st_ref_get(#2))"]
public opaque get {Alpha : Type} (reference : @& _root_.IO.Ref Alpha) : IO Alpha

/-- Replace a reference's contents with the result of the supplied update.

Native execution takes the original value exclusively, applies the update once,
and sets that same cell before releasing its owned reference argument. This
preserves the original mutation order and permits reuse of unshared values.
-/
@[extern c inline
  "({ extern lean_object* lean_st_ref_take(lean_object*);
      lean_object* purelib_previous = lean_st_ref_take(#2);
      lean_object* purelib_next = lean_apply_1(#3, purelib_previous);
      lean_dec(lean_st_ref_set(#2, purelib_next));
      lean_dec(#2);
      lean_io_result_mk_ok(lean_box(0)); })"]
public opaque modify {Alpha : Type} (reference : _root_.IO.Ref Alpha)
    (update : Alpha → Alpha) : IO Unit := do
  let previous ← get reference
  reference.set (update previous)

end Ref

end Purelib.System.IO
