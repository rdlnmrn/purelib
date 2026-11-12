module

public import Purelib.Data.Vector.Dependent

/-! # Retained dependent subtype entries

Materialization keeps each original entry and its whole factory equality.
Readback projects the same stored subtype without reconstructing an entry.
-/

public section

namespace Purelib.Data.Vector.DependentVector

universe u

/-- Store each dependent entry once with its complete original factory equality.

This is the same materialized finite spine as `ofFn`; each stored subtype
retains the original entry factory at its actual finite index.
-/
@[expose, noinline] def ofFnWithEq {size : Nat} {family : Fin size → Type u}
    (entries : (index : Fin size) → family index) :
    DependentVector (fun index => { value : family index // value = entries index }) :=
  ofFn (fun index => ⟨entries index, rfl⟩)

/-- The whole retained-equality vector is exactly the original dependent `ofFn` construction. -/
theorem ofFnWithEq_eq {size : Nat} {family : Fin size → Type u}
    (entries : (index : Fin size) → family index) :
    ofFnWithEq entries = ofFn (fun index => ⟨entries index, rfl⟩) := rfl

/-- Read the literal value of a retained dependent subtype entry.

The original family and predicate keep the same finite index. This operation
projects the already stored entry without evaluating its original factory.
-/
@[expose, noinline] def getSubtypeValue {size : Nat} {family : Fin size → Type u}
    {property : (index : Fin size) → family index → Prop}
    (retained : DependentVector (fun index => { value : family index // property index value }))
    (index : Fin size) : family index :=
  (get retained index).val

/-- The value operation is exactly the original stored entry's subtype projection. -/
theorem getSubtypeValue_eq {size : Nat} {family : Fin size → Type u}
    {property : (index : Fin size) → family index → Prop}
    (retained : DependentVector (fun index => { value : family index // property index value }))
    (index : Fin size) : getSubtypeValue retained index = (get retained index).val := rfl

/-- The stored dependent subtype supplies its original predicate at the same finite index. -/
theorem getSubtypeValue_property {size : Nat} {family : Fin size → Type u}
    {property : (index : Fin size) → family index → Prop}
    (retained : DependentVector (fun index => { value : family index // property index value }))
    (index : Fin size) : property index (getSubtypeValue retained index) :=
  (get retained index).property

/-- A retained factory vector reads back the same original entry at every index. -/
theorem ofFnWithEq_getSubtypeValue {size : Nat} {family : Fin size → Type u}
    (entries : (index : Fin size) → family index) (index : Fin size) :
    getSubtypeValue (ofFnWithEq entries) index = entries index :=
  getSubtypeValue_property (ofFnWithEq entries) index

end Purelib.Data.Vector.DependentVector
