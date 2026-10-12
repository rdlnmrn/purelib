module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Purelib.LinearAlgebra.Coordinates3.Vector

public import Purelib.LinearAlgebra.Coordinates3.Vector.Permutation
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib.Geometry.Trigonometry

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates3.Vector

open Purelib.LinearAlgebra.Coordinates3.Vector.Permutation

@[expose] public section
namespace Purelib.Geometry.Triangles.Similarity.Entries
variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The three denominator products in the Quadrea--spread identities. -/
def spreadDenominators (entries : Coordinates3.Vector K) : Coordinates3.Vector K :=
  ⟨4 * entries.r * entries.s,
    4 * entries.t * entries.s,
    4 * entries.t * entries.r⟩

/-- Archimedes' symmetric polynomial evaluated on the three entries. -/
def archimedesValue (entries : Coordinates3.Vector K) : K :=
  QuadTriple.Basic.archimedesFunction entries.t entries.r entries.s

/-- Permuting the three scalar entries preserves their Archimedes polynomial. -/
theorem archimedesValue_eq_of_sameEntries
    {left right : Coordinates3.Vector K} (same : Permutation.SameEntries left right) :
    (archimedesValue left) = (archimedesValue right) := by
  rcases same with
    ⟨first, second, third⟩ | ⟨first, second, third⟩ |
    ⟨first, second, third⟩ | ⟨first, second, third⟩ |
    ⟨first, second, third⟩ | ⟨first, second, third⟩
  all_goals
    (unfold archimedesValue QuadTriple.Basic.archimedesFunction
     rw [first, second, third] <;> ring1)

/-- Permuting three entries permutes the three complementary products in the same way.

The six supplied permutation witnesses determine the corresponding order of the three products, with no new choice of
scalar entries. -/
theorem spreadDenominators_sameEntries
    {left right : Coordinates3.Vector K} (same : Permutation.SameEntries left right) :
    Permutation.SameEntries (spreadDenominators left) (spreadDenominators right) := by
  rcases same with
    ⟨first, second, third⟩ | ⟨first, second, third⟩ |
    ⟨first, second, third⟩ | ⟨first, second, third⟩ |
    ⟨first, second, third⟩ | ⟨first, second, third⟩
  · apply SameEntries.abc
    all_goals
      simp only [spreadDenominators, first, second, third, mul_comm, mul_left_comm, -eq_self, -iff_self]
      rfl
  · apply SameEntries.acb
    all_goals
      simp only [spreadDenominators, first, second, third, mul_comm, mul_left_comm, -eq_self, -iff_self]
      rfl
  · apply SameEntries.bac
    all_goals
      simp only [spreadDenominators, first, second, third, mul_comm, mul_left_comm, -eq_self, -iff_self]
      rfl
  · apply SameEntries.bca
    all_goals
      simp only [spreadDenominators, first, second, third, mul_comm, mul_left_comm, -eq_self, -iff_self]
      rfl
  · apply SameEntries.cab
    all_goals
      simp only [spreadDenominators, first, second, third, mul_comm, mul_left_comm, -eq_self, -iff_self]
      rfl
  · apply SameEntries.cba
    all_goals
      simp only [spreadDenominators, first, second, third, mul_comm, mul_left_comm, -eq_self, -iff_self]
      rfl

end Purelib.Geometry.Triangles.Similarity.Entries
end
