module
import Purelib.Data.List.OfFn.Basic

import Purelib.Topology.Knot.Braid.Basic
public import Purelib.Topology.Knot.Braid.Word.Writhe
import Purelib.Topology.Knot.Braid.Word.Basic

open Purelib.Data

section
public section

/-!
# Finite torus braids

This file constructs the positive braid
`(σ₁ · … · σₚ₋₁)^q` as an executable finite word on `p`
strands.  It is the combinatorial braid predicted for the algebraic
singularity `z^p = w^q`.  The construction exposes exact crossing count,
writhe, and endpoint permutation iteration without invoking a completed
curve or a topological quotient.
-/

namespace Purelib.Topology.Knot.Braid.PositiveBand.Basic

open Purelib.Topology.Knot.Braid

/-- List the positive adjacent crossings in increasing strand order.

There is one generator for each bounded index below strands minus one, including the empty band when there are fewer
than two strands. -/
@[expose] def positiveBand (strands : Nat) : Word strands :=
  List.ofFn fun index : Fin (strands - 1) => Generator.positiveGenerator index

/-- The positive band contains exactly strands minus one generators. -/
@[simp] theorem positiveBand_length (strands : Nat) :
    (PositiveBand.Basic.positiveBand strands).length = strands - 1 := by
  simp only [-eq_self, -iff_self, PositiveBand.Basic.positiveBand, List.OfFn.Basic.length_ofFn]
  rfl

/-- The writhe of the positive band is its number of generators. -/
@[simp] theorem positiveBand_writhe (strands : Nat) :
    (PositiveBand.Basic.positiveBand strands).writhe = (strands - 1 : Nat) := by
  rw [Word.writhe_eq_length_of_positive]
  · simp only [-eq_self, -iff_self, PositiveBand.Basic.positiveBand_length]
    rfl
  · intro generator member
    change generator ∈ List.ofFn (fun index : Fin (strands - 1) => Generator.positiveGenerator index) at member
    obtain ⟨index, equal⟩ := List.OfFn.Basic.mem_ofFn.mp member
    rw [← equal]
    rfl

end Purelib.Topology.Knot.Braid.PositiveBand.Basic

end
