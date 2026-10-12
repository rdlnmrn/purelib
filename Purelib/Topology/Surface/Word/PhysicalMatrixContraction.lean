module
import Purelib.Algebra.Ring.IntCast
import Purelib.Algebra.FiniteSum.Fin

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Word.Pairing
public import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Data.Gaussian.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Vector.Basic

public section

/-! The remaining cut matrix vanishes only after its physical readings vanish. -/
namespace Purelib.Topology.Surface.Word.PhysicalMatrixContraction

open Purelib.Algebra
open Purelib.Topology.Polygon
open Purelib.Topology.Polygon.Stokes
open Purelib.Topology.Surface.Cut
open Purelib.Topology.Surface.Cut.IntegralPairing
open Purelib.Topology.Surface.Word

open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint)

open Purelib.Algebra.FiniteSum.Fin (sumFin_congr sumFin_zero)
open Purelib.Topology.Surface.Cut.BoundaryWord (CutBoundaryWord)
open _root_.Purelib.Topology.Surface.Cut.IntegralPairing renaming CutBoundaryWord -> IntegralPairing

variable {source target : Nat} {labels : Fin source → Fin target}
  {edges : List (Stokes.OrientedEdge source)} {word : BoundaryWord.CutBoundaryWord labels edges}
  (pairing : Cut.IntegralPairing.CutBoundaryWord word) (values : Fin word.alphabet.count → Stokes.PrimitivePoint)
  (physical : ∀ index, word.alphabet.oneSided index = true → values index = PrimitivePoint.zero)

include physical

/-- The retained remaining cut matrix contracts to zero when every physical generator reading vanishes.

Entries with two paired indices are zero by the original matrix split; each other term contains a vanishing physical
reading. -/
theorem remaining_contract_zero :
    Pairing.contract (fun row column => pairing.remaining row column) values = 0 := by
  apply Eq.trans (FiniteSum.Fin.sumFin_congr (fun row => ?_)) FiniteSum.Fin.sumFin_zero
  apply Eq.trans (FiniteSum.Fin.sumFin_congr (fun column => ?_)) FiniteSum.Fin.sumFin_zero
  dsimp only
  cases first : word.alphabet.oneSided row
  · cases last : word.alphabet.oneSided column
    · rw [pairing.remaining_paired_zero row column first last, Purelib.Algebra.Ring.IntCast.cast_zero, zero_mul,
        zero_mul]
    · rw [physical column last]
      exact mul_zero _
  · rw [physical row first]
    exact (congrArg (· * (values _).right) (mul_zero _)).trans (zero_mul _)

/-- Vanishing physical readings reduce the original word contraction to twice its paired integral block. -/
theorem contract_eq_twice_paired :
    Pairing.contract (fun row column => word.signature.matrix row column) values =
      2 * Pairing.contract (fun row column => pairing.paired row column) values := by
  rw [pairing.contract_eq, remaining_contract_zero pairing values physical, add_zero]

end Purelib.Topology.Surface.Word.PhysicalMatrixContraction
