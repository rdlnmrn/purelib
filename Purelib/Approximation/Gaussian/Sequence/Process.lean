module
import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Process.Basic
public import Purelib.Approximation.Gaussian.Sequence
import Init.Prelude
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation

section
@[expose] public section

/-!
# Limit-free progressive rational approximations

A transcendental computation in the constructive CCL layer must not first
manufacture a completed non-rational point.  `ApproximationData` instead records
only a sequence of displayed Gaussian-rational samples, a rational
squared-error allowance at each finite index, and a terminating refinement
operation which reaches any requested positive rational allowance.

The possibility predicate used below has an explicit natural-number witness:
`value` is one particular later finite sample.  It is a predicate, not a set
of all samples, and it does not assert that the samples have a limit.
-/

namespace Purelib.Approximation.Gaussian.Sequence
namespace ApproximationData

/-- Forget only the sequence presentation, retaining its explicit finite-index predicate as the sidecar semantics
consumed by the ordinary CCL controller. -/
def toProcess (approximation :
  Gaussian.Sequence.ApproximationData) : Approximation.Gaussian.Process where
  State := Nat
  ball index :=
    { center := approximation.sample index
      radiusSq := approximation.radiusSq index
      radiusSq_nonneg := approximation.radiusSq_nonneg index }
  Possible := approximation.Possible
  witness index := ⟨approximation.sample index,
    approximation.sample_possible index⟩
  possible_inside := by
    intro index value possible
    exact approximation.possible_inside possible
  refine := approximation.refineIndex
  refine_persists := by
    intro current target positive value possible
    exact approximation.possible_persists
      (approximation.refineIndex_ge current target positive) possible
  accurate := approximation.refineIndex_accurate
  centerBound := approximation.centerBound
  centerBound_nonneg := approximation.centerBound_nonneg
  center_bounded := approximation.sample_bounded

/-- The sequence-backed process ball retains the original sample centre and indexed squared-error allowance. -/
@[simp] theorem toProcess_ball (approximation :
  Gaussian.Sequence.ApproximationData) (index : Nat) :
    (approximation.toProcess.ball
      (show approximation.toProcess.State from index)).center =
        approximation.sample index ∧
      (approximation.toProcess.ball
        (show approximation.toProcess.State from index)).radiusSq =
        approximation.radiusSq index :=
  ⟨rfl, rfl⟩

/-- Possibility in the sequence-backed process is exactly the original finite later-sample predicate. -/
theorem toProcess_possible (approximation :
  Gaussian.Sequence.ApproximationData)
    (index : Nat) (value : Data.Gaussian.Basic.Canonical) :
    approximation.toProcess.Possible
        (show approximation.toProcess.State from index) value ↔
      approximation.Possible index value := by
  rfl
end ApproximationData

end Purelib.Approximation.Gaussian.Sequence

end
