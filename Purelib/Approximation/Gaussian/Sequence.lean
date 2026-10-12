module

import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Data.Rat

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

set_option genInjectivity false in
/-- Entirely finite data sufficient to answer arbitrarily accurate rational sample requests, without adjoining a
completed value. -/
structure ApproximationData where
  /-- The actual Gaussian rational sample at each finite index. -/ sample : Nat → Data.Gaussian.Basic.Canonical
  /-- The rational squared-error allowance at each finite index. -/ radiusSq : Nat → Fraction.Rational
  /-- Every displayed squared-error allowance is nonnegative. -/ radiusSq_nonneg : ∀ index, 0 ≤ radiusSq index
  /-- Every later sample stays inside the earlier index's squared-error allowance. -/ later_close : ∀ {earlier later :
    Nat}, earlier ≤ later →
    Data.Gaussian.Norm.Basic.normSq (sample later - sample earlier) ≤ radiusSq earlier
  /-- Compute a later finite index meeting the displayed positive error request. -/ refineIndex : (current : Nat) →
    (target : Fraction.Rational) →
    0 < target → Nat
  /-- The computed refinement index is at least the original index. -/ refineIndex_ge : ∀ (current : Nat) (target :
    Fraction.Rational)
      (positive : 0 < target),
    current ≤ refineIndex current target positive
  /-- The computed refinement index has squared-error allowance strictly below the request. -/ refineIndex_accurate : ∀
    (current : Nat) (target : Fraction.Rational)
      (positive : 0 < target),
    radiusSq (refineIndex current target positive) < target
  /-- The retained uniform rational upper bound on sample squared norms. -/ centerBound : Fraction.Rational
  /-- The retained uniform sample bound is nonnegative. -/ centerBound_nonneg : 0 ≤ centerBound
  /-- Every finite sample meets the retained uniform squared-norm bound. -/ sample_bounded : ∀ index,
    Data.Gaussian.Norm.Basic.normSq (sample index) ≤ centerBound

constructive_injectivity ApproximationData

namespace ApproximationData

/-- A value is possible at `index` when a displayed finite later index witnesses it. -/
def Possible (approximation :
  Approximation.Gaussian.Sequence.ApproximationData) (index : Nat)
    (value : Data.Gaussian.Basic.Canonical) : Prop :=
  ∃ later : Nat, index ≤ later ∧ value = approximation.sample later

/-- The current finite sample witnesses possibility at its own index. -/
theorem sample_possible (approximation :
  Approximation.Gaussian.Sequence.ApproximationData) (index : Nat) :
    approximation.Possible index (approximation.sample index) :=
  ⟨index, Nat.le_refl index, rfl⟩

/-- A reading witnessed at a later index remains possible at every earlier index. -/
theorem possible_persists (approximation :
  Approximation.Gaussian.Sequence.ApproximationData)
    {earlier later : Nat} (order : earlier ≤ later) {value : Data.Gaussian.Basic.Canonical}
    (possible : approximation.Possible later value) :
    approximation.Possible earlier value := by
  rcases possible with ⟨witnessIndex, laterLe, identity⟩
  exact ⟨witnessIndex, Nat.le_trans order laterLe, identity⟩

/-- Every explicitly witnessed later sample lies in the current finite ball. -/
theorem possible_inside (approximation :
  Approximation.Gaussian.Sequence.ApproximationData)
    {index : Nat} {value : Data.Gaussian.Basic.Canonical}
    (possible : approximation.Possible index value) :
    ({ center := approximation.sample index
       radiusSq := approximation.radiusSq index
       radiusSq_nonneg := approximation.radiusSq_nonneg index } :
         Enclosure.Ball).Contains
      value := by
  rcases possible with ⟨later, order, rfl⟩
  exact approximation.later_close order
end ApproximationData

end Purelib.Approximation.Gaussian.Sequence

end
