module
import Purelib.Data.Nat.Subtraction
import Purelib.Approximation.Rational.Geometric.Basic
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Field
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric

open Purelib.Data.Rat

open Purelib.Data

section
public section

/-!
# Rational diameter content of finite CCL cylinders

The quantity here is explicitly a geometric squared-diameter budget, not a
probability mass.  Every statement concerns a supplied finite block list and
supplied finite realization certificates.
-/

namespace Purelib.Approximation.Rational.Budget.Dyadic

/-- Every nonnegative integral power of one half is at most one. -/
theorem half_pow_le_one (count : Nat) :
    (1 / 2 : Fraction.Rational) ^ count ≤ 1 := by
  induction count with
  | zero => exact le_rfl
  | succ count inductionHypothesis =>
      rw [pow_succ]
      calc
        (1 / 2 : Fraction.Rational) ^ count * (1 / 2) ≤ 1 * (1 / 2) :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            inductionHypothesis (by decide)
        _ ≤ 1 := by decide

/-- A finite number of completed blocks calculated from a positive rational squared-chordal request. The factor two
converts quarter-power search into the CCL half-power spread. -/
@[expose] def requiredBlockCount (target : Fraction.Rational) : Nat
  :=
  2 * Search.firstQuarterBelow 1 0 target

/-- An even half-power is the corresponding quarter-power. -/
private theorem half_pow_two_mul (index : Nat) :
    (1 / 2 : Fraction.Rational) ^ (2 * index) = (1 / 4 : Fraction.Rational) ^ index := by
  calc
    (1 / 2 : Fraction.Rational) ^ (2 * index) =
        ((1 / 2 : Fraction.Rational) ^ 2) ^ index := by rw [pow_mul]
    _ = (1 / 4 : Fraction.Rational) ^ index := by
      have halfSquare : (1 / 2 : Fraction.Rational) ^ 2 = 1 / 4 := by decide
      rw [halfSquare]

/-- The computed finite block count has canonical spread below the supplied positive rational request. -/
theorem requiredBlockCount_spread_lt
    {target : Fraction.Rational} (positive : 0 < target) :
    (1 / 2 : Fraction.Rational) ^ requiredBlockCount target < target := by
  let index := Search.firstQuarterBelow 1 0 target
  have requested := Search.firstQuarterBelow_accurate
    (scale := (1 : Fraction.Rational)) (by decide) 0 target positive
  rw [Geometric.Basic.quarterRadius_eq_mul_pow] at requested
  simp only [-eq_self, -iff_self, one_mul] at requested
  simpa only [-eq_self, -iff_self, requiredBlockCount, index,
    half_pow_two_mul] using requested
end Purelib.Approximation.Rational.Budget.Dyadic

end

section
public section

/-!
# Progressive witness-centred variance from finite CCL prefixes

This module turns the static witness-centred variance construction into a
finite-request process.  Its states remain ordinary finite prefix families.
One request computes a finite block count large enough for both the centred
second-deviation enclosure and the squared mean-radius correction.
-/

namespace Purelib.Approximation.Rational.Budget

section PrefixFamilyProcess

/-- A computable positive half-power whose square is below half the supplied positive variance tolerance. -/
@[expose] def centeredVarianceMeanTarget (target : Fraction.Rational) :
  Fraction.Rational :=
  (1 / 2 : Fraction.Rational) ^ Dyadic.requiredBlockCount (target / 2)

/-- The selected dyadic mean tolerance is strictly positive. -/
theorem centeredVarianceMeanTarget_positive
    {target : Fraction.Rational} (_positive : 0 < target) :
    0 < centeredVarianceMeanTarget target :=
  Fraction.Order.Arithmetic.pow_pos_direct (by decide) _

/-- For a positive variance request, the selected mean tolerance squared is below half the request. -/
theorem centeredVarianceMeanTarget_sq_lt_half
    {target : Fraction.Rational} (positive : 0 < target) :
    centeredVarianceMeanTarget target ^ 2 < target / 2 := by
  have halfPositive : (0 : Fraction.Rational) < target / 2 :=
    Fraction.Order.Field.div_pos_direct positive (by decide)
  have targetSmall : centeredVarianceMeanTarget target < target / 2 :=
    Dyadic.requiredBlockCount_spread_lt halfPositive
  have targetNonnegative : 0 ≤ centeredVarianceMeanTarget target :=
    (centeredVarianceMeanTarget_positive positive).le
  have targetLeOne : centeredVarianceMeanTarget target ≤ 1 :=
    Dyadic.half_pow_le_one _
  calc
    centeredVarianceMeanTarget target ^ 2 =
        centeredVarianceMeanTarget target *
          centeredVarianceMeanTarget target := by ring1
    _ ≤ centeredVarianceMeanTarget target * 1 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        targetLeOne targetNonnegative
    _ = centeredVarianceMeanTarget target := by ring1
    _ < target / 2 := targetSmall
end PrefixFamilyProcess

end Purelib.Approximation.Rational.Budget

end

section
public section

/-!
# Joint finite profile of a completed CCL prefix

A completed-block prefix carries two deliberately separate rational data:

* its fair-bit symbolic cylinder weight, calculated from the raw word; and
* its geometric squared-chordal spread, calculated from block contraction.

Both improve under finite extension, but no theorem identifies them.  A
finite realization certificate also turns the prefix into an inhabited
finite observation, without choosing a point from an eventual intersection.
-/

namespace Purelib.Approximation.Rational.Budget

/-- Half-powers decrease as their finite exponents increase. -/
theorem half_pow_antitone {smaller larger : Nat}
    (order : smaller ≤ larger) :
    (1 / 2 : Fraction.Rational) ^ larger ≤ (1 / 2 : Fraction.Rational) ^ smaller := by
  let extra := larger - smaller
  have equal : larger = smaller + extra := (Nat.Subtraction.add_sub_of_le order).symm
  rw [equal, pow_add]
  have extraLeOne : (1 / 2 : Fraction.Rational) ^ extra ≤ 1 := by
    have powerBound := Fraction.Order.Arithmetic.pow_le_pow_direct
      (by decide : (0 : Fraction.Rational) ≤ 1 / 2)
      (by decide : (1 / 2 : Fraction.Rational) ≤ 1) extra
    simpa only [-eq_self, -iff_self, one_pow] using powerBound
  have prefixNonnegative : 0 ≤ (1 / 2 : Fraction.Rational) ^ smaller :=
    Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) smaller
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    extraLeOne prefixNonnegative
  simpa only [-eq_self, -iff_self, mul_one] using scaled

/-- Finite completed-block count requested for a positive rational probe width and positive sensitivity factor. -/
@[expose] def requiredProbeBlockCount (target factor : Fraction.Rational) :
  Nat :=
  Dyadic.requiredBlockCount (target / (2 * factor))
end Purelib.Approximation.Rational.Budget

end

section
public section

/-!
# Root-free L2 stability of finite CCL prefix probes

Direct Lipschitz control by `chordalSq` is stronger than is natural for many
nonconstant projective observables.  This module instead accepts the
square-root-free estimate

`rationalSeparation (probe x) (probe y) ^ 2 ≤ factor * chordalSq x y`.

CCL cylinder contraction then controls exact finite powered-L2 distances.
Finite Cauchy--Schwarz transfers that control to squared expectation error,
and a request at the square of a supplied rational tolerance recovers an
ordinary strict expectation-separation theorem.  No square root is selected.
-/

namespace Purelib.Approximation.Rational.Budget

/-- Block count used to recover an ordinary rational expectation tolerance from a squared-probe sensitivity estimate.
The factor `1/2` leaves a strict finite averaging margin. -/
@[expose] def requiredSquaredProbeBlockCount
    (epsilon factor : Fraction.Rational) : Nat :=
  Dyadic.requiredBlockCount ((epsilon ^ 2 / 2) / factor)

end Purelib.Approximation.Rational.Budget

end

section
public section

/-!
# End-to-end finite estimation of encoded affine expectations

For the concrete distance-to-`omega` observable, a heterogeneous finite table
of CCL encoder outputs can be estimated by an explicit finite iid sample.
Half of a requested rational error is assigned to finite-prefix bias and half
to sampling fluctuation.  The global `[0, 1]` range of the observable supplies
the uniform variance budget `1` used by the constructive Chebyshev request.
-/

namespace Purelib.Approximation.Rational.Budget

/-- Executable completed-block request assigning half of the desired estimator error to CCL representation bias. -/
@[expose] def encodedChordalOmegaEstimatorBlockCount (epsilon :
  Fraction.Rational) : Nat :=
  requiredSquaredProbeBlockCount (epsilon / 2) 2
end Purelib.Approximation.Rational.Budget

end

section
public section

/-!
# Concentration of squared-sensitive probes inside one finite CCL cylinder

For a probe satisfying a squared-separation sensitivity estimate, CCL's
`2^-k` squared-chordal cylinder contraction gives a `factor * 2^-k` second
moment bound directly.  This is the natural rate for nonconstant Lipschitz
observables and avoids selecting a square root.

Every statement concerns an explicitly supplied finite distribution and
finite realization traces.  No measure on an infinite cylinder is formed.
-/

namespace Purelib.Approximation.Rational.Budget

/-- Computed block count for making a squared-sensitive variance budget smaller than a positive rational target. -/
@[expose] def requiredSquaredVarianceBlockCount
    (target factor : Fraction.Rational) : Nat :=
  Dyadic.requiredBlockCount (target / factor)
end Purelib.Approximation.Rational.Budget

end

section
public section

/-!
# Threshold stability for squared-sensitive finite CCL probes

Discontinuous threshold events cannot be controlled from a shrinking metric
bound alone when a value may lie on the threshold.  An explicit positive
rational witness margin repairs this constructively.  Squared-probe
sensitivity then requires a finite request at `margin^2`; after that request
every compatible realization has exactly the witness's Boolean
classification, so all resulting finite probabilities are equal.
-/

namespace Purelib.Approximation.Rational.Budget

/-- Sufficient block count for resolving a squared-sensitive threshold event with a displayed positive rational margin.
-/
@[expose] def requiredSquaredThresholdBlockCount
    (margin factor : Fraction.Rational) : Nat :=
  requiredSquaredVarianceBlockCount (margin ^ 2) factor
end Purelib.Approximation.Rational.Budget

end
