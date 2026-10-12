module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Bool.Decide
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Division.Basic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Sign.Pair.Resolution
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Dominance
import Purelib.Data.Rat.Interval.Radius
public import Purelib.Polynomial.Clearance.Pair.SignedRemainder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Pair.Operations

public section

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Radius

open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Data.Nat
open Purelib.Data.Bool

/-- Combine the three local squared radii at a signed Euclidean step.

The retained clearance supplies two adjacent-pair radii and a quotient-dominance
radius for the same signed remainder. Their minimum retains all three tests. -/
@[expose] def signedStepResolutionRadiusSq {p q : Dense.Rational.Basic.CoordinatePolynomial}
    {root : Data.Rat.Interval.Bounds} (clearance : Clearance.Pair.Basic.Certificate p q root) : Fraction.Rational :=
  let next := -((Dense.Basic.DensePolynomial.divMod p q).remainder)
  min (Dense.Rational.Sign.Pair.Resolution.pairResolutionRadiusSq clearance)
    (min (Dense.Rational.Sign.Pair.Resolution.pairResolutionRadiusSq clearance.signedStep)
      (Dense.Rational.SignedRemainder.Signs.Dominance.dominanceResolutionRadiusSq q (Dense.Basic.DensePolynomial.divMod
        p q).quotient next
        clearance.signedStep))

/-- The joint signed-step resolution radius is positive.

It is the minimum of two positive adjacent-pair radii and a positive quotient-dominance radius. -/
theorem signedStepResolutionRadiusSq_pos {p q : Dense.Rational.Basic.CoordinatePolynomial}
    {root : Data.Rat.Interval.Bounds} (clearance : Clearance.Pair.Basic.Certificate p q root) :
    0 < signedStepResolutionRadiusSq clearance := by
  apply Fraction.Order.Basic.lt_min
  · exact Dense.Rational.Sign.Pair.Resolution.pairResolutionRadiusSq_pos clearance
  · apply Fraction.Order.Basic.lt_min
    · exact Dense.Rational.Sign.Pair.Resolution.pairResolutionRadiusSq_pos clearance.signedStep
    · exact Dense.Rational.SignedRemainder.Signs.Dominance.dominanceResolutionRadiusSq_pos q
        (Dense.Basic.DensePolynomial.divMod p q).quotient
        (-((Dense.Basic.DensePolynomial.divMod p q).remainder)) clearance.signedStep

/-- A sufficiently small refined interval resolves all three signed-step tests.

The joint radius supplies both adjacent-pair resolutions and the quotient-dominance resolution for the same restricted
clearance. -/
theorem signedStepResolutions_of_refined_radiusSq
    {p q : Dense.Rational.Basic.CoordinatePolynomial} {root interval : Data.Rat.Interval.Bounds}
    (clearance : Clearance.Pair.Basic.Certificate p q root)
    (refines : interval.Refines root)
    (radius : Interval.Radius.sampleRadiusSq interval interval.lower <
      signedStepResolutionRadiusSq clearance) :
    Dense.Rational.Sign.Pair.Resolution.PairResolution (clearance.restrict refines) ∧
      Dense.Rational.Sign.Pair.Resolution.PairResolution (clearance.signedStep.restrict refines) ∧
      Dense.Rational.SignedRemainder.Signs.Dominance.DominanceResolution q (Dense.Basic.DensePolynomial.divMod p
        q).quotient
        (-((Dense.Basic.DensePolynomial.divMod p q).remainder))
        (clearance.signedStep.restrict refines) := by
  refine ⟨Dense.Rational.Sign.Pair.Resolution.pairResolution_of_refined_radiusSq clearance refines
      (radius.trans_le (Fraction.Order.Basic.min_le_left _ _)), ?_⟩
  refine ⟨Dense.Rational.Sign.Pair.Resolution.pairResolution_of_refined_radiusSq clearance.signedStep refines
      (radius.trans_le ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _))), ?_⟩
  exact Dense.Rational.SignedRemainder.Signs.Dominance.dominanceResolution_of_refined_radiusSq clearance.signedStep
    refines
    (radius.trans_le ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_right _ _)))

/-- Fold resolution radii along a signed Euclidean chain with finite fuel.

Zero fuel returns the current adjacent-pair radius. Covering the second
polynomial's coefficient count ensures that this fallback is reached only
at a zero second polynomial. -/
@[expose] def signedChainResolutionRadiusSqFuel : Nat →
    (p q : Dense.Rational.Basic.CoordinatePolynomial) → {root : Data.Rat.Interval.Bounds} →
      Clearance.Pair.Basic.Certificate p q root → Fraction.Rational
  | 0, _, _, _, clearance => Dense.Rational.Sign.Pair.Resolution.pairResolutionRadiusSq clearance
  | fuel + 1, p, q, _, clearance =>
      if q.isZero then Dense.Rational.Sign.Pair.Resolution.pairResolutionRadiusSq clearance
      else
        let next := -((Dense.Basic.DensePolynomial.divMod p q).remainder)
        if next.isZero then
          Dense.Rational.Sign.Pair.Resolution.pairResolutionRadiusSq clearance.signedStep
        else
          min (signedStepResolutionRadiusSq clearance)
            (Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Radius.signedChainResolutionRadiusSqFuel fuel q
              next
              clearance.signedStep)

/-- Zero fuel returns the current adjacent-pair resolution radius. -/
@[simp] theorem signedChainResolutionRadiusSqFuel_zero
    (p q : Dense.Rational.Basic.CoordinatePolynomial) {root : Data.Rat.Interval.Bounds}
    (clearance : Clearance.Pair.Basic.Certificate p q root) :
    signedChainResolutionRadiusSqFuel 0 p q clearance =
      Dense.Rational.Sign.Pair.Resolution.pairResolutionRadiusSq clearance := rfl

/-- One fuel step tests the next signed remainder and combines resolution radii.

A zero current or next polynomial selects the corresponding pair radius; otherwise recursion continues under a minimum
with the signed-step radius. -/
theorem signedChainResolutionRadiusSqFuel_succ
    (fuel : Nat) (p q : Dense.Rational.Basic.CoordinatePolynomial) {root : Data.Rat.Interval.Bounds}
    (clearance : Clearance.Pair.Basic.Certificate p q root) :
    signedChainResolutionRadiusSqFuel (fuel + 1) p q clearance =
      if q.isZero then Dense.Rational.Sign.Pair.Resolution.pairResolutionRadiusSq clearance
      else
        let next := -((Dense.Basic.DensePolynomial.divMod p q).remainder)
        if next.isZero then
          Dense.Rational.Sign.Pair.Resolution.pairResolutionRadiusSq clearance.signedStep
        else
          min (signedStepResolutionRadiusSq clearance)
            (signedChainResolutionRadiusSqFuel fuel q next
              clearance.signedStep) := rfl

/-- Additional fuel leaves a degree-covered radius fold unchanged.

Every nonzero signed remainder has smaller coefficient count, so the
recursive fold has sufficient remaining fuel after the same stop tests. -/
theorem signedChainResolutionRadiusSqFuel_succ_of_degreeCount_le :
    ∀ (fuel : Nat) (p q : Dense.Rational.Basic.CoordinatePolynomial) {root : Data.Rat.Interval.Bounds}
      (clearance : Clearance.Pair.Basic.Certificate p q root),
      q.degreeCount ≤ fuel →
        signedChainResolutionRadiusSqFuel (fuel + 1) p q clearance =
          signedChainResolutionRadiusSqFuel fuel p q clearance := by
  intro fuel
  induction fuel with
  | zero =>
      intro p q root clearance enough
      have degreeZero : q.degreeCount = 0 :=
        Nat.eq_zero_of_le_zero enough
      have qZero := Dense.Basic.DensePolynomial.isZero_true_of_degreeCount_eq_zero degreeZero
      change (if q.isZero then Dense.Rational.Sign.Pair.Resolution.pairResolutionRadiusSq clearance
          else
            let next := -((Dense.Basic.DensePolynomial.divMod p q).remainder)
            if next.isZero then
              Dense.Rational.Sign.Pair.Resolution.pairResolutionRadiusSq clearance.signedStep
            else
              min (signedStepResolutionRadiusSq clearance)
                (signedChainResolutionRadiusSqFuel 0 q next
                  clearance.signedStep)) =
        Dense.Rational.Sign.Pair.Resolution.pairResolutionRadiusSq clearance
      rw [qZero]
      rfl
  | succ fuel inductionHypothesis =>
      intro p q root clearance enough
      change (if q.isZero then Dense.Rational.Sign.Pair.Resolution.pairResolutionRadiusSq clearance
          else
            let next := -((Dense.Basic.DensePolynomial.divMod p q).remainder)
            if next.isZero then
              Dense.Rational.Sign.Pair.Resolution.pairResolutionRadiusSq clearance.signedStep
            else
              min (signedStepResolutionRadiusSq clearance)
                (signedChainResolutionRadiusSqFuel (fuel + 1) q next
                  clearance.signedStep)) =
        if q.isZero then Dense.Rational.Sign.Pair.Resolution.pairResolutionRadiusSq clearance
          else
            let next := -((Dense.Basic.DensePolynomial.divMod p q).remainder)
            if next.isZero then
              Dense.Rational.Sign.Pair.Resolution.pairResolutionRadiusSq clearance.signedStep
            else
              min (signedStepResolutionRadiusSq clearance)
                (signedChainResolutionRadiusSqFuel fuel q next
                  clearance.signedStep)
      cases qZero : q.isZero
      · dsimp only
        let next := -((Dense.Basic.DensePolynomial.divMod p q).remainder)
        cases nextZero : next.isZero
        · change
            min (signedStepResolutionRadiusSq clearance)
                (signedChainResolutionRadiusSqFuel (fuel + 1) q next clearance.signedStep) =
              min (signedStepResolutionRadiusSq clearance)
                (signedChainResolutionRadiusSqFuel fuel q next clearance.signedStep)
          apply congrArg (fun tail =>
            min (signedStepResolutionRadiusSq clearance) tail)
          apply inductionHypothesis q next clearance.signedStep
          have remainderDegree :=
            Dense.Basic.DensePolynomial.divMod_remainder_degreeCount_lt p q qZero
          change (-((Dense.Basic.DensePolynomial.divMod p q).remainder)).degreeCount ≤ fuel
          rw [Dense.Basic.DensePolynomial.degreeCount_neg]
          exact Nat.lt_succ_iff.mp
            (remainderDegree.trans_le enough)
        · rfl
      · rfl

/-- Additional fuel leaves a completed signed-chain radius unchanged.

The initial fuel must cover the second polynomial's represented coefficient count. -/
theorem signedChainResolutionRadiusSqFuel_add_of_degreeCount_le
    (extra fuel : Nat) (p q : Dense.Rational.Basic.CoordinatePolynomial) {root : Data.Rat.Interval.Bounds}
    (clearance : Clearance.Pair.Basic.Certificate p q root)
    (enough : q.degreeCount ≤ fuel) :
    signedChainResolutionRadiusSqFuel (fuel + extra) p q clearance =
      signedChainResolutionRadiusSqFuel fuel p q clearance := by
  induction extra with
  | zero => rw [Nat.add_zero]
  | succ extra inductionHypothesis =>
      rw [Nat.add_succ]
      calc
        signedChainResolutionRadiusSqFuel
              (fuel + extra + 1) p q clearance =
            signedChainResolutionRadiusSqFuel
              (fuel + extra) p q clearance :=
          signedChainResolutionRadiusSqFuel_succ_of_degreeCount_le
            (fuel + extra) p q clearance
              (enough.trans (Nat.le_add_right fuel extra))
        _ = signedChainResolutionRadiusSqFuel fuel p q clearance :=
          inductionHypothesis

/-- Sufficient fuel gives the canonical coefficient-count radius.

The retained degree bound writes the supplied fuel as the coefficient count
plus a natural remainder. Additional covered fuel leaves the same fold unchanged. -/
theorem signedChainResolutionRadiusSqFuel_stable
    (fuel : Nat) (p q : Dense.Rational.Basic.CoordinatePolynomial) {root : Data.Rat.Interval.Bounds}
    (clearance : Clearance.Pair.Basic.Certificate p q root)
    (enough : q.degreeCount ≤ fuel) :
    signedChainResolutionRadiusSqFuel fuel p q clearance =
      signedChainResolutionRadiusSqFuel q.degreeCount p q clearance := by
  have fuelEquation : q.degreeCount + (fuel - q.degreeCount) = fuel :=
    Subtraction.add_sub_of_le enough
  rw [← fuelEquation]
  exact signedChainResolutionRadiusSqFuel_add_of_degreeCount_le
    (fuel - q.degreeCount) q.degreeCount p q clearance le_rfl

/-- Compute the squared resolution radius of a complete signed Euclidean chain.

The second polynomial's coefficient count is the exact finite recursion
budget. Each retained signed step contributes its local resolution radius. -/
@[expose] def signedChainResolutionRadiusSq
    (p q : Dense.Rational.Basic.CoordinatePolynomial) {root : Data.Rat.Interval.Bounds}
    (clearance : Clearance.Pair.Basic.Certificate p q root) : Fraction.Rational :=
  signedChainResolutionRadiusSqFuel q.degreeCount p q clearance

/-- Unfold the radius fold at its canonical coefficient-count budget.

A nonzero signed remainder has smaller coefficient count. Fuel stability
therefore identifies the recursive tail with its own canonical budget. -/
theorem signedChainResolutionRadiusSq_eq
    (p q : Dense.Rational.Basic.CoordinatePolynomial) {root : Data.Rat.Interval.Bounds}
    (clearance : Clearance.Pair.Basic.Certificate p q root) :
    signedChainResolutionRadiusSq p q clearance =
      if q.isZero then Dense.Rational.Sign.Pair.Resolution.pairResolutionRadiusSq clearance
      else
        let next := -((Dense.Basic.DensePolynomial.divMod p q).remainder)
        if next.isZero then
          Dense.Rational.Sign.Pair.Resolution.pairResolutionRadiusSq clearance.signedStep
        else
          min (signedStepResolutionRadiusSq clearance)
            (signedChainResolutionRadiusSq q next
              clearance.signedStep) := by
  change signedChainResolutionRadiusSqFuel q.degreeCount p q clearance =
    if q.isZero then Dense.Rational.Sign.Pair.Resolution.pairResolutionRadiusSq clearance
    else
      let next := -((Dense.Basic.DensePolynomial.divMod p q).remainder)
      if next.isZero then
        Dense.Rational.Sign.Pair.Resolution.pairResolutionRadiusSq clearance.signedStep
      else
        min (signedStepResolutionRadiusSq clearance)
          (signedChainResolutionRadiusSqFuel
            (-((Dense.Basic.DensePolynomial.divMod p q).remainder)).degreeCount q
              (-((Dense.Basic.DensePolynomial.divMod p q).remainder)) clearance.signedStep)
  cases qZero : q.isZero
  · have degreePositive := Dense.Basic.DensePolynomial.degreeCount_pos_of_isZero_false qZero
    obtain ⟨qDegree, degreeEq⟩ :=
      Nat.exists_eq_succ_of_ne_zero degreePositive.ne'
    rw [degreeEq, signedChainResolutionRadiusSqFuel_succ, qZero]
    dsimp only
    let next := -((Dense.Basic.DensePolynomial.divMod p q).remainder)
    cases nextZero : next.isZero
    · change
        min (signedStepResolutionRadiusSq clearance)
            (signedChainResolutionRadiusSqFuel qDegree q next clearance.signedStep) =
          min (signedStepResolutionRadiusSq clearance)
            (signedChainResolutionRadiusSqFuel next.degreeCount q next clearance.signedStep)
      apply congrArg (fun tail =>
        min (signedStepResolutionRadiusSq clearance) tail)
      apply signedChainResolutionRadiusSqFuel_stable qDegree q next
        clearance.signedStep
      have remainderDegree := Dense.Basic.DensePolynomial.divMod_remainder_degreeCount_lt p q qZero
      change (-((Dense.Basic.DensePolynomial.divMod p q).remainder)).degreeCount ≤ qDegree
      rw [Dense.Basic.DensePolynomial.degreeCount_neg]
      rw [degreeEq] at remainderDegree
      exact Nat.lt_succ_iff.mp remainderDegree
    · rfl
  · have degreeZero := Dense.Basic.DensePolynomial.degreeCount_eq_zero_of_isZero qZero
    rw [degreeZero, signedChainResolutionRadiusSqFuel_zero]
    rfl

/-- The complete finite signed-chain resolution radius is positive.

Each recursive Euclidean step decreases the coefficient count and combines positive local radii. -/
theorem signedChainResolutionRadiusSq_pos
    (p q : Dense.Rational.Basic.CoordinatePolynomial) {root : Data.Rat.Interval.Bounds}
    (clearance : Clearance.Pair.Basic.Certificate p q root) :
    0 < signedChainResolutionRadiusSq p q clearance := by
  rw [signedChainResolutionRadiusSq_eq]
  split
  · exact Dense.Rational.Sign.Pair.Resolution.pairResolutionRadiusSq_pos clearance
  · dsimp only
    split
    · exact Dense.Rational.Sign.Pair.Resolution.pairResolutionRadiusSq_pos clearance.signedStep
    · apply Fraction.Order.Basic.lt_min
      · exact signedStepResolutionRadiusSq_pos clearance
      · exact Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq_pos q
          (-((Dense.Basic.DensePolynomial.divMod p q).remainder)) clearance.signedStep
termination_by q.degreeCount
decreasing_by
  rename_i qZero _
  have qNonzero : q.isZero = false :=
    Decide.bool_eq_false_of_not_eq_true q.isZero qZero
  rw [Dense.Basic.DensePolynomial.degreeCount_neg]
  exact Dense.Basic.DensePolynomial.divMod_remainder_degreeCount_lt p q qNonzero
end Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Radius

end
