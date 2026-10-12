module
import Purelib.Polynomial.Dense.Rational.Sign.Interval.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Radius
import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Sign.Interval.Resolved
import Purelib.Polynomial.Dense.Rational.Bounds.Lipschitz
import Purelib.Polynomial.Dense.Rational.Sign.Interval.Prepare
public import Purelib.Polynomial.Clearance.Pair.Operations
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

namespace Purelib.Polynomial.Dense.Rational.Sign.Pair.Resolution

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Data.Rat.Fraction.Order

/-- A small-cell inequality forcing one member of an adjacent clear pair to
be sign-resolved whenever the other is not.

The original paired Lipschitz bounds multiply the same retained
lower-endpoint squared radius. Their strict comparison with the
clearance retains the interval and both polynomial owners. -/
@[expose] public def PairResolution {p q : Dense.Rational.Basic.CoordinatePolynomial}
    (clearance : Clearance.Pair.Basic.Certificate p q interval) : Prop :=
  (Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound p interval +
      Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound q interval) *
      Interval.Radius.sampleRadiusSq interval interval.lower <
    clearance.bound

/-- Decide the adjacent-pair resolution inequality using exact rational comparison. -/
public instance {p q : Dense.Rational.Basic.CoordinatePolynomial} {interval : Data.Rat.Interval.Bounds}
    (clearance : Clearance.Pair.Basic.Certificate p q interval) :
    Decidable (PairResolution clearance) := by
  unfold PairResolution
  infer_instance

/-- Positive ambient squared radius making one adjacent-pair resolution
inequality hold on every displayed refinement.

The original clearance is divided by the sum of both retained
Lipschitz bounds increased by one. This exact positive threshold
controls the original paired margin on refinements. -/
@[expose] public def pairResolutionRadiusSq {p q : Dense.Rational.Basic.CoordinatePolynomial}
    {root : Data.Rat.Interval.Bounds} (clearance : Clearance.Pair.Basic.Certificate p q root) : Fraction.Rational :=
  clearance.bound /
    (Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound p root +
      Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound q root + 1)

/-- Positive pair clearance yields a positive ambient squared-radius threshold for sign resolution.

The original paired Lipschitz sum is nonnegative. Increasing it by
one makes the retained denominator positive, so the same clearance
quotient is positive. -/
public theorem pairResolutionRadiusSq_pos {p q : Dense.Rational.Basic.CoordinatePolynomial}
    {root : Data.Rat.Interval.Bounds} (clearance : Clearance.Pair.Basic.Certificate p q root) :
    0 < pairResolutionRadiusSq clearance := by
  apply Fraction.Order.Field.div_pos_direct
  · exact clearance.positive
  · have coefficientNonnegative : 0 ≤
        Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound p root +
          Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound q root :=
      add_nonneg (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg p root).2
        (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg q root).2
    calc
      0 < 1 := by decide
      _ ≤ Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound p root +
          Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound q root + 1 := by
        exact add_le_add coefficientNonnegative (le_refl 1)

/-- A refined interval below the ambient threshold satisfies the pair-resolution inequality with the restricted original
clearance.

The original refinement decreases both paired Lipschitz bounds.
The retained endpoint radius and positive ambient denominator
transport the same clearance to the refined interval. -/
public theorem pairResolution_of_refined_radiusSq
    {p q : Dense.Rational.Basic.CoordinatePolynomial} {root interval : Data.Rat.Interval.Bounds}
    (clearance : Clearance.Pair.Basic.Certificate p q root)
    (refines : interval.Refines root)
    (radius : Interval.Radius.sampleRadiusSq interval interval.lower <
      pairResolutionRadiusSq clearance) :
    PairResolution (clearance.restrict refines) := by
  let localCoefficient := Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound p interval +
    Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound q interval
  let rootCoefficient := Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound p root +
    Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound q root
  let localRadius := Interval.Radius.sampleRadiusSq interval interval.lower
  have localCoefficientNonnegative : 0 ≤ localCoefficient :=
    add_nonneg (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg p interval).2
      (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg q interval).2
  have rootCoefficientNonnegative : 0 ≤ rootCoefficient :=
    add_nonneg (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg p root).2
      (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg q root).2
  have localRadiusNonnegative : 0 ≤ localRadius := Interval.Radius.sampleRadiusSq_nonneg interval
  have coefficientLe : localCoefficient ≤ rootCoefficient :=
    add_le_add (Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound_le_of_refines p refines)
      (Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound_le_of_refines q refines)
  have denominatorPositive : 0 < rootCoefficient + 1 := by
    calc
      0 < 1 := by decide
      _ ≤ rootCoefficient + 1 := by
        exact add_le_add rootCoefficientNonnegative (le_refl 1)
  have scaledRadius : (rootCoefficient + 1) * localRadius <
      clearance.bound := by
    calc
      (rootCoefficient + 1) * localRadius <
          (rootCoefficient + 1) * pairResolutionRadiusSq clearance :=
        Arithmetic.mul_lt_mul_of_pos_left_direct
          denominatorPositive radius
      _ = clearance.bound := by
        dsimp only [pairResolutionRadiusSq]
        rw [Fraction.Field.mul_comm]
        apply Fraction.Field.div_mul_cancel_of_ne
        simpa only [rootCoefficient] using denominatorPositive.ne'
  change localCoefficient * localRadius < clearance.bound
  calc
    localCoefficient * localRadius ≤ rootCoefficient * localRadius :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct
        coefficientLe localRadiusNonnegative
    _ ≤ (rootCoefficient + 1) * localRadius :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct
        (le_add_of_nonneg_right (by decide)) localRadiusNonnegative
    _ < clearance.bound := scaledRadius

/-- Under pair resolution, failure of the first polynomial's strict sample margin forces the second polynomial's margin.

The original paired margin is strictly below the retained clearance.
Failure of the first margin supplies its weak opposite comparison,
leaving the same second margin strictly below its endpoint square. -/
public theorem second_margin_of_first_unresolved
    {p q : Dense.Rational.Basic.CoordinatePolynomial} {interval : Data.Rat.Interval.Bounds}
    (clearance : Clearance.Pair.Basic.Certificate p q interval)
    (resolution : PairResolution clearance)
    (firstUnresolved : ¬(
      Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound p interval *
          Interval.Radius.sampleRadiusSq interval interval.lower <
        p.eval interval.lower ^ 2)) :
    Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound q interval *
        Interval.Radius.sampleRadiusSq interval interval.lower <
      q.eval interval.lower ^ 2 := by
  let radius := Interval.Radius.sampleRadiusSq interval interval.lower
  let pMargin := Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound p interval * radius
  let qMargin := Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound q interval * radius
  have firstBound : p.eval interval.lower ^ 2 ≤ pMargin :=
    Arithmetic.le_of_not_gt_direct firstUnresolved
  have lower := clearance.lower
    interval.lower ⟨le_rfl, interval.valid⟩
  have marginBelowValues : pMargin + qMargin <
      p.eval interval.lower ^ 2 + q.eval interval.lower ^ 2 := by
    calc
      pMargin + qMargin =
          (Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound p interval +
            Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound q interval) * radius := by
        dsimp only [pMargin, qMargin]
        ring1
      _ < clearance.bound := resolution
      _ ≤ p.eval interval.lower ^ 2 + q.eval interval.lower ^ 2 := lower
  have shifted : p.eval interval.lower ^ 2 + qMargin <
      p.eval interval.lower ^ 2 + q.eval interval.lower ^ 2 := by
    calc
      p.eval interval.lower ^ 2 + qMargin ≤ pMargin + qMargin :=
        add_le_add firstBound (le_refl qMargin)
      _ < p.eval interval.lower ^ 2 + q.eval interval.lower ^ 2 :=
        marginBelowValues
  apply Arithmetic.lt_of_add_lt_add_right_direct (c := p.eval interval.lower ^ 2)
  rw [Fraction.Field.add_comm qMargin (p.eval interval.lower ^ 2),
    Fraction.Field.add_comm (q.eval interval.lower ^ 2) (p.eval interval.lower ^ 2)]
  exact shifted

/-- The second finite sign-certificate check succeeds when pair resolution holds and the first check returns none.

The original first classifier result excludes its strict margin.
The retained pair resolution then proves the second margin, and
that same second classifier returns its endpoint certificate. -/
public theorem certificate?_isSome_of_pairResolution_of_first_none
    {p q : Dense.Rational.Basic.CoordinatePolynomial} {interval : Data.Rat.Interval.Bounds}
    (clearance : Clearance.Pair.Basic.Certificate p q interval)
    (resolution : PairResolution clearance)
    (firstNone : Dense.Rational.Sign.Interval.Prepare.certificate? p interval = none) :
    (Dense.Rational.Sign.Interval.Prepare.certificate? q interval).isSome = true := by
  have firstUnresolved : ¬(
      Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound p interval *
          Interval.Radius.sampleRadiusSq interval interval.lower <
        p.eval interval.lower ^ 2) := by
    intro margin
    have firstSome := (Dense.Rational.Sign.Interval.Prepare.certificate?_isSome_iff p interval).2 margin
    rw [firstNone] at firstSome
    contradiction
  exact (Dense.Rational.Sign.Interval.Prepare.certificate?_isSome_iff q interval).2
    (second_margin_of_first_unresolved clearance resolution firstUnresolved)

/-- The terminal member of a signed chain is sign-resolved by the same
adjacent-pair inequality when its displayed successor is the zero
polynomial.

The original successor polynomial is zero at the retained endpoint.
The same pair inequality forces the terminal margin, so the original
classifier returns the displayed endpoint certificate and its equality. -/
@[expose] public def resolvedSign_of_terminal_pairResolution
    {q next : Dense.Rational.Basic.CoordinatePolynomial} {interval : Data.Rat.Interval.Bounds}
    (nextZero : next.isZero = true)
    (clearance : Clearance.Pair.Basic.Certificate q next interval)
    (resolution : PairResolution clearance) :
    Dense.Rational.Sign.Interval.Resolved.ResolvedSign q interval := by
  let radius := Interval.Radius.sampleRadiusSq interval interval.lower
  have radiusNonnegative : 0 ≤ radius :=
    (Arithmetic.sq_nonneg_direct
      (interval.lower - interval.lower)).trans (Fraction.Order.Basic.le_max_left _ _)
  have nextEvalZero := Dense.Basic.DensePolynomial.eval_eq_zero_of_isZero nextZero interval.lower
  have qMargin : Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound q interval * radius <
      q.eval interval.lower ^ 2 := by
    calc
      Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound q interval * radius ≤
          (Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound q interval +
            Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound next interval) * radius :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct
          (le_add_of_nonneg_right
            (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg next interval).2)
          radiusNonnegative
      _ < clearance.bound := resolution
      _ ≤ q.eval interval.lower ^ 2 + next.eval interval.lower ^ 2 :=
        clearance.lower interval.lower ⟨le_rfl, interval.valid⟩
      _ = q.eval interval.lower ^ 2 := by rw [nextEvalZero]; ring1
  have qMargin' : Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound q interval *
      Interval.Radius.sampleRadiusSq interval interval.lower < q.eval interval.lower ^ 2 := by
    simpa only [radius] using qMargin
  let certificate : Dense.Rational.Sign.Interval.Basic.Certificate q interval :=
    { sample := interval.lower
      sampleInside := ⟨le_rfl, interval.valid⟩
      margin := qMargin' }
  have found : Dense.Rational.Sign.Interval.Prepare.certificate? q interval = some certificate := by
    unfold Dense.Rational.Sign.Interval.Prepare.certificate?
    split
    · rfl
    · rename_i marginFailure
      exact (marginFailure qMargin').elim
  exact ⟨certificate, found⟩

end Purelib.Polynomial.Dense.Rational.Sign.Pair.Resolution
