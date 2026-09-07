import CCL.Boundary.Curve.Clear
import CCL.Boundary.WindingPointExclusion

/-!
# Uniform polynomial residual clearance on rational curve arcs

A constant cleared-coordinate gcd gives a positive coefficient-computed
lower bound for the denominator-cleared polynomial value on any displayed
finite parameter interval.  Dividing by a finite upper bound for the Horner
denominator power turns that into a positive lower bound for the original
polynomial residual at every non-pole point of the curve.

The final construction feeds that uniform residual directly to the
winding-one exclusion theorem.  One finite box refinement then excludes the
entire clear curve arc, rather than excluding only a selected rational point.
-/

namespace CCL.CurveResidualClearance

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev RationalCurve := CCL.RationalCurve.RationalCurve
abbrev Interval := RFAP.PathClearance.Interval
abbrev Box := RFAP.Boxes.Box
abbrev WindingOneState := RFAP.ShrinkingTrack.WindingOneState
abbrev WindingOneTrack := RFAP.ShrinkingTrack.WindingOneTrack

open RFAP.ConstructiveGaussian.Gaussian

/-- Real coordinate polynomial of the finite Horner denominator power. -/
def denominatorPowerReal
    (p : GaussianPolynomial) (curve : RationalCurve) :=
  RFAP.PathPolynomial.realPart
    (CCL.RationalCurve.clearingState p curve).denominatorPower

/-- Imaginary coordinate polynomial of the finite Horner denominator power. -/
def denominatorPowerImaginary
    (p : GaussianPolynomial) (curve : RationalCurve) :=
  RFAP.PathPolynomial.imagPart
    (CCL.RationalCurve.clearingState p curve).denominatorPower

/-- Strictly positive upper majorant for the squared norm of the finite
Horner denominator power throughout one parameter interval. -/
def denominatorPowerNormMajorant
    (p : GaussianPolynomial) (curve : RationalCurve)
    (interval : Interval) : Coordinate :=
  RFAP.PathClearance.evalSqBound
      (denominatorPowerReal p curve) interval +
    RFAP.PathClearance.evalSqBound
      (denominatorPowerImaginary p curve) interval + 1

theorem denominatorPowerNormMajorant_pos
    (p : GaussianPolynomial) (curve : RationalCurve)
    (interval : Interval) :
    0 < denominatorPowerNormMajorant p curve interval := by
  apply add_pos_of_nonneg_of_pos
  · exact add_nonneg
      (RFAP.PathClearance.evalSqBound_nonneg _ _)
      (RFAP.PathClearance.evalSqBound_nonneg _ _)
  · decide

theorem normSq_denominatorPower_eval_le
    (p : GaussianPolynomial) (curve : RationalCurve)
    (interval : Interval) {parameter : Coordinate}
    (inside : interval.Contains parameter) :
    normSq
        ((CCL.RationalCurve.clearingState p curve).denominatorPower.eval
          (RFAP.PathPolynomial.ofCoordinate parameter)) ≤
      denominatorPowerNormMajorant p curve interval := by
  have componentBound := add_le_add
    (RFAP.PathClearance.eval_sq_le_evalSqBound
      (denominatorPowerReal p curve) interval inside)
    (RFAP.PathClearance.eval_sq_le_evalSqBound
      (denominatorPowerImaginary p curve) interval inside)
  have normComponentBound :
      normSq
          ((CCL.RationalCurve.clearingState p curve).denominatorPower.eval
            (RFAP.PathPolynomial.ofCoordinate parameter)) ≤
        RFAP.PathClearance.evalSqBound
            (denominatorPowerReal p curve) interval +
          RFAP.PathClearance.evalSqBound
            (denominatorPowerImaginary p curve) interval := by
    simpa only [denominatorPowerReal, denominatorPowerImaginary,
      RFAP.PathPolynomial.eval_realPart,
      RFAP.PathPolynomial.eval_imagPart, normSq] using
        componentBound
  have majorantBound :
      RFAP.PathClearance.evalSqBound
            (denominatorPowerReal p curve) interval +
          RFAP.PathClearance.evalSqBound
            (denominatorPowerImaginary p curve) interval ≤
        denominatorPowerNormMajorant p curve interval := by
    unfold denominatorPowerNormMajorant
    exact le_add_of_nonneg_right (show (0 : Coordinate) ≤ 1 by decide)
  exact normComponentBound.trans majorantBound

/-- A positive pointwise lower bound for the original polynomial residual on
the non-pole part of one displayed rational curve interval. -/
structure Certificate
    (p : GaussianPolynomial) (curve : RationalCurve)
    (interval : Interval) where
  bound : Coordinate
  positive : 0 < bound
  lower : ∀ parameter : Coordinate, interval.Contains parameter →
    curve.denominatorAt parameter ≠ 0 →
      bound ≤ normSq (p.eval (curve.point parameter))

/-- Convert constant-gcd curve clearance into a lower bound for the original
polynomial by an entirely finite denominator-power majorant. -/
def certificate
    {p : GaussianPolynomial} {curve : RationalCurve}
    (clear : CCL.CurveClear.GlobalClear p curve)
    (interval : Interval) : Certificate p curve interval := by
  let cleared := clear.clearance interval
  let majorant := denominatorPowerNormMajorant p curve interval
  have majorantPositive : 0 < majorant :=
    denominatorPowerNormMajorant_pos p curve interval
  exact
    { bound := cleared.bound / majorant
      positive := RFAP.ConstructiveFraction.div_pos_direct cleared.positive
        majorantPositive
      lower := by
        intro parameter inside denominatorNonzero
        have clearedLower : cleared.bound ≤
            normSq ((CCL.RationalCurve.clearedEval p curve).eval
              (RFAP.PathPolynomial.ofCoordinate parameter)) := by
          simpa only [cleared,
            CCL.CurveClear.GlobalClear.clearance,
            CCL.CurveClear.realPolynomial,
            CCL.CurveClear.imaginaryPolynomial,
            CCL.RationalCurve.clearedReal,
            CCL.RationalCurve.clearedImag,
            RFAP.PathPolynomial.eval_realPart,
            RFAP.PathPolynomial.eval_imagPart, normSq] using
              (clear.clearance interval).lower parameter inside
        have semantics := CCL.RationalCurve.eval_clearedEval
          p curve parameter denominatorNonzero
        rw [semantics, normSq_mul] at clearedLower
        have powerUpper := normSq_denominatorPower_eval_le
          p curve interval inside
        have residualNonnegative :=
          normSq_nonneg (p.eval (curve.point parameter))
        have scaledUpper :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            powerUpper residualNonnegative
        apply (RFAP.ConstructiveFraction.div_le_iff_pos majorantPositive).2
        calc
          cleared.bound ≤
              normSq
                  ((CCL.RationalCurve.clearingState p curve).denominatorPower.eval
                    (RFAP.PathPolynomial.ofCoordinate parameter)) *
                normSq (p.eval (curve.point parameter)) := clearedLower
          _ ≤ majorant * normSq (p.eval (curve.point parameter)) :=
            scaledUpper
          _ = normSq (p.eval (curve.point parameter)) * majorant :=
            RFAP.ConstructiveFraction.mul_comm _ _ }

namespace Certificate

/-- Refine a winding-one box far enough that no non-pole point of this clear
curve interval can remain in the box. -/
def refinePast
    {p : GaussianPolynomial} {curve : RationalCurve} {interval : Interval}
    (clearance : Certificate p curve interval) {ambient : Box}
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient) :
    WindingOneState p ambient :=
  CCL.WindingPointExclusion.refinePastUniformMargin
    track current clearance.bound clearance.positive

theorem refinePast_refines
    {p : GaussianPolynomial} {curve : RationalCurve} {interval : Interval}
    (clearance : Certificate p curve interval) {ambient : Box}
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient) :
    (clearance.refinePast track current).box.Refines current.box :=
  CCL.WindingPointExclusion.refinePastUniformMargin_refines
    track current clearance.bound clearance.positive

theorem refinePast_excludes
    {p : GaussianPolynomial} {curve : RationalCurve} {interval : Interval}
    (clearance : Certificate p curve interval) {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (parameter : Coordinate) (inside : interval.Contains parameter)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    ¬(clearance.refinePast track current).box.Contains
      (curve.point parameter) :=
  CCL.WindingPointExclusion.refinePastUniformMargin_excludes
    degreePositive track current clearance.bound clearance.positive
      (curve.point parameter)
      (clearance.lower parameter inside denominatorNonzero)

end Certificate

end CCL.CurveResidualClearance
