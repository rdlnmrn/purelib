module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Ratio.Cleared
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Parallel.Through
import Purelib.Geometry.Plane.Line.Quadrance
public import Purelib.Geometry.Plane.Line.Spread
public import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Affine.Quadrance
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.Geometry.Triangles.Right.Trigonometry
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Basic

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Plane.Point.Affine

section
@[expose] public section

/-!
# Divine Proportions, Chapter 21: two-dimensional problems

The applications are separated into their finite metric identities and the
geometric incidence arguments that supply those identities.  Denominators are
always accompanied by explicit nonzero certificates.
-/

namespace Purelib.Geometry.Circles.Eyeball

section

variable {K : Type*} [ExplicitField K]

/-! ## Problem 6: the eyeball theorem -/

/-- The first Spread-ratio step in the Eyeball theorem. A marker on the source circle lies on the same displayed tangent
ray as the tangent point on the other circle, so replacing that ray representative preserves its spread with the line of
centers. -/
theorem eyeball_tangent_spread [DecidableEq K]
    (source other tangent marker : Geometry.Plane.Point K)
    (tangentRay : Geometry.Plane.Line K)
    (sourceOtherDistinct : source ≠ other)
    (sourceTangentDistinct : source ≠ tangent)
    (otherTangentDistinct : other ≠ tangent)
    (sourceMarkerDistinct : source ≠ marker)
    (sourceOtherNonNull :
      ¬ (Incidence.lineThrough source other sourceOtherDistinct).IsNull)
    (sourceTangentNonNull :
      ¬ (Incidence.lineThrough source tangent sourceTangentDistinct).IsNull)
    (sourceMarkerNonNull :
      ¬ (Incidence.lineThrough source marker sourceMarkerDistinct).IsNull)
    (twoNonzero : (2 : K) ≠ 0)
    (rightAtTangent :
      (Incidence.lineThrough source tangent sourceTangentDistinct).Perpendicular
        (Incidence.lineThrough other tangent otherTangentDistinct))
    (rayContainsSource : tangentRay.Contains source)
    (rayContainsTangent : tangentRay.Contains tangent)
    (rayContainsMarker : tangentRay.Contains marker)
    (otherRadius centerSeparation : K)
    (otherRadiusValue : Quadrance.quadrance other tangent = otherRadius)
    (centerSeparationValue :
      Quadrance.quadrance source other = centerSeparation) :
    Spread.spread (Incidence.lineThrough source marker sourceMarkerDistinct)
        (Incidence.lineThrough source other sourceOtherDistinct)
        sourceMarkerNonNull sourceOtherNonNull =
      otherRadius / centerSeparation := by
  have tangentMarkerParallel :
      (Incidence.lineThrough source tangent sourceTangentDistinct).Parallel
        (Incidence.lineThrough source marker sourceMarkerDistinct) :=
    Parallel.Through.parallel_pair_through_common_line source tangent marker
      sourceTangentDistinct sourceMarkerDistinct tangentRay
      rayContainsSource rayContainsTangent rayContainsMarker
  have replacement := Spread.spread_eq_of_parallel_pairs
    (Incidence.lineThrough source tangent sourceTangentDistinct)
    (Incidence.lineThrough source other sourceOtherDistinct)
    (Incidence.lineThrough source marker sourceMarkerDistinct)
    (Incidence.lineThrough source other sourceOtherDistinct)
    sourceTangentNonNull sourceOtherNonNull sourceMarkerNonNull
    sourceOtherNonNull tangentMarkerParallel
    (Geometry.Plane.Line.parallel_refl _)
  have ratio := Triangles.Right.Trigonometry.spread_ratio source other tangent sourceOtherDistinct
    sourceTangentDistinct otherTangentDistinct sourceOtherNonNull
    sourceTangentNonNull twoNonzero rightAtTangent
  calc
    Spread.spread (Incidence.lineThrough source marker sourceMarkerDistinct)
        (Incidence.lineThrough source other sourceOtherDistinct)
        sourceMarkerNonNull sourceOtherNonNull =
      Spread.spread (Incidence.lineThrough source tangent sourceTangentDistinct)
        (Incidence.lineThrough source other sourceOtherDistinct)
        sourceTangentNonNull sourceOtherNonNull := replacement.symm
    _ = Spread.spread (Incidence.lineThrough source other sourceOtherDistinct)
        (Incidence.lineThrough source tangent sourceTangentDistinct)
        sourceOtherNonNull sourceTangentNonNull :=
      Spread.spread_symm _ _ sourceTangentNonNull sourceOtherNonNull
    _ = Quadrance.quadrance other tangent / Quadrance.quadrance source other := ratio
    _ = otherRadius / centerSeparation := by
      rw [otherRadiusValue, centerSeparationValue]

/-- The metric calculation for either eye of the Eyeball theorem. A right triangle from one endpoint of a chord to its
midpoint converts the supplied tangent spread `otherRadius / centerSeparation` into the common cleared chord quadrance
`centerSeparation * chord = 4 * ownRadius * otherRadius`. -/
theorem eyeball_chord_quadrance_cleared [DecidableEq K]
    (center first second : Geometry.Plane.Point K)
    (centerFirstDistinct : center ≠ first)
    (centerMidpointDistinct : center ≠ Affine.midpoint first second)
    (firstMidpointDistinct : first ≠ Affine.midpoint first second)
    (centerFirstNonNull :
      ¬ (Incidence.lineThrough center first centerFirstDistinct).IsNull)
    (centerMidpointNonNull :
      ¬ (Incidence.lineThrough center (Affine.midpoint first second)
        centerMidpointDistinct).IsNull)
    (twoNonzero : (2 : K) ≠ 0)
    (rightAtMidpoint :
      (Incidence.lineThrough center (Affine.midpoint first second)
          centerMidpointDistinct).Perpendicular
        (Incidence.lineThrough first (Affine.midpoint first second)
          firstMidpointDistinct))
    (ownRadius otherRadius centerSeparation : K)
    (centerSeparationNonzero : centerSeparation ≠ 0)
    (ownRadiusValue : Quadrance.quadrance center first = ownRadius)
    (tangentSpreadValue :
      Spread.spread (Incidence.lineThrough center first centerFirstDistinct)
          (Incidence.lineThrough center (Affine.midpoint first second)
            centerMidpointDistinct)
          centerFirstNonNull centerMidpointNonNull =
        otherRadius / centerSeparation) :
    centerSeparation * Quadrance.quadrance first second =
      4 * ownRadius * otherRadius := by
  have ownQuadranceNonzero : Quadrance.quadrance center first ≠ 0 :=
    fun quadranceZero => centerFirstNonNull
      ((Quadrance.null_line_iff_quadrance_zero center first centerFirstDistinct).2
        quadranceZero)
  have ratioAtCenter := Triangles.Right.Trigonometry.spread_ratio center first (Affine.midpoint first second)
    centerFirstDistinct centerMidpointDistinct firstMidpointDistinct
    centerFirstNonNull centerMidpointNonNull twoNonzero rightAtMidpoint
  have ratioEquality :
      otherRadius / centerSeparation =
        Quadrance.quadrance first (Affine.midpoint first second) /
          Quadrance.quadrance center first := by
    calc
      otherRadius / centerSeparation =
          Spread.spread (Incidence.lineThrough center first centerFirstDistinct)
            (Incidence.lineThrough center (Affine.midpoint first second)
              centerMidpointDistinct)
            centerFirstNonNull centerMidpointNonNull :=
        tangentSpreadValue.symm
      _ = Quadrance.quadrance first (Affine.midpoint first second) /
          Quadrance.quadrance center first := ratioAtCenter
  have spreadCrossProduct := Ratio.Cleared.cross_mul_of_div_eq_div
    centerSeparationNonzero ownQuadranceNonzero ratioEquality
  rw [ownRadiusValue] at spreadCrossProduct
  have fourAsProduct : (4 : K) = 2 * 2 := by ring1
  have fourNonzero : (4 : K) ≠ 0 := by
    rw [fourAsProduct]
    exact ExplicitField.mul_ne_zero twoNonzero twoNonzero
  have midpointValue := Quadrance.midpoint_quadrance first second twoNonzero
  have midpointCleared :
      Quadrance.quadrance (Affine.midpoint first second) first * 4 =
        Quadrance.quadrance first second := by
    calc
      Quadrance.quadrance (Affine.midpoint first second) first * 4 =
          (Quadrance.quadrance first second / 4) * 4 := by rw [midpointValue]
      _ = Quadrance.quadrance first second :=
        ExplicitField.div_mul_cancel _ fourNonzero
  calc
    centerSeparation * Quadrance.quadrance first second =
        centerSeparation *
          (Quadrance.quadrance (Affine.midpoint first second) first * 4) := by
            rw [midpointCleared]
    _ = 4 *
        (Quadrance.quadrance first (Affine.midpoint first second) * centerSeparation) := by
          rw [Quadrance.quadrance_symm (Affine.midpoint first second) first]
          ring1
    _ = 4 * (otherRadius * ownRadius) := by rw [← spreadCrossProduct]
    _ = 4 * ownRadius * otherRadius := by ring1

/-- Problem 6 (Eyeball theorem), final symmetric cancellation. Applying `eyeball_chord_quadrance_cleared` to the two
circles supplies the two premises. -/
theorem problem_6
    (firstChord secondChord firstRadius secondRadius
      centerSeparation : K)
    (centerSeparationNonzero : centerSeparation ≠ 0)
    (firstChordFormula :
      centerSeparation * firstChord = 4 * firstRadius * secondRadius)
    (secondChordFormula :
      centerSeparation * secondChord = 4 * secondRadius * firstRadius) :
    firstChord = secondChord := by
  have productsEqual :
      centerSeparation * firstChord = centerSeparation * secondChord := by
    calc
      centerSeparation * firstChord = 4 * firstRadius * secondRadius :=
        firstChordFormula
      _ = 4 * secondRadius * firstRadius := by ring1
      _ = centerSeparation * secondChord := secondChordFormula.symm
  have centerCancel : centerSeparation * centerSeparation⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel centerSeparation
      centerSeparationNonzero
  have inverseCenterCancel :
      centerSeparation⁻¹ * centerSeparation = (1 : K) := by
    calc
      centerSeparation⁻¹ * centerSeparation =
          centerSeparation * centerSeparation⁻¹ := by ring1
      _ = 1 := centerCancel
  calc
    firstChord = 1 * firstChord := by rw [one_mul]
    _ = centerSeparation⁻¹ *
        (centerSeparation * firstChord) := by
          rw [← mul_assoc, inverseCenterCancel, one_mul]
    _ = centerSeparation⁻¹ *
        (centerSeparation * secondChord) := by rw [productsEqual]
    _ = secondChord := by rw [← mul_assoc, inverseCenterCancel, one_mul]
end
end Purelib.Geometry.Circles.Eyeball

end
