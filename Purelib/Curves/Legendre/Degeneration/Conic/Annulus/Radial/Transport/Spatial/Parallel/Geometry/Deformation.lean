module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Tangent.Chord
import Purelib.Geometry.Rational.Box.Segment
import Purelib.Geometry.Rational.Affine.Segment
import Purelib.Data.Rat.Interval.Radius
import Purelib.Data.Rat.Interval.ConvexCombination
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # The actual short radial arc and chord in the same retained clear square

The original depth-seven width payment contains the entire actual curved
arc, not just its queried endpoints. Its displayed endpoint chord and the
pointwise ruled deformation stay in that SAME sharp square. The original
retained full-box clearance consequently pays every deformation point.
This is a quantitative base-plane deformation with fixed endpoints; no
signed root lift, owner-path identity or integral equality is asserted.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Geometry

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Rational
open Purelib.Riemann.RootContinuation

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Rational) < 2} {actual : Transport.Quarter site parameter 2 quarter positive}
variable {first last : Rational} {firstInside : FixedRootBoxPath.Inside first}
variable {lastInside : FixedRootBoxPath.Inside last}
variable {reading : Transport.Reading actual first firstInside}
variable {targetReading : Transport.Reading actual last lastInside}
variable {regular : parameter ≠ criticalValue site}
variable {payment : (last - first) ^ 2 ≤ Approximation.Rational.Geometric.Basic.quarterRadius 1 7}

/-- The SAME sharp source square contains every actual curved point between its ordered original chart endpoints. -/
theorem arc_inside (_geometry : Geometry reading targetReading regular payment)
    (ordered : first ≤ last) {time : Rational} (contained : first ≤ time ∧ time ≤ last) :
    (box site parameter quarter first regular).Contains
      (coordinate site parameter 2 quarter positive time) := by
  let interval : Interval.Bounds := ⟨first, last, ordered⟩
  have small := Interval.Radius.sub_sq_le_sampleRadiusSq interval (sample := interval.lower) contained
  rewrite [Interval.Radius.sampleRadiusSq_lower_eq_widthSq] at small
  exact Radial.Clearance.quarter_target_inside site parameter quarter regular first time (small.trans payment)

/-- Unit-fraction interpolation of the original times remains on the SAME actual short curved arc. -/
theorem fraction_inside (geometry : Geometry reading targetReading regular payment)
    (ordered : first ≤ last) {fraction : Rational} (inside : 0 ≤ fraction ∧ fraction ≤ 1) :
    (box site parameter quarter first regular).Contains
      (coordinate site parameter 2 quarter positive (first + fraction * (last - first))) :=
  geometry.arc_inside ordered (Box.coordinate_between ⟨Order.Basic.le_refl _, ordered⟩
    ⟨ordered, Order.Basic.le_refl _⟩ inside)

/-- The actual endpoint chord stays in the SAME square already retained for the original spatial Route. -/
theorem chord_inside (_geometry : Geometry reading targetReading regular payment)
    {fraction : Rational} (inside : 0 ≤ fraction ∧ fraction ≤ 1) :
    (box site parameter quarter first regular).Contains
      (Tangent.baseChord site parameter 2 quarter positive first (last - first) fraction) := by
  unfold Tangent.baseChord
  rewrite [show first + (last - first) = last by ring1]
  exact Box.contains_line (source_inside (positive := positive) regular)
    (target_inside (positive := positive) regular payment) inside

/-- The pointwise affine deformation joins the actual radial curve to its displayed endpoint chord.

The unchanged Geometry is an explicit input. Its Reading and Route owners
are not replaced. The deformation changes only the displayed base point;
the actual signed-root continuation must be certified separately.
-/
@[expose] def deformation (_geometry : Geometry reading targetReading regular payment)
    (fraction blend : Rational) : Canonical :=
  let curve := coordinate site parameter 2 quarter positive (first + fraction * (last - first))
  let chord := Tangent.baseChord site parameter 2 quarter positive first (last - first) fraction
  Affine.line curve (chord - curve) blend

/-- Every displayed deformation point stays inside the identical retained factor-clear source square. -/
theorem deformation_inside (geometry : Geometry reading targetReading regular payment)
    (ordered : first ≤ last) {fraction blend : Rational}
    (fractionInside : 0 ≤ fraction ∧ fraction ≤ 1) (blendInside : 0 ≤ blend ∧ blend ≤ 1) :
    (box site parameter quarter first regular).Contains (geometry.deformation fraction blend) :=
  Box.contains_line (geometry.fraction_inside ordered fractionInside) (geometry.chord_inside fractionInside) blendInside

/-- The zero deformation parameter reads the original actual curved conic point. -/
theorem deformation_curve (geometry : Geometry reading targetReading regular payment) (fraction : Rational) :
    geometry.deformation fraction 0 =
      coordinate site parameter 2 quarter positive (first + fraction * (last - first)) := Affine.line_zero _ _

/-- The unit deformation parameter reads that same original endpoint chord at its retained fraction. -/
theorem deformation_chord (geometry : Geometry reading targetReading regular payment) (fraction : Rational) :
    geometry.deformation fraction 1 =
      Tangent.baseChord site parameter 2 quarter positive first (last - first) fraction := Affine.line_one _ _

/-- Every deformation parameter fixes the exact original source coordinate. -/
theorem deformation_first (geometry : Geometry reading targetReading regular payment) (blend : Rational) :
    geometry.deformation 0 blend = coordinate site parameter 2 quarter positive first := by
  unfold deformation
  rewrite [show first + 0 * (last - first) = first by ring1, Tangent.baseChord_zero]
  exact Affine.Segment.line_self _ _

/-- Every deformation parameter fixes the exact original target coordinate. -/
theorem deformation_last (geometry : Geometry reading targetReading regular payment) (blend : Rational) :
    geometry.deformation 1 blend = coordinate site parameter 2 quarter positive last := by
  unfold deformation
  rewrite [show first + 1 * (last - first) = last by ring1, Tangent.baseChord_one,
    show first + (last - first) = last by ring1]
  exact Affine.Segment.line_self _ _

/-- The SAME retained original full-cubic clearance bound pays every actual ruled-deformation point. -/
theorem deformation_lower (geometry : Geometry reading targetReading regular payment)
    (ordered : first ≤ last) {fraction blend : Rational}
    (fractionInside : 0 ≤ fraction ∧ fraction ≤ 1) (blendInside : 0 ≤ blend ∧ blend ≤ 1) :
    geometry.clearance.bound ≤
      Norm.Basic.normSq ((Paths.polynomial parameter).eval (geometry.deformation fraction blend)) :=
  geometry.clearance.lower _ (geometry.deformation_inside ordered fractionInside blendInside)

/-- The original Legendre cubic has no zero on this explicitly displayed short-arc deformation. -/
theorem deformation_nonroot (geometry : Geometry reading targetReading regular payment)
    (ordered : first ≤ last) {fraction blend : Rational}
    (fractionInside : 0 ≤ fraction ∧ fraction ≤ 1) (blendInside : 0 ≤ blend ∧ blend ≤ 1) :
    (Paths.polynomial parameter).eval (geometry.deformation fraction blend) ≠ 0 :=
  geometry.clearance.eval_ne_zero (geometry.deformation_inside ordered fractionInside blendInside)

/-- The actual ruled deformation has the same internally computed fourth-power tube budget as its original chord.

The estimate uses the original conic tangent certificates and contracts the
same chord displacement by the retained affine blend. It preserves the
original half-gap and time width; no period or integral comparison is used.
-/
theorem deformation_distance_le (geometry : Geometry reading targetReading regular payment)
    {fraction blend : Rational} (fractionInside : 0 ≤ fraction ∧ fraction ≤ 1)
    (blendInside : 0 ≤ blend ∧ blend ≤ 1) :
    Norm.Basic.normSq (geometry.deformation fraction blend -
      coordinate site parameter 2 quarter positive (first + fraction * (last - first))) ≤
      25 * Norm.Basic.normSq (halfGap site parameter) * (last - first) ^ 4 := by
  unfold deformation
  rewrite [Norm.Bounds.normSq_sub_symm]
  exact (Affine.Segment.normSq_source_sub_line_le _ _ blendInside).trans
    (Tangent.baseChord_error_le site parameter 2 quarter positive
      (of_decide_eq_true rfl : (1 : Rational) ≤ 2) (Order.Basic.le_refl _) first (last - first) fraction fractionInside)

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Geometry

end
