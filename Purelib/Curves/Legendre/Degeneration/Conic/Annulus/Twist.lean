module

public import Purelib.Curves.Legendre.Degeneration.Conic.Rotation
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial
import Purelib.Geometry.Gaussian.UnitCircle.Stereographic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # An explicit rational twist map of the original conic annulus

The original squared radius determines a rational phase on four original
Waist.direction charts. Multiplication by that phase and its conjugate
preserves the exact conic product and both coordinate radii. The existing
1/64 parameter bound derives the proper radial interval internally; its two
boundary phases are exactly one. Conjugate rotation is an executable inverse.

This constructs an annulus automorphism on rational conic points. It does
not identify it with parameter monodromy, prove a Dehn homology formula,
transport cofactor/full-cubic Owners, glue a fixed collar to a complement,
or attach canonical cycles. Smoothing winding two is usable for the labelled
monodromy only after those independent realization certificates are built.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus

open Purelib.Data.Rat.Fraction
open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Basic (UnitVertex)
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)

namespace Twist

/-- Select one original rational quarter and its affine time for one complete unit phase circuit. -/
def phaseChart (position : Fraction.Rational) : UnitCircuitQuarter × Fraction.Rational :=
  if position ≤ 1 / 4 then ⟨.first, 4 * position⟩
  else if position ≤ 1 / 2 then ⟨.second, 4 * position - 1⟩
  else if position ≤ 3 / 4 then ⟨.third, 4 * position - 2⟩
  else ⟨.fourth, 4 * position - 3⟩

/-- Read the exact certified unit vertex on the selected original waist quarter and its retained affine time. -/
def phase (position : Fraction.Rational) : UnitVertex :=
  let chart := phaseChart position
  Waist.direction chart.1 chart.2

/-- The phase uses the SAME original quarter and affine time selected by its finite rational comparison. -/
theorem phase_chart (position : Fraction.Rational) :
    phase position = Waist.direction (phaseChart position).1 (phaseChart position).2 := by
  unfold phase
  rfl

/-- Scaling an actual rational interval to a quarter phase keeps its affine time in the unit interval. -/
private theorem chart_bounds {lower upper position offset : Fraction.Rational}
    (inside : lower ≤ position ∧ position ≤ upper)
    (first : 4 * lower - offset = 0) (last : 4 * upper - offset = 1) :
    0 ≤ 4 * position - offset ∧ 4 * position - offset ≤ 1 := by
  have lowerBound := Order.Arithmetic.sub_le_sub_right_direct
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct inside.1
      (by decide +kernel : (0 : Fraction.Rational) ≤ 4)) offset
  have upperBound := Order.Arithmetic.sub_le_sub_right_direct
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct inside.2
      (by decide +kernel : (0 : Fraction.Rational) ≤ 4)) offset
  rewrite [first] at lowerBound
  rewrite [last] at upperBound
  exact ⟨lowerBound, upperBound⟩

/-- Every admitted phase position selects an actual unit-interval time in its original retained rational quarter. -/
theorem phaseChart_inside (position : Fraction.Rational) (inside : 0 ≤ position ∧ position ≤ 1) :
    0 ≤ (phaseChart position).2 ∧ (phaseChart position).2 ≤ 1 := by
  by_cases first : position ≤ 1 / 4
  · unfold phaseChart
    rewrite [if_pos first]
    have actual := chart_bounds (offset := 0) ⟨inside.1, first⟩
      (by decide +kernel : (4 : Fraction.Rational) * 0 - 0 = 0)
      (by decide +kernel : (4 : Fraction.Rational) * (1 / 4) - 0 = 1)
    exact Eq.mp (congrArg (fun time : Fraction.Rational => 0 ≤ time ∧ time ≤ 1)
      (by change 4 * position - 0 = 4 * position; ring1)) actual
  · by_cases second : position ≤ 1 / 2
    · unfold phaseChart
      rewrite [if_neg first, if_pos second]
      exact chart_bounds
        ⟨(Fraction.Order.Basic.le_total (1 / 4) position).resolve_right first, second⟩
        (by decide +kernel : (4 : Fraction.Rational) * (1 / 4) - 1 = 0)
        (by decide +kernel : (4 : Fraction.Rational) * (1 / 2) - 1 = 1)
    · by_cases third : position ≤ 3 / 4
      · unfold phaseChart
        rewrite [if_neg first, if_neg second, if_pos third]
        exact chart_bounds
          ⟨(Fraction.Order.Basic.le_total (1 / 2) position).resolve_right second, third⟩
          (by decide +kernel : (4 : Fraction.Rational) * (1 / 2) - 2 = 0)
          (by decide +kernel : (4 : Fraction.Rational) * (3 / 4) - 2 = 1)
      · unfold phaseChart
        rewrite [if_neg first, if_neg second, if_neg third]
        exact chart_bounds
          ⟨(Fraction.Order.Basic.le_total (3 / 4) position).resolve_right third, inside.2⟩
          (by decide +kernel : (4 : Fraction.Rational) * (3 / 4) - 3 = 0)
          (by decide +kernel : (4 : Fraction.Rational) * 1 - 3 = 1)

/-- The actual phase begins at the original first quarter's initial unit vertex. -/
theorem phase_zero : phase 0 = Waist.direction .first 0 := by
  unfold phase phaseChart
  rewrite [if_pos (by decide +kernel : (0 : Fraction.Rational) ≤ 1 / 4)]
  change Waist.direction .first (4 * 0) = Waist.direction .first 0
  exact congrArg (Waist.direction .first) (by decide +kernel)

/-- The first retained rational phase seam is the actual first-to-second quarter join. -/
theorem phase_first_join : phase (1 / 4) = Waist.direction .second 0 := by
  unfold phase phaseChart
  rewrite [if_pos (Fraction.Order.Basic.le_refl (1 / 4))]
  change Waist.direction .first (4 * (1 / 4)) = _
  exact (congrArg (Waist.direction .first) (by decide +kernel : (4 : Fraction.Rational) * (1 / 4) = 1)).trans
    Waist.directions_join.1

/-- The second retained rational phase seam is the actual second-to-third quarter join. -/
theorem phase_second_join : phase (1 / 2) = Waist.direction .third 0 := by
  unfold phase phaseChart
  rewrite [if_neg (by decide +kernel : ¬ (1 / 2 : Fraction.Rational) ≤ 1 / 4),
    if_pos (Fraction.Order.Basic.le_refl (1 / 2))]
  change Waist.direction .second (4 * (1 / 2) - 1) = _
  exact (congrArg (Waist.direction .second)
    (by decide +kernel : (4 : Fraction.Rational) * (1 / 2) - 1 = 1)).trans Waist.directions_join.2.1

/-- The third retained rational phase seam is the actual third-to-fourth quarter join. -/
theorem phase_third_join : phase (3 / 4) = Waist.direction .fourth 0 := by
  unfold phase phaseChart
  rewrite [if_neg (by decide +kernel : ¬ (3 / 4 : Fraction.Rational) ≤ 1 / 4),
    if_neg (by decide +kernel : ¬ (3 / 4 : Fraction.Rational) ≤ 1 / 2),
    if_pos (Fraction.Order.Basic.le_refl (3 / 4))]
  change Waist.direction .third (4 * (3 / 4) - 2) = _
  exact (congrArg (Waist.direction .third)
    (by decide +kernel : (4 : Fraction.Rational) * (3 / 4) - 2 = 1)).trans Waist.directions_join.2.2.1

/-- The actual first closed phase quarter uses its original affine time. -/
theorem phase_first_chart (time : Fraction.Rational) (upper : time ≤ 1 / 4) :
    phase time = Waist.direction .first (4 * time) := by
  unfold phase phaseChart
  rewrite [if_pos upper]
  rfl

/-- The actual second closed quarter retains the original first cardinal join. -/
theorem phase_second_chart (time : Fraction.Rational) (inside : 1 / 4 ≤ time ∧ time ≤ 1 / 2) :
    phase time = Waist.direction .second (4 * time - 1) := by
  by_cases first : time ≤ 1 / 4
  · have same : time = 1 / 4 := first.antisymm inside.1
    rewrite [same, phase_first_join]
    exact congrArg (Waist.direction .second) (by decide +kernel)
  · unfold phase phaseChart
    rewrite [if_neg first, if_pos inside.2]
    rfl

/-- The actual third closed quarter retains the original second cardinal join. -/
theorem phase_third_chart (time : Fraction.Rational) (inside : 1 / 2 ≤ time ∧ time ≤ 3 / 4) :
    phase time = Waist.direction .third (4 * time - 2) := by
  have notFirst : ¬ time ≤ 1 / 4 := fun first =>
    (by decide +kernel : ¬ (1 / 2 : Fraction.Rational) ≤ 1 / 4) (inside.1.trans first)
  by_cases second : time ≤ 1 / 2
  · have same : time = 1 / 2 := second.antisymm inside.1
    rewrite [same, phase_second_join]
    exact congrArg (Waist.direction .third) (by decide +kernel)
  · unfold phase phaseChart
    rewrite [if_neg notFirst, if_neg second, if_pos inside.2]
    rfl

/-- The actual fourth closed quarter retains the original third cardinal join. -/
theorem phase_fourth_chart (time : Fraction.Rational) (inside : 3 / 4 ≤ time ∧ time ≤ 1) :
    phase time = Waist.direction .fourth (4 * time - 3) := by
  have notFirst : ¬ time ≤ 1 / 4 := fun first =>
    (by decide +kernel : ¬ (3 / 4 : Fraction.Rational) ≤ 1 / 4) (inside.1.trans first)
  have notSecond : ¬ time ≤ 1 / 2 := fun second =>
    (by decide +kernel : ¬ (3 / 4 : Fraction.Rational) ≤ 1 / 2) (inside.1.trans second)
  by_cases third : time ≤ 3 / 4
  · have same : time = 3 / 4 := third.antisymm inside.1
    rewrite [same, phase_third_join]
    exact congrArg (Waist.direction .fourth) (by decide +kernel)
  · unfold phase phaseChart
    rewrite [if_neg notFirst, if_neg notSecond, if_neg third]
    rfl

/-- The complete original phase returns to the first quarter's identical initial unit vertex. -/
theorem phase_one : phase 1 = Waist.direction .first 0 := by
  unfold phase phaseChart
  rewrite [if_neg (by decide +kernel : ¬ (1 : Fraction.Rational) ≤ 1 / 4),
    if_neg (by decide +kernel : ¬ (1 : Fraction.Rational) ≤ 1 / 2),
    if_neg (by decide +kernel : ¬ (1 : Fraction.Rational) ≤ 3 / 4)]
  change Waist.direction .fourth (4 * 1 - 3) = _
  exact (congrArg (Waist.direction .fourth)
    (by decide +kernel : (4 : Fraction.Rational) * 1 - 3 = 1)).trans Waist.directions_join.2.2.2

/-- The common original initial phase is exactly the Gaussian multiplicative identity. -/
private theorem first_value : (Waist.direction .first 0).value = (1 : Canonical) := by
  rewrite [Waist.direction_value, Geometry.Gaussian.UnitCircle.Stereographic.unitQuarterPoint_zero]
  decide +kernel

/-- The original phase is exactly one on the inner radial endpoint. -/
theorem phase_zero_value : (phase 0).value = (1 : Canonical) :=
  (congrArg UnitVertex.value phase_zero).trans first_value

/-- The same original phase is exactly one on the outer radial endpoint after the full circuit. -/
theorem phase_one_value : (phase 1).value = (1 : Canonical) :=
  (congrArg UnitVertex.value phase_one).trans first_value

/-- The original chart selector retains its exact quarter times at all five cardinal positions.

At an internal seam the earlier quarter retains time one. Its original
joined endpoint is also the next quarter's time zero; the first and final
positions retain their two original outer roles.
-/
theorem phaseChart_cardinals :
    phaseChart 0 = (.first, 0) ∧ phaseChart (1 / 4) = (.first, 1) ∧
      phaseChart (1 / 2) = (.second, 1) ∧ phaseChart (3 / 4) = (.third, 1) ∧
      phaseChart 1 = (.fourth, 1) := by
  decide +kernel

/-- The admitted original parameter bound gives an explicit upper bound on the annulus inner squared radius. -/
theorem innerRadiusSq_le (site : Fin 2) (parameter : Canonical)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational)) :
    innerRadiusSq site parameter ≤ 1 / 1024 := by
  have gap := Radial.halfGap_bound site parameter bound
  have squared := Order.Arithmetic.pow_le_pow_direct (Norm.Basic.normSq_nonneg (halfGap site parameter)) gap 2
  unfold innerRadiusSq
  apply (Fraction.Order.Field.div_le_iff_pos
    (by decide +kernel : (0 : Fraction.Rational) < outerRadiusSq)).mpr
  calc
    _ = Norm.Basic.normSq (halfGap site parameter) ^ 2 := by
      unfold smoothing
      rewrite [pow_two, Norm.Basic.normSq_mul]
      ring1
    _ ≤ (1 / 256 : Fraction.Rational) ^ 2 := squared
    _ = (1 / 1024 : Fraction.Rational) * outerRadiusSq := by decide +kernel

/-- The SAME admitted parameter bound derives a strictly proper original radial interval. -/
theorem proper (site : Fin 2) (parameter : Canonical)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational)) :
    innerRadiusSq site parameter < outerRadiusSq :=
  (innerRadiusSq_le site parameter bound).trans_lt (by decide +kernel)

/-- Normalize the actual original first-coordinate squared radius in the SAME original radial interval. -/
@[expose] def radialParameter (site : Fin 2) (parameter coordinate : Canonical) : Fraction.Rational :=
  (Norm.Basic.normSq coordinate - innerRadiusSq site parameter) /
    (outerRadiusSq - innerRadiusSq site parameter)

/-- Every admitted original annulus point has an actual unit-interval radial parameter; width is derived internally. -/
theorem radialParameter_inside {site : Fin 2} {parameter coordinate : Canonical}
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational))
    (inside : Contains site parameter coordinate) :
    0 ≤ radialParameter site parameter coordinate ∧ radialParameter site parameter coordinate ≤ 1 :=
  Fraction.Order.Field.fraction_inside (proper site parameter bound) inside

/-- Exact preservation of the actual squared radius preserves the whole original phase selection. -/
theorem phase_eq_of_radius {site : Fin 2} {parameter first last : Canonical}
    (same : Norm.Basic.normSq first = Norm.Basic.normSq last) :
    phase (radialParameter site parameter first) = phase (radialParameter site parameter last) := by
  unfold radialParameter
  rewrite [same]
  rfl

/-- The same original inner-boundary squared radius has exactly zero normalized radial parameter. -/
theorem radialParameter_inner {site : Fin 2} {parameter coordinate : Canonical}
    (boundary : Norm.Basic.normSq coordinate = innerRadiusSq site parameter) :
    radialParameter site parameter coordinate = 0 := by
  unfold radialParameter
  rewrite [boundary]
  have zero : innerRadiusSq site parameter - innerRadiusSq site parameter = 0 := by ring1
  rewrite [zero]
  exact Fraction.Field.zero_div_direct _

/-- The actual outer boundary has exactly unit radial parameter, using the internally proved proper width. -/
theorem radialParameter_outer {site : Fin 2} {parameter coordinate : Canonical}
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational))
    (boundary : Norm.Basic.normSq coordinate = outerRadiusSq) : radialParameter site parameter coordinate = 1 := by
  unfold radialParameter
  rewrite [boundary]
  exact (Fraction.Field.div_eq_mul_inv_direct _ _).trans
    (Fraction.Field.mul_inv_cancel _ ((Order.Arithmetic.sub_pos_direct (proper site parameter bound)).ne'))

end Twist

/-- Apply the actual radius-dependent rational phase to the SAME original product-conic Point.

The selected certified phase executes once. Its unit norm proves preservation
of the original conic equation. Both original coordinate radii remain exact,
so conjugate rotation can later use the identical phase without reconstruction
of any curve, root, sheet, transport or matrix owner.
-/
def annularTwist {site : Fin 2} {parameter : Canonical} (point : Point site parameter) : Point site parameter :=
  let phase := Twist.phase (Twist.radialParameter site parameter point.plus)
  point.rotate phase.value phase.unit

/-- Undo the same original radius-dependent phase by its conjugate, using the unchanged squared-radius selector. -/
def annularTwistInverse {site : Fin 2} {parameter : Canonical} (point : Point site parameter) : Point site parameter :=
  let phase := Twist.phase (Twist.radialParameter site parameter point.plus)
  point.rotate (Basic.conj phase.value) ((Norm.Basic.normSq_conj phase.value).trans phase.unit)

/-- Read the actual original first coordinate multiplied by its selected rational phase. -/
theorem annularTwist_plus {site : Fin 2} {parameter : Canonical} (point : Point site parameter) :
    (annularTwist point).plus = point.plus * (Twist.phase (Twist.radialParameter site parameter point.plus)).value := by
  unfold annularTwist
  exact Point.rotate_plus _ _ _

/-- Read the original second coordinate multiplied by the conjugate of that SAME selected phase. -/
theorem annularTwist_minus {site : Fin 2} {parameter : Canonical} (point : Point site parameter) :
    (annularTwist point).minus =
      point.minus * Basic.conj (Twist.phase (Twist.radialParameter site parameter point.plus)).value := by
  unfold annularTwist
  exact Point.rotate_minus _ _ _

/-- The actual annular twist preserves the first original conic coordinate's exact squared radius. -/
theorem annularTwist_plus_normSq {site : Fin 2} {parameter : Canonical} (point : Point site parameter) :
    Norm.Basic.normSq (annularTwist point).plus = Norm.Basic.normSq point.plus := by
  unfold annularTwist
  exact Point.rotate_plus_normSq _ _ _

/-- The same twist preserves the second original conic coordinate's exact squared radius. -/
theorem annularTwist_minus_normSq {site : Fin 2} {parameter : Canonical} (point : Point site parameter) :
    Norm.Basic.normSq (annularTwist point).minus = Norm.Basic.normSq point.minus := by
  unfold annularTwist
  exact Point.rotate_minus_normSq _ _ _

/-- Conjugate inverse rotation preserves that same original first-coordinate squared radius. -/
theorem annularTwistInverse_plus_normSq {site : Fin 2} {parameter : Canonical} (point : Point site parameter) :
    Norm.Basic.normSq (annularTwistInverse point).plus = Norm.Basic.normSq point.plus := by
  unfold annularTwistInverse
  exact Point.rotate_plus_normSq _ _ _

/-- The explicit inverse also preserves the second original conic coordinate's exact squared radius. -/
theorem annularTwistInverse_minus_normSq {site : Fin 2} {parameter : Canonical} (point : Point site parameter) :
    Norm.Basic.normSq (annularTwistInverse point).minus = Norm.Basic.normSq point.minus := by
  unfold annularTwistInverse
  exact Point.rotate_minus_normSq _ _ _

/-- The identical original annulus predicate is preserved by the actual twist, without a replacement radial owner. -/
theorem annularTwist_contains {site : Fin 2} {parameter : Canonical} (point : Point site parameter)
    (inside : Contains site parameter point.plus) : Contains site parameter (annularTwist point).plus :=
  Eq.mpr (congrArg (fun radius : Fraction.Rational =>
    innerRadiusSq site parameter ≤ radius ∧ radius ≤ outerRadiusSq) (annularTwist_plus_normSq point)) inside

/-- The same original annulus predicate is preserved by the explicit conjugate inverse. -/
theorem annularTwistInverse_contains {site : Fin 2} {parameter : Canonical} (point : Point site parameter)
    (inside : Contains site parameter point.plus) : Contains site parameter (annularTwistInverse point).plus :=
  Eq.mpr (congrArg (fun radius : Fraction.Rational =>
    innerRadiusSq site parameter ≤ radius ∧ radius ≤ outerRadiusSq) (annularTwistInverse_plus_normSq point)) inside

/-- The actual twist retains exactly the SAME radial parameter used to select its original phase. -/
theorem annularTwist_radialParameter {site : Fin 2} {parameter : Canonical} (point : Point site parameter) :
    Twist.radialParameter site parameter (annularTwist point).plus =
      Twist.radialParameter site parameter point.plus := by
  unfold Twist.radialParameter
  rewrite [annularTwist_plus_normSq]
  rfl

/-- Conjugate phase rotation undoes the actual twist on the complete original Point. -/
theorem annularTwistInverse_twist {site : Fin 2} {parameter : Canonical} (point : Point site parameter) :
    annularTwistInverse (annularTwist point) = point := by
  have phases := Twist.phase_eq_of_radius (site := site) (parameter := parameter) (annularTwist_plus_normSq point)
  have rotated := congrArg (fun phase : UnitVertex =>
    (annularTwist point).rotate (Basic.conj phase.value) ((Norm.Basic.normSq_conj phase.value).trans phase.unit))
    phases
  exact rotated.trans (Point.rotate_conj point
    (Twist.phase (Twist.radialParameter site parameter point.plus)).value
    (Twist.phase (Twist.radialParameter site parameter point.plus)).unit)

/-- The actual twist undoes its conjugate inverse on the SAME complete original Point. -/
theorem annularTwist_twistInverse {site : Fin 2} {parameter : Canonical} (point : Point site parameter) :
    annularTwist (annularTwistInverse point) = point := by
  have phases := Twist.phase_eq_of_radius (site := site) (parameter := parameter)
    (annularTwistInverse_plus_normSq point)
  have rotated := congrArg (fun phase : UnitVertex => (annularTwistInverse point).rotate phase.value phase.unit) phases
  exact rotated.trans (Point.conj_rotate point
    (Twist.phase (Twist.radialParameter site parameter point.plus)).value
    (Twist.phase (Twist.radialParameter site parameter point.plus)).unit)

/-- The actual whole conic Point on the inner original annulus boundary is fixed exactly. -/
theorem annularTwist_inner {site : Fin 2} {parameter : Canonical} (point : Point site parameter)
    (boundary : Norm.Basic.normSq point.plus = innerRadiusSq site parameter) : annularTwist point = point := by
  have phaseOne : (Twist.phase (Twist.radialParameter site parameter point.plus)).value = 1 :=
    (congrArg (fun time => (Twist.phase time).value) (Twist.radialParameter_inner boundary)).trans
      Twist.phase_zero_value
  unfold annularTwist
  exact Point.rotate_eq_of_one _ _ _ phaseOne

/-- The admitted parameter bound derives proper width and exact fixation of the whole original outer-boundary Point. -/
theorem annularTwist_outer {site : Fin 2} {parameter : Canonical} (point : Point site parameter)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational))
    (boundary : Norm.Basic.normSq point.plus = outerRadiusSq) : annularTwist point = point := by
  have phaseOne : (Twist.phase (Twist.radialParameter site parameter point.plus)).value = 1 :=
    (congrArg (fun time => (Twist.phase time).value) (Twist.radialParameter_outer bound boundary)).trans
      Twist.phase_one_value
  unfold annularTwist
  exact Point.rotate_eq_of_one _ _ _ phaseOne

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus

end
