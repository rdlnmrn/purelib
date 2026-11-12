module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Joint.Bounds.Envelope
import Purelib.Riemann.Normalization.ContinuedInverseRoot.Bounds
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Gaussian.RationalEmbedding
import Purelib.Data.Rat.Fraction.Order.Field

/-! # Original strip ceilings on actual later neighborhoods

The original all-point strip clearance pays the actual later seed at its
retained center. Center lineage and the original unit radius give one fixed
enlargement and one original four-row ceiling for every affine strip time.
No neighborhood, sign, observation or Taylor certificate is substituted.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)

/-- Original whole-box clearance and actual center lineage bound every original row ceiling of a later neighborhood.

The later patch supplies its own retained seed residual and cached rootLower.
The fixed original strip provides its polynomial floor at that same center;
no signed-owner relation or desired numerical ceiling is assumed.
-/
theorem rowCeiling_le_of_center {parameter offset : Canonical} {count actualCount : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count} (range : Range patch)
    (admitted : Norm.Basic.normSq offset ≤ range.shiftedBound)
    (actual : ContinuedNeighborhood (Paths.polynomial (parameter + offset)) actualCount)
    (inside : patch.box.Contains actual.base.site.center) (laterIncrement : Canonical) (order coordinate : Fin 2) :
    Step.Joint.rowCeiling (parameter := parameter + offset) actual laterIncrement order coordinate ≤
      Step.Joint.shiftedEnvelopeCeiling (parameter := parameter) patch := by
  have floorPositive : 0 < (patch.base.site.denominatorValue / 4) / 4 :=
    Order.Field.div_pos_direct
      (Order.Field.div_pos_direct patch.base.site.denominatorValue_positive
        (by decide +kernel : (0 : Rational) < 4))
      (by decide +kernel : (0 : Rational) < 4)
  have polynomialLower := range.shifted_lower inside offset admitted
  rewrite [Norm.Basic.normSq_eq_canonical] at polynomialLower
  have lower := actual.rootLower_ge floorPositive polynomialLower
  have bound := Step.Joint.rowCeiling_le_box actual laterIncrement order coordinate
    (actual.box_refines_enlarge inside) (ContinuedNeighborhood.rootFloor_positive floorPositive) lower
  exact bound.trans_eq (Step.Joint.shiftedEnvelopeCeiling_eq patch floorPositive).symm

/-- One original strip payment bounds all actual later rows at every unit-interval parameter time.

Only the retained original interpolated_admitted law is used. Neither a
mesh-dependent minimum nor independent local-step bounds replace the
original absolute parameter index or its whole-window payment.
-/
theorem rowCeiling_le_at_time {parameter direction : Canonical} {count actualCount : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count} (range : Range patch)
    (admitted : Norm.Basic.normSq direction ≤ range.stripBound)
    (time : Rational) (timeInside : 0 ≤ time ∧ time ≤ 1)
    (actual : ContinuedNeighborhood
      (Paths.polynomial (parameter + (⟨time, 0⟩ : Canonical) * direction)) actualCount)
    (inside : patch.box.Contains actual.base.site.center) (laterIncrement : Canonical) (order coordinate : Fin 2) :
    Step.Joint.rowCeiling (parameter := parameter + (⟨time, 0⟩ : Canonical) * direction)
        actual laterIncrement order coordinate ≤ Step.Joint.shiftedEnvelopeCeiling (parameter := parameter) patch :=
  range.rowCeiling_le_of_center
    ((range.interpolated_admitted time timeInside direction admitted).trans range.stripBound_le_shiftedBound)
    actual inside laterIncrement order coordinate

/-- Coordinate-scaled affine parameter windows have the same fixed original ceiling at every retained time.

The scalar embedding and coordinate scale are identified by the original
Gaussian scale law. The actual neighborhood remains indexed at that exact
scaled parameter, including a zero direction; no shifted sample is queried.
-/
theorem rowCeiling_le_at_scaledTime {parameter direction : Canonical} {count actualCount : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count} (range : Range patch)
    (admitted : Norm.Basic.normSq direction ≤ range.stripBound)
    (time : Rational) (timeInside : 0 ≤ time ∧ time ≤ 1)
    (actual : ContinuedNeighborhood (Paths.polynomial (parameter + Scale.scale time direction)) actualCount)
    (inside : patch.box.Contains actual.base.site.center) (laterIncrement : Canonical) (order coordinate : Fin 2) :
    Step.Joint.rowCeiling (parameter := parameter + Scale.scale time direction)
        actual laterIncrement order coordinate ≤ Step.Joint.shiftedEnvelopeCeiling (parameter := parameter) patch := by
  have same : (⟨time, 0⟩ : Canonical) * direction = Scale.scale time direction :=
    Scale.scalar_mul_eq_scale time direction
  have interpolated := range.interpolated_admitted time timeInside direction admitted
  have absolute := Eq.mp (congrArg (fun offset => Norm.Basic.normSq offset ≤ range.stripBound) same) interpolated
  exact range.rowCeiling_le_of_center (absolute.trans range.stripBound_le_shiftedBound)
    actual inside laterIncrement order coordinate

/-- The same fixed original strip bounds an actual later patch under its exact affine parameter-index identity.

Equality elimination changes only the polynomial parameter index of the
supplied actual neighborhood. Its whole seed, rootLower, physical box and
owner caches remain present; no neighborhood or observation is constructed.
-/
theorem rowCeiling_le_at_parameter {parameter actualParameter direction : Canonical} {count actualCount : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count} (range : Range patch)
    (admitted : Norm.Basic.normSq direction ≤ range.stripBound)
    (time : Rational) (timeInside : 0 ≤ time ∧ time ≤ 1)
    (actual : ContinuedNeighborhood (Paths.polynomial actualParameter) actualCount)
    (parameterEq : actualParameter = parameter + Scale.scale time direction)
    (inside : patch.box.Contains actual.base.site.center) (laterIncrement : Canonical) (order coordinate : Fin 2) :
    Step.Joint.rowCeiling (parameter := actualParameter) actual laterIncrement order coordinate ≤
      Step.Joint.shiftedEnvelopeCeiling (parameter := parameter) patch := by
  cases parameterEq
  exact range.rowCeiling_le_at_scaledTime admitted time timeInside actual inside laterIncrement order coordinate

end Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range

end
