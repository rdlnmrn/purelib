module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Tangent.Expansion
public import Purelib.Calculus.Jet.Quadratic.Chord
import Purelib.Geometry.Gaussian.UnitCircle.Stereographic.Tangent
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-! # Actual radial base and ordinate chords with quantified deviation

Each chord is the original affine line between the displayed actual conic
endpoints. The original full and short tangent expansions supply their
common base/slope and half-gap factor. Their original certificate chord
bound pays every rational unit-fraction sample by the fourth power of the
actual full chart width, including zero-width spans.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Tangent

open Purelib
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Gaussian.UnitCircle
open Purelib.Geometry.Rational

/-- Real scalar multiplication identifies the actual original short and full chart increment indices. -/
private theorem increment_scaled (fraction delta : Rational) :
    Stereographic.Tangent.increment (fraction * delta) =
      Gaussian.Cast.Path.ofCoordinate fraction * Stereographic.Tangent.increment delta := by
  change Gaussian.Cast.CoordinateTaylor.ofCoordinate (fraction * delta) =
    Gaussian.Cast.CoordinateTaylor.ofCoordinate fraction * Gaussian.Cast.CoordinateTaylor.ofCoordinate delta
  exact Gaussian.Cast.ofCoordinate_mul fraction delta

/-- The displayed original base-coordinate chord joins the actual full radial conic endpoints. -/
@[expose] def baseChord (site : Fin 2) (parameter : Canonical) (scale : Rational)
    (quarter : UnitCircuitQuarter) (positive : 0 < scale) (time delta fraction : Rational) : Canonical :=
  Affine.line (point site parameter scale (Waist.direction quarter time) positive).base
    ((point site parameter scale (Waist.direction quarter (time + delta)) positive).base -
      (point site parameter scale (Waist.direction quarter time) positive).base) fraction

/-- The displayed original normalized-ordinate chord retains those same actual conic endpoints. -/
@[expose] def ordinateChord (site : Fin 2) (parameter : Canonical) (scale : Rational)
    (quarter : UnitCircuitQuarter) (positive : 0 < scale) (time delta fraction : Rational) : Canonical :=
  Affine.line (point site parameter scale (Waist.direction quarter time) positive).ordinate
    ((point site parameter scale (Waist.direction quarter (time + delta)) positive).ordinate -
      (point site parameter scale (Waist.direction quarter time) positive).ordinate) fraction

/-- The original base chord starts at its exact actual radial source coordinate. -/
theorem baseChord_zero (site : Fin 2) (parameter : Canonical) (scale : Rational)
    (quarter : UnitCircuitQuarter) (positive : 0 < scale) (time delta : Rational) :
    baseChord site parameter scale quarter positive time delta 0 =
      (point site parameter scale (Waist.direction quarter time) positive).base := Affine.line_zero _ _

/-- The original base chord finishes at its exact actual radial target coordinate. -/
theorem baseChord_one (site : Fin 2) (parameter : Canonical) (scale : Rational)
    (quarter : UnitCircuitQuarter) (positive : 0 < scale) (time delta : Rational) :
    baseChord site parameter scale quarter positive time delta 1 =
      (point site parameter scale (Waist.direction quarter (time + delta)) positive).base := Affine.line_one _ _

/-- The actual original radial base curve differs from its displayed chord by the computed fourth-power budget.

Both actual tangent certificates keep their original increment indices,
endpoint values, slope and half-gap factor. The scalar increment equality
only cancels the shared affine terms; no root Owner, path or integral is
constructed or substituted in this finite geometric estimate.
-/
theorem baseChord_error_le (site : Fin 2) (parameter : Canonical) (scale : Rational)
    (quarter : UnitCircuitQuarter) (positive : 0 < scale) (lower : 1 ≤ scale) (upper : scale ≤ 2)
    (time delta fraction : Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1) :
    Norm.Basic.normSq ((point site parameter scale (Waist.direction quarter (time + fraction * delta))
      positive).base - baseChord site parameter scale quarter positive time delta fraction) ≤
      25 * Norm.Basic.normSq (halfGap site parameter) * delta ^ 4 := by
  let full := baseExpansion site parameter scale quarter positive lower upper time delta
  let short := baseExpansion site parameter scale quarter positive lower upper time (fraction * delta)
  have bases : short.base = full.base :=
    (baseExpansion_base site parameter scale quarter positive lower upper time (fraction * delta)).trans
      (baseExpansion_base site parameter scale quarter positive lower upper time delta).symm
  have slopes : short.slope = full.slope :=
    (baseExpansion_slope site parameter scale quarter positive lower upper time (fraction * delta)).trans
      (baseExpansion_slope site parameter scale quarter positive lower upper time delta).symm
  have fullFactor : full.factor ≤ (25 / 4) * Norm.Basic.normSq (halfGap site parameter) := by
    dsimp only [full]
    rewrite [baseExpansion_factor]
    exact Order.Basic.le_refl _
  have partialFactor : short.factor ≤ (25 / 4) * Norm.Basic.normSq (halfGap site parameter) := by
    dsimp only [short]
    rewrite [baseExpansion_factor]
    exact Order.Basic.le_refl _
  have bound := full.chord_error_le short (increment_scaled fraction delta) bases slopes
    fullFactor partialFactor inside
  dsimp only [full, short] at bound
  rewrite [baseExpansion_output site parameter scale quarter positive lower upper time (fraction * delta),
    baseExpansion_base site parameter scale quarter positive lower upper time delta,
    baseExpansion_output site parameter scale quarter positive lower upper time delta,
    Stereographic.Tangent.increment_fourth] at bound
  change Norm.Basic.normSq ((point site parameter scale (Waist.direction quarter (time + fraction * delta))
      positive).base - baseChord site parameter scale quarter positive time delta fraction) ≤
    4 * ((25 / 4) * Norm.Basic.normSq (halfGap site parameter)) * delta ^ 4 at bound
  exact bound.trans_eq (by
    have scalar : (4 : Rational) * (25 / 4) = 25 := of_decide_eq_true rfl
    calc
      _ = ((4 * (25 / 4)) * Norm.Basic.normSq (halfGap site parameter)) * delta ^ 4 := by ring1
      _ = _ := congrArg (fun factor : Rational => factor * Norm.Basic.normSq (halfGap site parameter) * delta ^ 4)
        scalar)

/-- The actual original radial ordinate curve differs from its displayed chord by the computed fourth-power budget.

Both actual tangent certificates keep their original increment indices,
endpoint values, slope and half-gap factor. The scalar increment equality
only cancels the shared affine terms; no root Owner, path or integral is
constructed or substituted in this finite geometric estimate.
-/
theorem ordinateChord_error_le (site : Fin 2) (parameter : Canonical) (scale : Rational)
    (quarter : UnitCircuitQuarter) (positive : 0 < scale) (lower : 1 ≤ scale) (upper : scale ≤ 2)
    (time delta fraction : Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1) :
    Norm.Basic.normSq ((point site parameter scale (Waist.direction quarter (time + fraction * delta))
      positive).ordinate - ordinateChord site parameter scale quarter positive time delta fraction) ≤
      25 * Norm.Basic.normSq (halfGap site parameter) * delta ^ 4 := by
  let full := ordinateExpansion site parameter scale quarter positive lower upper time delta
  let short := ordinateExpansion site parameter scale quarter positive lower upper time (fraction * delta)
  have bases : short.base = full.base :=
    (ordinateExpansion_base site parameter scale quarter positive lower upper time (fraction * delta)).trans
      (ordinateExpansion_base site parameter scale quarter positive lower upper time delta).symm
  have slopes : short.slope = full.slope :=
    (ordinateExpansion_slope site parameter scale quarter positive lower upper time (fraction * delta)).trans
      (ordinateExpansion_slope site parameter scale quarter positive lower upper time delta).symm
  have fullFactor : full.factor ≤ (25 / 4) * Norm.Basic.normSq (halfGap site parameter) := by
    dsimp only [full]
    rewrite [ordinateExpansion_factor]
    exact Order.Basic.le_refl _
  have partialFactor : short.factor ≤ (25 / 4) * Norm.Basic.normSq (halfGap site parameter) := by
    dsimp only [short]
    rewrite [ordinateExpansion_factor]
    exact Order.Basic.le_refl _
  have bound := full.chord_error_le short (increment_scaled fraction delta) bases slopes
    fullFactor partialFactor inside
  dsimp only [full, short] at bound
  rewrite [ordinateExpansion_output site parameter scale quarter positive lower upper time (fraction * delta),
    ordinateExpansion_base site parameter scale quarter positive lower upper time delta,
    ordinateExpansion_output site parameter scale quarter positive lower upper time delta,
    Stereographic.Tangent.increment_fourth] at bound
  change Norm.Basic.normSq ((point site parameter scale (Waist.direction quarter (time + fraction * delta))
      positive).ordinate - ordinateChord site parameter scale quarter positive time delta fraction) ≤
    4 * ((25 / 4) * Norm.Basic.normSq (halfGap site parameter)) * delta ^ 4 at bound
  exact bound.trans_eq (by
    have scalar : (4 : Rational) * (25 / 4) = 25 := of_decide_eq_true rfl
    calc
      _ = ((4 * (25 / 4)) * Norm.Basic.normSq (halfGap site parameter)) * delta ^ 4 := by ring1
      _ = _ := congrArg (fun factor : Rational => factor * Norm.Basic.normSq (halfGap site parameter) * delta ^ 4)
        scalar)

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Tangent

end
