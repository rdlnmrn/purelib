module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Coefficient
public import Purelib.Geometry.Rational.Box.Square.Centered.Nesting
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Refinement
import Purelib.Geometry.Rational.Box.Square.Centered.Separation.Bounds
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Bounds
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Ordinate

/-! # One fixed coarse-block envelope for genuinely finer original Anchors

Every finer chart source in the coarse depth-seven interval lies inside its
original sharp square. The finer square has the SAME physical half-width,
so the original box refinement places it in one fixed doubled coarse square.
One actual numerator fold there bounds every finer cache. Original signed
separation margins also bound the finer radii independently of mesh depth.
The envelope is only a polynomial bounding box; no root clearance or root
continuation is claimed on it, and all finer Owners remain the original ones.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Clearance

namespace Envelope

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Rational
open Purelib.Geometry.Rational.Box.Square.Centered
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Riemann.RootContinuation
open Purelib.Polynomial.Dense.Gaussian.Bounds

/-- The original coarse spatial center and twice its unchanged sharp radius determine a fixed numerator envelope. -/
@[expose] def box (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
    (reference : Fraction.Rational) (regular : parameter ≠ criticalValue site) : Geometry.Rational.Box :=
  Affine.centeredSquare (Parameter.sourcePoint site parameter (Waist.direction quarter reference)).base
    (2 * Clearance.radius site parameter)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (of_decide_eq_true rfl) (radius_positive site parameter regular).le)

/-- A genuinely finer original source square refines the SAME fixed doubled coarse square. -/
theorem box_refines (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
    (reference fine : Fraction.Rational) (regular : parameter ≠ criticalValue site)
    (paid : (fine - reference) ^ 2 ≤ Approximation.Rational.Geometric.Basic.quarterRadius 1 7) :
    (Clearance.box site parameter (Waist.direction quarter fine) regular).Refines
      (box site parameter quarter reference regular) := by
  have inside := quarter_target_inside site parameter quarter regular reference fine paid
  exact translated_refines_double (radius_positive site parameter regular).le inside

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {fine : Fraction.Rational} {fineInside : FixedRootBoxPath.Inside fine}
variable {source : Transport.Reading actual fine fineInside} {anchor : Parameter.Anchor source.lift}

/-- The actual finer Anchor's own source square refines the fixed envelope through the original geometric time law. -/
theorem sourceBox_refines (anchor : Parameter.Anchor source.lift) (reference : Fraction.Rational)
    (paid : (fine - reference) ^ 2 ≤ Approximation.Rational.Geometric.Basic.quarterRadius 1 7) :
    (Transport.Spatial.Factors.sourceBox anchor).Refines (box site parameter quarter reference anchor.regular) :=
  box_refines site parameter quarter reference fine anchor.regular paid

/-- Each finer Anchor retains its OWN signed radius between fixed half-gap-dependent lower and upper bounds. -/
theorem radius_bounds (anchor : Parameter.Anchor source.lift) :
    (9 / 128) * Norm.Basic.normSq (halfGap site parameter) ≤ anchor.seed.separation.radius ^ 2 ∧
      anchor.seed.separation.radius ^ 2 ≤ (25 / 16) * Norm.Basic.normSq (halfGap site parameter) := by
  refine ⟨anchor.radius_lower, ?_⟩
  have center := anchor.seed.separation.radius_sq_le_normSq
  have ordinate := Radial.point_ordinate_normSq_le site parameter 2 (Waist.direction quarter fine) positive
    (of_decide_eq_true rfl : (1 : Fraction.Rational) ≤ 2) (Fraction.Order.Basic.le_refl (2 : Fraction.Rational))
  have radius : anchor.seed.separation.radius ^ 2 ≤
      Norm.Basic.normSq (Parameter.sourcePoint site parameter (Waist.direction quarter fine)).ordinate := by
    calc
      _ = 1 * anchor.seed.separation.radius ^ 2 := (Fraction.Field.one_mul _).symm
      _ ≤ 4 * anchor.seed.separation.radius ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (by decide +kernel : (1 : Fraction.Rational) ≤ 4)
          (Fraction.Order.Arithmetic.sq_nonneg_direct anchor.seed.separation.radius)
      _ ≤ _ := center
  exact radius.trans ordinate

variable (differential : OddPowerDifferential (Paths.polynomial parameter))
variable (reference : Fraction.Rational) (regular : parameter ≠ criticalValue site)

/-- One complete original numerator Horner cache on the SAME fixed coarse envelope. -/
@[expose] def Numerator :=
  { cached : Polynomial.Bounds.Horner //
    cached = Box.denseHornerNormBounds differential.numerator (box site parameter quarter reference regular) }

namespace Numerator

/-- Compute and store the original numerator fold once on this unchanged finite coarse envelope. -/
def build : Numerator (quarter := quarter) differential reference regular :=
  let cached := Box.denseHornerNormBounds differential.numerator (box site parameter quarter reference regular)
  ⟨cached, rfl⟩

variable {differential reference regular}
variable (retained : Numerator (quarter := quarter) differential reference regular)

/-- Read the SAME original joint value/slope fold retained on the fixed envelope. -/
@[expose] def cache : Polynomial.Bounds.Horner := retained.val

/-- The complete cache retains its original numerator and coarse-envelope factory equation. -/
theorem cache_eq : retained.cache =
    Box.denseHornerNormBounds differential.numerator (box site parameter quarter reference regular) :=
  retained.property

/-- Both exact original coarse-envelope readings are nonnegative. -/
theorem nonnegative : 0 ≤ retained.cache.value ∧ 0 ≤ retained.cache.slope := by
  have known := Box.denseHornerNormBounds_nonneg differential.numerator
    (box site parameter quarter reference regular)
  change 0 ≤ (Box.denseHornerNormBounds differential.numerator _).value ∧
    0 ≤ (Box.denseHornerNormBounds differential.numerator _).slope at known
  rewrite [← retained.cache_eq] at known
  exact known

/-- Every actual finer numerator cache is bounded by the SAME original fixed-envelope cache without recomputing it. -/
theorem fine_bounds_le {data : Waist.Differential.Bounds.Data site parameter differential}
    (bounds : Transport.Spatial.Factors.Coefficient.Bounds data anchor)
    (paid : (fine - reference) ^ 2 ≤ Approximation.Rational.Geometric.Basic.quarterRadius 1 7) :
    bounds.value ≤ data.scaleNorm * retained.cache.value ∧
      bounds.slope ≤ data.scaleNorm * retained.cache.slope := by
  have refined := sourceBox_refines anchor reference paid
  have known := Box.denseHornerNormBounds_mono differential.numerator refined
  rewrite [← bounds.cache_eq, ← retained.cache_eq] at known
  exact ⟨Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct known.1 data.scaleNorm_nonnegative,
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct known.2 data.scaleNorm_nonnegative⟩

end Numerator

end Envelope

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Clearance

end
