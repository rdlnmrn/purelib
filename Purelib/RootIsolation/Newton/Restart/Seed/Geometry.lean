module
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Band.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Prepare.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Band
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.Newton.Restart.Displacement
public import Purelib.RootIsolation.Newton.Restart.Seed.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Winding bands from displayed rational residuals

A sufficiently small value of a squarefree polynomial at a displayed
Gaussian-rational sample gives a finite Newton certificate.  When supplied
with explicit rational displacement, Taylor, and containment budgets, the
selected eliminant-safe band has winding four and therefore starts a normal
shrinking track.

Nothing in this module turns a small residual, a winding count, or a Sturm
count into a root.  The only distinguished point is the supplied rational
anchor of `source`.
-/

namespace Purelib.RootIsolation.Newton.Restart.Seed

section Seed

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
  Purelib.Geometry.Rational.Box}
  {degreeBound : Nat}
variable {squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p}
variable {elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound}
variable {current : Clearance.Box.Region.ProtectedAmbient p ambient}

/-- The Newton point is computed entirely from the displayed source anchor. -/
def newton (seed : Seed squarefree
  elimination current) :
    Dense.Gaussian.Newton.Box.Squarefree.NewtonCenterCertificate p current.box seed.source squarefree :=
  Dense.Gaussian.Newton.Box.Prepare.Squarefree.computeNewtonCenterOfResidual p squarefree seed.sourceRefines
    seed.residual
    seed.threshold

/-- The four eliminant-safe rational coordinates around the computed Newton
point. -/
def band (seed : Seed squarefree
  elimination current) :
    Box.Band.Basic.BandBox (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p seed.source) seed.radius :=
  Elimination.Axis.Band.selectedBand elimination (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p seed.source)
    seed.radius
    seed.radiusPositive

/-- The retained Newton point lies within the seed's squared-radius displacement budget from its anchor. -/
theorem displacementSmall (seed :
  Seed squarefree elimination current) :
    Data.Gaussian.Norm.Basic.normSq (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p seed.source -
      seed.source.anchor) ≤
      seed.radius ^ 2 :=
  (Newton.Restart.Displacement.newton_displacementResidualMargin seed.newton).trans seed.displacementBudget

/-- The selected eliminant-safe band refines the seed's original current box. -/
theorem band_refines_current (seed :
  Seed squarefree elimination current) :
    seed.band.box.Refines current.box :=
  (Geometry.Rational.Box.Refinement.StrictInterior.refines seed.bandStrict)

/-- The selected band refines the seed's original fixed ambient box. -/
theorem band_refines_ambient (seed :
  Seed squarefree elimination current) :
    seed.band.box.Refines ambient :=
  seed.band_refines_current.trans current.refinesAmbient

/-! ## Predictable centered restarts -/

/-- The centered radius-`r` square contained in the eliminant-safe band of a
residual seed.  Unlike the selected band, all of its geometric data are exact
expressions in the seed radius. -/
def centeredBox (seed : Seed
  squarefree elimination current) : Purelib.Geometry.Rational.Box :=
  Box.Square.Centered.Affine.centeredSquare
    (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p seed.source) seed.radius seed.radiusPositive.le

/-- The predictable centered square lies within the selected eliminant-safe band. -/
theorem centeredBox_refines_band
    (seed : Seed squarefree elimination current) :
    seed.centeredBox.Refines seed.band.box := by
  exact ⟨seed.band.left_upper, seed.band.right_lower,
    seed.band.bottom_upper, seed.band.top_lower⟩

/-- The predictable centered square refines the original current box. -/
theorem centeredBox_refines_current
    (seed : Seed squarefree elimination current) :
    seed.centeredBox.Refines current.box :=
  seed.centeredBox_refines_band.trans seed.band_refines_current

/-- The centered square's squared diagonal is exactly eight times the seed's squared radius. -/
@[simp] theorem centeredBox_diagonalSq
    (seed : Seed squarefree elimination current) :
    seed.centeredBox.diagonalSq = 8 * seed.radius ^ 2 := by
  exact Box.Square.Centered.Affine.centeredSquare_diagonalSq _ seed.radiusPositive.le

/-! ## Location of the displayed rational anchor -/

/-- Each coordinate of the Newton-center displacement lies between minus and plus the seed radius. -/
theorem center_sub_anchor_coordinate_bounds
    (seed : Seed squarefree elimination current) :
    -seed.radius ≤
        (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p seed.source - seed.source.anchor).re ∧
      (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p seed.source - seed.source.anchor).re ≤
        seed.radius ∧
      -seed.radius ≤
        (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p seed.source - seed.source.anchor).im ∧
      (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p seed.source - seed.source.anchor).im ≤
        seed.radius :=
  Gaussian.Norm.Bounds.coordinate_bounds_of_normSq_le
    seed.radiusPositive.le seed.displacementSmall

/-- Every side of the selected band stays within three radii of the original
displayed rational sample. -/
theorem anchor_band_coordinate_bounds
    (seed : Seed squarefree elimination current) :
    seed.source.anchor.re - 3 * seed.radius ≤ seed.band.box.xLower ∧
      seed.band.box.xUpper ≤ seed.source.anchor.re + 3 * seed.radius ∧
      seed.source.anchor.im - 3 * seed.radius ≤ seed.band.box.yLower ∧
      seed.band.box.yUpper ≤ seed.source.anchor.im + 3 * seed.radius := open Purelib.Data.Rat in by
  have centerBounds := seed.center_sub_anchor_coordinate_bounds
  have centerRealLower : seed.source.anchor.re - seed.radius ≤
      (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p seed.source).re := by
    calc
      seed.source.anchor.re - seed.radius =
          -seed.radius + seed.source.anchor.re := by ring1
      _ ≤ (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p seed.source - seed.source.anchor).re +
          seed.source.anchor.re :=
        Fraction.Order.Arithmetic.add_le_add_right_direct centerBounds.1
          seed.source.anchor.re
      _ = (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p seed.source).re := by
        simp only [Gaussian.Basic.sub_re]
        ring1
  have centerRealUpper : (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p seed.source).re ≤
      seed.source.anchor.re + seed.radius := by
    calc
      (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p seed.source).re =
          (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p seed.source - seed.source.anchor).re +
            seed.source.anchor.re := by
        simp only [Gaussian.Basic.sub_re]
        ring1
      _ ≤ seed.radius + seed.source.anchor.re :=
        Fraction.Order.Arithmetic.add_le_add_right_direct centerBounds.2.1
          seed.source.anchor.re
      _ = seed.source.anchor.re + seed.radius := by ring1
  have centerImagLower : seed.source.anchor.im - seed.radius ≤
      (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p seed.source).im := by
    calc
      seed.source.anchor.im - seed.radius =
          -seed.radius + seed.source.anchor.im := by ring1
      _ ≤ (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p seed.source - seed.source.anchor).im +
          seed.source.anchor.im :=
        Fraction.Order.Arithmetic.add_le_add_right_direct centerBounds.2.2.1
          seed.source.anchor.im
      _ = (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p seed.source).im := by
        simp only [Gaussian.Basic.sub_im]
        ring1
  have centerImagUpper : (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p seed.source).im ≤
      seed.source.anchor.im + seed.radius := by
    calc
      (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p seed.source).im =
          (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p seed.source - seed.source.anchor).im +
            seed.source.anchor.im := by
        simp only [Gaussian.Basic.sub_im]
        ring1
      _ ≤ seed.radius + seed.source.anchor.im :=
        Fraction.Order.Arithmetic.add_le_add_right_direct centerBounds.2.2.2
          seed.source.anchor.im
      _ = seed.source.anchor.im + seed.radius := by ring1
  exact
    ⟨(by
        calc
          seed.source.anchor.re - 3 * seed.radius =
              (seed.source.anchor.re - seed.radius) - 2 * seed.radius := by
            ring1
          _ ≤ (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p seed.source).re - 2 * seed.radius :=
            Fraction.Order.Arithmetic.sub_le_sub_right_direct centerRealLower _
          _ ≤ seed.band.box.xLower := seed.band.left_lower),
      (by
        calc
          seed.band.box.xUpper ≤
              (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p seed.source).re + 2 * seed.radius :=
            seed.band.right_upper
          _ ≤ (seed.source.anchor.re + seed.radius) + 2 * seed.radius :=
            Fraction.Order.Arithmetic.add_le_add_right_direct centerRealUpper _
          _ = seed.source.anchor.re + 3 * seed.radius := by ring1),
      (by
        calc
          seed.source.anchor.im - 3 * seed.radius =
              (seed.source.anchor.im - seed.radius) - 2 * seed.radius := by
            ring1
          _ ≤ (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p seed.source).im - 2 * seed.radius :=
            Fraction.Order.Arithmetic.sub_le_sub_right_direct centerImagLower _
          _ ≤ seed.band.box.yLower := seed.band.bottom_lower),
      (by
        calc
          seed.band.box.yUpper ≤
              (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p seed.source).im + 2 * seed.radius :=
            seed.band.top_upper
          _ ≤ (seed.source.anchor.im + seed.radius) + 2 * seed.radius :=
            Fraction.Order.Arithmetic.add_le_add_right_direct centerImagUpper _
          _ = seed.source.anchor.im + 3 * seed.radius := by ring1)⟩

end Seed

end Purelib.RootIsolation.Newton.Restart.Seed

end
