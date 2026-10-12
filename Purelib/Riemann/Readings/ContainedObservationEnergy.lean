module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Riemann.Readings.PreparedObservationSeparation
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Riemann.Readings.PreparedObservationBoxes
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Riemann.Topology.PreparedObservationSurface
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Content
import Purelib.Geometry.Rational.Box.Dimensions
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Riemann.Readings.PreparedObservationInterpolation
import Purelib.Topology.BranchedCover.Double.Attachment

public import Purelib.Riemann.Readings.ContainedObservationPoints
public import Purelib.Riemann.Topology.PreparedSurfacePartitions
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Riemann.Readings.PreparedObservationPoints
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Uniform observation coercivity retained inside an actual rectangle

The existing interpolation, majorants, densities and clearance certificates
are reused. A common smaller radius pays geometric containment; its exact
area rescales the positive lower constant. Nothing is assumed about a
coefficient vector when constructing this bank.
-/

namespace Purelib.Riemann.Readings

open Purelib.Data.Rat.Fraction

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (Coordinate)
open Purelib.Riemann.Topology.PreparedObservationSurface (ObservationBoxEnergy)
open Purelib.Riemann.Readings.ContainedObservationPoints (BoxObservationPoints)
open _root_.Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial -> Dense
open Purelib.Riemann.Readings.PreparedObservationSeparation (minimumRadius minimumRadius_positive minimumRadius_le)
open Purelib.Riemann.Readings.PreparedObservationNeighborhoods (centeredBox_proper centeredBox_refines)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq coefficientNormSq_positive)
open Purelib.LinearAlgebra.Gaussian.Energy (NonzeroGaussianVector)

open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_mul_left)

namespace ContainedObservationEnergy

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
/-- The minimum of the four signed distances from a point to the original box's sides. -/
public def pointMargin (box : Box) (point : Basic.Canonical) : Coordinate :=
  min (point.re - box.xLower) (min (box.xUpper - point.re) (min (point.im - box.yLower) (box.yUpper - point.im)))

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
/-- A point strictly inside the original box has positive four-side margin. -/
private theorem pointMargin_positive {box : Box} {point : Basic.Canonical} (inside : box.StrictContains
  point) :
    0 < pointMargin box point :=
  Order.Basic.lt_min (Fraction.Order.Arithmetic.sub_pos_direct inside.1)
    (Order.Basic.lt_min (Fraction.Order.Arithmetic.sub_pos_direct inside.2.1)
      (Order.Basic.lt_min (Fraction.Order.Arithmetic.sub_pos_direct inside.2.2.1)
        (Fraction.Order.Arithmetic.sub_pos_direct inside.2.2.2)))

open Purelib.Data.Rat in
/-- A radius within both endpoint margins keeps the centered interval inside the original interval. -/
private theorem interval_refines {lower upper center radius : Coordinate}
    (first : radius ≤ center - lower) (last : radius ≤ upper - center) : lower ≤ center - radius ∧ center + radius ≤
      upper := by
  constructor
  · apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    have nonnegative := Fraction.Order.Arithmetic.sub_nonneg_direct first
    exact (show (center - lower) - radius = (center - radius) - lower from by ring1) ▸ nonnegative
  · exact (show center + radius = radius + center from by ring1).trans_le
      ((Fraction.Order.Arithmetic.add_le_add_right_direct last center).trans_eq (by ring1))

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
/-- A centered square with radius within the original four-side margin refines that box.

The bound compares the original retained rational quantities. Direct order
certificates preserve the same minimum or maximum branch and its supplied
positive or weak bounds without changing any cached value. -/
private theorem centered_refines {box : Box} {point : Basic.Canonical} {radius : Coordinate}
  (nonnegative : 0 ≤ radius)
    (bound : radius ≤ pointMargin box point) : (Box.Square.Centered.BoxTransport.centeredBox point radius
      nonnegative).Refines box := by
  have x := interval_refines (bound.trans (Order.Basic.min_le_left _ _))
    (bound.trans ((Order.Basic.min_le_right _ _).trans (Order.Basic.min_le_left _ _)))
  have y := interval_refines (bound.trans ((Order.Basic.min_le_right _ _).trans ((Order.Basic.min_le_right _ _).trans
    (Order.Basic.min_le_left _ _))))
    (bound.trans ((Order.Basic.min_le_right _ _).trans ((Order.Basic.min_le_right _ _).trans (Order.Basic.min_le_right _
      _))))
  exact ⟨x.1, x.2, y.1, y.2⟩

end ContainedObservationEnergy

open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
set_option genInjectivity false in
/-- Retained observation energy restricted to one original containing region.

The record preserves the exact observation bank, original energy owner and their identity, then caches a common
margin-limited radius, square area and density-weighted lower coefficient. -/
structure ContainedObservationEnergy (polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (region : Box) (count : Nat)
  where
  /-- The original certified observation points strictly inside the retained region. -/ points : BoxObservationPoints
    polynomial region count
  /-- The retained observation energy before containment refinement. -/ original : ObservationBoxEnergy polynomial count
  /-- The original energy uses exactly the same observation bank as the contained points. -/ bank_eq :
    original.boxes.coercivity.interpolation.bank = points.bank
  /-- The cached common four-side margin to the original containing region. -/ margin : Coordinate
  /-- The margin equals the finite minimum over the exact original observation points. -/ margin_eq : margin =
    minimumRadius count (fun index => ContainedObservationEnergy.pointMargin region (points.bank.pointAt index))
  /-- The retained common radius after imposing the region margins. -/ radius : Coordinate
  /-- The radius is the minimum of the original energy radius and common margin. -/ radius_eq : radius = min
    original.boxes.radius margin
  /-- The cached common area of the contained observation squares. -/ area : Coordinate
  /-- The area is exactly four times the retained contained radius squared. -/ area_eq : area = 4 * radius ^ 2
  /-- The cached contained energy lower coefficient. -/ lower : Coordinate
  /-- The lower coefficient is the contained area times the original density constant. -/ lower_eq : lower = area *
    original.boxes.densityConstant

constructive_injectivity ContainedObservationEnergy

namespace ContainedObservationEnergy

variable {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {region :
  Box} {count : Nat}

open Purelib.Riemann.Readings in
/-- Build contained observation energy from the original certified interior observation points.

The original bank supplies interpolation and coercivity; the common radius is the minimum of its retained observation
radius and the original region's finite point-margin minimum. -/
def build (points : BoxObservationPoints polynomial region count) : ContainedObservationEnergy polynomial region count
  :=
  let interpolation := PreparedObservationInterpolation.ObservationInterpolation.ofBank points.bank
  let original := ObservationBoxEnergy.ofBoxes (PreparedObservationBoxes.ObservationBoxes.ofCoercivity
    (PreparedObservationCoercivity.ObservationCoercivity.ofInterpolation interpolation))
  let margin := minimumRadius count (fun index => pointMargin region (points.bank.pointAt index))
  let radius := min original.boxes.radius margin
  let area := 4 * radius ^ 2
  ⟨points, original, rfl, margin, rfl, radius, rfl, area, rfl, area * original.boxes.densityConstant, rfl⟩

/-- The common margin-limited observation radius is positive.

The bound compares the original retained rational quantities. Direct order
certificates preserve the same minimum or maximum branch and its supplied
positive or weak bounds without changing any cached value. -/
theorem radius_positive (energy : ContainedObservationEnergy polynomial region count) : 0 < energy.radius := by
  rw [energy.radius_eq, energy.margin_eq]
  exact Order.Basic.lt_min energy.original.boxes.radius_positive (minimumRadius_positive _
    (fun index => pointMargin_positive (energy.points.inside index)))

/-- The contained observation radius is bounded by its original energy owner's radius.

The bound compares the original retained rational quantities. Direct order
certificates preserve the same minimum or maximum branch and its supplied
positive or weak bounds without changing any cached value. -/
theorem radius_le_original (energy : ContainedObservationEnergy polynomial region count) : energy.radius ≤
  energy.original.boxes.radius :=
  energy.radius_eq ▸ Order.Basic.min_le_left _ _

/-- The common radius fits within every original observation point's four-side margin.

The bound compares the original retained rational quantities. Direct order
certificates preserve the same minimum or maximum branch and its supplied
positive or weak bounds without changing any cached value. -/
theorem radius_le_margin (energy : ContainedObservationEnergy polynomial region count) (index : Fin count) :
    energy.radius ≤ pointMargin region (energy.points.bank.pointAt index) := by
  rw [energy.radius_eq, energy.margin_eq]
  exact (Order.Basic.min_le_right _ _).trans (minimumRadius_le _ index)

open Purelib.Geometry.Rational in
/-- The centered square at the original observation point with the retained contained radius. -/
def box (energy : ContainedObservationEnergy polynomial region count) (index : Fin count) : Box :=
  Box.Square.Centered.BoxTransport.centeredBox (energy.points.bank.pointAt index) energy.radius
    energy.radius_positive.le

/-- Every retained contained observation square has strictly ordered sides. -/
theorem box_proper (energy : ContainedObservationEnergy polynomial region count) (index : Fin count) : (energy.box
  index).Proper :=
  centeredBox_proper _ energy.radius_positive

/-- Every contained observation square refines the original region. -/
theorem box_refines_region (energy : ContainedObservationEnergy polynomial region count) (index : Fin count) :
    (energy.box index).Refines region := centered_refines energy.radius_positive.le (energy.radius_le_margin index)

open Purelib.Riemann.Readings in
/-- Every contained square refines the corresponding original observation box at the same bank index. -/
theorem box_refines_original (energy : ContainedObservationEnergy polynomial region count) (index : Fin count) :
    (energy.box index).Refines (energy.original.boxes.box index) := by
  unfold box PreparedObservationBoxes.ObservationBoxes.box
  rw [energy.original.boxes.sites_center, energy.bank_eq]
  exact centeredBox_refines _ energy.radius_positive.le energy.original.boxes.radius_positive.le
    energy.radius_le_original

/-- Distinct original observation indices remain separated after containment refinement. -/
theorem boxes_separated (energy : ContainedObservationEnergy polynomial region count) {first last : Fin count}
  (different : first ≠ last) :
    (energy.box first).Separated (energy.box last) :=
  (energy.original.boxes.box_separated different).of_refines (energy.box_refines_original first)
    (energy.box_refines_original last)

section
open Purelib.Data.Rat
/-- The cached common area of the contained squares is positive. -/
theorem area_positive (energy : ContainedObservationEnergy polynomial region count) : 0 < energy.area := by
  rw [energy.area_eq]
  exact Fraction.Order.Arithmetic.mul_pos_direct (by decide)
    (Fraction.Order.Arithmetic.pow_pos_direct energy.radius_positive 2)

/-- The retained contained energy lower coefficient is positive. -/
theorem lower_positive (energy : ContainedObservationEnergy polynomial region count) : 0 < energy.lower := by
  rw [energy.lower_eq]
  exact Fraction.Order.Arithmetic.mul_pos_direct energy.area_positive energy.original.boxes.densityConstant_positive

end

open Purelib.Geometry.Rational in
/-- Each retained contained square has the exact cached common area. -/
theorem boxContent_eq_area (energy : ContainedObservationEnergy polynomial region count) (index : Fin count) :
    Box.Content.boxContent (energy.box index) = energy.area := by
  rw [energy.area_eq]
  unfold Box.Content.boxContent Box.widthX Box.widthY box
    Box.Square.Centered.BoxTransport.centeredBox
  ring1

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}

open Purelib in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.LinearAlgebra.Gaussian in
open Purelib.Riemann.Topology in
/-- Restrict the original certified energy cell to its exact contained observation square. -/
def surfaceCell (energy : ContainedObservationEnergy curve.polynomial region genus)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (face :
      Topology.BranchedCover.Double.Attachment.Face) (index :
      Fin genus) :
    Energy.Prepared.PreparedEnergy.SurfaceCell curve coefficients :=
  PreparedSurfacePartitions.BoxPartition.restrictCell (PreparedObservationSurface.ObservationBoxes.surfaceCell
    energy.original.boxes coefficients face index)
    (energy.box index) (energy.box_proper index) (energy.box_refines_original index)

open Purelib in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Data in
open Purelib.LinearAlgebra.Gaussian in
/-- Cache the indexed restricted energy cells on the same original cover face. -/
def surfaceCells (energy : ContainedObservationEnergy curve.polynomial region genus)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (face :
      Topology.BranchedCover.Double.Attachment.Face) :
    Data.Vector (Energy.Prepared.PreparedEnergy.SurfaceCell curve coefficients) genus :=
  Vector.Basic.vectorOfFn (energy.surfaceCell coefficients face)

section
open Purelib
open Purelib.Data
open Purelib.LinearAlgebra.Gaussian
/-- The cached restricted cell retains the exact contained square at its original index. -/
theorem surfaceCells_box (energy : ContainedObservationEnergy curve.polynomial region genus)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (face :
      Topology.BranchedCover.Double.Attachment.Face) (index :
      Fin genus) :
    (energy.surfaceCells coefficients face index).box = energy.box index := by
  rw [surfaceCells, Vector.Basic.vectorOfFn_apply]; rfl

/-- Restriction preserves the exact original numerator-to-denominator density lower bound. -/
theorem surfaceCells_density (energy : ContainedObservationEnergy curve.polynomial region genus)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (face :
      Topology.BranchedCover.Double.Attachment.Face) (index :
      Fin genus) :
    (energy.surfaceCells coefficients face index).densityLower =
      energy.original.boxes.numeratorLower coefficients index / energy.original.boxes.denominatorScale := by
  rw [surfaceCells, Vector.Basic.vectorOfFn_apply]; rfl

end

open Purelib in
open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Geometry.Rational in
open Purelib.LinearAlgebra.Gaussian in
/-- Contained cell energy equals their common area times the original retained density sum. -/
theorem surfaceEnergy_eq (energy : ContainedObservationEnergy curve.polynomial region genus)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (face :
      Topology.BranchedCover.Double.Attachment.Face) :
    Energy.Prepared.surfaceEnergy (fun index => energy.surfaceCells coefficients face index) =
      energy.area * FiniteSum.Fin.sumFin (fun index => energy.original.boxes.numeratorLower coefficients index /
        energy.original.boxes.denominatorScale) := by
  change FiniteSum.Fin.sumFin (fun index => Box.Content.boxContent (energy.surfaceCells coefficients face index).box *
    (energy.surfaceCells coefficients face index).densityLower) = _
  calc
    _ = FiniteSum.Fin.sumFin (fun index => energy.area *
        (energy.original.boxes.numeratorLower coefficients index / energy.original.boxes.denominatorScale)) :=
      FiniteSum.Fin.sumFin_congr (fun index => by
          rw [energy.surfaceCells_box, energy.boxContent_eq_area, energy.surfaceCells_density])
    _ = _ := FiniteSum.Fin.sumFin_mul_left _ _

open Purelib
open Purelib.Curves.Hyperelliptic.Integration
open Purelib.Data.Rat
open Purelib.LinearAlgebra.Gaussian
/-- The retained contained lower coefficient controls energy for every original coefficient vector. -/
theorem uniform_lower (energy : ContainedObservationEnergy curve.polynomial region genus)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (face :
      Topology.BranchedCover.Double.Attachment.Face) :
    energy.lower * coefficientNormSq coefficients ≤ Energy.Prepared.surfaceEnergy (fun index => energy.surfaceCells
      coefficients face index) := by
  rw [energy.surfaceEnergy_eq, energy.lower_eq]
  exact (show energy.area * energy.original.boxes.densityConstant * coefficientNormSq coefficients =
    energy.area * (energy.original.boxes.densityConstant * coefficientNormSq coefficients) from by ring1).trans_le
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (energy.original.densitySum_lower coefficients)
        energy.area_positive.le)

/-- A nonzero coefficient vector has positive energy on the original contained cell family. -/
theorem positive_energy (energy : ContainedObservationEnergy curve.polynomial region genus)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (nonzero : Energy.NonzeroGaussianVector
      coefficients) (face :
      Topology.BranchedCover.Double.Attachment.Face) :
    0 < Energy.Prepared.surfaceEnergy (fun index => energy.surfaceCells coefficients face index) :=
  (Fraction.Order.Arithmetic.mul_pos_direct energy.lower_positive (coefficientNormSq_positive nonzero)).trans_le
    (energy.uniform_lower coefficients face)

end ContainedObservationEnergy
end Purelib.Riemann.Readings
