module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
public import Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Content
import Purelib.Geometry.Rational.Box.Dimensions
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Topology.BranchedCover.Double.Attachment

public import Purelib.Riemann.Readings.PreparedObservationBoxes
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Polynomial.Geometry.EvaluationLower
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Uniform positive geometry-backed observation energy

Turn the automatically separated boxes into the existing checked surface-cell
interface.  Exact box area and one shared denominator majorant convert the
homogeneous numerator bound into a positive energy constant fixed by the curve.

This is a local lower-sum theorem.  Identifying these cells with a refining
cut-surface mesh and paying its discrepancy from the actual period boundary
remain separate geometric obligations.
-/

namespace Purelib.Riemann.Topology.PreparedObservationSurface

open Purelib.Riemann.Readings.PreparedObservationBoxes (ObservationBoxes curveObservationBoxes)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (Coordinate coefficientNormSq coefficientNormSq_positive)
open _root_.Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial -> Dense

open Purelib.LinearAlgebra
open Purelib.Data.Gaussian.Basic.Canonical

namespace ObservationBoxes

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}

open Purelib in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.LinearAlgebra.Gaussian in
/-- A certified energy cell on the original observation box and chosen cover face.

The cell reuses the exact site's numerator lower bound and denominator certificate, divided by the common retained
denominator scale; its original geometric and density proof fields are preserved. -/
def surfaceCell (boxes : ObservationBoxes curve.polynomial genus)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (face : Topology.BranchedCover.Double.Attachment.Face) (index : Fin genus) :
    Energy.Prepared.PreparedEnergy.SurfaceCell curve coefficients where
  face := face
  box := boxes.box index
  proper := boxes.box_proper index
  densityLower := boxes.numeratorLower coefficients index / boxes.denominatorScale
  densityLower_nonnegative := Fraction.Order.Field.div_nonneg_direct
    (boxes.numeratorLower_nonnegative coefficients index) boxes.denominatorScale_positive.le
  denominatorLower := (boxes.sites index).denominatorValue / 4
  denominatorLower_positive := Fraction.Order.Field.div_pos_direct
    (boxes.sites index).denominatorValue_positive (by decide)
  denominator_apart := by
    intro point inside
    simpa only [Norm.Basic.normSq_eq_canonical] using (boxes.sites index).denominator_lower
      boxes.radius_positive.le (boxes.radius_le_site index) inside
  density_below_numerator := by
    intro point inside
    rw [Norm.Basic.normSq_eq_canonical]
    apply le_trans _ (boxes.numeratorLower_le coefficients index inside)
    apply (Fraction.Order.Field.div_le_iff_pos boxes.denominatorScale_positive).2
    calc
      boxes.numeratorLower coefficients index = boxes.numeratorLower coefficients index * 1 := by ring1
      _ <= boxes.numeratorLower coefficients index * boxes.denominatorScale :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct boxes.one_le_denominatorScale
          (boxes.numeratorLower_nonnegative coefficients index)
  density_valid := by
    intro point inside
    simp only [Norm.Basic.normSq_eq_canonical]
    have numeratorNonnegative := boxes.numeratorLower_nonnegative coefficients index
    have denominatorBound := ((boxes.sites index).denominator_upper boxes.radius_positive.le
      (boxes.radius_le_site index) inside).trans (boxes.majorant_le_denominatorScale index)
    calc
      _ <= (boxes.numeratorLower coefficients index / boxes.denominatorScale) * boxes.denominatorScale :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct denominatorBound
          (Fraction.Order.Field.div_nonneg_direct numeratorNonnegative boxes.denominatorScale_positive.le)
      _ = boxes.numeratorLower coefficients index :=
        Fraction.Field.div_mul_cancel_of_ne _ _ boxes.denominatorScale_positive.ne'
      _ <= _ := boxes.numeratorLower_le coefficients index inside

open Purelib in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Data in
open Purelib.LinearAlgebra.Gaussian in
/-- Cache the indexed energy cells of the original observation boxes on one retained cover face. -/
def surfaceCells (boxes : ObservationBoxes curve.polynomial genus)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (face : Topology.BranchedCover.Double.Attachment.Face) :
    Data.Vector (Energy.Prepared.PreparedEnergy.SurfaceCell curve coefficients) genus :=
  Vector.Basic.vectorOfFn (surfaceCell boxes coefficients face)

section
open Purelib
open Purelib.Data
open Purelib.LinearAlgebra.Gaussian
/-- The cached energy cell keeps the exact original observation box at its index. -/
theorem surfaceCells_box (boxes : ObservationBoxes curve.polynomial genus)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (face : Topology.BranchedCover.Double.Attachment.Face) (index : Fin genus) :
    (surfaceCells boxes coefficients face index).box = boxes.box index := by
  rw [surfaceCells, Vector.Basic.vectorOfFn_apply]
  rfl

/-- The cached cell density is the original numerator lower bound divided by the common denominator scale. -/
theorem surfaceCells_density (boxes : ObservationBoxes curve.polynomial genus)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (face : Topology.BranchedCover.Double.Attachment.Face) (index : Fin genus) :
    (surfaceCells boxes coefficients face index).densityLower =
      boxes.numeratorLower coefficients index / boxes.denominatorScale := by
  rw [surfaceCells, Vector.Basic.vectorOfFn_apply]
  rfl

end

open Purelib in
open Purelib.LinearAlgebra.Gaussian in
/-- Distinct original observation indices give separated cached energy-cell boxes. -/
theorem surfaceCells_separated (boxes : ObservationBoxes curve.polynomial genus)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (face : Topology.BranchedCover.Double.Attachment.Face) {left right : Fin genus} (different : left ≠ right) :
    (surfaceCells boxes coefficients face left).box.Separated
      (surfaceCells boxes coefficients face right).box := by
  rw [surfaceCells_box, surfaceCells_box]
  exact boxes.box_separated different

end ObservationBoxes

open Purelib.Polynomial.Dense.Gaussian in
set_option genInjectivity false in
/-- The original observation boxes with their common area and energy lower coefficient.

Both scalars are cached with defining equations: area is four times the radius squared, and the lower coefficient is
that area times the original density constant. -/
structure ObservationBoxEnergy (polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (count : Nat) where
  /-- The exact retained observation boxes and their original coercivity data. -/ boxes : ObservationBoxes polynomial
    count
  /-- The cached common rational area of the original squares. -/ area : Coordinate
  /-- The area is exactly four times the retained radius squared. -/ area_eq : area = 4 * boxes.radius ^ 2
  /-- The cached energy lower coefficient of these exact boxes. -/ lower : Coordinate
  /-- The lower coefficient equals their common area times the original density constant. -/ lower_eq : lower = area *
    boxes.densityConstant

constructive_injectivity ObservationBoxEnergy

namespace ObservationBoxEnergy

open Purelib.Riemann.Topology.PreparedObservationSurface.ObservationBoxes (surfaceCells surfaceCells_box
  surfaceCells_density)

variable {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {count : Nat}

/-- Cache the exact common square area and density-weighted lower coefficient for the original boxes. -/
def ofBoxes (boxes : ObservationBoxes polynomial count) : ObservationBoxEnergy polynomial count :=
  let area := 4 * boxes.radius ^ 2
  { boxes := boxes
    area := area
    area_eq := rfl
    lower := area * boxes.densityConstant
    lower_eq := rfl }

section
open Purelib.Data.Rat
/-- The common observation-square area is positive. -/
theorem area_positive (energy : ObservationBoxEnergy polynomial count) : 0 < energy.area := by
  rw [energy.area_eq, pow_two]
  exact Fraction.Order.Arithmetic.mul_pos_direct (by decide)
    (Fraction.Order.Arithmetic.mul_pos_direct energy.boxes.radius_positive energy.boxes.radius_positive)

/-- The retained observation energy lower coefficient is positive. -/
theorem lower_positive (energy : ObservationBoxEnergy polynomial count) : 0 < energy.lower := by
  rw [energy.lower_eq]
  exact Fraction.Order.Arithmetic.mul_pos_direct energy.area_positive energy.boxes.densityConstant_positive

end

open Purelib.Geometry.Rational in
/-- Each original observation square has the cached common rational area. -/
theorem boxContent_eq_area (energy : ObservationBoxEnergy polynomial count) (index : Fin count) :
    Box.Content.boxContent (energy.boxes.box index) = energy.area := by
  rw [energy.area_eq]
  unfold Box.Content.boxContent Box.widthX Box.widthY
    ObservationBoxes.box Box.Square.Centered.BoxTransport.centeredBox
  ring1

open Purelib.Algebra in
open Purelib.Data.Rat in
open Purelib.LinearAlgebra.Gaussian in
/-- The sum of original cell densities controls the exact coefficient squared norm.

The same retained density constant multiplies the coefficient norm; denominator scaling transports the original
quarter-coercivity estimate. -/
theorem densitySum_lower (energy : ObservationBoxEnergy polynomial count)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector count) :
    energy.boxes.densityConstant * coefficientNormSq coefficients <=
      FiniteSum.Fin.sumFin (fun index => energy.boxes.numeratorLower coefficients index / energy.boxes.denominatorScale)
        := by
  have inverseNonnegative : 0 <= energy.boxes.denominatorScale⁻¹ :=
    (Fraction.Order.Field.inv_pos_direct energy.boxes.denominatorScale_positive).le
  have bound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (energy.boxes.quarter_coercivity_le_numeratorSum coefficients) inverseNonnegative
  have sumEquation := FiniteSum.Fin.sumFin_mul_right (energy.boxes.numeratorLower coefficients)
    energy.boxes.denominatorScale⁻¹
  change FiniteSum.Fin.sumFin (fun index => energy.boxes.numeratorLower coefficients index /
    energy.boxes.denominatorScale) =
    _ at sumEquation
  rw [sumEquation]
  exact (show energy.boxes.densityConstant * coefficientNormSq coefficients =
      (energy.boxes.coercivity.lower / 4 * coefficientNormSq coefficients) *
        energy.boxes.denominatorScale⁻¹ by
      rw [energy.boxes.densityConstant_eq]
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      ring1).trans_le bound

open Purelib in
open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Geometry.Rational in
open Purelib.LinearAlgebra.Gaussian in
open Purelib.Riemann.Topology in
/-- The energy of the retained surface cells equals their common area times the original density sum. -/
theorem surfaceEnergy_eq {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (energy : ObservationBoxEnergy curve.polynomial genus)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (face : Topology.BranchedCover.Double.Attachment.Face) :
    Energy.Prepared.surfaceEnergy (fun index => surfaceCells energy.boxes coefficients face index) =
      energy.area * FiniteSum.Fin.sumFin (fun index =>
        energy.boxes.numeratorLower coefficients index / energy.boxes.denominatorScale) := by
  change FiniteSum.Fin.sumFin (fun index =>
    Box.Content.boxContent (surfaceCells energy.boxes coefficients face index).box *
      (surfaceCells energy.boxes coefficients face index).densityLower) = _
  calc
    _ = FiniteSum.Fin.sumFin (fun index => energy.area *
        (energy.boxes.numeratorLower coefficients index / energy.boxes.denominatorScale)) :=
      FiniteSum.Fin.sumFin_congr (fun index => by
        rw [PreparedObservationSurface.ObservationBoxes.surfaceCells_box energy.boxes, energy.boxContent_eq_area,
          PreparedObservationSurface.ObservationBoxes.surfaceCells_density energy.boxes])
    _ = _ := FiniteSum.Fin.sumFin_mul_left _ _

open Purelib
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Integration
open Purelib.Data.Rat
open Purelib.LinearAlgebra.Gaussian
/-- The retained energy lower coefficient controls the surface energy for every original coefficient vector. -/
theorem lower_mul_coefficientNorm_le_surfaceEnergy {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (energy : ObservationBoxEnergy curve.polynomial genus)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (face : Topology.BranchedCover.Double.Attachment.Face) :
    energy.lower * coefficientNormSq coefficients <=
      Energy.Prepared.surfaceEnergy (fun index => surfaceCells energy.boxes coefficients face index) := by
  rw [energy.surfaceEnergy_eq, energy.lower_eq]
  exact (show energy.area * energy.boxes.densityConstant * coefficientNormSq coefficients =
      energy.area * (energy.boxes.densityConstant * coefficientNormSq coefficients) by ring1).trans_le
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (energy.densitySum_lower coefficients) energy.area_positive.le)

/-- A nonzero coefficient vector gives positive energy on the retained observation cells. -/
theorem surfaceEnergy_positive {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (energy : ObservationBoxEnergy curve.polynomial genus)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (nonzero : Energy.NonzeroGaussianVector coefficients)
    (face : Topology.BranchedCover.Double.Attachment.Face) :
    0 < Energy.Prepared.surfaceEnergy (fun index => surfaceCells energy.boxes coefficients face index) :=
  (Fraction.Order.Arithmetic.mul_pos_direct energy.lower_positive
    (coefficientNormSq_positive nonzero)).trans_le
      (energy.lower_mul_coefficientNorm_le_surfaceEnergy coefficients face)

end ObservationBoxEnergy

open Purelib.Curves.Hyperelliptic in
/-- Build the original curve's observation boxes with cached area and energy lower coefficient. -/
def curveObservationBoxEnergy {genus : Nat}
    (curve : Basic.HyperellipticCurve genus) :
    ObservationBoxEnergy curve.polynomial genus :=
  ObservationBoxEnergy.ofBoxes (curveObservationBoxes curve)

end Purelib.Riemann.Topology.PreparedObservationSurface
