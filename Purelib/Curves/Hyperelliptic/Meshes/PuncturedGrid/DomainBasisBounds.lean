module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Integration.Energy.AffineTriangle

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
public import Purelib.Integration.Polynomial.Rectangle.Accuracy.FragmentIndex
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy
public import Purelib.Riemann.Integration.RectangularPrimitiveDerivative
import Purelib.Riemann.Periods.PeriodMatrix
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.AffineBasisEnergy
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring
public import Purelib.Riemann.Readings.RectangularObservationEnergy

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Data.Rat

open Purelib.Data.Vector

open Purelib.Integration.Energy

open Purelib.Integration.Polynomial.Rectangle.Accuracy.FragmentIndex

open Purelib.Riemann.Comparison

open Purelib.Riemann.Comparison.PrimitiveEdgeComparison

open Purelib.Riemann.Integration

open Purelib.Riemann.Integration.RectangularOwnedTriangulation

open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy

open Purelib.Riemann.Integration.RectangularPrimitiveDerivative

open Purelib.Riemann.Integration.RectangularSharedPrimitives

open Purelib.Riemann.Normalization

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings

public section

/-!
# Coefficient-independent ceilings for retained domain basis readings

The fixed model derivatives and monomial bounds are cached before choosing
a spatial depth. Requests for all basis rows are synchronized at one finite
maximum index. Every estimate consumes the actual supplied domain primitives
and their shared owner readings.
-/

section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open Purelib.Riemann.Normalization.RectangularInverseModels (Bank Geometry)
open Purelib.Riemann.Integration.RectangularPrimitiveDerivative (DerivativeBank)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (ModelTriangle OwnedTriangulation)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)
open Purelib.Integration.Energy.AffineTriangle (affinePrimitiveIncrement affinePrimitiveIncrementError)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_mul_right sumFin_mul_left)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg normSq_mul)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy (BasisReadings)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (ambient_numerator_inverse_le)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    RegularFace bank} {models :
    FaceModels frames face} {sheet :
    Fin 2}
  {domain : PeriodDomain models sheet}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds

/-- A finite sum of nonnegative rational terms is nonnegative. -/
private theorem sum_nonnegative {count : Nat} (values : Fin count → InverseRootPolynomial.Coordinate) (nonnegative : ∀
  index, 0 ≤ values index) :
    0 ≤ FiniteSum.Fin.sumFin values := by
  have estimate := Order.Positivity.sumFin_mono (fun _ => 0) values nonnegative
  simpa only [FiniteSum.Fin.sumFin_zero] using estimate

/-- A finite constant sum equals the retained index count times its value. -/
private theorem sum_constant (count : Nat) (value : InverseRootPolynomial.Coordinate) : FiniteSum.Fin.sumFin (fun _ :
  Fin count => value) = (count : InverseRootPolynomial.Coordinate) * value := by
  induction count with
  | zero => change 0 = 0 * value; ring1
  | succ count ih => rw [FiniteSum.Fin.sumFin_succ, ih, Nat.cast_succ]; ring1

set_option genInjectivity false in
/-- Cached coefficient-independent derivative and overlap ceilings for one retained face-sheet domain.

The original models and standard-differential rows determine both scales before spatial refinement or linear-combination
coefficients are selected. -/
structure EnergyPreflight (domain : Periods.PeriodDomain models sheet) where
  /-- The cached derivative bank on the exact retained coarse inverse models. -/ derivatives :
    RectangularPrimitiveDerivative.DerivativeBank face.clearance domain.patch.models
  /-- The cached derivative bounds for each actual standard-differential numerator. -/ numerators :
    Data.Vector.DependentVector (fun row : Fin genus =>
    DerivativeBank.Numerator derivatives (PreparedPrimitiveSamples.differentialNumerator
      (PeriodMatrix.standardDifferential row)))
  /-- The cached primitive-overlap bounds for every retained basis row. -/ overlaps : Data.Vector.DependentVector (fun
    row : Fin genus =>
    PrimitiveEdgeComparison.PrimitiveOverlapBounds face.clearance (PreparedPrimitiveSamples.differentialNumerator
      (PeriodMatrix.standardDifferential row)))
  /-- The cached common scale bounding finite affine coefficients. -/ coefficientScale :
    InverseRootPolynomial.Coordinate
  /-- The coefficient scale is the exact genus-weighted sum of the retained numerator and inverse bounds. -/
    coefficientScale_eq : coefficientScale = (genus : InverseRootPolynomial.Coordinate) * FiniteSum.Fin.sumFin (fun row
    =>
    (overlaps.get row).numeratorUpper * (overlaps.get row).inverseUpper)
  /-- The cached common scale bounding finite affine-increment remainders. -/ taylorScale :
    InverseRootPolynomial.Coordinate
  /-- The Taylor scale is the exact genus-weighted sum of the retained derivative totals. -/ taylorScale_eq :
    taylorScale = 8 * (genus : InverseRootPolynomial.Coordinate) * FiniteSum.Fin.sumFin (fun row => (numerators.get
    row).total)

constructive_injectivity EnergyPreflight

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds

section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds.EnergyPreflight

/-- Cache all retained basis-row derivative and overlap bounds before selecting a mesh depth. -/
@[expose] def build (domain : Periods.PeriodDomain models sheet) :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds.EnergyPreflight domain :=
  let derivatives := DerivativeBank.build face.clearance domain.patch.models domain.patch.cell_refines
  let numerators := DependentVector.ofFn fun row : Fin genus =>
    derivatives.forNumerator (PreparedPrimitiveSamples.differentialNumerator (PeriodMatrix.standardDifferential row))
  let overlaps := DependentVector.ofFn fun row : Fin genus =>
    PrimitiveOverlapBounds.build face.clearance (PreparedPrimitiveSamples.differentialNumerator
      (PeriodMatrix.standardDifferential row))
  { derivatives := derivatives
    numerators := numerators
    overlaps := overlaps
    coefficientScale := Aggregate.countCoordinate genus * FiniteSum.Fin.sumFin (fun row =>
      (overlaps.get row).numeratorUpper * (overlaps.get row).inverseUpper)
    coefficientScale_eq := by rw [Aggregate.countCoordinate_eq]
    taylorScale := 8 * Aggregate.countCoordinate genus * FiniteSum.Fin.sumFin (fun row => (numerators.get row).total)
    taylorScale_eq := by rw [Aggregate.countCoordinate_eq] }

/-- The retained common coefficient scale is nonnegative. -/
theorem coefficientScale_nonnegative (preflight :
  DomainBasisBounds.EnergyPreflight domain) : 0 ≤ preflight.coefficientScale
  := by
  rw [preflight.coefficientScale_eq]
  exact Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le genus))
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds.sum_nonnegative _ (fun row =>
      Fraction.Order.Arithmetic.mul_nonneg_direct
      (preflight.overlaps.get row).numeratorUpper_nonnegative (preflight.overlaps.get row).inverseUpper_positive.le))

/-- The retained common Taylor-error scale is nonnegative. -/
theorem taylorScale_nonnegative (preflight : DomainBasisBounds.EnergyPreflight
  domain) : 0 ≤ preflight.taylorScale := by
  rw [preflight.taylorScale_eq]
  exact Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le
      genus)))
    (PuncturedGrid.DomainBasisBounds.sum_nonnegative _ (fun row => (preflight.numerators.get
      row).total_nonnegative))

set_option genInjectivity false in
/-- The common index is selected before any requested inverse polynomial or primitive is built. All rows retain their
individual exact error reports. -/
structure Request (preflight : DomainBasisBounds.EnergyPreflight domain)
  (target : InverseRootPolynomial.Coordinate) where
  /-- The cached common polynomial index of all retained row requests. -/ index : Nat
  /-- The original retained basis-row accuracy requests at the common index. -/ rows : Data.Vector.DependentVector (fun
    row => RectangularPrimitiveAccuracy.GridPrimitiveAccuracy (preflight.overlaps.get row) domain.steps target)
  /-- Every actual retained row request has exactly the common index. -/ index_eq : ∀ row, (rows.get row).index = index

constructive_injectivity Request

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds.EnergyPreflight

section

variable {preflight : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds.EnergyPreflight domain}
  {target : Coordinate}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds.EnergyPreflight.Request

/-- Synchronize every original basis-row accuracy request at the exact finite maximum index before constructing
primitive polynomials. -/
@[expose] def build (preflight : DomainBasisBounds.EnergyPreflight domain)
  (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds.EnergyPreflight.Request preflight target :=
  let initial := DependentVector.ofFn fun row => GridPrimitiveAccuracy.build (preflight.overlaps.get row) domain.steps
    target positive
  let index := initial.maximum (fun _ request => request.index)
  { index := index
    rows := DependentVector.ofFn fun row => GridPrimitiveAccuracy.atIndex (initial.get row) index
      (initial.get_le_maximum (fun _ request => request.index) row)
    index_eq := fun row => by rw [DependentVector.ofFn_get]; rfl }

/-- Raise all retained basis-row requests to a supplied later common index without replacing their error owners. -/
@[expose] def refineIndex (request : EnergyPreflight.Request
  preflight target) (index : Nat) (later : request.index ≤ index) :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds.EnergyPreflight.Request preflight target :=
  { index := index
    rows := DependentVector.ofFn fun row =>
      GridPrimitiveAccuracy.atIndex (request.rows.get row) index ((request.index_eq row).trans_le later)
    index_eq := fun row => by rw [DependentVector.ofFn_get]; rfl }

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds.EnergyPreflight.Request

end
end

section

variable {stage : Nat}
  {cached : (row : Fin genus) → DomainPrimitives
    domain (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential row) stage}
  {triangles : List (ModelTriangle domain.geometry)} {surface
    : OwnedTriangulation triangles}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy.BasisReadings

/-- Each retained affine coefficient satisfies its cached row-specific numerator/inverse bound. -/
theorem row_coefficient_bound
  (readings : DomainBasisEnergy.BasisReadings cached surface) (preflight :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds.EnergyPreflight domain)
    (row : Fin genus) (index : Fin (triangles.map ModelTriangle.triangle).length) :
    Data.Gaussian.Norm.Basic.normSq (readings.affine.coefficients row index) ≤
      (preflight.overlaps.get row).numeratorUpper * (preflight.overlaps.get row).inverseUpper := by
  rw [readings.coefficients_eq, SharedPrimitiveValues.faceCoefficients, Data.Vector.Basic.vectorOfFn_apply,
    (cached row).primitives.coefficient_eq]
  rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
  exact RectangularPrimitiveModels.ambient_numerator_inverse_le (preflight.overlaps.get row) _
    (preflight.derivatives.refines _ _) (surface.face_inside index).1

/-- Each actual affine increment is bounded by its retained row coefficient ceiling times the supplied squared movement
bound. -/
theorem row_affine_bound
  (readings : DomainBasisEnergy.BasisReadings cached surface) (preflight :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds.EnergyPreflight domain)
    (row : Fin genus) (index : Fin (triangles.map ModelTriangle.triangle).length) (last : Fin
      surface.mesh.vertices.length)
    {distance : InverseRootPolynomial.Coordinate} (movement : Data.Gaussian.Norm.Basic.normSq
      (surface.mesh.coordinate last -
      surface.mesh.coordinate (surface.mesh.triangulation.faces index).first) ≤ distance) :
    Data.Gaussian.Norm.Basic.normSq (Purelib.Integration.Energy.AffineTriangle.affinePrimitiveIncrement
      (readings.affine.coefficients row index)
      (surface.mesh.coordinate (surface.mesh.triangulation.faces index).first) (surface.mesh.coordinate last)) ≤
      ((preflight.overlaps.get row).numeratorUpper * (preflight.overlaps.get row).inverseUpper) * distance := by
  have equal : AffineTriangle.affinePrimitiveIncrement (readings.affine.coefficients row index)
      (surface.mesh.coordinate (surface.mesh.triangulation.faces index).first) (surface.mesh.coordinate last) =
      readings.affine.coefficients row index *
        (surface.mesh.coordinate last - surface.mesh.coordinate (surface.mesh.triangulation.faces index).first) := by
    unfold AffineTriangle.affinePrimitiveIncrement; ring1
  rw [equal, Data.Gaussian.Norm.Basic.normSq_mul]
  exact Fraction.Order.Arithmetic.mul_le_mul_direct (readings.row_coefficient_bound preflight row index) movement
    (Data.Gaussian.Norm.Basic.normSq_nonneg _) (Fraction.Order.Arithmetic.mul_nonneg_direct
      (preflight.overlaps.get row).numeratorUpper_nonnegative (preflight.overlaps.get row).inverseUpper_positive.le)

/-- Each retained affine-increment error is bounded by the paid row target and cached fourth-order movement remainder.
-/
theorem row_error_bound
  (readings : DomainBasisEnergy.BasisReadings cached surface) (preflight :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds.EnergyPreflight domain)
    {target : InverseRootPolynomial.Coordinate} (request : preflight.Request target) (stage_eq : stage = request.index)
    (row : Fin genus) (index : Fin (triangles.map ModelTriangle.triangle).length) (last : Fin
      surface.mesh.vertices.length)
    (inside : (domain.geometry.box (surface.faceSource index).column (surface.faceSource index).row).Contains
      (surface.mesh.coordinate last)) :
    Data.Gaussian.Norm.Basic.normSq (Purelib.Integration.Energy.AffineTriangle.affinePrimitiveIncrementError
      (readings.affine.coefficients row index)
      (surface.mesh.coordinate (surface.mesh.triangulation.faces index).first) (surface.mesh.coordinate last)
      (readings.affine.values row (surface.mesh.triangulation.faces index).first) (readings.affine.values row last)) ≤
      32 * target + 8 * (preflight.numerators.get row).total *
        Data.Gaussian.Norm.Basic.normSq (surface.mesh.coordinate last - surface.mesh.coordinate
          (surface.mesh.triangulation.faces index).first) ^ 2 := by
  have estimate := (preflight.numerators.get row).shared_increment_bound (request.rows.get row)
    (stage_eq.trans (request.index_eq row).symm) (readings.rows.get row)
    (surface.faceSource index).column (surface.faceSource index).row
    (surface.mesh.triangulation.faces index).first last (surface.face_inside index).1 inside
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
  have upper : 32 * (request.rows.get row).globalBound +
      8 * (((preflight.numerators.get row).entries.get (surface.faceSource index).column).get (surface.faceSource
        index).row).bound *
        Data.Gaussian.Norm.Basic.normSq (surface.mesh.coordinate last - surface.mesh.coordinate
          (surface.mesh.triangulation.faces index).first) ^ 2 ≤
      32 * target + 8 * (preflight.numerators.get row).total *
        Data.Gaussian.Norm.Basic.normSq (surface.mesh.coordinate last - surface.mesh.coordinate
          (surface.mesh.triangulation.faces index).first) ^ 2 := add_le_add
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (request.rows.get row).accurate.le (by
        decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 32))
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        ((preflight.numerators.get row).entry_le_total _ _) (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 8))
          (Fraction.Order.Arithmetic.sq_nonneg_direct _))
  rw [readings.coefficients_eq, readings.values_eq, readings.values_eq, SharedPrimitiveValues.faceCoefficients,
    Data.Vector.Basic.vectorOfFn_apply]
  unfold AffineTriangle.affinePrimitiveIncrementError AffineTriangle.affinePrimitiveIncrement
  rw [← mul_sub]
  exact estimate.trans upper

/-- The finite genus-weighted sum of retained affine increments satisfies the shared coefficient-scale ceiling. -/
theorem affine_scale_bound
  (readings : DomainBasisEnergy.BasisReadings cached surface) (preflight :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds.EnergyPreflight domain)
    (index : Fin (triangles.map ModelTriangle.triangle).length) (last : Fin surface.mesh.vertices.length)
    {distance : InverseRootPolynomial.Coordinate} (movement : Data.Gaussian.Norm.Basic.normSq
      (surface.mesh.coordinate last -
      surface.mesh.coordinate (surface.mesh.triangulation.faces index).first) ≤ distance) :
    (genus : InverseRootPolynomial.Coordinate) * FiniteSum.Fin.sumFin (fun row =>
      Data.Gaussian.Norm.Basic.normSq (AffineTriangle.affinePrimitiveIncrement (readings.affine.coefficients
      row index)
      (surface.mesh.coordinate (surface.mesh.triangulation.faces index).first) (surface.mesh.coordinate last))) ≤
      preflight.coefficientScale * distance := by
  have estimate := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Order.Positivity.sumFin_mono _ _ (fun row => readings.row_affine_bound preflight row index last movement))
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le genus))
  rw [FiniteSum.Fin.sumFin_mul_right] at estimate
  exact estimate.trans_eq (by rw [preflight.coefficientScale_eq]; ring1)

/-- The finite genus-weighted sum of retained affine errors satisfies the common target and Taylor-scale ceiling. -/
theorem error_scale_bound
  (readings : DomainBasisEnergy.BasisReadings cached surface) (preflight :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds.EnergyPreflight domain)
    {target : InverseRootPolynomial.Coordinate} (request : preflight.Request target) (stage_eq : stage = request.index)
    (index : Fin (triangles.map ModelTriangle.triangle).length) (last : Fin surface.mesh.vertices.length)
    (inside : (domain.geometry.box (surface.faceSource index).column (surface.faceSource index).row).Contains
      (surface.mesh.coordinate last))
    {distance : InverseRootPolynomial.Coordinate} (movement : Data.Gaussian.Norm.Basic.normSq
      (surface.mesh.coordinate last -
      surface.mesh.coordinate (surface.mesh.triangulation.faces index).first) ≤ distance) :
    (genus : InverseRootPolynomial.Coordinate) * FiniteSum.Fin.sumFin (fun row =>
      Data.Gaussian.Norm.Basic.normSq (AffineTriangle.affinePrimitiveIncrementError
      (readings.affine.coefficients row index)
      (surface.mesh.coordinate (surface.mesh.triangulation.faces index).first) (surface.mesh.coordinate last)
      (readings.affine.values row (surface.mesh.triangulation.faces index).first) (readings.affine.values row last))) ≤
      32 * (genus : InverseRootPolynomial.Coordinate) ^ 2 * target + preflight.taylorScale * distance ^ 2 := by
  have pointwise (row : Fin genus) := (readings.row_error_bound preflight request stage_eq row index last inside).trans
    (add_le_add (le_refl (32 * target))
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.pow_le_pow_direct (Data.Gaussian.Norm.Basic.normSq_nonneg _) movement 2)
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (preflight.numerators.get row).total_nonnegative)))
  have estimate := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Order.Positivity.sumFin_mono _ _ pointwise) (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le genus))
  rw [FiniteSum.Fin.sumFin_add, Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds.sum_constant,
    FiniteSum.Fin.sumFin_mul_right, FiniteSum.Fin.sumFin_mul_left] at estimate
  exact estimate.trans_eq (by rw [preflight.taylorScale_eq]; ring1)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy.BasisReadings

end
end
