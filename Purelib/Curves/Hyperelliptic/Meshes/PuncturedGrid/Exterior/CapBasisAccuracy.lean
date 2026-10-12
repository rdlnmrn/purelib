module
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.List.Flatten
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Algebra.FiniteSum.Rational.Squares
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisUniform
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapRefinement
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.AffineBasisEnergy
import Purelib.Riemann.Topology.PreparedSurfacePartitions
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Tactic.Ring

public section

/-! Requested homogeneous energy on the complete cached regular reciprocal cap. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest

open Purelib
open Purelib.Algebra
open Purelib.Algebra.FiniteSum.Rational
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate
open Purelib.Data.Rat
open Purelib.LinearAlgebra.Gaussian.Energy
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Readings

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Integration.Energy.AffineTriangle (coordinateTriangleArea)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation (CapAttachment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment
  (ReciprocalGeometry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapRefinement (Refinement)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials
  RegularBasisSample)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds (RegularBasisBounds)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate (RegularBasisFace RegularBasisCap)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)
open Purelib.Riemann.Normalization
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_zero sumFin_congr)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains differential} {attached :
    CapAttachment prepared}
  {geometry :
    Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry
    attached} {coarse : Purelib.Topology.Polygon.Stokes.OrientedTriangle (lifted.vertices.count +
    attached.words.length)}
  {depth : Nat} {parameters : Purelib.Integration.Path.Dyadic.RadialTriangles.Parameters depth}
  {index : Nat} {box : Purelib.Geometry.Rational.Box}

open Purelib.Riemann.Readings.AffineBasisEnergy (AffineBasis)
open Purelib.Integration.Energy.Polygon (energyPrimitivePoint)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)

open _root_.Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap (EnergyBounds)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Algebra.FiniteSum.Fin (sumFin_mul_right)
open Purelib.Integration.Energy.AffineTriangle (affinePrimitiveIncrement affinePrimitiveIncrementError)

open Purelib.Riemann.Topology.PrimitiveSurfaceBudget (SurfaceTolerance)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Approximation.Rational.Geometric.Search (firstQuarterBelow firstQuarterBelow_ge firstQuarterBelow_accurate)

open Purelib.Algebra.FiniteSum.Rational.Squares (coordinateSum)

namespace RegularBasisRequest

variable {polynomials :
  RegularBasisPolynomials cap index box}
  {bounds : RegularBasisBounds polynomials
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.boundingBox}
  {minimum : Nat} {target : Purelib.Data.Rat.Fraction.Rational}
  (request : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest.RegularBasisRequest bounds
    attached.caps.length target minimum)
  {parameters : Purelib.Integration.Path.Dyadic.RadialTriangles.Parameters request.depth}

/-- Replace only the error certificate, retaining every original basis value and the coordinates of the cap refinement.
-/
@[expose] def certifyFace (entry : CapBasisAggregate.RegularBasisFace geometry parameters polynomials) :
  CapBasisAggregate.RegularBasisFace geometry parameters polynomials :=
  { entry with sample := { entry.sample with budget := request.surfaceBudget entry.sample entry.member } }

/-- Replacing only the retained face error certificates preserves the exact original coarse face list. -/
theorem coarses (entries : List (CapBasisAggregate.RegularBasisFace geometry parameters polynomials)) :
    (entries.map request.certifyFace).map RegularBasisFace.coarse = entries.map RegularBasisFace.coarse := by
  induction entries with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons head.coarse) ih

/-- The complete certified cap reuses the existing geometry and basis cache. -/
@[expose] def certify (prepared : CapBasisAggregate.RegularBasisCap geometry parameters polynomials) :
  CapBasisAggregate.RegularBasisCap geometry parameters polynomials :=
  let entries := prepared.entries.map request.certifyFace
  ⟨entries, (request.coarses prepared.entries).trans prepared.coarses_eq,
    Squares.coordinateSum (entries.map (fun entry => entry.sample.budget.total)), rfl⟩

/-- The certified cap's complete cached error budget is exactly the original request's paid total. -/
theorem certify_budget (prepared : CapBasisAggregate.RegularBasisCap geometry parameters polynomials) :
    (request.certify prepared).budget = request.total := by
  have aggregate (entries : List (CapBasisAggregate.RegularBasisFace geometry parameters polynomials)) :
      Squares.coordinateSum ((entries.map request.certifyFace).map (fun entry => entry.sample.budget.total)) =
        (entries.length : Fraction.Rational) * (128 * (2 * bounds.coefficient + 3) * request.tolerance.epsilon) := by
    induction entries with
    | nil => change 0 = 0 * _; ring1
    | cons head tail ih =>
        change (request.surfaceBudget head.sample head.member).total + _ = _
        rw [request.surfaceBudget_total, ih, List.length_cons, Nat.cast_succ]
        ring1
  have count := congrArg List.length prepared.coarses_eq
  rw [Data.List.Map.length_map] at count
  rw [(request.certify prepared).budget_eq]
  change Squares.coordinateSum ((prepared.entries.map request.certifyFace).map (fun entry => entry.sample.budget.total))
    = _
  rw [aggregate, count, request.total_eq]
  ring1

/-- The original request pays the complete certified cap budget strictly below its target. -/
theorem certify_accurate (prepared : CapBasisAggregate.RegularBasisCap geometry parameters polynomials) :
    (request.certify prepared).budget < target :=
  (request.certify_budget prepared).trans_lt request.accurate

/-- The requested homogeneous energy bound includes the zero vector and reads the cached energy of the complete cap. -/
theorem energy_lower (prepared : CapBasisAggregate.RegularBasisCap geometry parameters polynomials)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (evaluated : (request.certify prepared).Evaluation coefficients) :
    -(target * PreparedObservationCoercivity.coefficientNormSq coefficients) ≤ evaluated.area.im / 4 := by
  have normNonnegative : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le (Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : Fraction.Rational))
      _
      (fun row => Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (request.certify_accurate prepared).le
    normNonnegative
  have lower := (Fraction.Order.Arithmetic.neg_le_neg_direct paid).trans evaluated.lower
  exact (show -(target * PreparedObservationCoercivity.coefficientNormSq coefficients) =
    -(PreparedObservationCoercivity.coefficientNormSq coefficients * target) by ring1).trans_le lower

/-- The exact inverse-arc boundary inherits the requested homogeneous cap bound after all radial edges have cancelled.
-/
theorem arcs_lower (prepared : CapBasisAggregate.RegularBasisCap geometry parameters polynomials)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (evaluated : (request.certify prepared).Evaluation coefficients) :
    -(target * PreparedObservationCoercivity.coefficientNormSq coefficients) ≤
      (CellBoundary.sumValues (fun word => CellBoundary.sumValues (fun edge =>
        ReciprocalRadialGeometry.arcArea (polynomials.value coefficients) request.depth
          (lifted.vertices.coordinate edge.finish) (lifted.vertices.coordinate edge.start)) word) attached.words).im / 4
            := by
  rw [← evaluated.area_eq_arcs]
  exact request.energy_lower prepared coefficients evaluated

end RegularBasisRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest
