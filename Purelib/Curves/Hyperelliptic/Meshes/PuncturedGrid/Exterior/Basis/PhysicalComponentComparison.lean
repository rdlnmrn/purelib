module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HierarchicalRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PreparedPhysicalRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonSourceArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceMagnitude
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PreparedPhysicalBounds
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalRunEntries
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalRunBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Budget.Trace.Family
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Topology.Polygon.Stokes

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

public section

/-! Pay the component comparison using certified physical runs on the same prepared sources. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalComponentComparison

open Purelib

open Purelib.Data.Rat

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Differentials.Basic.Differential genus}
  {collar : Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : PeriodPrograms.ExteriorProgram lifted differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

variable {bounds : Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {retained : Preparation.CommonBasisPreparation prepared}
  {basis : Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {target coefficientTarget : InverseRootPolynomial.Coordinate} {coverFloor floor index minimum stage
    energyFloor radialDepth : Nat}
  {box : Rational.Box} {capSample : Charts.Reciprocal.Cap.Primitives.Sample cap
    differential index box}
  {polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box}

namespace CommonBasisRequest

variable {request : Preparation.CommonBasisRequest retained basis
  target coefficientTarget coverFloor floor}
  {plans : request.Plans capSample polynomials minimum} {inputs : retained.Inputs index}
  {readings : Charts.Reciprocal.Disk.Basis.CommonParentPlans.Readings retained.anchors retained.sources
    request.schedule.bank plans inputs stage}

variable {fans : Connection.CommonBasisRequest.FanPreparation request
  plans inputs readings energyFloor}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace Sampled

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)

open Purelib.Data.Rat.Fraction.Compatibility

variable (sample : Connection.CommonBasisRequest.Sampled fans
  coefficients radialDepth) (comparisons :
  CommonPreparedComparison.CommonBasisRequest.Sampled.PreparedComparisons
  sample)
  {faceIndex : Nat} (banks : PhysicalRunEntries
    retained inputs coefficients faceIndex)

/-- Source-oriented paths are read directly from the retained occurrence banks. -/
@[expose] def physicalPaths (outer : Fin prepared.occurrences.length)
    (position : Fin (ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length) : List PrimitivePoint :=
  (banks.get outer).bank.physical position

/-- Every certificate retains the exact prepared source and physical path of
its occurrence and parent, at the computed homogeneous parent target. -/
@[expose] def PreparedPhysicalRows (magnitude requested : InverseRootPolynomial.Coordinate) :=
  Vector.DependentVector (fun outer : Fin prepared.occurrences.length =>
    Vector.DependentVector (fun position : Fin
      (ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length =>
      PreparedPhysicalRuns.PhysicalRunBank.PreparedRun (banks.get
        outer).bank position
        (ParentPrepared.CommonBasisRequest.Sampled.parentPrepared
        sample comparisons outer position)
        (HierarchicalRequest.CommonBasisRequest.Sampled.parentTarget
          prepared outer magnitude requested)))

variable {magnitude requested : InverseRootPolynomial.Coordinate}
  (magnitudeEq : magnitude =
    SourceMagnitude.CommonBasisRequest.Sampled.parentMagnitude
    retained inputs)
  (positive : 0 < requested) (runs :
    PreparedPhysicalRows
    sample comparisons banks magnitude requested)

include magnitudeEq positive runs

/-- The retained parent certificates pay both levels of joining terms in the
same component source-area expression consumed by the surface lower bound. -/
theorem physical_area_requested (periodStage : Nat) :
    Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area
      (List.ofFn (fun outer => (List.ofFn
        (physicalPaths
        banks outer)).flatten)).flatten -
      CommonSourceArea.CommonBasisRequest.Sampled.sourceAreaAt sample
        comparisons periodStage) ≤ requested * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2
        := open Algebra in open Rat in by
  have magnitudeNN : 0 ≤ magnitude :=
    (SourceMagnitude.CommonBasisRequest.Sampled.parentMagnitude_nonnegative
    retained inputs).trans_eq magnitudeEq.symm
  have massNN : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      InverseRootPolynomial.Coordinate)) _
      (fun row => Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  apply
    HierarchicalRequest.CommonBasisRequest.Sampled.hierarchical_area_requested
    sample comparisons periodStage
    (physicalPaths
    banks) magnitudeNN positive
  · intro outer position
    exact
      PreparedPhysicalBounds.PhysicalRunBank.PreparedRun.area_requested
      ((runs.get outer).get position)
  · intro outer position
    exact
      PreparedPhysicalBounds.PhysicalRunBank.PreparedRun.total_requested
      ((runs.get outer).get position)
      (HierarchicalRequest.CommonBasisRequest.Sampled.parentTarget_positive
      outer magnitudeNN positive).le
  · intro outer position
    have bounded :=
      PreparedPhysicalBounds.PhysicalRunBank.PreparedRun.total_bounded_requested
      ((runs.get outer).get position)
      (HierarchicalRequest.CommonBasisRequest.Sampled.parentTarget_le_one
      outer magnitude requested)
    have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      ((SourceMagnitude.CommonBasisRequest.Sampled.runMagnitude_le
        retained inputs outer position).trans_eq magnitudeEq.symm) massNN
    exact ⟨bounded.1.trans paid, bounded.2.trans paid⟩
  · intro outer position
    have bounded :=
      SourceMagnitude.CommonBasisRequest.Sampled.source_uniform_bounded
      sample comparisons outer position
    have equal := congrArg (fun value : InverseRootPolynomial.Coordinate => value *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) magnitudeEq.symm
    exact ⟨bounded.1.trans_eq equal, bounded.2.trans_eq equal⟩

end Sampled
end CommonBasisRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalComponentComparison
