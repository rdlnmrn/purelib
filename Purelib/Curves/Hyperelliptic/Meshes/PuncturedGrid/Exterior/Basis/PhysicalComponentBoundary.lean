module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.OfFn.Basic
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
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OccurrenceComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalRunEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceMagnitude
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonSourceArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalComponentComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OccurrenceSourcePaths
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
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

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalComponentComparison.CommonBasisRequest

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Retain the complete signed-side boundary and its occurrence joining polygon. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalComponentBoundary

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

open Purelib.Data.Rat.Fraction.Compatibility

variable (sample : Connection.CommonBasisRequest.Sampled fans
  coefficients radialDepth) (comparisons :
  CommonPreparedComparison.CommonBasisRequest.Sampled.PreparedComparisons
  sample)
  {faceIndex : Nat} (banks : PhysicalRunEntries
    retained inputs coefficients faceIndex)

/-- The inner parent joins are already in each certified side area. The outer
joining polygon remains explicit; its closure would not justify discarding it. -/
theorem physical_boundary : Path.PairedIncrementArea.area
    (List.ofFn (fun outer => (List.ofFn
      (Sampled.physicalPaths
      banks outer)).flatten)).flatten =
    Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn (fun outer => if
      (ParentIndices.occurrenceAt prepared.occurrences
      outer).sourceForward
      then (banks.get outer).sideArea else -(banks.get outer).sideArea)) +
    Path.PairedIncrementArea.area (List.ofFn (fun outer => Path.PairedIncrementArea.total
      (List.ofFn
        (Sampled.physicalPaths
        banks outer)).flatten)) := by
  rw [Path.PairedAreaBlocks.area_flatten, List.OfFn.Basic.map_ofFn, List.OfFn.Basic.map_ofFn]
  apply congrArg₂ (fun first last : InverseRootPolynomial.Gaussian => first + last)
  · apply congrArg Gaussian.Norm.Sum.Basic.gaussianSum
    exact List.OfFn.Basic.ofFn_congr (fun outer => (banks.get outer).bank.area_readback)
  · rfl

variable {magnitude requested : InverseRootPolynomial.Coordinate}
  (magnitudeEq : magnitude =
    SourceMagnitude.CommonBasisRequest.Sampled.parentMagnitude
    retained inputs)
  (positive : 0 < requested) (runs :
    Sampled.PreparedPhysicalRows
    sample comparisons banks magnitude requested)

include magnitudeEq positive runs

/-- The component estimate pays the entire geometric boundary expression. -/
theorem physical_boundary_requested (periodStage : Nat) :
    Gaussian.Norm.Basic.normSq ((Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn (fun outer => if
      (ParentIndices.occurrenceAt prepared.occurrences
      outer).sourceForward
      then (banks.get outer).sideArea else -(banks.get outer).sideArea)) +
    Path.PairedIncrementArea.area (List.ofFn (fun outer => Path.PairedIncrementArea.total
      (List.ofFn
        (Sampled.physicalPaths
        banks outer)).flatten))) -
      CommonSourceArea.CommonBasisRequest.Sampled.sourceAreaAt sample
        comparisons periodStage) ≤ requested * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2
        := by
  have bound :=
    Sampled.physical_area_requested
    sample comparisons banks magnitudeEq positive runs periodStage
  rw
    [physical_boundary
    banks] at bound
  exact bound

/-- Both sides retain their own occurrence joining polygons. This is the form
needed when matching the physical boundary with the prepared source trace. -/
theorem physical_source_joining_requested (periodStage : Nat) :
    Gaussian.Norm.Basic.normSq ((Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn (fun outer => if
      (ParentIndices.occurrenceAt prepared.occurrences
      outer).sourceForward
      then (banks.get outer).sideArea else -(banks.get outer).sideArea)) +
    Path.PairedIncrementArea.area (List.ofFn (fun outer => Path.PairedIncrementArea.total
      (List.ofFn
        (Sampled.physicalPaths
        banks outer)).flatten))) -
    (Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn
      (Connection.CommonBasisRequest.Sampled.occurrenceSourceArea
      sample comparisons)) +
      Path.IncrementArea.pathArea (List.ofFn
        (Connection.CommonBasisRequest.Sampled.occurrenceSourceTotal
        sample comparisons)))) ≤
      requested * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  have bound :=
    physical_boundary_requested
    sample comparisons banks magnitudeEq positive runs periodStage
  rw
    [Connection.CommonBasisRequest.Sampled.sourceAreaAt_occurrence_joining
    sample comparisons periodStage] at bound
  exact bound

end Sampled
end CommonBasisRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalComponentBoundary
