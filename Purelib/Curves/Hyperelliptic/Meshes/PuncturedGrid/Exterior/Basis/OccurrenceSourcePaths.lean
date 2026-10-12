module
import Purelib.Data.List.Flatten
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.OfFn.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedSelection
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonSourceArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OccurrenceComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SelectedSourceArea
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonDepthRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Budget.Trace.Family
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedParentSplitSelection
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

public section

/-! Reassemble retained occurrence paths without discarding their joining polygon. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

variable {bounds : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared}
  {basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {target coefficientTarget : Normalization.InverseRootPolynomial.Coordinate} {coverFloor floor index minimum stage
    energyFloor radialDepth : Nat}
  {box : Rational.Box} {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap
    differential index box}
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}

namespace CommonBasisRequest

variable {request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisRequest retained basis
  target coefficientTarget coverFloor floor}
  {plans : request.Plans capSample polynomials minimum} {inputs : retained.Inputs index}
  {readings : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Readings retained.anchors retained.sources
    request.schedule.bank plans inputs stage}

variable {fans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest.FanPreparation request
  plans inputs readings energyFloor}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace Sampled

variable (sample : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest.Sampled fans
  coefficients radialDepth) (comparisons :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison.CommonBasisRequest.Sampled.PreparedComparisons
  sample)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest in
/-- The occurrence path is precisely the corresponding positional slice of
the global source bank; equal payloads never change the selected position. -/
theorem occurrenceSourcePath_eq_selected (outer : Fin prepared.occurrences.length) :
    sample.occurrenceSourcePath comparisons outer =
      (List.ofFn (fun position =>
        (Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedSelection.Samples.PreparedComparisons.select
          retained.anchors retained.sources request.schedule.bank
          plans inputs readings fans sample.parents comparisons
            (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.parentIndex prepared outer
            position)).weighted.values.map Prod.fst)).flatten := by
  apply congrArg List.flatten
  exact Data.List.OfFn.Basic.ofFn_congr
    (SelectedSourceArea.CommonBasisRequest.Sampled.parentPrepared_source
    sample comparisons outer)

/-- Flattening the occurrence paths recovers the complete global source path. -/
theorem occurrenceSourcePaths_flatten :
    (List.ofFn (sample.occurrenceSourcePath comparisons)).flatten =
      (List.ofFn (fun position : Fin program.cache.parents.length =>
        (Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedSelection.Samples.PreparedComparisons.select
          retained.anchors retained.sources request.schedule.bank
          plans inputs readings fans sample.parents comparisons position).weighted.values.map Prod.fst)).flatten := by
  have localRead := Data.List.OfFn.Basic.ofFn_congr (sample.occurrenceSourcePath_eq_selected comparisons)
  rw [localRead]
  have indices := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.parentIndex_all prepared (fun position
    =>
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedSelection.Samples.PreparedComparisons.select retained.anchors
      retained.sources request.schedule.bank
      plans inputs readings fans sample.parents comparisons position).weighted.values.map Prod.fst)
  have flattened := congrArg List.flatten indices
  rw [Data.List.Flatten.flatten_flatten, Data.List.OfFn.Basic.map_ofFn] at flattened
  exact flattened

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest
/-- The source-area interface consumes this very same complete path. -/
theorem sourceAreaAt_eq_occurrences (periodStage : Nat) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonSourceArea.CommonBasisRequest.Sampled.sourceAreaAt sample
      comparisons periodStage = Path.IncrementArea.pathArea
      (List.ofFn (sample.occurrenceSourcePath comparisons)).flatten :=

    (SelectedSourceArea.CommonBasisRequest.Sampled.sourceAreaAt_eq_selected
    sample comparisons periodStage).trans
    (congrArg Path.IncrementArea.pathArea (sample.occurrenceSourcePaths_flatten comparisons).symm)

/-- Internal areas and the polygon of occurrence totals both survive assembly. -/
theorem sourceAreaAt_occurrence_joining (periodStage : Nat) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonSourceArea.CommonBasisRequest.Sampled.sourceAreaAt sample
      comparisons periodStage =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn (sample.occurrenceSourceArea comparisons)) +
        Path.IncrementArea.pathArea (List.ofFn (sample.occurrenceSourceTotal comparisons)) := by
  rw [sample.sourceAreaAt_eq_occurrences comparisons periodStage, Path.IncrementArea.pathArea_flatten,
    Data.List.OfFn.Basic.map_ofFn, Data.List.OfFn.Basic.map_ofFn]
  rfl

end Sampled
end CommonBasisRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection
