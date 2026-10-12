module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentSourceStages
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentRunSchedule
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceMagnitudeStages
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunRequestSourceStages
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HierarchicalRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.QuerySchedule
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceMagnitude
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches

/-! Reuse computed parent requests at a certified later numerical source stage. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentRunSourceStages

open Purelib.Curves

open Purelib

open Purelib.Riemann

public section

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

namespace CommonBasisPreparation

open Purelib.Data.Rat.Fraction.Compatibility

namespace ParentRunSchedule
variable {retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared}
  {index laterIndex : Nat} {inputs : retained.Inputs index}
  {outer : Fin prepared.occurrences.length} {capacity minimum : Nat} {requested :
    Normalization.InverseRootPolynomial.Coordinate}
  (schedule :
    ParentRunSchedule
    retained inputs outer capacity requested minimum) (laterInputs : retained.Inputs laterIndex)

/-- Transport the retained parent requests to equal source data at a new numerical input stage.

The dependent vector keeps each original computed request; only its source equality witness changes. -/
@[expose] def requestsAtInputs :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentRunSchedule.CommonBasisPreparation.ParentRequests retained
  laterInputs outer capacity schedule.magnitude requested minimum :=
  Data.Vector.DependentVector.ofFn (fun position =>
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns.RunRequest.castSources
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentSourceStages.parentInput_sources_eq retained inputs
      laterInputs outer position) (schedule.requests.get position))

/-- Transporting retained requests to new input data preserves each source-stage threshold. -/
theorem requestsAtInputs_sourceMinimum
    (position : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length) :
    ((requestsAtInputs schedule laterInputs).get position).blocks.queries.sourceMinimum =
      (schedule.requests.get position).blocks.queries.sourceMinimum := by
  dsimp only [requestsAtInputs]
  rw [Data.Vector.DependentVector.ofFn_get]
  exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns.RunRequest.castSources_sourceMinimum _ _

/-- Transporting retained requests to new input data preserves each refinement depth. -/
theorem requestsAtInputs_depth
    (position : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length) :
    ((requestsAtInputs schedule laterInputs).get position).refinement.depth =
      (schedule.requests.get position).refinement.depth := by
  dsimp only [requestsAtInputs]
  rw [Data.Vector.DependentVector.ofFn_get]
  exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns.RunRequest.castSources_depth _ _

/-- Transport a retained parent schedule to a certified later input stage.

The computed requests and source magnitude are reused. Equal pointwise request
thresholds preserve their maximum, so the later stage pays the same bounds and
keeps the original refinement depth. -/
@[expose] def atInputs (later : schedule.sourceIndex ≤ laterIndex) :
    ParentRunSchedule
      retained laterInputs outer capacity requested minimum := by
  let requests := requestsAtInputs schedule laterInputs
  have sourceRead := Data.Vector.DependentVector.maximum_eq requests schedule.requests
    (fun _ request => request.blocks.queries.sourceMinimum) (fun _ request => request.blocks.queries.sourceMinimum)
    (requestsAtInputs_sourceMinimum schedule laterInputs)
  have depthRead := Data.Vector.DependentVector.maximum_eq requests schedule.requests
    (fun _ request => request.refinement.depth) (fun _ request => request.refinement.depth)
    (requestsAtInputs_depth schedule laterInputs)
  have sourceBound : requests.maximum (fun _ request => request.blocks.queries.sourceMinimum) ≤ laterIndex :=
    sourceRead.trans_le (((Data.Nat.Order.le_max_right ..).trans_eq schedule.source_eq.symm).trans later)
  exact
    { magnitude := schedule.magnitude
      magnitude_eq := schedule.magnitude_eq.trans
        (SourceMagnitudeStages.CommonBasisRequest.Sampled.parentMagnitude_eq
        retained inputs laterInputs)
      magnitude_nonnegative := schedule.magnitude_nonnegative
      requests := requests
      sourceIndex := laterIndex
      source_eq := (Nat.le_antisymm (Data.Nat.Order.max_le (Nat.le_refl _) sourceBound)
        (Data.Nat.Order.le_max_left _ _)).symm
      depth := schedule.depth
      depth_eq := schedule.depth_eq.trans (congrArg (Nat.max minimum) depthRead.symm) }

/-- The transported schedule records the supplied later numerical input stage. -/
theorem atInputs_sourceIndex (later : schedule.sourceIndex ≤ laterIndex) :
    (atInputs schedule laterInputs later).sourceIndex = laterIndex := rfl

/-- Advancing a retained schedule to later input data preserves its refinement depth. -/
theorem atInputs_depth (later : schedule.sourceIndex ≤ laterIndex) :
    (atInputs schedule laterInputs later).depth = schedule.depth := rfl

/-- Advancing a retained schedule to later input data preserves its source magnitude. -/
theorem atInputs_magnitude (later : schedule.sourceIndex ≤ laterIndex) :
    (atInputs schedule laterInputs later).magnitude = schedule.magnitude := rfl

end ParentRunSchedule
end CommonBasisPreparation
end

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentRunSourceStages
