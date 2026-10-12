module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentRunSchedule
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalRunBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Paths.RectangularPerimeterTraces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOccurrenceRuns
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOwnerSchedule
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Approximation.Budget.RequestedLengthBudget
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Periods.CenteredBilinearPath

public section

/-! Build the retained occurrence runs directly on its requested whole-face mesh. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence

open Purelib.Curves
open Purelib.Integration
open Purelib
open Purelib.Riemann

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterSamples

open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedHorizontalRuns
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedRunBudgets.SharedHorizontalRuns

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOccurrenceRuns

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

open Purelib.Riemann.Normalization.RectangularInverseModels

namespace RequestedOccurrenceRuns

variable (retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared)
  {index : Nat} (inputs : retained.Inputs index)
  (outer : Fin prepared.occurrences.length)
  {whole :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains differential} {previous :
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains}
  (selected : SourceCuts whole previous)
  (member : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer ∈
    whole.occurrences)
  {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains sheet} {meshTarget :
    Normalization.InverseRootPolynomial.Coordinate}
  (request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest
    (fun sheet => Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains selected.cuts sheet
      coarseDepth) fixed meshTarget)

/-- Read the very mesh used by the retained occurrence's parent assignment. -/
@[expose] def mesh :=
  (request.entries.get (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
    prepared.occurrences outer).sideOccurrence.sheet).meshes.entries.get
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).sideOccurrence.position

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence.RequestedOccurrenceRuns in
/-- Schedule parent requests using this occurrence's actual requested side capacity.
The same retained input bank owns both the source magnitude and every request. -/
@[expose] def parentSchedule (requested : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < requested)
  (minimum : Nat) :
    ParentRunSchedule
      retained inputs outer
      (SharedOccurrenceRuns.sideCapacity outer
        (mesh := mesh outer selected request)) requested minimum :=
  ParentRunSchedule.build
    retained inputs outer _ requested positive minimum

variable {stage : Nat} (traces : Paths.RectangularPerimeterTraces.PerimeterTraces (mesh outer selected request))
  (cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage)
  (banks : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterSamples.SharedPerimeter.Banks (occurrence :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer) traces
    cache)
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
  {allowance : Normalization.InverseRootPolynomial.Coordinate} (budget : Path.NoisyPathArea.LengthErrorBudget
    (Paths.RectangularDyadicPairedTrace.dyadicCount (mesh outer selected request).depth) allowance)
  (owners : OwnerRequest
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer)
    budget.tolerance) (later : owners.index ≤ stage)
  {junctionAllowance : Normalization.InverseRootPolynomial.Coordinate} (junctionBudget :
    Path.NoisyPathArea.LengthErrorBudget 1 junctionAllowance)
  (junctionOwners : OwnerRequest
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer)
    junctionBudget.tolerance)
  (junctionLater : junctionOwners.index ≤ stage)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence.RequestedOccurrenceRuns
/-- Parent location, the actual face box, side choice, fixed coordinates and
traversal all come from the retained geometry. Numerical budgets remain explicit. -/
@[expose] def build : PhysicalRunBank retained inputs
  outer coefficients stage (mesh outer selected request).depth
    (SharedOccurrenceRuns.sideCapacity outer
      (mesh := mesh outer selected request))
    (SharedOccurrenceRuns.sideArea outer traces
      cache banks coefficients)
    (max allowance junctionAllowance) (max budget.tolerance junctionBudget.tolerance) :=
  let blocks := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank.ParentBlock.forOccurrence selected member
    request
  SharedOccurrenceRuns.build retained inputs
    outer traces cache banks coefficients
    budget owners later junctionBudget junctionOwners junctionLater blocks rfl

/-- Acquire the geometric bank with shared owner budgets already paid at the
same face stage. Source and reference-depth certificates remain on `schedule`. -/
@[expose] def buildScheduled {requested : Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}
    (schedule :
      ParentRunSchedule
      retained inputs outer
      (SharedOccurrenceRuns.sideCapacity outer
        (mesh := mesh outer selected request)) requested minimum)
    {vertices : Fin
      (SharedOccurrenceRuns.sideCapacity outer
      (mesh := mesh outer selected request)) → Nat}
    (scheduled :
      SharedOwnerSchedule.CommonBasisPreparation.ParentRunSchedule.SharedOwners
      schedule (Paths.RectangularDyadicPairedTrace.dyadicCount (mesh outer selected request).depth) vertices)
    (facePaid : scheduled.faceIndex ≤ stage) :
    PhysicalRunBank retained inputs outer coefficients
      stage (mesh outer selected request).depth
      (SharedOccurrenceRuns.sideCapacity outer
        (mesh := mesh outer selected request))
      (SharedOccurrenceRuns.sideArea outer traces
        cache banks coefficients)
      (max 1 1) (max scheduled.piece.budget.tolerance scheduled.junction.budget.tolerance) :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence.RequestedOccurrenceRuns.build retained inputs
    outer selected member request traces cache banks coefficients
    scheduled.piece.budget scheduled.pieceOwner (scheduled.piece_le.trans facePaid)
    scheduled.junction.budget scheduled.junctionOwner (scheduled.junction_le.trans facePaid)

end RequestedOccurrenceRuns
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence
