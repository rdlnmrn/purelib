module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.RequestedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedPathDecomposition
public import Purelib.Riemann.Readings.PreparedPrimitiveRequestBatches
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.SynchronizedPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SharedCornerRequests
import Purelib.Approximation.Budget.PreparedPrimitiveBatchBudget
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SharedPrimitiveRequests
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
import Purelib.Riemann.Readings.PreparedPrimitiveRequestWeakening
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.UniformPreparedRequests
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.SynchronizedPrimitives.AssignedSegments

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Polynomial.Geometry

open Purelib.Riemann.Meshes.GridLiftedMesh

open Purelib.Riemann.Normalization

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.PreparedPathDecomposition

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.PreparedPrimitiveRequestBatches

open Purelib.Riemann.Topology

@[expose] public section

/-!
# Fixed face-corner increments for whole cut-period requests

The comparison values now depend only on the retained oriented face/sheet
occurrences and their one shared four-value cache. Mesh ownership errors are
paid inside each finite batch part, along with its original fragment error.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open _root_.Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath)
open Purelib.Riemann.Paths.PreparedPathDecomposition (CoveredSegment)
open Purelib.Riemann.Paths.PreparedPathDecomposition.PreparedPath (CoveredSegments)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Readings.PreparedPrimitiveRequestBatches (RequestPart)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularFace)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh (SegmentFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments (AssignedSegments)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh (SegmentComparison)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments (Comparisons)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons
  (UsesDomains)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.SynchronizedPrimitives.AssignedSegments.Comparisons
  (UsesPrimitives)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveRequests (Requests)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBudgets (Budgets)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : PuncturedFaces bank} {mesh :
    LiftedMesh vertices edges faces} {ambient :
    Purelib.Geometry.Rational.Box}

namespace PrimitiveBanks.LiftedMesh.SegmentComparison

/-- The exact shared face-corner increment satisfies its retained original segment primitive-sum request. -/
theorem
  corner_accurate
  {start finish : Data.Gaussian.Basic.Canonical} {segment : ClearPath.ClearSegment curve.polynomial ambient start
  finish}
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {placement : LiftedMesh.SegmentFace mesh
      segment} {piece : PreparedPathDecomposition.CoveredSegment segment owner}
    {differential : Differentials.Basic.Differential genus} {parentSheet : Fin 2} (compared :
      LiftedMesh.SegmentComparison placement piece differential parentSheet)
    {domains : DomainBanks.FaceDomainBank frames faces.regulars} {index : Nat} (shared : PrimitiveData.FacePrimitiveBank
      differential index domains)
    (aligned : compared.domains = domains.atRoute placement.location) {target : InverseRootPolynomial.Coordinate}
    (request : Face.RequestedFragments compared.entered.mesh compared.entered.bounds
      compared.entered.globalBounds genus target)
    (uses : compared.entered.UsesData request (compared.sharedData shared aligned)) :
    Data.Gaussian.Norm.Basic.normSq (shared.edgeIncrement placement.location - request.request.primitiveSum) <
      target := by
  have coordinates := placement.location.corner_coordinates
  have bound := SharedCornerRequests.corner_accurate
    compared.entered request (compared.sharedData shared aligned) uses
    placement.location.corners.start placement.location.corners.finish
    ((congrArg Prod.fst coordinates).trans placement.start_eq) ((congrArg Prod.snd coordinates).trans
      placement.finish_eq)
  rw [compared.sharedData_corners] at bound
  exact bound

end PrimitiveBanks.LiftedMesh.SegmentComparison

namespace CornerRequests

namespace AssignedSegments

/-- The same finite face-corner assignment can be consumed by sewing. The specification contains no segment-local mesh
readings or comparison cache. -/
def cornerIncrements {domains : DomainBanks.FaceDomainBank frames faces.regulars} {differential :
  Differentials.Basic.Differential genus} {index : Nat}
    (shared : PrimitiveData.FacePrimitiveBank differential index domains) :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient
      start finish}
      {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
        PreparedClearPathModels.PreparedPath path owner} {pieces : PreparedPath.CoveredSegments prepared},
      PreparedFaceSegments.AssignedSegments mesh pieces → List Data.Gaussian.Basic.Canonical
  | _, _, _, _, _, _, .nil _ _ => []
  | _, _, _, _, _, _, .cons placement remaining => shared.edgeIncrement placement.location ::
    cornerIncrements shared
    remaining

end AssignedSegments

section Comparisons.CornerRequests

/-- Build every actual batch part from the same retained face-corner cache and original prepared parent request. -/
def parts (differential : Differentials.Basic.Differential genus) (parentSheet : Fin 2)
    {domains : DomainBanks.FaceDomainBank frames faces.regulars} {index : Nat} (shared : PrimitiveData.FacePrimitiveBank
      differential index domains)
    {target localTarget coefficientTarget errorBound : InverseRootPolynomial.Coordinate}
    (localLe : target / 4 ≤ localTarget) (coefficientLe : target / 4 ≤ coefficientTarget) (errorLe : target ≤
      errorBound) :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient
      start finish}
      {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
        PreparedClearPathModels.PreparedPath path owner} {pieces : PreparedPath.CoveredSegments prepared}
      (assigned : PreparedFaceSegments.AssignedSegments mesh pieces) (compared : AssignedSegments.Comparisons
        differential parentSheet assigned)
      (aligned : Comparisons.UsesDomains domains differential parentSheet assigned compared)
      (requested : PrimitiveRequests.Requests differential parentSheet target assigned compared),
      Comparisons.UsesPrimitives differential parentSheet shared assigned compared aligned requested →
        List (PreparedPrimitiveRequestBatches.RequestPart curve differential genus localTarget coefficientTarget
          errorBound)
  | _, _, _, _, _, _, .nil _ _, _, _, _, _ => []
  | _, _, _, _, _, _, .cons placement remaining, compared, aligned, requested, uses =>
      { parents := compared.1.entered.cache.parents
        target := target / 4
        request := requested.1.request
        value := shared.edgeIncrement placement.location
        local_le := requested.1.request.localTarget_le.trans localLe
        coefficient_lt := requested.1.request.coefficient_accurate.trans_le
          (requested.1.request.coefficientTarget_le.trans coefficientLe)
        accurate :=
          (Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.corner_accurate
          compared.1 shared aligned.1 requested.1 uses.1).le.trans errorLe } ::

          parts
          differential parentSheet shared localLe coefficientLe errorLe remaining compared.2 aligned.2 requested.2
          uses.2

/-- The corner-valued batch retains exactly the original ordered parent list of the assigned comparisons. -/
theorem parts_parents (differential : Differentials.Basic.Differential genus) (parentSheet : Fin 2)
    {domains : DomainBanks.FaceDomainBank frames faces.regulars} {index : Nat} (shared : PrimitiveData.FacePrimitiveBank
      differential index domains)
    {target localTarget coefficientTarget errorBound : InverseRootPolynomial.Coordinate}
    (localLe : target / 4 ≤ localTarget) (coefficientLe : target / 4 ≤ coefficientTarget) (errorLe : target ≤
      errorBound) :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient
      start finish}
      {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
        PreparedClearPathModels.PreparedPath path owner} {pieces : PreparedPath.CoveredSegments prepared}
      (assigned : PreparedFaceSegments.AssignedSegments mesh pieces) (compared : AssignedSegments.Comparisons
        differential parentSheet assigned)
      (aligned : Comparisons.UsesDomains domains differential parentSheet assigned compared)
      (requested : PrimitiveRequests.Requests differential parentSheet target assigned compared)
      (uses : Comparisons.UsesPrimitives differential parentSheet shared assigned compared aligned requested),
      RequestBatch.parents
        (parts
          differential parentSheet shared localLe coefficientLe errorLe assigned compared aligned requested uses) =
          Comparisons.parents differential parentSheet assigned compared
  | _, _, _, _, _, _, .nil _ _, _, _, _, _ => rfl
  | _, _, _, _, _, _, .cons _ remaining, compared, aligned, requested, uses =>
      congrArg (List.append _)
        (parts_parents
        differential parentSheet shared localLe coefficientLe errorLe
        remaining compared.2 aligned.2 requested.2 uses.2)

/-- The batch contains exactly one retained part for each actual covered segment. -/
theorem parts_length (differential : Differentials.Basic.Differential genus) (parentSheet : Fin 2)
    {domains : DomainBanks.FaceDomainBank frames faces.regulars} {index : Nat} (shared : PrimitiveData.FacePrimitiveBank
      differential index domains)
    {target localTarget coefficientTarget errorBound : InverseRootPolynomial.Coordinate}
    (localLe : target / 4 ≤ localTarget) (coefficientLe : target / 4 ≤ coefficientTarget) (errorLe : target ≤
      errorBound) :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient
      start finish}
      {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
        PreparedClearPathModels.PreparedPath path owner} {pieces : PreparedPath.CoveredSegments prepared}
      (assigned : PreparedFaceSegments.AssignedSegments mesh pieces) (compared : AssignedSegments.Comparisons
        differential parentSheet assigned)
      (aligned : Comparisons.UsesDomains domains differential parentSheet assigned compared)
      (requested : PrimitiveRequests.Requests differential parentSheet target assigned compared)
      (uses : Comparisons.UsesPrimitives differential parentSheet shared assigned compared aligned requested),
      (parts
        differential parentSheet shared localLe coefficientLe errorLe assigned compared aligned requested uses).length =
        pieces.count
  | _, _, _, _, _, _, .nil _ _, _, _, _, _ => rfl
  | _, _, _, _, _, _, .cons _ remaining, compared, aligned, requested, uses =>
      (congrArg Nat.succ
        (parts_length
        differential parentSheet shared localLe coefficientLe errorLe
        remaining compared.2 aligned.2 requested.2 uses.2)).trans (Nat.one_add _).symm

/-- The batch values are exactly the original assigned segments' shared face-corner increments. -/
theorem parts_values (differential : Differentials.Basic.Differential genus) (parentSheet : Fin 2)
    {domains : DomainBanks.FaceDomainBank frames faces.regulars} {index : Nat} (shared : PrimitiveData.FacePrimitiveBank
      differential index domains)
    {target localTarget coefficientTarget errorBound : InverseRootPolynomial.Coordinate}
    (localLe : target / 4 ≤ localTarget) (coefficientLe : target / 4 ≤ coefficientTarget) (errorLe : target ≤
      errorBound) :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient
      start finish}
      {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
        PreparedClearPathModels.PreparedPath path owner} {pieces : PreparedPath.CoveredSegments prepared}
      (assigned : PreparedFaceSegments.AssignedSegments mesh pieces) (compared : AssignedSegments.Comparisons
        differential parentSheet assigned)
      (aligned : Comparisons.UsesDomains domains differential parentSheet assigned compared)
      (requested : PrimitiveRequests.Requests differential parentSheet target assigned compared)
      (uses : Comparisons.UsesPrimitives differential parentSheet shared assigned compared aligned requested),
      RequestBatch.values
        (parts
          differential parentSheet shared localLe coefficientLe errorLe assigned compared aligned requested uses) =
          Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CornerRequests.AssignedSegments.cornerIncrements shared assigned
  | _, _, _, _, _, _, .nil _ _, _, _, _, _ => rfl
  | _, _, _, _, _, _, .cons _ remaining, compared, aligned, requested, uses =>
      congrArg (List.cons _)
        (parts_values
        differential parentSheet shared localLe coefficientLe errorLe
        remaining compared.2 aligned.2 requested.2 uses.2)

end Comparisons.CornerRequests
end CornerRequests
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut
