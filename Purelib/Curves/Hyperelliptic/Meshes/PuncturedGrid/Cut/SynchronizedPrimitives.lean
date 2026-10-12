module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBudgets
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SharedPrimitiveRequests
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.RequestedFragments
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBudgets

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData

open Purelib.Polynomial.Geometry

open Purelib.Riemann.Meshes.GridLiftedMesh

open Purelib.Riemann.Normalization

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.PreparedPathDecomposition

open Purelib.Riemann.Topology

public section

/-!
# Shared numerical primitives for every occurrence of a cut-period path

First select all scalar budgets, then one common polynomial index, and only
then construct the memoized face/sheet numerical bank. Each retained segment
uses that bank's exact primitive, anchor and offset data. This is stronger
than independently accurate polynomials at the same index. Local mesh-cell
ownership and the global primitive-jump identity remain separate obligations.
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
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh (SegmentFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomains FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives FacePrimitives
  FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments (AssignedSegments)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh (SegmentComparison)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments (Comparisons)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons
  (UsesDomains)
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

/-- Read the retained face position and sheet; equality transport changes only the dependent indices. No models or
numerical witnesses are acquired. -/
@[expose] def
  sharedData
  {start finish : Data.Gaussian.Basic.Canonical} {segment : ClearPath.ClearSegment curve.polynomial ambient start
  finish}
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {placement : LiftedMesh.SegmentFace mesh
      segment} {piece : PreparedPathDecomposition.CoveredSegment segment owner}
    {differential : Differentials.Basic.Differential genus} {parentSheet : Fin 2} (compared :
      LiftedMesh.SegmentComparison placement piece differential parentSheet)
    {domains : DomainBanks.FaceDomainBank frames faces.regulars} {index : Nat} (shared : PrimitiveData.FacePrimitiveBank
      differential index domains)
    (aligned : compared.domains = domains.atRoute placement.location) : PrimitiveData.DomainPrimitives
      compared.entered.domain differential index :=
  DomainPrimitives.castDomain compared.domain_eq.symm
    (((shared.atRoute placement.location).castDomains aligned.symm).atSheet compared.entered.entry.sheet)

/-- Transporting the retained shared numerical cache preserves the exact corner values at the assigned face and sheet.
-/
theorem
  sharedData_corners
  {start finish : Data.Gaussian.Basic.Canonical} {segment : ClearPath.ClearSegment curve.polynomial ambient start
  finish}
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {placement : LiftedMesh.SegmentFace mesh
      segment} {piece : PreparedPathDecomposition.CoveredSegment segment owner}
    {differential : Differentials.Basic.Differential genus} {parentSheet : Fin 2} (compared :
      LiftedMesh.SegmentComparison placement piece differential parentSheet)
    {domains : DomainBanks.FaceDomainBank frames faces.regulars} {index : Nat} (shared : PrimitiveData.FacePrimitiveBank
      differential index domains)
    (aligned : compared.domains = domains.atRoute placement.location) :
    (compared.sharedData shared aligned).corners.values = ((shared.atRoute placement.location).atSheet
      placement.location.sheet).corners.values := by
  rw [sharedData,
    DomainPrimitives.castDomain_corners, FacePrimitives.castDomains_corners, compared.sheet_eq]

end PrimitiveBanks.LiftedMesh.SegmentComparison

namespace SynchronizedPrimitives.AssignedSegments.Comparisons

/-- Every actual local request uses the exact primitive, anchor and offset caches selected from the one retained
numerical bank. -/
@[expose] def UsesPrimitives (differential : Differentials.Basic.Differential genus) (parentSheet : Fin 2) {target :
  InverseRootPolynomial.Coordinate}
    {domains : DomainBanks.FaceDomainBank frames faces.regulars} {index : Nat} (shared : PrimitiveData.FacePrimitiveBank
      differential index domains) :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient
      start finish}
      {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
        PreparedClearPathModels.PreparedPath path owner} {pieces : PreparedPath.CoveredSegments prepared}
      (assigned : PreparedFaceSegments.AssignedSegments mesh pieces) (compared : AssignedSegments.Comparisons
        differential parentSheet assigned)
      (_aligned : Comparisons.UsesDomains domains differential parentSheet assigned compared),
      PrimitiveRequests.Requests differential parentSheet target assigned compared → Prop
  | _, _, _, _, _, _, .nil _ _, _, _, _ => True
  | _, _, _, _, _, _, .cons _ remaining, compared, aligned, requested =>
      compared.1.entered.UsesData requested.1 (compared.1.sharedData shared aligned.1) ∧

          UsesPrimitives
          differential parentSheet shared remaining compared.2 aligned.2 requested.2

/-- Acquire each actual local request from its retained scalar budget and supplied shared numerical cache at a
sufficient common index. -/
@[expose] def acquireShared (differential : Differentials.Basic.Differential genus) (parentSheet : Fin 2) {target :
  InverseRootPolynomial.Coordinate}
    {domains : DomainBanks.FaceDomainBank frames faces.regulars} {index : Nat} (shared : PrimitiveData.FacePrimitiveBank
      differential index domains) :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient
      start finish}
      {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
        PreparedClearPathModels.PreparedPath path owner} {pieces : PreparedPath.CoveredSegments prepared}
      (assigned : PreparedFaceSegments.AssignedSegments mesh pieces) (compared : AssignedSegments.Comparisons
        differential parentSheet assigned)
      (_aligned : Comparisons.UsesDomains domains differential parentSheet assigned compared)
      (budgets : PrimitiveBudgets.Budgets differential parentSheet target assigned compared),
      Budgets.IndicesBelow differential parentSheet index assigned compared budgets → PrimitiveRequests.Requests
        differential parentSheet target assigned compared
  | _, _, _, _, _, _, .nil _ _, _, _, _, _ => ⟨⟩
  | _, _, _, _, _, _, .cons _ remaining, compared, aligned, budgets, later =>
      ⟨compared.1.entered.requestShared budgets.1 index later.1 (compared.1.sharedData shared aligned.1),

          acquireShared
          differential parentSheet shared remaining compared.2 aligned.2 budgets.2 later.2⟩

/-- Every acquired local request retains the exact shared numerical cache selected by its original face and sheet. -/
theorem acquireShared_usesPrimitives (differential : Differentials.Basic.Differential genus) (parentSheet : Fin 2)
  {target : InverseRootPolynomial.Coordinate}
    {domains : DomainBanks.FaceDomainBank frames faces.regulars} {index : Nat} (shared : PrimitiveData.FacePrimitiveBank
      differential index domains) :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient
      start finish}
      {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
        PreparedClearPathModels.PreparedPath path owner} {pieces : PreparedPath.CoveredSegments prepared}
      (assigned : PreparedFaceSegments.AssignedSegments mesh pieces) (compared : AssignedSegments.Comparisons
        differential parentSheet assigned)
      (aligned : Comparisons.UsesDomains domains differential parentSheet assigned compared)
      (budgets : PrimitiveBudgets.Budgets differential parentSheet target assigned compared)
      (later : Budgets.IndicesBelow differential parentSheet index assigned compared budgets),
      UsesPrimitives
        differential parentSheet shared assigned compared aligned
        (acquireShared
          differential parentSheet shared assigned compared aligned budgets later)
  | _, _, _, _, _, _, .nil _ _, _, _, _, _ => trivial
  | _, _, _, _, _, _, .cons _ remaining, compared, aligned, budgets, later =>
      ⟨compared.1.entered.requestShared_usesData budgets.1 index later.1 (compared.1.sharedData shared aligned.1),

          acquireShared_usesPrimitives
          differential parentSheet shared remaining compared.2 aligned.2 budgets.2 later.2⟩

set_option genInjectivity false in
/-- Every actual local result retains exact readback to the one shared numerical bank. Generated scalar budgets and
primitive caches may satisfy the same contracts without reproducing canonical searches or polynomial builds. -/
structure Synchronized (domains : DomainBanks.FaceDomainBank frames faces.regulars) (differential :
  Differentials.Basic.Differential genus) (parentSheet : Fin 2)
    {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start
      finish}
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
      PreparedClearPathModels.PreparedPath path owner} {pieces : PreparedPath.CoveredSegments prepared}
    (assigned : PreparedFaceSegments.AssignedSegments mesh pieces) (compared : AssignedSegments.Comparisons differential
      parentSheet assigned)
    (aligned : Comparisons.UsesDomains domains differential parentSheet assigned compared) (target :
      InverseRootPolynomial.Coordinate) where
  /-- The original ordered scalar accuracy budgets for every actual assigned segment. -/ budgets :
    PrimitiveBudgets.Budgets differential parentSheet target assigned compared
  /-- The retained common polynomial index used by the shared numerical bank. -/ index : Nat
  /-- The common index is sufficient for every original retained scalar budget. -/ indicesBelow : Budgets.IndicesBelow
    differential parentSheet index assigned compared budgets
  /-- The exact retained face-and-sheet numerical cache at this common index. -/ numerics :
    PrimitiveData.FacePrimitiveBank differential index domains
  /-- The actual local requests for the original assigned segment comparison spine. -/ requested :
    PrimitiveRequests.Requests differential parentSheet target assigned compared
  /-- Every local request uses exactly its selected primitive, anchor and offset entries in the retained shared bank. -/
    usesPrimitives :
    UsesPrimitives
    differential parentSheet numerics assigned compared aligned requested

constructive_injectivity Synchronized

namespace Synchronized

/-- Reuse an already selected numerical bank at any sufficient index. Only the actual per-segment requests are acquired
here. -/
@[expose] def ofShared {domains : DomainBanks.FaceDomainBank frames faces.regulars} (differential :
  Differentials.Basic.Differential genus) (parentSheet : Fin 2)
    {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start
      finish}
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
      PreparedClearPathModels.PreparedPath path owner} {pieces : PreparedPath.CoveredSegments prepared}
    (assigned : PreparedFaceSegments.AssignedSegments mesh pieces) (compared : AssignedSegments.Comparisons differential
      parentSheet assigned)
    (aligned : Comparisons.UsesDomains domains differential parentSheet assigned compared) {target :
      InverseRootPolynomial.Coordinate}
    (budgets : PrimitiveBudgets.Budgets differential parentSheet target assigned compared) {index : Nat}
    (later : Budgets.IndicesBelow differential parentSheet index assigned compared budgets)
    (numerics : PrimitiveData.FacePrimitiveBank differential index domains) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.SynchronizedPrimitives.AssignedSegments.Comparisons.Synchronized
      domains differential parentSheet assigned compared aligned target :=
  let requested :=
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.SynchronizedPrimitives.AssignedSegments.Comparisons.acquireShared
    differential parentSheet numerics assigned compared aligned budgets later
  ⟨budgets, index, later, numerics, requested,

      acquireShared_usesPrimitives
      differential parentSheet numerics assigned compared aligned budgets later⟩

end Synchronized
end SynchronizedPrimitives.AssignedSegments.Comparisons
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut
