module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.SynchronizedPrimitives
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

open Purelib

open Purelib.Approximation

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests

open Purelib.Riemann.Meshes.GridLiftedMesh

open Purelib.Riemann.Normalization

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.PreparedPathParentCaches

public section

/-!
# Contact bounds for retained lifted-mesh segment occurrences

Both face assignments refer to one actual covered segment and parent cache.
Their inherited owner alignment selects the correct local sheets. Shared
triangle data then inherit the computed contact threshold, with no extra
numerical matching or independently sampled-period premise.
-/

open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Paths.PreparedPathDecomposition (CoveredSegment)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests (ContactBudget)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularFace)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh (SegmentFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

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
  {start finish : Purelib.Data.Gaussian.Basic.Canonical} {segment : ClearSegment
    curve.polynomial ambient start finish}
  {owner : Owner (curve.polynomial.eval start)} {piece :
    CoveredSegment segment owner}
  {first last : SegmentFace mesh segment} {differential :
    Differential genus} {parentSheet : Fin 2}
  {domains : FaceDomainBank frames faces.regulars}

namespace Cut.PrimitiveBanks.LiftedMesh.SegmentComparison

/-- The two source occurrences use the same incoming owner, not necessarily the same local sheet numeral or the same
numerical primitive polynomial. -/
theorem
  contact_accurate
    (left : LiftedMesh.SegmentComparison first piece differential parentSheet)
    (right : LiftedMesh.SegmentComparison last piece differential parentSheet)
    (leftDomains : left.domains = domains.atRoute first.location) (rightDomains : right.domains = domains.atRoute
      last.location)
    {target : InverseRootPolynomial.Coordinate} (budget : ContactRequests.ContactBudget left.entered right.entered
      target)
    {index : Nat} (later : budget.index ≤ index) (shared : PrimitiveData.FacePrimitiveBank differential index domains) :
    Data.Gaussian.Norm.Basic.normSq (shared.edgeIncrement first.location - shared.edgeIncrement last.location)
      < target := by
  have firstCoordinates := first.location.corner_coordinates
  have lastCoordinates := last.location.corner_coordinates
  have bounded := budget.accurate later (left.sharedData shared leftDomains) (right.sharedData shared rightDomains)
    first.location.corners.start first.location.corners.finish last.location.corners.start last.location.corners.finish
    ((congrArg Prod.fst firstCoordinates).trans first.start_eq) ((congrArg Prod.snd firstCoordinates).trans
      first.finish_eq)
    ((congrArg Prod.fst lastCoordinates).trans last.start_eq) ((congrArg Prod.snd lastCoordinates).trans last.finish_eq)
  rw [left.sharedData_corners, right.sharedData_corners] at bounded
  exact bounded

/-- The actual shared triangle-edge readings for both retained segment occurrences satisfy the original contact target.
-/
theorem
  triangle_contact_accurate
    (left : LiftedMesh.SegmentComparison first piece differential parentSheet)
    (right : LiftedMesh.SegmentComparison last piece differential parentSheet)
    (leftDomains : left.domains = domains.atRoute first.location) (rightDomains : right.domains = domains.atRoute
      last.location)
    {target : InverseRootPolynomial.Coordinate} (budget : ContactRequests.ContactBudget left.entered right.entered
      target)
    {index : Nat} (later : budget.index ≤ index) {shared : PrimitiveData.FacePrimitiveBank differential index domains}
    (readings : TrianglePrimitiveReadings.TriangleReadings shared mesh) :
    Data.Gaussian.Norm.Basic.normSq (first.location.sourceEdge.increment readings.values -
      last.location.sourceEdge.increment readings.values) < target := by
  rw [readings.route_increment, readings.route_increment]
  exact left.contact_accurate right leftDomains rightDomains budget later shared

end Cut.PrimitiveBanks.LiftedMesh.SegmentComparison

set_option genInjectivity false in
/-- Generated contact geometry supplies its original common segment and cache. Neither face may independently prepare or
select another root owner. -/
structure SegmentContactRequests.SegmentContact (first last : LiftedMesh.SegmentFace mesh segment) (piece :
  PreparedPathDecomposition.CoveredSegment segment owner)
    (differential : Differentials.Basic.Differential genus) (parentSheet : Fin 2) (domains : DomainBanks.FaceDomainBank
      frames faces.regulars) where
  /-- The first actual face comparison on the shared original covered segment. -/ left : LiftedMesh.SegmentComparison
    first piece differential parentSheet
  /-- The second actual face comparison on the same retained covered segment. -/ right : LiftedMesh.SegmentComparison
    last piece differential parentSheet
  /-- The first comparison uses exactly the selected original shared face-domain entry. -/ left_domains : left.domains =
    domains.atRoute first.location
  /-- The second comparison uses exactly the selected original shared face-domain entry. -/ right_domains :
    right.domains = domains.atRoute last.location

constructive_injectivity SegmentContactRequests.SegmentContact

namespace SegmentContactRequests.SegmentContact

/-- Reuse one actual covered segment and parent cache to construct both face comparisons with their retained
incoming-owner alignments. -/
@[expose] def build (first last : LiftedMesh.SegmentFace mesh segment) (piece : PreparedPathDecomposition.CoveredSegment
  segment owner)
    (differential : Differentials.Basic.Differential genus) (parentSheet : Fin 2) (domains : DomainBanks.FaceDomainBank
      frames faces.regulars)
    (cache : PreparedClearPathModels.ParentCache piece.path differential parentSheet)
    (leftAligned : Nonempty (Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName owner)
      (OwnerTraceReadings.ownerName (vertices.owner frames first.indexed.start))))
    (rightAligned : Nonempty (Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName owner)
      (OwnerTraceReadings.ownerName (vertices.owner frames last.indexed.start)))) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentContactRequests.SegmentContact first last piece differential
      parentSheet domains :=
  ⟨SegmentComparison.build first piece differential parentSheet domains cache leftAligned,
    SegmentComparison.build last piece differential parentSheet domains cache rightAligned, rfl, rfl⟩

/-- A shared indexed start reuses the same alignment certificate on both faces, including a reversed occurrence on the
second face. -/
@[expose] def ofSameStart (first last : LiftedMesh.SegmentFace mesh segment) (sameStart : first.indexed.start =
  last.indexed.start)
    (piece : PreparedPathDecomposition.CoveredSegment segment owner) (differential : Differentials.Basic.Differential
      genus) (parentSheet : Fin 2)
    (domains : DomainBanks.FaceDomainBank frames faces.regulars) (cache : PreparedClearPathModels.ParentCache piece.path
      differential parentSheet)
    (aligned : Nonempty (Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName owner)
      (OwnerTraceReadings.ownerName (vertices.owner frames first.indexed.start)))) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentContactRequests.SegmentContact first last piece differential
      parentSheet domains :=
  build first last piece differential
    parentSheet domains cache aligned (sameStart ▸ aligned)

/-- Select the original contact threshold from both retained entered-face paths before constructing a shared numerical
bank. -/
@[expose] def budget (contact : Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentContactRequests.SegmentContact first
  last piece differential parentSheet domains)
    (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) : ContactRequests.ContactBudget
      contact.left.entered contact.right.entered target :=
  ContactBudget.build contact.left.entered contact.right.entered target positive

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentContactRequests.SegmentContact in
/-- The threshold is computed before any shared face-polynomial bank. All later banks satisfy the contact estimate at
their actual triangle values. -/
theorem accurate (contact : Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentContactRequests.SegmentContact first last
  piece differential parentSheet domains)
    {target : InverseRootPolynomial.Coordinate} (budget : ContactRequests.ContactBudget contact.left.entered
      contact.right.entered target)
    {index : Nat} (later : budget.index ≤ index) {shared : PrimitiveData.FacePrimitiveBank differential index domains}
    (readings : TrianglePrimitiveReadings.TriangleReadings shared mesh) :
    Data.Gaussian.Norm.Basic.normSq (first.location.sourceEdge.increment readings.values -
      last.location.sourceEdge.increment readings.values) < target :=
  contact.left.triangle_contact_accurate contact.right contact.left_domains contact.right_domains budget later readings

end SegmentContactRequests.SegmentContact
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
