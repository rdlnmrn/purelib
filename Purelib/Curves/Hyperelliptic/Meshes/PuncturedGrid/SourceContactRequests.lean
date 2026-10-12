module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
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
import Purelib.Topology.Mesh.TriangleSourceUniqueness
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentContactRequests
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

public section

/-!
# Original source contacts located on the actual lifted mesh

Finite positive-occurrence uniqueness identifies both retained face sources.
One common forward segment is used on the first face and on the reversed
second occurrence. The resulting estimate is for the original contact's
mismatch, not for an unrelated pair of polynomial increments.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SourceContactRequests

open Purelib
open Purelib.Approximation
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentContactRequests
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness
open Purelib.Polynomial.Geometry
open Purelib.Riemann.Meshes
open Purelib.Riemann.Meshes.GridLiftedMesh
open Purelib.Riemann.Normalization
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.PreparedPathParentCaches
open Purelib.Riemann.Topology
open Purelib.Topology.Mesh.TriangleSourceUniqueness
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Paths.PreparedPathDecomposition (CoveredSegment)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceContact SourceEdge)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.RootIsolation.SquareRoot.Grid (RootEdgeBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh LiftedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedFaces (EdgeLocation)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh (SegmentFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks (EdgeRoute)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentContactRequests (SegmentContact)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces bank} {mesh :
    Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}

set_option genInjectivity false in
/-- The indices refer to the contact's actual source edge and its reversal. Generated locations satisfy the same
semantic source equations. -/
structure LocatedContact (contact : SewnPrimitiveContacts.SourceContact mesh.triangulation.faces) where
  /-- The actual original mesh location of the contact's first positive source edge. -/ left : LiftedFaces.EdgeLocation
    mesh.lifts (contact.left.project mesh.triangulation.faces)
  /-- The actual original mesh location of the reversed first edge and the contact's second positive source. -/ right :
    LiftedFaces.EdgeLocation mesh.lifts (contact.left.project mesh.triangulation.faces).reverse
  /-- The located first source edge is exactly the original contact's retained first occurrence. -/ left_eq :
    left.sourceEdge = contact.left
  /-- The located second source edge is exactly the original contact's retained second occurrence. -/ right_eq :
    right.sourceEdge = contact.right

constructive_injectivity LocatedContact

namespace LocatedContact

variable {contact : Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts.SourceContact mesh.triangulation.faces}

/-- Locate both actual positive source occurrences using the original mesh and certify their identities from finite
source uniqueness. -/
@[expose] def build (mesh : GridLiftedMesh.LiftedMesh vertices edges faces) (contact :
  SewnPrimitiveContacts.SourceContact mesh.triangulation.faces)
    (leftPositive : SourceEdge.Positive contact.left mesh.triangulation.faces)
    (rightPositive : SourceEdge.Positive contact.right mesh.triangulation.faces) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.SourceContactRequests.LocatedContact contact :=
  let left := mesh.locateEdge _ (SourceEdge.member leftPositive)
  let right := mesh.locateEdge _ (contact.opposite ▸ SourceEdge.member rightPositive)
  ⟨left, right, LiftedMesh.source_eq_of_project_eq mesh
      (LiftedFaces.EdgeLocation.sourceEdge_positive left) leftPositive left.sourceEdge_project,
    LiftedMesh.source_eq_of_project_eq mesh
      (LiftedFaces.EdgeLocation.sourceEdge_positive right) rightPositive (right.sourceEdge_project.trans
        contact.opposite.symm)⟩

variable {ambient : Purelib.Geometry.Rational.Box}
  {segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment curve.polynomial ambient
    (vertices.coordinate (contact.left.project mesh.triangulation.faces).start)
    (vertices.coordinate (contact.left.project mesh.triangulation.faces).finish)}

/-- Place the supplied common forward segment on the original first positive source occurrence. -/
@[expose] def firstPlacement (located : Curves.Hyperelliptic.Meshes.PuncturedGrid.SourceContactRequests.LocatedContact
  contact) (segment : ClearPath.ClearSegment curve.polynomial ambient
    (vertices.coordinate (contact.left.project mesh.triangulation.faces).start)
    (vertices.coordinate (contact.left.project mesh.triangulation.faces).finish)) : LiftedMesh.SegmentFace mesh segment
      :=
  ⟨_, .forward located.left, rfl, rfl⟩

/-- Place the same supplied forward segment along the reverse of the original second positive source occurrence. -/
@[expose] def lastPlacement (located : Curves.Hyperelliptic.Meshes.PuncturedGrid.SourceContactRequests.LocatedContact
  contact) (segment : ClearPath.ClearSegment curve.polynomial ambient
    (vertices.coordinate (contact.left.project mesh.triangulation.faces).start)
    (vertices.coordinate (contact.left.project mesh.triangulation.faces).finish)) : LiftedMesh.SegmentFace mesh segment
      :=
  ⟨_, .backward located.right, rfl, rfl⟩

/-- Both face entries share the actual prepared segment and its incoming root. The second entry follows the reverse of
its positive source edge. -/
@[expose] def prepare (located : Curves.Hyperelliptic.Meshes.PuncturedGrid.SourceContactRequests.LocatedContact contact)
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval (vertices.coordinate (contact.left.project
      mesh.triangulation.faces).start))}
    (piece : PreparedPathDecomposition.CoveredSegment segment owner) (differential : Differentials.Basic.Differential
      genus) (parentSheet : Fin 2)
    (domains : DomainBanks.FaceDomainBank frames faces.regulars) (cache : PreparedClearPathModels.ParentCache piece.path
      differential parentSheet)
    (aligned : Nonempty (Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName owner)
      (OwnerTraceReadings.ownerName (vertices.owner frames (contact.left.project mesh.triangulation.faces).start)))) :
    SegmentContactRequests.SegmentContact (located.firstPlacement segment) (located.lastPlacement segment) piece
      differential parentSheet domains :=
  SegmentContact.ofSameStart (mesh := mesh) (located.firstPlacement segment) (located.lastPlacement segment)
    rfl piece differential parentSheet domains cache aligned

/-- The computed threshold controls the original sewing contact's mismatch at every later shared index.

All location and orientation equalities are constructed from the retained mesh, not supplied as analytic hypotheses. -/
theorem mismatch_accurate (located : Curves.Hyperelliptic.Meshes.PuncturedGrid.SourceContactRequests.LocatedContact
  contact)
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval (vertices.coordinate (contact.left.project
      mesh.triangulation.faces).start))}
    {piece : PreparedPathDecomposition.CoveredSegment segment owner} {differential : Differentials.Basic.Differential
      genus} {parentSheet : Fin 2}
    {domains : DomainBanks.FaceDomainBank frames faces.regulars}
    (prepared : SegmentContactRequests.SegmentContact (located.firstPlacement segment) (located.lastPlacement segment)
      piece differential parentSheet domains)
    {target : InverseRootPolynomial.Coordinate} (budget : ContactRequests.ContactBudget prepared.left.entered
      prepared.right.entered target)
    {index : Nat} (later : budget.index ≤ index) {shared : PrimitiveData.FacePrimitiveBank differential index domains}
    (readings : TrianglePrimitiveReadings.TriangleReadings shared mesh) : contact.mismatch readings.values < target :=
      by
  have bounded := prepared.accurate budget later readings
  change Data.Gaussian.Norm.Basic.normSq
    (located.left.sourceEdge.increment readings.values - (EdgeRoute.backward located.right).sourceEdge.increment
      readings.values) < target at bounded
  have reversed : (EdgeRoute.backward located.right).sourceEdge.increment readings.values =
    -located.right.sourceEdge.increment readings.values := by
    unfold EdgeRoute.sourceEdge SourceEdge.increment
    ring1
  rw [reversed, located.left_eq, located.right_eq] at bounded
  have scalar : contact.left.increment readings.values - -contact.right.increment readings.values =
      contact.left.increment readings.values + contact.right.increment readings.values := by ring1
  rewrite [scalar] at bounded
  exact bounded

end LocatedContact
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SourceContactRequests

end
