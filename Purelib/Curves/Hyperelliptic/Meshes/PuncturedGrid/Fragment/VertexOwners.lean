module
import Purelib.Data.Int.Arithmetic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Polygon.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Riemann.Integration.PreparedQueryNegation
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ReverseJunctions
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.EdgeSides
import Purelib.Riemann.Meshes.PuncturedEdgeFaces
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Topology.Polygon.Stokes

/-! Actual query roots at complete-edge endpoints agree with the retained
vertex owners. The proof consumes finite reachability, not coordinate equality alone. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.VertexOwners.Reached
public section
open Purelib
open Purelib.Approximation
open Purelib.Curves.Hyperelliptic.Integration.Observation
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
open Purelib.Geometry
open Purelib.Polynomial.Geometry
open Purelib.Polynomial.Winding
open Purelib.Riemann.Integration.PreparedQueryNegation
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerLoopMonodromy
open Purelib.Riemann.Topology
open Purelib.Data.Int

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Polynomial.Geometry.ClearPath (GaussianPolynomial)
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (Reached)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

/-- A reached loop at the same point has zero potential difference.

The same-point winding difference cancels directly in the retained integer operations. The resulting zero difference
supplies the original finite equivalence witness. -/
theorem equivalent_at_same_point {polynomial : ClearPath.GaussianPolynomial} {box : Rational.Box}
    {start finish : Data.Gaussian.Basic.Canonical} {first : SquareRootContinuationChain.Owner (polynomial.eval start)}
      {last : SquareRootContinuationChain.Owner (polynomial.eval finish)}
    (reached : PreparedFaceTracePrefixes.Reached box first last) (equal : start = finish) (reference :
      OwnerLoopMonodromy.WindingOneLoop polynomial start) :
    Nonempty (Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName first) (OwnerTraceReadings.ownerName
      last)) := by
  cases equal
  obtain ⟨trace, winding⟩ := reached
  have zero : Polygon.Basic.chainRaw polynomial start trace.vertices = 8 * (0 : Int) := by
    rewrite [winding, Int.sub_eq_add_neg, Arithmetic.add_comm, Arithmetic.neg_add_cancel]
    exact Eq.refl _
  exact ⟨(OwnerPath.rootEquivalent_of_even_with_reference reference trace 0 zero).symm⟩

end
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.VertexOwners.Reached

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.VertexOwners.LiftedFragment
public section
open Purelib
open Purelib.Approximation
open Purelib.Curves.Hyperelliptic.Integration.Observation
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
open Purelib.Geometry
open Purelib.Polynomial.Geometry
open Purelib.Polynomial.Winding
open Purelib.Riemann.Integration.PreparedQueryNegation
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerLoopMonodromy
open Purelib.Riemann.Topology
open Purelib.Data.Int

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords (LiftedFragment)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {source : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {axes :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveAxes base.bank.grid}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames
    base.faces.regulars} {mesh : Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces}
  {count : Nat} {target : Purelib.Data.Rat.Fraction.Rational}

/-- The lower query owner is the actual selected vertex owner whenever its retained coordinate is a full-edge endpoint.
-/
theorem first_vertex_owner (piece : RootedWords.LiftedFragment axes domains mesh source count target) (atStart : Bool)
    (equal : vertices.coordinate (if atStart then piece.occurrence.side.edge.start else
      piece.occurrence.side.edge.finish) = piece.first) :
    Nonempty (Gaussian.Equivalence.NamedEquivalent
      (OwnerTraceReadings.ownerName (vertices.owner frames (if atStart then piece.occurrence.side.edge.start else
        piece.occurrence.side.edge.finish)))
      piece.firstName) := by
  have query := piece.occurrence.first_reached
  cases atStart with
  | false =>
      obtain ⟨same⟩ := Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.VertexOwners.Reached.equivalent_at_same_point
        (piece.occurrence.from_finish query) equal
        (BranchCellBank.referenceAt base.bank.toBranchCellBank _ (vertices.coordinate_onGrid
          piece.occurrence.side.edge.finish)).toLoop
      rw [PreparedEdge.ownerAtPoint_name] at same
      exact ⟨same⟩
  | true =>
      obtain ⟨same⟩ := Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.VertexOwners.Reached.equivalent_at_same_point
        query equal
        (BranchCellBank.referenceAt base.bank.toBranchCellBank _ (vertices.coordinate_onGrid
          piece.occurrence.side.edge.start)).toLoop
      rw [PreparedEdge.ownerAtPoint_name] at same
      exact ⟨same⟩

/-- The upper query retains the same endpoint-owner guarantee. -/
theorem last_vertex_owner (piece : RootedWords.LiftedFragment axes domains mesh source count target) (atStart : Bool)
    (equal : vertices.coordinate (if atStart then piece.occurrence.side.edge.start else
      piece.occurrence.side.edge.finish) = piece.last) :
    Nonempty (Gaussian.Equivalence.NamedEquivalent
      (OwnerTraceReadings.ownerName (vertices.owner frames (if atStart then piece.occurrence.side.edge.start else
        piece.occurrence.side.edge.finish)))
      piece.lastName) := by
  have query := piece.occurrence.finish_reached
  cases atStart with
  | false =>
      obtain ⟨same⟩ := Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.VertexOwners.Reached.equivalent_at_same_point
        (piece.occurrence.from_finish query) equal
        (BranchCellBank.referenceAt base.bank.toBranchCellBank _ (vertices.coordinate_onGrid
          piece.occurrence.side.edge.finish)).toLoop
      rw [PreparedEdge.ownerAtPoint_name] at same
      exact ⟨same⟩
  | true =>
      obtain ⟨same⟩ := Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.VertexOwners.Reached.equivalent_at_same_point
        query equal
        (BranchCellBank.referenceAt base.bank.toBranchCellBank _ (vertices.coordinate_onGrid
          piece.occurrence.side.edge.start)).toLoop
      rw [PreparedEdge.ownerAtPoint_name] at same
      exact ⟨same⟩

end
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.VertexOwners.LiftedFragment
