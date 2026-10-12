module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.VertexOwners
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.VertexEdges
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceGeometry
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.JunctionSheets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ReverseJunctions

public section

/-! Propagate the actual incoming vertex owner through a complete rooted
group and recover the destination owner of the same indexed grid edge. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.GroupOwners

open Purelib

open Purelib.Approximation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.VertexOwners

open Purelib.Polynomial.Geometry.Grid

open Purelib.Riemann.Paths

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords (LiftedFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment (RootedWord)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)

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

/-- Two actual rooted fragments with matching query junctions and oriented physical endpoints select the same oriented
retained indexed edge. -/
private theorem oriented_junction {left right : RootedWords.LiftedFragment axes domains mesh source count target}
    (joined : left.last = right.first) (roots : Gaussian.Equivalence.NamedEquivalent left.lastName right.firstName)
    (leftForward rightForward : Bool) {first last : Data.Gaussian.Basic.Canonical}
    (leftFirst : (if leftForward then left.fragment.source.start else left.fragment.source.finish) = first)
    (leftLast : (if leftForward then left.fragment.source.finish else left.fragment.source.start) = last)
    (rightFirst : (if rightForward then right.fragment.source.start else right.fragment.source.finish) = first)
    (rightLast : (if rightForward then right.fragment.source.finish else right.fragment.source.start) = last) :
    (if leftForward then left.occurrence.side.edge else left.occurrence.side.edge.reverse) =
      (if rightForward then right.occurrence.side.edge else right.occurrence.side.edge.reverse) := by
  cases leftForward <;> cases rightForward
  · exact congrArg OrientedEdge.reverse (left.occurrence.edge_eq_of_query_junction right.occurrence joined roots
      (leftLast.trans rightLast.symm) (leftFirst.trans rightFirst.symm))
  · have same := congrArg OrientedEdge.reverse (left.occurrence.edge_eq_of_reverse_query_junction right.occurrence
      joined roots
      (leftLast.trans rightLast.symm) (leftFirst.trans rightFirst.symm))
    exact same.trans (OrientedEdge.reverse_reverse _)
  · exact left.occurrence.edge_eq_of_reverse_query_junction right.occurrence joined roots
      (leftFirst.trans rightFirst.symm) (leftLast.trans rightLast.symm)
  · exact left.occurrence.edge_eq_of_query_junction right.occurrence joined roots
      (leftFirst.trans rightFirst.symm) (leftLast.trans rightLast.symm)

/-- The retained indexed finish owner of an oriented fragment is equivalent to its actual last query root. -/
private theorem last_owner (piece : RootedWords.LiftedFragment axes domains mesh source count target) (forward : Bool)
    (vertex : Fin vertices.count)
    (indexed : (if forward then piece.occurrence.side.edge else piece.occurrence.side.edge.reverse).finish = vertex)
    (coordinate : vertices.coordinate vertex = piece.last) :
    Nonempty (Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName (vertices.owner frames vertex))
      piece.lastName) := by
  have selected : (if !forward then piece.occurrence.side.edge.start else piece.occurrence.side.edge.finish) = vertex :=
    by
    cases forward <;> exact indexed
  have same := LiftedFragment.last_vertex_owner piece (!forward) ((congrArg vertices.coordinate selected).trans
    coordinate)
  exact (congrArg (fun index => Nonempty (Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName
    (vertices.owner frames index)) piece.lastName)) selected).mp same

/-- Propagate a retained indexed edge's destination owner through its rooted tail.

Each original tail piece presents the same oriented endpoints. The recursive
certificate retains its junction witnesses and the exact destination root. -/
private theorem tail_owner (previous : RootedWords.LiftedFragment axes domains mesh source count target) (forward :
  Bool)
    {first last : Data.Gaussian.Basic.Canonical}
    (previousFirst : (if forward then previous.fragment.source.start else previous.fragment.source.finish) = first)
    (previousLast : (if forward then previous.fragment.source.finish else previous.fragment.source.start) = last)
    (indexed : Stokes.OrientedEdge vertices.count)
    (edgeEq : (if forward then previous.occurrence.side.edge else previous.occurrence.side.edge.reverse) = indexed)
    (coordinate : vertices.coordinate indexed.finish = last)
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {lastName : Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord pieces previous.last previous.lastName last lastName)
    (geometry : ∀ piece ∈ pieces, SourceGeometry.Presents piece first last) :
    Nonempty (Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName (vertices.owner frames indexed.finish))
      lastName) := by
  cases word with
  | nil equal root =>
      obtain ⟨same⟩ := Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.GroupOwners.last_owner previous forward
        indexed.finish (congrArg OrientedEdge.finish edgeEq)
        (coordinate.trans equal.symm)
      obtain ⟨root⟩ := root
      exact ⟨same.trans root⟩
  | @cons piece rest _ _ _ _ joined roots tail =>
      obtain ⟨roots⟩ := roots
      have go (direction : Bool)
          (firstEq : (if direction then piece.fragment.source.start else piece.fragment.source.finish) = first)
          (lastEq : (if direction then piece.fragment.source.finish else piece.fragment.source.start) = last) :=
        Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.GroupOwners.tail_owner piece direction firstEq lastEq
          indexed
          ((Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.GroupOwners.oriented_junction joined roots forward
            direction previousFirst previousLast firstEq lastEq).symm.trans edgeEq)
          coordinate tail (fun child member => geometry child (List.mem_cons_of_mem _ member))
      rcases geometry piece List.mem_cons_self with positive | negative
      · exact go true positive.1 positive.2
      · exact go false negative.1 negative.2
termination_by pieces.length
decreasing_by
  subst_vars
  exact Nat.lt_succ_self _

/-- The same standard indexed edge used by a complete group ends at the actual outgoing root of that group. This
supplies the next group's sheet. -/
theorem RootedWord.routed_finish_owner {head : RootedWords.LiftedFragment axes domains mesh source count target}
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {first last : Data.Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord (head :: pieces) first firstName last lastName)
    (geometry : ∀ piece ∈ head :: pieces, SourceGeometry.Presents piece first last)
    (edge : Walks.Edge base.bank.grid first last)
    (vertex : Fin vertices.count) (coordinate : vertices.coordinate vertex = first)
    (root : Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName (vertices.owner frames vertex))
      firstName) :
    Nonempty (Gaussian.Equivalence.NamedEquivalent
      (OwnerTraceReadings.ownerName (vertices.owner frames (edges.indexedEdge vertices edge (vertices.sheet
        vertex)).finish)) lastName) := by
  cases word with
  | cons head equal entry tail =>
      obtain ⟨entry⟩ := entry
      have go (direction : Bool)
          (firstEq : (if direction then head.fragment.source.start else head.fragment.source.finish) = first)
          (lastEq : (if direction then head.fragment.source.finish else head.fragment.source.start) = last) :=
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.GroupOwners.tail_owner head direction firstEq lastEq
          (edges.indexedEdge vertices edge (vertices.sheet vertex))
          (VertexEdges.edge_eq_of_first_vertex head direction edge firstEq lastEq equal.symm vertex coordinate
            (root.trans entry))
          (vertices.coordinate_index _ edge.vertices.2 _) tail
          (fun child member => geometry child (List.mem_cons_of_mem _ member))
      rcases geometry head List.mem_cons_self with positive | negative
      · exact go true positive.1 positive.2
      · exact go false negative.1 negative.2

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.GroupOwners
