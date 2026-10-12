module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.JunctionSheets
import Init.Prelude
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
import Purelib.Polynomial.Geometry.Grid.EdgeSides
import Purelib.Riemann.Meshes.PuncturedEdgeFaces
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Topology.Polygon.Stokes

open Purelib

open Purelib.Approximation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords

@[expose] public section

/-!
# Lifted-edge coherence at all junctions of the original fragment word

The full original root chain certifies cross-parent joins as well as joins
inside each parent. Applying the same result to two copies certifies the
closing junction, without dropping stationary handoffs or inferring root
closure from equality of coordinates.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WordJunctions

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords (LiftedFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment (RootedWord)
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

/-- At an actual query junction, repeated complete source edges have one lifted occurrence, even across different
parents and face choices. -/
def Junction (first last : RootedWords.LiftedFragment axes domains mesh source count target) : Prop :=
  first.last = last.first ∧ Nonempty (Gaussian.Equivalence.NamedEquivalent first.lastName last.firstName) ∧
    (first.fragment.source.start = last.fragment.source.start →
      first.fragment.source.finish = last.fragment.source.finish → first.occurrence.side.edge =
        last.occurrence.side.edge)

/-- Every actual consecutive fragment pair retains its original coordinate, root and repeated-edge junction
certificates. -/
def Junctions : List (RootedWords.LiftedFragment axes domains mesh source count target) → Prop
  | [] => True
  | [_] => True
  | first :: next :: rest => Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WordJunctions.Junction first next ∧
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WordJunctions.Junctions (next :: rest)

/-- Consume the original rooted word, rather than a per-junction root or sheet-alignment premise supplied by the caller.
-/
theorem RootedWord.junctions {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {first last : Data.Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord pieces first firstName last lastName) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WordJunctions.Junctions pieces := by
  induction word with
  | nil => trivial
  | cons piece coordinate root tail ih =>
      cases tail with
      | nil => trivial
      | cons next joined roots remaining =>
          refine ⟨⟨joined, roots, ?_⟩, ih⟩
          intro startEq finishEq
          obtain ⟨equivalent⟩ := roots
          exact piece.occurrence.edge_eq_of_query_junction next.occurrence joined equivalent startEq finishEq

/-- Doubling a certified closed word includes its last-to-first junction. The original fragments and their
multiplicities remain explicit. -/
theorem RootedWord.closed_junctions {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {first last : Data.Gaussian.Basic.Canonical} {root : Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord pieces first root last root) (closed : last = first) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WordJunctions.Junctions (pieces ++ pieces) :=
  junctions ((word.castFinish closed).append (word.castFinish closed))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WordJunctions
