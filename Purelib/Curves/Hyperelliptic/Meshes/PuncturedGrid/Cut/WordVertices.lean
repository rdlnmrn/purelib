module
import Purelib.Algebra.NatCast
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ActiveVertices
public import Purelib.Topology.Surface.Chord.WordVertexTrace
import Purelib.Topology.Surface.Word.NormalForm
public import Purelib.Topology.Surface.Word.PairedWord
import Purelib.Topology.Surface.Word.Vertices
import Purelib.Topology.Surface.Word.ZeroReduction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordGenusAccounting
public import Purelib.Topology.Surface.Word.VertexCancellation
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryComponents
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles
import Purelib.Topology.Surface.Word.SignedWord

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ActiveVertices.BranchCellBank

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut

open Purelib.Topology.Surface.Chord

open Purelib.Topology.Surface.Word

open Purelib.Topology.Surface.Word.PairedWord

open Purelib.Topology.Surface.Word.PairedWord.CutBoundaryWord

open Purelib.Topology.Surface.Word.VertexCancellation

open Purelib.Topology.Surface.Word.ZeroReduction

open Purelib

public section

/-!
# Exact finite vertex model of the actual paired cut word

The retained terminal tree and surgery trace construct every vertex class,
with universal factorization. Its size is no longer just a proposed count.
Identifying it with the actual surface after contracting physical boundary
cycles remains the final vertex comparison needed for the genus identity.
-/

namespace Purelib.Riemann.Meshes.LiftedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Topology.Surface.Word.NormalForm (WordNormalForm)
open Purelib.Topology.Surface.Word.ZeroReduction (WordCancellation)
open Purelib.Topology.Surface.Word.Vertices (WordVertexModel)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}

/-- Consume the cached normal form and cancellation tree; do not normalize or prepare the surface again to construct its
finite vertex presentation. -/
@[expose] def cutWordVertexModelWith (lifted : LiftedPuncturedGrid base)
    (normal : NormalForm.WordNormalForm (CutBoundaryWord.pairedLetters lifted.cutBoundaryWord)
      (IntegralPairing.wordSignature lifted.cutIntegralPairing))
    (terminal : ZeroReduction.WordCancellation normal.trace.terminalWord) :
    Vertices.WordVertexModel (CutBoundaryWord.pairedLetters lifted.cutBoundaryWord) (terminal.pairs + 1) :=
  WordVertexTrace.restoreVertices normal.trace
    (WordCancellation.vertexModel terminal
    (WordSurgeryTrace.terminal_unique normal.trace
      (CutBoundaryWord.pairedLetters_unique lifted.cutBoundaryWord)))

/-- Every exact finite vertex model of the original paired cut word has one more vertex than retained terminal
cancellations. -/
theorem cutWord_vertex_count (lifted : LiftedPuncturedGrid base)
    (normal : NormalForm.WordNormalForm (CutBoundaryWord.pairedLetters lifted.cutBoundaryWord)
      (IntegralPairing.wordSignature lifted.cutIntegralPairing))
    (terminal : ZeroReduction.WordCancellation normal.trace.terminalWord) {size : Nat}
    (model : Vertices.WordVertexModel (CutBoundaryWord.pairedLetters lifted.cutBoundaryWord) size) : size =
      terminal.pairs + 1 :=
  model.size_eq (lifted.cutWordVertexModelWith normal terminal)

/-- The original exact word-vertex count and retained handle count satisfy the actual surface Euler balance. -/
theorem cutWord_vertex_euler_balance (lifted : LiftedPuncturedGrid base)
    (normal : NormalForm.WordNormalForm (CutBoundaryWord.pairedLetters lifted.cutBoundaryWord)
      (IntegralPairing.wordSignature lifted.cutIntegralPairing))
    (terminal : ZeroReduction.WordCancellation normal.trace.terminalWord) {size : Nat}
    (model : Vertices.WordVertexModel (CutBoundaryWord.pairedLetters lifted.cutBoundaryWord) size) :
    2 * (normal.pivots.length : Int) + size =
      ((LiftedMesh.activeVertices lifted.mesh).indices.length : Int) - lifted.boundaryComponents.cycles.flatten.length +
        lifted.boundaryComponents.cycles.length + 2 * genus := by
  have census := lifted.cutWord_vertex_count normal terminal model
  rw [census, Algebra.NatCast.add, Nat.cast_one, ← add_assoc,
    WordGenusAccounting.cutWord_euler_accounting lifted normal terminal,
    sub_add_cancel]

end Purelib.Riemann.Meshes.LiftedPuncturedGrid
