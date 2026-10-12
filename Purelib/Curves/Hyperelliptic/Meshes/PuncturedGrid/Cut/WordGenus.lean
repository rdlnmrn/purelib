module
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordCancellation
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Surface.Cut.VertexReading
import Purelib.Topology.Surface.Word.NormalForm
import Purelib.Topology.Surface.Word.PairedWord
import Purelib.Topology.Surface.Word.Vertices
import Purelib.Topology.Surface.Word.ZeroReduction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.VertexDescent
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ActiveVertices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryComponents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Chain.PathBoundary
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryContraction
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordVertices

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.VertexDescent

open Purelib.Riemann

open Purelib.Topology.Surface.Cut.VertexReading

open Purelib.Topology.Surface.Word

open Purelib.Topology.Surface.Word.PairedWord

open Purelib.Topology.Surface.Word.PairedWord.CutBoundaryWord

@[expose] public section

/-!
# The actual cut-word reduction has exactly the curve genus many handles

The reverse factor is constructed from a literal reading of the original
cut boundary, descent through its proved gluing fibers, and contraction of
its physical cycles. Both finite vertex models are therefore universal.
Their exact cardinality comparison closes the actual surface Euler balance.
-/

section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContraction (ContractedCutWord)
open Purelib.Topology.Surface.Cut.VertexReading (CutVertexReading)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.VertexDescent (SurfaceVertexReading)
open Purelib.Topology.Surface.Word.Vertices (WordVertexModel WordVertexRealization)
open Purelib.Topology.Surface.Word.NormalForm (WordNormalForm)
open Purelib.Topology.Surface.Word.ZeroReduction (WordCancellation)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContraction.ContractedCutWord

/-- Every field, including executable universal factorization, is derived from the retained actual surface and
physical-boundary caches. -/
def vertexModel {lifted :
  Meshes.LiftedPuncturedGrid base} (cache : BoundaryContraction.ContractedCutWord lifted) :
    Vertices.WordVertexModel (CutBoundaryWord.pairedLetters lifted.cutBoundaryWord)
      cache.contraction.representatives.length where
  toWordVertexRealization := cache.word
  covered := cache.covered
  lift := fun other => by
    change cache.word.Factor other
    rw [cache.word_eq]
    let reading := CutVertexReading.build lifted.cutBoundaryWord other lifted.cutPolygon.patch.cut.anchor
      lifted.cutPolygon.patch.cut.closed lifted.cutPolygon.patch.cut.simple
    let surface := SurfaceVertexReading.build lifted reading
    exact surface.factor cache.contraction cache.indexed

/-- The actual contracted surface has exactly one more vertex than the terminal cancellation-pair count. -/
theorem vertex_count
  {lifted : Meshes.LiftedPuncturedGrid base} (cache : BoundaryContraction.ContractedCutWord lifted)
    (normal : NormalForm.WordNormalForm (CutBoundaryWord.pairedLetters lifted.cutBoundaryWord)
      (IntegralPairing.wordSignature lifted.cutIntegralPairing))
    (terminal : ZeroReduction.WordCancellation normal.trace.terminalWord) :
    cache.contraction.representatives.length = terminal.pairs + 1 :=
  cache.vertexModel.size_eq (lifted.cutWordVertexModelWith normal terminal)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContraction.ContractedCutWord

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordGenus

/-- The exact integral Euler balance identifies the retained handle count with the curve genus. -/
private theorem handles_eq_of_balance (handles pairs curveGenus : Nat)
    (balance : 2 * (handles : Int) + (pairs + 1 : Nat) =
      ((pairs + 1 : Nat) : Int) + 2 * curveGenus) : handles = curveGenus := by
  omega

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordGenus

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContraction.ContractedCutWord

/-- Literal word surgery, exact surface incidence, and actual boundary contraction agree on the number of handles,
uniformly in the genus. -/
theorem handle_count
  {lifted : Meshes.LiftedPuncturedGrid base} (cache : BoundaryContraction.ContractedCutWord lifted)
    (normal : NormalForm.WordNormalForm (CutBoundaryWord.pairedLetters lifted.cutBoundaryWord)
      (IntegralPairing.wordSignature lifted.cutIntegralPairing))
    (terminal : ZeroReduction.WordCancellation normal.trace.terminalWord) : normal.pivots.length = genus := by
  have balance := lifted.contracted_cutWord_genus_balance normal terminal cache.contraction
  rw [cache.vertex_count normal terminal] at balance
  exact Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordGenus.handles_eq_of_balance _ _ _ balance

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContraction.ContractedCutWord

namespace Purelib.Riemann.Meshes.LiftedPuncturedGrid

/-- The actual lifted cut-word normal form contains exactly the curve genus many handle pivots. -/
theorem cutWord_handle_count (lifted : Meshes.LiftedPuncturedGrid
  base)
    (normal : NormalForm.WordNormalForm (CutBoundaryWord.pairedLetters lifted.cutBoundaryWord)
      (IntegralPairing.wordSignature lifted.cutIntegralPairing)) :
    normal.pivots.length = genus :=
  lifted.contractedCutWord.handle_count normal (WordCancellation.cutWordTerminalCancellationWith lifted normal)

end Purelib.Riemann.Meshes.LiftedPuncturedGrid

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContraction.ContractedCutWord

/-- The two comparison maps preserve every actual cut generator and are inverse on every vertex, rather than merely
having equal cardinalities. -/
theorem vertex_inverse
  {lifted : Meshes.LiftedPuncturedGrid base} (cache : BoundaryContraction.ContractedCutWord lifted)
    {size : Nat} (model : Vertices.WordVertexModel (CutBoundaryWord.pairedLetters lifted.cutBoundaryWord) size) (vertex
      : Fin size) :
    (cache.vertexModel.lift model.toWordVertexRealization).vertices ((model.lift cache.word).vertices vertex) = vertex
      := by
  exact ((model.lift cache.word).comp (cache.vertexModel.lift model.toWordVertexRealization)).unique
    model.covered (.identity model.toWordVertexRealization) vertex

/-- The two universal paired-word vertex maps are inverse at every retained contracted surface vertex. -/
theorem
  surface_vertex_inverse
  {lifted : Meshes.LiftedPuncturedGrid base} (cache : BoundaryContraction.ContractedCutWord lifted)
    {size : Nat} (model : Vertices.WordVertexModel (CutBoundaryWord.pairedLetters lifted.cutBoundaryWord) size)
    (vertex : Fin cache.contraction.representatives.length) :
    (model.lift cache.word).vertices ((cache.vertexModel.lift model.toWordVertexRealization).vertices vertex) = vertex
      := by
  exact ((cache.vertexModel.lift model.toWordVertexRealization).comp (model.lift cache.word)).unique
    cache.covered (.identity cache.word) vertex

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContraction.ContractedCutWord

end
