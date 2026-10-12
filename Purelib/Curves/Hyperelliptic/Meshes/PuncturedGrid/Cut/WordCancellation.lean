module
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Topology.Surface.Word.NormalForm
public import Purelib.Topology.Surface.Word.PairedWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordNormalForm
public import Purelib.Topology.Surface.Word.ZeroReduction
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Word.Pairing
import Purelib.Topology.Surface.Word.SignedWord

open Purelib.Riemann

open Purelib.Topology.Surface.Word

open Purelib.Topology.Surface.Word.PairedWord

open Purelib.Topology.Surface.Word.PairedWord.CutBoundaryWord

open Purelib.Topology.Surface.Word.ZeroReduction

@[expose] public section

/-!
# Explicit cancellation of the actual cut word's terminal zero block

Consume the retained word-surgery trace. Every terminal occurrence belongs
to a displayed cancelling chord, so the word accounting now separates
actual handles from actual cancelling pairs. This does not yet identify
the latter count with the surface's vertex-gluing count.
-/

open Purelib.Riemann.Meshes (FramedPuncturedGrid)
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordCancellation

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Word.NormalForm (WordNormalForm)
open Purelib.Topology.Surface.Word.ZeroReduction (WordCancellation)
variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}

/-- Reuse any already retained normal form of this actual cut word. -/
def cutWordTerminalCancellationWith (lifted : Meshes.LiftedPuncturedGrid base)
    (normal : NormalForm.WordNormalForm
      (CutBoundaryWord.pairedLetters lifted.cutBoundaryWord)
      (IntegralPairing.wordSignature lifted.cutIntegralPairing)) :
    ZeroReduction.WordCancellation normal.trace.terminalWord :=
  WordSurgeryTrace.terminalCancellation normal.trace
    (CutBoundaryWord.pairedLetters_unique lifted.cutBoundaryWord)
    (CutBoundaryWord.pairedLetters_closed lifted.cutBoundaryWord)

/-- The actual original cut word has four occurrences per retained handle plus two per explicit terminal cancellation
pair. -/
theorem cutWord_complete_accounting (lifted : Meshes.LiftedPuncturedGrid base)
    (normal : NormalForm.WordNormalForm
      (CutBoundaryWord.pairedLetters lifted.cutBoundaryWord)
      (IntegralPairing.wordSignature lifted.cutIntegralPairing))
    (terminal : ZeroReduction.WordCancellation normal.trace.terminalWord) :
    (CutBoundaryWord.pairedLetters lifted.cutBoundaryWord).length =
      4 * normal.pivots.length + 2 * terminal.pairs := by
  have accounting := normal.trace.length_accounting
  rw [terminal.length_eq] at accounting
  exact accounting.symm.trans (Nat.add_comm _ _)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordCancellation
