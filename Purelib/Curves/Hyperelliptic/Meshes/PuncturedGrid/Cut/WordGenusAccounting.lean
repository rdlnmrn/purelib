module
import Purelib.Algebra.NatCast
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ActiveVertices
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Surface.Word.NormalForm
public import Purelib.Topology.Surface.Word.PairedWord
public import Purelib.Topology.Surface.Word.ZeroReduction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.VertexCensus
import Purelib.Topology.Surface.Word.PairedWordCount
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordCancellation
import Init.Data.Int.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryComponents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs
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
import Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ActiveVertices.BranchCellBank

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut

open Purelib.Riemann

open Purelib.Topology.Surface.Word

open Purelib.Topology.Surface.Word.PairedWord

open Purelib.Topology.Surface.Word.PairedWord.CutBoundaryWord

open Purelib.Topology.Surface.Word.PairedWordCount

public section

/-!
# Connect the computed cut-word reduction to the actual surface census

Each displayed handle uses two actual cut pairs and each terminal
cancellation uses one. Combining this with the actual Euler calculation
isolates the vertex-gluing count needed to identify the number of handles
with the curve genus. No equality of those counts is assumed here.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordGenusAccounting

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Topology.Surface.Word.NormalForm (WordNormalForm)
open Purelib.Topology.Surface.Word.ZeroReduction (WordCancellation)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}

/-- The retained normal form of the actual cut boundary word. -/
@[expose] def CutWordNormal (lifted : Meshes.LiftedPuncturedGrid base) : Type :=
  NormalForm.WordNormalForm
    (CutBoundaryWord.pairedLetters lifted.cutBoundaryWord)
    (IntegralPairing.wordSignature lifted.cutIntegralPairing)

/-- The terminal cancellation certificate attached to that normal form. -/
@[expose] def CutWordTerminal {lifted : Meshes.LiftedPuncturedGrid base} (normal :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordGenusAccounting.CutWordNormal lifted) : Type :=
  ZeroReduction.WordCancellation normal.trace.terminalWord

/-- The exact original paired-cut count equals twice the retained handle count plus terminal cancellations. -/
@[expose] def PairedCutsAccounting (lifted : Meshes.LiftedPuncturedGrid base)
    (normal : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordGenusAccounting.CutWordNormal lifted) (terminal :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordGenusAccounting.CutWordTerminal normal) : Prop :=
  2 * normal.pivots.length + terminal.pairs = lifted.cutBoundaryPairs.pairs.length

/-- The retained handles and terminal cancellations satisfy the original active-vertex and physical-boundary Euler
balance. -/
@[expose] def EulerAccounting (lifted : Meshes.LiftedPuncturedGrid base)
    (normal : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordGenusAccounting.CutWordNormal lifted) (terminal :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordGenusAccounting.CutWordTerminal normal) : Prop :=
  2 * (normal.pivots.length : Int) + terminal.pairs =
    ((LiftedMesh.activeVertices lifted.mesh).indices.length : Int) - lifted.boundaryComponents.cycles.flatten.length +
      lifted.boundaryComponents.cycles.length + 2 * genus - 1

/-- Cancel the common factor two in the original finite handle and terminal-pair count identity. -/
private theorem cancel_twice (pivot terminal pairs : Nat)
    (scaled : 2 * pairs = 4 * pivot + 2 * terminal) :
    2 * pivot + terminal = pairs := by
  omega

/-- Consume a retained normal form and its terminal cancellation tree; neither the word reduction nor the surface
preparation is repeated. -/
theorem cutWord_pairedCuts_accounting (lifted : Meshes.LiftedPuncturedGrid base)
    (normal : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordGenusAccounting.CutWordNormal lifted)
    (terminal : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordGenusAccounting.CutWordTerminal normal) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordGenusAccounting.PairedCutsAccounting lifted normal terminal :=
      by
  have letters :
      (CutBoundaryWord.pairedLetters lifted.cutBoundaryWord).length =
        2 * lifted.cutBoundaryPairs.pairs.length :=
    ProjectedEdgePairing.pairedLetters_length
      lifted.cutBoundaryPairs
  have accounting := WordCancellation.cutWord_complete_accounting lifted normal terminal
  have scaled : 2 * lifted.cutBoundaryPairs.pairs.length =
      4 * normal.pivots.length + 2 * terminal.pairs := letters.symm.trans accounting
  change 2 * normal.pivots.length + terminal.pairs = lifted.cutBoundaryPairs.pairs.length
  exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordGenusAccounting.cancel_twice _ _ _ scaled

/-- The outstanding handle-count step is to identify terminal cancellations with `V - boundaryEdges + boundaryComponents
- 1`. All quantities on the right below are the already certified actual surface counts. -/
theorem cutWord_euler_accounting (lifted : Meshes.LiftedPuncturedGrid base)
    (normal : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordGenusAccounting.CutWordNormal lifted)
    (terminal : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordGenusAccounting.CutWordTerminal normal) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordGenusAccounting.EulerAccounting lifted normal terminal := by
  change 2 * (normal.pivots.length : Int) + terminal.pairs = _
  have pairs := congrArg (fun value : Nat => (value : Int))
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordGenusAccounting.cutWord_pairedCuts_accounting lifted normal
    terminal)
  simp only [-eq_self, -iff_self, Purelib.Algebra.NatCast.add, Purelib.Algebra.NatCast.mul, Nat.cast_ofNat] at pairs
  exact pairs.trans lifted.cut_pairs_euler_balance

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordGenusAccounting
