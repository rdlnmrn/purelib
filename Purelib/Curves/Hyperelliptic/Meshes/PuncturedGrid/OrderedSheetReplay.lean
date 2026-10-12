module
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchFaceCorrections
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedPairedSheets
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.RowCircuitOrder
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes

open Purelib.Curves

open Purelib.RootIsolation

@[expose] public section

/-! Replay the same ordered partition and branch pairing on another starting sheet. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}

/-- Retain the original window, partition, order, stems and root bank; materialize only the new sheet occurrences. -/
def
  BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered.atSheet
    (ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank
      sheet) (next : Fin 2) :
      Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank next :=
  let original := ordered.prepared
  let prepared : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.Window.OrderedBranches base.faces
    ordered.window lifted.edges lifted.vertices next :=
    ⟨original.ordered, original.partition, original.kept, original.kept_eq, original.labels, original.labels_eq,
      original.unique, original.selected,
      Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.compile
        lifted.edges lifted.vertices original.partition next⟩
  ⟨ordered.window, ordered.exterior_eq, prepared, ordered.complete, ordered.walk, ordered.walk_eq,
    lifted.edges.indexedEdges lifted.vertices ordered.walk next, rfl, ordered.comparison,
    Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchFaceCorrections.OrderedBranches.corrections prepared lifted.mesh⟩

namespace OrderedBranchPairs.Ordered.Paired
variable {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank
  sheet}

/-- Both replays use the same ordered branch split and retained physical reference hole. -/
def atSheet
    (paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered) (next : Fin 2) :
      Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired (ordered.atSheet next) :=
  ⟨paired.split,
    Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRows.build bank paired.split.ending.reference next
      paired.split.pairs
      (SquareRoot.Grid.Walk.Vertex.VertexWalk.nil lifted.vertices lifted.edges
        (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor lifted next)),
    Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.EndingTours.build bank next paired.split.ending,
    paired.reference, paired.reference_eq⟩

end OrderedBranchPairs.Ordered.Paired
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
