module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Topology.Surface.Chord.Spanning
import Purelib.Topology.Surface.Cut.BoundaryPairs
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Sewing.ChordCycleBank
import Purelib.Topology.Surface.Sewing.PhysicalCycleCoordinates
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates
public import Purelib.Topology.Surface.Sewing.CutPhysicalCycles
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryComponents
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Word.ProjectedEdgePairs

open Purelib

open Purelib.Data.Vector

open Purelib.Topology.Surface.Chord.Spanning

open Purelib.Topology.Surface.Cut.BoundaryPairs

open Purelib.Topology.Surface.Cut.BoundaryPairs.SewingForest

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.CutPhysicalCycles

open Purelib.Topology.Surface.Sewing.PhysicalCycleCoordinates

open Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles

open Purelib.Topology.Surface.Sewing.VertexSewing

public section

/-!
# Corrected A/B chains with complete physical hole and exterior loops

The actual corrected program words are a retained chord chain, integer
multiples of the original physical loops, and a signed face correction.
All loop coefficients come from their proved closed physical rows. One
boundary cache is shared by every A/B row; no loop matching is assumed.
-/

section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes (OrientedEdge triangleEdgeOccurrences)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue faceValue)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates (CutBank CutRow)
open _root_.Purelib.Topology.Surface.Cut.IntegralPairing renaming CutBoundaryWord -> IntegralPairing
open _root_.Purelib.Topology.Surface.Sewing (ChordCycleBank)
open Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles.PolygonStokes (BoundaryCycleDecomposition)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
    {prepared : Prepared paired}

namespace Purelib.Riemann

/-- Mapping the retained cut boundary to the original mesh vertices preserves distinct oriented edge occurrences. -/
public theorem cut_unique :
    (lifted.cutPolygon.patch.cut.boundary.map (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels)).Nodup := by
  rw [lifted.cutPolygon.patch.cut.boundary_eq]
  exact SewnPatch.boundary_unique lifted.cutPolygon.patch
    (SinglePolygon.originalEdges_unique
      lifted.cutPolygon lifted.mesh.orientedEdges_unique)

end Purelib.Riemann

section

variable {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord
  lifted.cutBoundaryWord}
  {chords : Topology.Surface.Sewing.ChordCycleBank lifted.cutBoundaryWord} {index : Fin genus}
  {row : CutRow prepared integral index}
  {boundary : BoundaryCycleDecomposition
    (triangleEdgeOccurrences lifted.mesh.triangulation.faces)}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutRow.OnChords

set_option genInjectivity false in
/-- The original corrected A and B rows expressed in complete physical boundary-loop coordinates. -/
structure LoopRows
  (data : row.OnChords chords)
    (boundary : PolygonStokes.BoundaryCycleDecomposition (triangleEdgeOccurrences lifted.mesh.triangulation.faces))
      where
  /-- The retained physical boundary-loop coordinates of the original A row. -/ a :
    Topology.Surface.Sewing.PhysicalCycleCoordinates.Data
    boundary
    (fun column => OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators
      column)) data.aPhysical.physical
  /-- The retained physical boundary-loop coordinates of the original B row. -/ b :
    Topology.Surface.Sewing.PhysicalCycleCoordinates.Data
    boundary
    (fun column => OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators
      column)) data.bPhysical.physical

constructive_injectivity
  CutRow.OnChords.LoopRows

/-- Construct both original physical loop rows from the supplied exact cut-boundary matching. -/
@[expose] def loopRows
  (data : row.OnChords chords)
    (boundary : PolygonStokes.BoundaryCycleDecomposition (triangleEdgeOccurrences lifted.mesh.triangulation.faces))
    (matching : ∀ edge, edge ∈ lifted.cutBoundaryPairs.boundary.map (OrientedEdge.map
      lifted.cutPolygon.patch.cut.vertexLabels) ↔
      edge ∈ boundary.cycles.flatten) : data.LoopRows boundary :=
  ⟨ProjectedEdgePairing.physicalCycles lifted.cutBoundaryPairs Purelib.Riemann.cut_unique boundary matching
    data.aPhysical.physical
      data.aPhysical.physical_paired_zero data.a_physical_boundary_zero,
    ProjectedEdgePairing.physicalCycles lifted.cutBoundaryPairs Purelib.Riemann.cut_unique boundary matching
      data.bPhysical.physical
      data.bPhysical.physical_paired_zero data.b_physical_boundary_zero⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutRow.OnChords

section

variable {data : row.OnChords chords}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutRow.OnChords.LoopRows

/-- The actual A word reading splits into its retained chord value, physical boundary-loop sum and signed face
correction. -/
theorem
  a_value
  (loops : data.LoopRows boundary) (value : OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    SewingRetraction.wordValue value (prepared.aWord index) = CutCycleChain.edgeValue data.aPhysical.chain value +
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (loops.a.rows.map (fun entry => (entry.1 :
        Data.Gaussian.Basic.Canonical) * SewingRetraction.wordValue value entry.2)) +
      SewingRetraction.faceValue lifted.mesh.triangulation.faces value row.a.route.correction := by
  rw [data.a_value value anti, loops.a.value_eq value]

/-- The actual B word reading splits into its retained chord value, physical boundary-loop sum and signed face
correction. -/
theorem
  b_value
  (loops : data.LoopRows boundary) (value : OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    SewingRetraction.wordValue value (prepared.bWord index) = CutCycleChain.edgeValue data.bPhysical.chain value +
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (loops.b.rows.map (fun entry => (entry.1 :
        Data.Gaussian.Basic.Canonical) * SewingRetraction.wordValue value entry.2)) +
      SewingRetraction.faceValue lifted.mesh.triangulation.faces value row.b.route.correction := by
  rw [data.b_value value anti, loops.b.value_eq value]

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutRow.OnChords.LoopRows

end
end

section

variable {cut : CutBank prepared}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank.OnChords

set_option genInjectivity false in
/-- One shared original physical boundary decomposition with all retained genus-indexed A/B loop rows. -/
structure Loops (data
  : cut.OnChords) where
  /-- The retained complete decomposition of the actual triangulation boundary. -/ boundary :
    PolygonStokes.BoundaryCycleDecomposition (triangleEdgeOccurrences lifted.mesh.triangulation.faces)
  /-- The retained decomposition's loop words equal the original lifted boundary-loop cache. -/ canonical :
    boundary.cycles = lifted.boundaryLoops
  /-- The dependent vector of actual A/B loop coordinates on this same retained boundary. -/ rows :
    Data.Vector.DependentVector (fun index : Fin genus => (data.rows.get index).LoopRows boundary)

constructive_injectivity
  CutBank.OnChords.Loops

/-- Construct all physical rows from the fixed cut and boundary caches. The original exterior and two-lap hole words are
retained unchanged. -/
@[expose] def loops
  (data : cut.OnChords) : data.Loops :=
  let boundary := lifted.boundaryComponents
  ⟨boundary, rfl, DependentVector.ofFn (fun index =>
    (data.rows.get index).loopRows boundary lifted.cut_boundary_iff_boundaryComponents)⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank.OnChords

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank.OnChords

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank.OnChords.Loops

/-- Every actual A physical row uses exactly the original complete boundary-loop list. -/
theorem
  a_words_eq
  {data : cut.OnChords} (loops : data.Loops) (index : Fin genus) :
    (loops.rows.get index).a.rows.map Prod.snd = lifted.boundaryLoops :=
  (loops.rows.get index).a.words_eq.trans loops.canonical

/-- Every actual B physical row uses exactly the original complete boundary-loop list. -/
theorem
  b_words_eq
  {data : cut.OnChords} (loops : data.Loops) (index : Fin genus) :
    (loops.rows.get index).b.rows.map Prod.snd = lifted.boundaryLoops :=
  (loops.rows.get index).b.words_eq.trans loops.canonical

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank.OnChords.Loops

end
end
