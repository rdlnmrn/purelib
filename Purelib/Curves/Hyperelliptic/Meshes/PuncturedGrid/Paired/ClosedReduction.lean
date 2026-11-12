module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.GeometricBasis
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningPhysical
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Chain.PathBoundary
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Sewing.PhysicalCycleCoordinates
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles

/-! # Actual closed-word reduction in a GIVEN corrected geometric basis

The supported source word, its actual start sheet and the GIVEN basis sheet
are distinct inputs. Original retraction/span/intersection constructors use
one retained cut. The full computed physical remainder is decomposed on one
GIVEN original boundary cache; face and one-sided terms are not discarded.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.ClosedCoordinates

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation (Data)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Topology.Chain
open Purelib.Topology.Polygon.Stokes (OrientedEdge triangleEdgeOccurrences)
open Purelib.Topology.Surface.Cut.JumpPaths
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles.PolygonStokes (BoundaryCycleDecomposition)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : Data curve}
    {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
    {lifted : LiftedPuncturedGrid base} {bank : BasedBranchBank lifted} {basisSheet : Fin 2}
    {ordered : BasedBranchBank.Ordered bank basisSheet} {paired : OrderedBranchPairs.Ordered.Paired ordered}
    {prepared : PeriodPrograms.Prepared paired} (basis : prepared.GeometricBasis)
    (word : List (OrientedEdge lifted.vertices.count)) (sourceSheet : Fin 2)
    (supported : CutPath.Supported (SewingConnected.SewnPatch.originalEdges lifted.cutPolygon.patch) word)
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish word
      (BasedBranchBank.anchor lifted sourceSheet) (BasedBranchBank.anchor lifted sourceSheet))
    (boundary : BoundaryCycleDecomposition (triangleEdgeOccurrences lifted.mesh.triangulation.faces))
    (factory : boundary = lifted.boundaryComponents)

/-- The three actual original computation caches for one supported closed word on one GIVEN corrected basis. -/
@[expose] def Reduction : Type _ :=
  (row : {value : PeriodCoordinates.ClosedCoordinates word basis.cut.integral //
    value = ClosedCoordinates.build (sheet := sourceSheet) word basis.cut.geometry supported closed basis.cut.retraction
      basis.cut.integral basis.cut.normal.normal}) ×
  (coordinates : {value : SpanningRows.BasisCoordinates basis.cut row.val //
    value = SpanningRows.BasisCoordinates.build (cut := basis.cut) (row := row.val)}) ×
  {loops : PhysicalCycleCoordinates.Data boundary
    (fun column => VertexSewing.OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
      (lifted.cutBoundaryWord.alphabet.generators column)) (Data.Vector.get coordinates.val.physical) //
    loops = coordinates.val.physicalLoops closed boundary factory}

/-- Run the ORIGINAL closed-coordinate and basis-coordinate constructors once, then retain the full physical loop cache.

No basis, integral pairing, retraction, geometry, root or source programme is
reconstructed. The source closure and support concern the actual word;
neither is replaced by a matrix or period agreement premise.
-/
def reduce : Reduction basis word sourceSheet supported closed boundary factory :=
  let row := ClosedCoordinates.build (sheet := sourceSheet) word basis.cut.geometry supported closed
    basis.cut.retraction
    basis.cut.integral basis.cut.normal.normal
  let coordinates := SpanningRows.BasisCoordinates.build (cut := basis.cut) (row := row)
  let loops := coordinates.physicalLoops closed boundary factory
  ⟨⟨row, rfl⟩, ⟨coordinates, rfl⟩, ⟨loops, rfl⟩⟩

namespace Reduction

variable {basis word sourceSheet supported closed boundary factory}
    (value : Reduction basis word sourceSheet supported closed boundary factory)

/-- Read the actual original retraction, coordinate word and integral span for this SAME closed source word. -/
@[expose] def row : PeriodCoordinates.ClosedCoordinates word basis.cut.integral := value.1.val

/-- Read the actual computed A/B intersection coefficients and full one-sided physical vector. -/
@[expose] def coordinates : SpanningRows.BasisCoordinates basis.cut value.row := value.2.1.val

/-- Read the SAME retained hole/exterior loop multiples of the complete physical remainder. -/
@[expose] def loops : PhysicalCycleCoordinates.Data boundary
    (fun column => VertexSewing.OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
      (lifted.cutBoundaryWord.alphabet.generators column)) (Data.Vector.get value.coordinates.physical) := value.2.2.val

/-- The whole source coordinate cache is the single original construction on the GIVEN word, support and closure. -/
theorem row_eq : value.row = ClosedCoordinates.build (sheet := sourceSheet) word basis.cut.geometry supported closed
    basis.cut.retraction basis.cut.integral basis.cut.normal.normal := value.1.property

/-- The whole computed coefficient/physical vector cache is the original basis-coordinate constructor result. -/
theorem coordinates_eq : value.coordinates =
    SpanningRows.BasisCoordinates.build (cut := basis.cut) (row := value.row) := value.2.1.property

/-- The whole physical-loop cache is the single original loop decomposition on this SAME retained boundary. -/
theorem loops_eq : value.loops = value.coordinates.physicalLoops closed boundary factory := value.2.2.property

/-- The original closed-word value retains its computed period combination, full physical loops and faces. -/
theorem value_eq (reading : OrientedEdge lifted.vertices.count → Canonical)
    (anti : ∀ edge, reading edge.reverse = -reading edge) :
    SewingRetraction.wordValue reading word = value.coordinates.periodValue reading +
      gaussianSum (value.loops.rows.map (fun entry => (entry.1 : Canonical) *
        SewingRetraction.wordValue reading entry.2)) + value.coordinates.faceResidual reading :=
  (value.coordinates.word_value_eq reading anti).trans
    (congrArg (fun amount => value.coordinates.periodValue reading + amount +
      value.coordinates.faceResidual reading) (PhysicalCycleCoordinates.Data.value_eq value.loops reading))

/-- The remainder retains the original complete boundary list, with its actual exterior parity and doubled holes. -/
theorem loops_words_eq : value.loops.rows.map Prod.snd = lifted.boundaryLoops :=
  value.loops.words_eq.trans (congrArg (fun actual : BoundaryCycleDecomposition
    (triangleEdgeOccurrences lifted.mesh.triangulation.faces) => actual.cycles) factory)

end Reduction

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.ClosedCoordinates

end
