module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.WeightedPeriods
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Chord.Spanning
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Topology.Surface.Word.GeneratorValuations
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PhysicalCycles
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HolePhysicalCorrection
import Batteries.Logic
import Mathlib.Tactic.Ring.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PhysicalCycleCoordinates
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib

open Purelib.Riemann

public section

/-!
# Separate the exterior and hole parts of cached physical rows

The split follows the original boundary-loop order and retains each integer
coefficient. It supplies the exact weights for the requested hole correction;
the exterior contribution stays explicit in the same value identity.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Topology.Polygon.Stokes

universe u

section
namespace PhysicalLoopSplit

/-- Collect the original weighted hole rows into their retained hole-indexed coefficient vector. -/
@[expose] def holeWeights {α : Type u} {count : Nat} (word : α → List (Topology.Polygon.Stokes.OrientedEdge count)) :
    (holes : List α) → (rows : List (Int × List (Topology.Polygon.Stokes.OrientedEdge count))) → rows.map Prod.snd =
      holes.map word →
      Data.Vector Int holes.length
  | [], _, _ => .nil
  | _ :: _, [], equal => (by cases equal)
  | _ :: holes, row :: rows, equal => .cons row.1 (holeWeights word holes rows (List.cons.inj equal).2)

/-- The original weighted hole-row value equals the coefficient-vector contraction with the same hole readings. -/
private theorem holeWeights_value {α : Type u} {count : Nat} (word : α → List (Topology.Polygon.Stokes.OrientedEdge
  count))
    (value : Topology.Polygon.Stokes.OrientedEdge count → Gaussian.Basic.Canonical) :
    ∀ (holes : List α) (rows : List (Int × List (Topology.Polygon.Stokes.OrientedEdge count))) (equal : rows.map
      Prod.snd = holes.map word),
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (rows.map (fun row => (row.1 : Gaussian.Basic.Canonical) *
        Topology.Surface.Sewing.SewingRetraction.wordValue value row.2)) =
        FiniteSum.Fin.sumFin (fun index : Fin holes.length => (holeWeights word holes rows equal index :
          Gaussian.Basic.Canonical) *
          Topology.Surface.Sewing.SewingRetraction.wordValue value (word holes[index.val]))
  | [], [], _ => rfl
  | [], _ :: _, equal => by cases equal
  | _ :: _, [], equal => by cases equal
  | hole :: holes, row :: rows, equal => by
      rw [FiniteSum.Fin.sumFin_succ]
      change (row.1 : Gaussian.Basic.Canonical) * Topology.Surface.Sewing.SewingRetraction.wordValue value row.2 +
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (rows.map _) =
        (row.1 : Gaussian.Basic.Canonical) * Topology.Surface.Sewing.SewingRetraction.wordValue value (word hole) +
          FiniteSum.Fin.sumFin _
      exact congrArg₂ (fun first last : Gaussian.Basic.Canonical => first + last)
        (congrArg (fun boundary => (row.1 : Gaussian.Basic.Canonical) *
          Topology.Surface.Sewing.SewingRetraction.wordValue value boundary) (List.cons.inj equal).1)
        (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalLoopSplit.holeWeights_value word value holes rows
          (List.cons.inj equal).2)

end PhysicalLoopSplit

end

namespace PhysicalLoopSplit

set_option genInjectivity false in
/-- An exact decomposition of the original ordered boundary rows into exterior rows and weighted hole readings. -/
structure RowSplit {α : Type u} {count : Nat} (word : α → List (Topology.Polygon.Stokes.OrientedEdge count))
    (exterior : List (List (Topology.Polygon.Stokes.OrientedEdge count))) (holes : List α) (rows : List (Int × List
      (Topology.Polygon.Stokes.OrientedEdge count))) where
  /-- The retained exterior occurrences in their original row order. -/ exteriorRows : List (Int × List
    (Topology.Polygon.Stokes.OrientedEdge count))
  /-- The retained exterior occurrences equal the original exterior-row filter. -/ exterior_eq : exteriorRows.map
    Prod.snd = exterior
  /-- The accumulated integer weight of each original hole row. -/ weights : Data.Vector Int holes.length
  /-- The original row reading splits exactly into the exterior reading and weighted original hole readings. -/ value_eq
    : ∀ value : Topology.Polygon.Stokes.OrientedEdge count → Gaussian.Basic.Canonical,
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (rows.map (fun row => (row.1 : Gaussian.Basic.Canonical) *
      Topology.Surface.Sewing.SewingRetraction.wordValue value row.2)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (exteriorRows.map (fun row => (row.1 : Gaussian.Basic.Canonical) *
        Topology.Surface.Sewing.SewingRetraction.wordValue value row.2)) +
        FiniteSum.Fin.sumFin (fun index : Fin holes.length => (weights index : Gaussian.Basic.Canonical) *
          Topology.Surface.Sewing.SewingRetraction.wordValue value (word holes[index.val]))

constructive_injectivity RowSplit

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalLoopSplit in
/-- Split the supplied original boundary rows recursively, preserving their ordered exterior occurrences and exact
reading identity. -/
@[expose] def splitRows {α : Type u} {count : Nat} (word : α → List (Topology.Polygon.Stokes.OrientedEdge count)) (holes
  : List α) :
    (exterior : List (List (Topology.Polygon.Stokes.OrientedEdge count))) → (rows : List (Int × List
      (Topology.Polygon.Stokes.OrientedEdge count))) →
    rows.map Prod.snd = exterior ++ holes.map word → Hyperelliptic.Meshes.PuncturedGrid.PhysicalLoopSplit.RowSplit word
      exterior holes rows
  | [], rows, equal =>
      ⟨[], rfl, holeWeights word holes rows equal, fun value => by
        change _ = 0 + _
        rw [zero_add]
        exact Hyperelliptic.Meshes.PuncturedGrid.PhysicalLoopSplit.holeWeights_value word value holes rows equal⟩
  | _ :: _, [], equal => by cases equal
  | head :: exterior, row :: rows, equal =>
      let rest := Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalLoopSplit.splitRows word holes exterior rows
        (List.cons.inj equal).2
      ⟨row :: rest.exteriorRows, congrArg₂ List.cons (List.cons.inj equal).1 rest.exterior_eq, rest.weights,
        fun value => by
          change (row.1 : Gaussian.Basic.Canonical) * Topology.Surface.Sewing.SewingRetraction.wordValue value row.2 +
            Data.Gaussian.Norm.Sum.Basic.gaussianSum (rows.map _) =
            ((row.1 : Gaussian.Basic.Canonical) * Topology.Surface.Sewing.SewingRetraction.wordValue value row.2 +
              Data.Gaussian.Norm.Sum.Basic.gaussianSum (rest.exteriorRows.map _)) + _
          rw [rest.value_eq value]
          ring1⟩

end PhysicalLoopSplit

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base}

set_option genInjectivity false in
/-- The retained exterior and hole decomposition of one original physical boundary-cycle reading.

The cached coefficients refer to the original hole owners and certify equality for every supplied reading. -/
structure PhysicalLoopSplit (lifted : Meshes.LiftedPuncturedGrid base)
    (rows : List (Int × List (Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count))) where
  /-- The original physical cycle's retained exterior rows. -/ exterior : List (Int × List
    (Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count))
  /-- The exterior rows are exactly those from the original physical cycle decomposition. -/ exterior_eq : exterior.map
    Prod.snd = lifted.exteriorBoundaries
  /-- The retained weighted hole-row list. -/ weights : Data.Vector Int base.faces.holes.length
  /-- The cached coefficient of each original hole owner. -/ coefficients : Periods.WeightedPeriods.Coefficients weights
  /-- The physical cycle reading is exactly its exterior reading plus the cached hole-coefficient contraction. -/
    value_eq : ∀ value : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical,
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (rows.map (fun row => (row.1 : Gaussian.Basic.Canonical) *
      Topology.Surface.Sewing.SewingRetraction.wordValue value row.2)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (exterior.map (fun row => (row.1 : Gaussian.Basic.Canonical) *
        Topology.Surface.Sewing.SewingRetraction.wordValue value row.2)) +
        coefficients.combine (fun index : Fin base.faces.holes.length =>
          Topology.Surface.Sewing.SewingRetraction.wordValue value (base.faces.holes[index.val].liftedBoundary
            lifted.vertices lifted.edges))

constructive_injectivity PhysicalLoopSplit

namespace PhysicalLoopSplit

/-- Split the actual physical cycle boundary loops and retain their original exterior rows and hole coefficients. -/
@[expose] def build (lifted : Meshes.LiftedPuncturedGrid base) (rows : List (Int × List
  (Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count)))
    (matching : rows.map Prod.snd = lifted.boundaryLoops) :
      PhysicalLoopSplit lifted rows :=
  let split := Hyperelliptic.Meshes.PuncturedGrid.PhysicalLoopSplit.splitRows (fun hole :
    Meshes.PuncturedGridFaces.BranchHole base.bank.toBranchCellBank =>
    hole.liftedBoundary lifted.vertices lifted.edges) base.faces.holes
    lifted.exteriorBoundaries rows matching
  let coefficients := Periods.WeightedPeriods.Coefficients.build split.weights
  ⟨split.exteriorRows, split.exterior_eq, split.weights, coefficients, fun value =>
    (split.value_eq value).trans (congrArg (fun rest =>
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (split.exteriorRows.map (fun row => (row.1 : Gaussian.Basic.Canonical) *
        Topology.Surface.Sewing.SewingRetraction.wordValue value row.2)) + rest)
        (coefficients.combine_eq _).symm)⟩

variable {rows : List (Int × List (Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count))}

/-- The original physical row differs from its retained exterior part
by exactly the combination paid by the shared hole request. -/
theorem hole_difference (split : PhysicalLoopSplit lifted rows)
  (value : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (rows.map (fun row => (row.1 : Gaussian.Basic.Canonical) *
      Topology.Surface.Sewing.SewingRetraction.wordValue value row.2)) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (split.exterior.map (fun row => (row.1 : Gaussian.Basic.Canonical) *
        Topology.Surface.Sewing.SewingRetraction.wordValue value row.2)) =
        split.coefficients.combine (fun index : Fin base.faces.holes.length =>
          Topology.Surface.Sewing.SewingRetraction.wordValue value (base.faces.holes[index.val].liftedBoundary
            lifted.vertices lifted.edges)) := by
  rw [split.value_eq value]
  ring1

variable {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
  base.faces.regulars}
  {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {prepared : Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts.BoundaryContactPreparations
    lifted.cutPolygon.patch lifted.cutBoundaryPairs differential domains}
  {target : Topology.Surface.Sewing.SewnPrimitiveFaces.Coordinate} {floor : Nat}

/-- Request accuracy of the retained weighted hole contribution at the supplied positive target and stage floor. -/
@[expose] def request (split : PhysicalLoopSplit lifted rows)
    (prepared : Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts.BoundaryContactPreparations
      lifted.cutPolygon.patch lifted.cutBoundaryPairs differential domains)
    (target : Topology.Surface.Sewing.SewnPrimitiveFaces.Coordinate) (positive : 0 < target) (floor : Nat) :
    Hyperelliptic.Meshes.PuncturedGrid.HolePhysicalCorrection.HolePhysicalRequest prepared split.coefficients target
      floor :=
  Hyperelliptic.Meshes.PuncturedGrid.HolePhysicalCorrection.HolePhysicalRequest.build prepared split.coefficients target
    positive floor

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalLoopSplit in
/-- The physical cycle reading differs from its retained exterior reading by less than the requested target at every
sufficient stage. -/
theorem accurate (split : PhysicalLoopSplit lifted rows)
    (request : Hyperelliptic.Meshes.PuncturedGrid.HolePhysicalCorrection.HolePhysicalRequest prepared split.coefficients
      target floor) {index : Nat}
    (later : request.index ≤ index)
    {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains}
    (triangles : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh)
    (surface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch triangles.values) :
    let value := Topology.Surface.Word.GeneratorValuations.ProjectedEdgePairing.generatorValue lifted.cutBoundaryPairs
      (fun column =>
      surface.sewn.values (lifted.cutBoundaryWord.alphabet.generators column).finish -
        surface.sewn.values (lifted.cutBoundaryWord.alphabet.generators column).start)
    Data.Gaussian.Norm.Basic.normSq
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum (rows.map (fun row => (row.1 : Gaussian.Basic.Canonical) *
        Topology.Surface.Sewing.SewingRetraction.wordValue value row.2)) -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (split.exterior.map (fun row => (row.1 : Gaussian.Basic.Canonical) *
          Topology.Surface.Sewing.SewingRetraction.wordValue value row.2))) < target := by
  dsimp only
  rw [split.hole_difference]
  exact request.accurate later triangles surface

end PhysicalLoopSplit

namespace PhysicalLoopSplit.Loops

variable {bank : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet
  : Fin 2} {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered
  bank sheet}
  {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered} {prepared :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired} {cut :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank prepared}
  {data : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank.OnChords cut}

/-- The A/B coefficients are extracted from their existing closed physical
rows; no independent vector of hole weights is supplied by the caller. -/
@[expose] def aPhysicalSplit (loops : data.Loops) (index : Fin genus) :
  PhysicalLoopSplit lifted (loops.rows.get index).a.rows :=
  build lifted _ (loops.a_words_eq index)

/-- Decompose the original b-cycle physical correction into its retained exterior and hole contributions. -/
@[expose] def bPhysicalSplit (loops : data.Loops) (index : Fin genus) :
  PhysicalLoopSplit lifted (loops.rows.get index).b.rows :=
  build lifted _ (loops.b_words_eq index)

/-- The physical cycle correction differs from the retained exterior reading by exactly its original weighted hole
contribution. -/
private theorem correction_difference (chain physical exterior faces : Gaussian.Basic.Canonical) :
    chain + physical + faces - (chain + exterior + faces) = physical - exterior := by ring1

variable {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
  base.faces.regulars}
  {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {contacts : Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts.BoundaryContactPreparations
    lifted.cutPolygon.patch lifted.cutBoundaryPairs differential domains}
  {target : Topology.Surface.Sewing.SewnPrimitiveFaces.Coordinate} {floor : Nat}

/-- The a-cycle reading equals its normal-form reading up to the requested retained exterior and face correction error.
-/
theorem a_value_accurate (loops : data.Loops) (index : Fin genus)
    (split : PhysicalLoopSplit lifted (loops.rows.get
      index).a.rows)
    (request : Hyperelliptic.Meshes.PuncturedGrid.HolePhysicalCorrection.HolePhysicalRequest contacts split.coefficients
      target floor) {sampleIndex : Nat}
    (later : request.index ≤ sampleIndex)
    {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential sampleIndex domains}
    (triangles : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh)
    (surface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch triangles.values) :
    let value := Topology.Surface.Word.GeneratorValuations.ProjectedEdgePairing.generatorValue lifted.cutBoundaryPairs
      (fun column =>
      surface.sewn.values (lifted.cutBoundaryWord.alphabet.generators column).finish -
        surface.sewn.values (lifted.cutBoundaryWord.alphabet.generators column).start)
    Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewingRetraction.wordValue value (prepared.aWord index)
      -
      (Topology.Surface.Chord.Spanning.CutCycleChain.edgeValue (data.rows.get index).aPhysical.chain value +
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (split.exterior.map (fun row => (row.1 : Gaussian.Basic.Canonical) *
          Topology.Surface.Sewing.SewingRetraction.wordValue value row.2)) +
          Topology.Surface.Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces value (cut.rows.get
            index).a.route.correction)) < target := by
  dsimp only
  rw [(loops.rows.get index).a_value _
    (Topology.Surface.Word.GeneratorValuations.ProjectedEdgePairing.generatorValue_reverse lifted.cutBoundaryPairs _),
    Hyperelliptic.Meshes.PuncturedGrid.PhysicalLoopSplit.Loops.correction_difference]
  exact split.accurate request later triangles surface

/-- The corrected standard B word keeps its earlier A prefix, its signed
face correction and the entire exterior term. Only the certified sum of
branch-hole contributions is paid by the requested error. -/
theorem b_value_accurate (loops : data.Loops) (index : Fin genus)
    (split : PhysicalLoopSplit lifted (loops.rows.get
      index).b.rows)
    (request : Hyperelliptic.Meshes.PuncturedGrid.HolePhysicalCorrection.HolePhysicalRequest contacts split.coefficients
      target floor) {sampleIndex : Nat}
    (later : request.index ≤ sampleIndex)
    {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential sampleIndex domains}
    (triangles : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh)
    (surface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch triangles.values) :
    let value := Topology.Surface.Word.GeneratorValuations.ProjectedEdgePairing.generatorValue lifted.cutBoundaryPairs
      (fun column =>
      surface.sewn.values (lifted.cutBoundaryWord.alphabet.generators column).finish -
        surface.sewn.values (lifted.cutBoundaryWord.alphabet.generators column).start)
    Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewingRetraction.wordValue value (prepared.bWord index)
      -
      (Topology.Surface.Chord.Spanning.CutCycleChain.edgeValue (data.rows.get index).bPhysical.chain value +
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (split.exterior.map (fun row => (row.1 : Gaussian.Basic.Canonical) *
          Topology.Surface.Sewing.SewingRetraction.wordValue value row.2)) +
          Topology.Surface.Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces value (cut.rows.get
            index).b.route.correction)) < target := by
  dsimp only
  rw [(loops.rows.get index).b_value _
    (Topology.Surface.Word.GeneratorValuations.ProjectedEdgePairing.generatorValue_reverse lifted.cutBoundaryPairs _),
    Hyperelliptic.Meshes.PuncturedGrid.PhysicalLoopSplit.Loops.correction_difference]
  exact split.accurate request later triangles surface

end PhysicalLoopSplit.Loops
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
