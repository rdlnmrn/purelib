module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection
public import Purelib.RootIsolation.SquareRoot.Grid.Walk.Combinations
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Closure
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourSpanning
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedOwnerClosedBridges
import Purelib.Riemann.Meshes.GridLiftedConnections
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Cut.Spanning
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree

open Purelib.Algebra

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib

open Purelib.Polynomial

open Purelib.Riemann

open Purelib.RootIsolation

public section

/-!
# Signed combinations of retained standard tours and their period programs

Read the original indexed words and root sheets from the tour bank. Actual
sheet-aware connectors move A loops to a selected B base point. Every signed
combination is a literal closed lifted walk, with its exact valuation law
and an automatic root-closed period preparation. No symplectic table or
equality to independently prepared period names is assumed or asserted.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
      SquareRoot.Grid.LiftedVertices.VertexBank
    base.bank.grid}
  {edges : SquareRoot.Grid.RootEdgeBank frames} {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges
    base.faces}
  {point : Gaussian.Basic.Canonical} {walk : Geometry.Grid.Walks.Walk base.bank.grid point point}
  {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval point)}

/-- Preserve the cached face word; the even-winding proof certifies its
return to the already selected sheet without acquiring a new owner. -/
@[expose] def
  TourFaces.FramedPuncturedGrid.OwnerWalkFaces.vertexLoop
  (faces : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid.OwnerWalkFaces mesh walk owner)
  (turns : Int)
    (winding : Paths.PreparedPathWinding.ClearPath.rawWinding walk.path = 8 * turns) :
    SquareRoot.Grid.Walk.Vertex.VertexWalk vertices edges (vertices.index point faces.first faces.sheet)
      (vertices.index point faces.first faces.sheet) :=
  { walk := walk.castEndpoints (vertices.coordinate_index point faces.first faces.sheet).symm
      (vertices.coordinate_index point faces.first faces.sheet).symm
    sheet_eq := by
      rw [edges.target_castEndpoints, vertices.sheet_index]
      exact SquareRoot.Grid.EdgeBank.RootEdgeBank.target_even edges
        (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt base.bank.toBranchCellBank point
        faces.first).toLoop walk faces.first turns winding faces.sheet
    indexed := faces.geometry.indexed
    indexed_eq := by rw [edges.indexedEdges_castEndpoints, vertices.sheet_index]; exact faces.indexed_eq }

/-- The original closed lifted loop reuses the exact retained face word. -/
theorem TourCombinations.OwnerWalkFaces.vertexLoop_indexed (faces :
  Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid.OwnerWalkFaces mesh walk owner) (turns :
  Int)
    (winding : Paths.PreparedPathWinding.ClearPath.rawWinding walk.path = 8 * turns) :
    (faces.vertexLoop turns winding).indexed = faces.geometry.indexed := rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}
  {base : Meshes.FramedPuncturedGrid curve (Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve
    branches).branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base}

/-- Read the original winding-one loop reference at the retained grid point. -/
@[expose] public def TourCombinations.StandardTours.reference (base : Meshes.FramedPuncturedGrid curve
  (Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve branches).branches higher)
    (point : Gaussian.Basic.Canonical) (member : Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid
      point) :
    Paths.OwnerLoopMonodromy.WindingOneLoop curve.polynomial point :=
      (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt base.bank.toBranchCellBank point
      member).toLoop

section Pair

variable {index : Fin genus}

/-- Read the original A tour's actual common lifted base vertex. -/
@[expose] def TourFaces.StandardTours.Pair.anchor
  (pair : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.Pair lifted index) : Fin
  lifted.vertices.count :=
  lifted.vertices.index _ pair.aFaces.first pair.aFaces.sheet

/-- Read the original A tour as a closed lifted walk at its retained anchor. -/
@[expose] def TourFaces.StandardTours.Pair.aVertexWalk
  (pair : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.Pair lifted index) :
  SquareRoot.Grid.Walk.Vertex.VertexWalk lifted.vertices lifted.edges pair.anchor pair.anchor :=
  pair.aFaces.vertexLoop 1 pair.aWalk_winding

/-- Transport the original B tour to the exact shared lifted anchor. -/
@[expose] def TourFaces.StandardTours.Pair.bVertexWalk
  (pair : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.Pair lifted index) :
  SquareRoot.Grid.Walk.Vertex.VertexWalk lifted.vertices lifted.edges pair.anchor pair.anchor :=
  (pair.bFaces.vertexLoop 1 pair.bWalk_winding).castVertices pair.common_base.symm pair.common_base.symm

/-- The original closed A walk retains its exact cached face word. -/
theorem
  TourFaces.StandardTours.Pair.aVertexWalk_indexed
  (pair : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.Pair lifted index) :
  pair.aVertexWalk.indexed = pair.aFaces.geometry.indexed := rfl

/-- The original closed B walk retains its exact cached face word. -/
theorem
  TourFaces.StandardTours.Pair.bVertexWalk_indexed
  (pair : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.Pair lifted index) :
  pair.bVertexWalk.indexed = pair.bFaces.geometry.indexed :=
  SquareRoot.Grid.Walk.Vertex.VertexWalk.castVertices_indexed _ pair.common_base.symm pair.common_base.symm

/-- Transporting the original point identity preserves the retained sheet's root name. -/
private theorem TourCombinations.StandardTours.Pair.frameNames_eq {first last : Gaussian.Basic.Canonical} (frames :
  RootIsolation.SquareRoot.Grid.RootFrames
  base.bank.grid)
    (equal : first = last) (firstMember : Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid first)
    (lastMember : Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid last) (sheet : Fin 2) :
    Paths.OwnerTraceReadings.ownerName ((frames.frameAt first firstMember).owners sheet) =
      Paths.OwnerTraceReadings.ownerName ((frames.frameAt last lastMember).owners sheet) := by
  cases equal
  rfl

/-- The retained anchor owner has the exact root name of the original selected frame sheet. -/
theorem TourFaces.StandardTours.Pair.anchor_owner
  (pair : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.Pair lifted index) :
    Paths.OwnerTraceReadings.ownerName (lifted.vertices.owner lifted.frames pair.anchor) =
      Paths.OwnerTraceReadings.ownerName ((lifted.frames.frameAt _ pair.aFaces.first).owners pair.aFaces.sheet) := by
  unfold SquareRoot.Grid.LiftedVertices.VertexBank.owner
    Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.Pair.anchor
  rw [lifted.vertices.sheet_index]
  exact Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCombinations.StandardTours.Pair.frameNames_eq lifted.frames
    (lifted.vertices.coordinate_index _ pair.aFaces.first pair.aFaces.sheet) _ _ _

/-- The original B forward owner is equivalent to the retained common-anchor owner. -/
theorem TourFaces.StandardTours.Pair.b_owner_aligned
  (pair : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.Pair lifted index) :
    Nonempty (Gaussian.Equivalence.NamedEquivalent
      (Paths.OwnerTraceReadings.ownerName pair.source.bTour.joined.data.forwardOwner)
      (Paths.OwnerTraceReadings.ownerName (lifted.vertices.owner lifted.frames pair.anchor))) := by
  rw [pair.anchor_owner, pair.source.bRoot_eq, ← pair.source.aRoot_eq]
  exact pair.aFaces.aligned

set_option genInjectivity false in
/-- Both the connector and its arrival sheet are retained executable data. -/
structure TourFaces.StandardTours.Pair.BasedA (pair :
  Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.Pair lifted index) (target : Fin
  lifted.vertices.count) where
  /-- The actual retained original A loop. -/ original : SquareRoot.Grid.Walk.Vertex.VertexWalk lifted.vertices
    lifted.edges pair.anchor pair.anchor
  /-- The retained loop is exactly the original pair's A walk. -/ original_eq : original = pair.aVertexWalk
  /-- The actual sheet-aware connector from the target vertex to the original A anchor. -/ connector :
    SquareRoot.Grid.Walk.Vertex.VertexWalk lifted.vertices lifted.edges target pair.anchor
  /-- The retained conjugated original A loop at the target vertex. -/ loop : SquareRoot.Grid.Walk.Vertex.VertexWalk
    lifted.vertices lifted.edges target target
  /-- The retained target loop is exactly the original connector conjugation. -/ loop_eq : loop = connector.conjugate
    original (Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCombinations.StandardTours.reference base)

constructive_injectivity TourFaces.StandardTours.Pair.BasedA

/-- Cache the original A loop and an actual sheet-aware connector to the supplied target vertex. -/
@[expose] def
  TourFaces.StandardTours.Pair.BasedA.build (pair :
  Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.Pair lifted index) (target : Fin
  lifted.vertices.count) : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.Pair.BasedA pair target
  :=
  let original := pair.aVertexWalk
  let connection := base.bank.toBranchCellBank.connectSheets lifted.edges
    (lifted.vertices.coordinate target) (lifted.vertices.coordinate pair.anchor)
    (lifted.vertices.coordinate_onGrid target) (lifted.vertices.coordinate_onGrid pair.anchor)
    (lifted.vertices.sheet target) (lifted.vertices.sheet pair.anchor)
  let connector := SquareRoot.Grid.Walk.Vertex.VertexWalk.ofLifted connection target pair.anchor rfl rfl rfl rfl
  ⟨original, rfl, connector, connector.conjugate original
    (Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCombinations.StandardTours.reference base), rfl⟩

/-- For an antisymmetric valuation, the conjugated original A loop retains the exact original A-word value. -/
theorem TourFaces.StandardTours.Pair.BasedA.value
  {pair : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.Pair lifted index} {target : Fin
  lifted.vertices.count} (based : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.Pair.BasedA pair
  target)
    (valuation : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical)
    (anti : ∀ edge, valuation edge.reverse = -valuation edge) :
    based.loop.value valuation = Topology.Surface.Sewing.SewingRetraction.wordValue valuation
      pair.aFaces.geometry.indexed := by
  rw [based.loop_eq, SquareRoot.Grid.Walk.Combinations.conjugate_value _ _ _ valuation anti, based.original_eq]
  rfl

end Pair

namespace TourCombinations.StandardTours.IntersectionBank

variable {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}

set_option genInjectivity false in
/-- Cache every based A loop and the literal signed concatenation. The
original B word and the source-row identities remain available to clients. -/
structure BShear (bank : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank lifted integral)
  (target : Fin genus)
    (weights : Data.Vector Int genus) where
  /-- The actual original A loops rebased by retained sheet-aware connectors. -/ based : Data.Vector.DependentVector
    (fun index : Fin genus => Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.Pair.BasedA
    (bank.rows.get index).pair (bank.rows.get target).pair.anchor)
  /-- The cached vector of original rebased A loops. -/ loops : Data.Vector
    (SquareRoot.Grid.Walk.Vertex.VertexWalk lifted.vertices lifted.edges (bank.rows.get target).pair.anchor
      (bank.rows.get target).pair.anchor) genus
  /-- Each cached loop is the exact corresponding retained rebased loop. -/ loops_eq : ∀ index, loops index = (based.get
    index).loop
  /-- The actual original B walk at the target anchor. -/ original : SquareRoot.Grid.Walk.Vertex.VertexWalk
    lifted.vertices lifted.edges (bank.rows.get target).pair.anchor (bank.rows.get target).pair.anchor
  /-- The retained original walk is exactly the selected row's B walk. -/ original_eq : original = (bank.rows.get
    target).pair.bVertexWalk
  /-- The actual signed concatenation of the retained A loops. -/ additions : SquareRoot.Grid.Walk.Vertex.VertexWalk
    lifted.vertices lifted.edges (bank.rows.get target).pair.anchor (bank.rows.get target).pair.anchor
  /-- The additions are the exact original finite weighted combination. -/ additions_eq : additions =
    SquareRoot.Grid.Walk.Combinations.combination
    (Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCombinations.StandardTours.reference base) loops weights
  /-- The actual retained original B walk followed by its signed A additions. -/ corrected :
    SquareRoot.Grid.Walk.Vertex.VertexWalk lifted.vertices lifted.edges (bank.rows.get target).pair.anchor
    (bank.rows.get target).pair.anchor
  /-- The corrected walk is the exact original concatenation. -/ corrected_eq : corrected = original.append additions

constructive_injectivity BShear

namespace BShear

variable {bank : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank lifted integral} {target
  : Fin genus}
  {weights : Data.Vector Int genus}

/-- Cache every original A loop at the target B anchor and form the literal retained signed concatenation. -/
@[expose] def build (bank : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank lifted
  integral) (target : Fin genus)
    (weights : Data.Vector Int genus) :
      Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCombinations.StandardTours.IntersectionBank.BShear bank target
      weights :=
  let based := Data.Vector.DependentVector.ofFn (fun index =>
    Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.Pair.BasedA.build (bank.rows.get index).pair
    (bank.rows.get target).pair.anchor)
  let loops := Data.Vector.Basic.vectorOfFn (fun index => (based.get index).loop)
  let original := (bank.rows.get target).pair.bVertexWalk
  let additions := SquareRoot.Grid.Walk.Combinations.combination
    (Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCombinations.StandardTours.reference base) loops weights
  ⟨based, loops, Data.Vector.Basic.vectorOfFn_apply _, original, rfl, additions, rfl, original.append additions, rfl⟩

/-- The actual corrected B walk reads as the original B value plus the finite integer-weighted original A values. -/
theorem value (shear :
  Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCombinations.StandardTours.IntersectionBank.BShear bank target
  weights) (valuation : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical)
    (anti : ∀ edge, valuation edge.reverse = -valuation edge) :
    shear.corrected.value valuation = Topology.Surface.Sewing.SewingRetraction.wordValue valuation (bank.rows.get
      target).pair.bFaces.geometry.indexed +
      FiniteSum.Fin.sumFin (fun index => (weights index : Gaussian.Basic.Canonical) *
        Topology.Surface.Sewing.SewingRetraction.wordValue valuation (bank.rows.get index).pair.aFaces.geometry.indexed)
        := by
  rw [shear.corrected_eq, SquareRoot.Grid.Walk.Combinations.append_value, shear.additions_eq,
    SquareRoot.Grid.Walk.Combinations.combination_value _ _ _ valuation anti, shear.original_eq]
  have original : (bank.rows.get target).pair.bVertexWalk.value valuation =
      Topology.Surface.Sewing.SewingRetraction.wordValue valuation (bank.rows.get target).pair.bFaces.geometry.indexed
        :=
    congrArg (Topology.Surface.Sewing.SewingRetraction.wordValue valuation) (bank.rows.get
      target).pair.bVertexWalk_indexed
  rw [original]
  congr 1
  apply FiniteSum.Fin.sumFin_congr
  intro index
  rw [shear.loops_eq, Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.Pair.BasedA.value
    (shear.based.get index) valuation anti]

/-- The corrected actual word consumes the original integral spans. Both
physical-boundary values and signed face corrections are retained. -/
theorem spanning_value (shear :
  Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCombinations.StandardTours.IntersectionBank.BShear bank target
  weights)
    (valuation : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical)
    (anti : ∀ edge, valuation edge.reverse = -valuation edge) :
    let generatorValue := fun column => valuation
      (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
        (lifted.cutBoundaryWord.alphabet.generators column))
    let pairedValue := fun index => Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine
      (integral.paired index) generatorValue
    shear.corrected.value valuation =
      Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine (bank.rows.get target).span.b.coefficients
        pairedValue +
      Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine (bank.rows.get target).span.b.physical
        generatorValue +
      Topology.Surface.Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces valuation
        (bank.rows.get target).coordinates.routes.b.correction +
      FiniteSum.Fin.sumFin (fun index => (weights index : Gaussian.Basic.Canonical) *
        (Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine (bank.rows.get index).span.a.coefficients
          pairedValue +
        Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine (bank.rows.get index).span.a.physical
          generatorValue +
        Topology.Surface.Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces valuation
          (bank.rows.get index).coordinates.routes.a.correction)) := by
  dsimp only
  rw [shear.value valuation anti, (bank.rows.get target).span.b_value valuation anti]
  congr 1
  apply FiniteSum.Fin.sumFin_congr
  intro index
  rw [(bank.rows.get index).span.a_value valuation anti]

set_option genInjectivity false in
/-- Prepare this very combined walk with its retained starting sheet. All
differentials and refinement stages consume the one cached preparation. -/
structure Prepared (shear :
  Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCombinations.StandardTours.IntersectionBank.BShear bank target
  weights) (source : Hyperelliptic.Differentials.Basic.Differential genus) where
  /-- The actual original root-closed period preparation of the retained corrected walk. -/ period :
    Periods.PreparedGridPeriodPrograms.PeriodWalk base.bank.grid (lifted.vertices.coordinate (bank.rows.get
    target).pair.anchor)
    (lifted.vertices.owner lifted.frames (bank.rows.get target).pair.anchor) source
  /-- The prepared period uses exactly the original retained corrected walk. -/ walk_eq : period.closed.walk =
    shear.corrected.walk

constructive_injectivity Prepared

/-- Prepare the exact retained combined walk once from its original anchor owner for all later differential readings. -/
@[expose] def prepare (shear :
  Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCombinations.StandardTours.IntersectionBank.BShear bank target
  weights) (source : Hyperelliptic.Differentials.Basic.Differential genus) :
  Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCombinations.StandardTours.IntersectionBank.BShear.Prepared shear
  source :=
  let closed := shear.corrected.rootClosed
    (Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCombinations.StandardTours.reference base _
      (lifted.vertices.coordinate_onGrid (bank.rows.get target).pair.anchor))
  ⟨Periods.PreparedGridPeriodPrograms.PeriodWalk.ofClosed closed source, rfl⟩

end BShear
end TourCombinations.StandardTours.IntersectionBank
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard
