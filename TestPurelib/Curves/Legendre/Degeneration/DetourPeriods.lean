module
import Batteries.Data.List.Basic
import Purelib.Algebra.FiniteSum.List.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBudgets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContinuedComparison.Entry
import Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Primitive
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.PreparedParentSplitSelection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
import Purelib.Riemann.Branches.ContainedPreparedPolynomialSheets
import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.Integration.Polynomial.Rectangle.Accuracy.FragmentIndex
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Nat.Order
import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Readings.RectangularPointReadings.Mesh
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RegularFaceInverseModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Primitive
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Occurrences
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Blocks
import Purelib.Riemann.RootContinuation.RootPathTransport
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.ClearBoxPaths
import Purelib.Geometry.Rational.Box.Hull
import Purelib.Geometry.Rational.Box.Point
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Clearance.Box.Region
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Block
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.SynchronizedPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CornerRequests
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Curves.Legendre.Periods.Fibre.Paired
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Sources.Assembly
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Faces.Coordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Chain.PathBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchCutCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Realization

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

open Purelib.Curves.Legendre.Periods.Jets.Specification

namespace Steps.Acquisition.Quarter.Circuit

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchCutCoordinates
open Purelib.Riemann.Meshes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider (AxisClearances)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue faceValue)
open Purelib.Topology.Surface.Boundary.BoundaryCoordinates (WordCoordinates)
open Purelib.Topology.Surface.Sewing
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Data.Vector (DependentVector)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)

variable {site : Fin 2} {parameter : Canonical}
  {circuit : Transport.Circuit site parameter} {firstInput : Input circuit.first}
  {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) firstInput.sourceEndpoint}
  {agreement : InitialAgreement firstInput.sourceEndpoint firstInput.sourceReading sourceOwner}
  {initial : Input.Realization firstInput sourceOwner agreement}
  {secondInput : Input circuit.second} {thirdInput : Input circuit.third} {fourthInput : Input circuit.fourth}

/-- The actual returned detour bank constructs its original paired genus-one words with the physical correction intact.

The retained signed execution supplies the same refined branch bank and
lifted mesh as its four actual quarter face assignments. The original
branch-loop, pair and period factories consume that cached mesh in order.
The same four retained assignments also supply their actual closed face
word through every original signed seam. Its boundary route consumes the
same canonical cut bank's retained retraction and keeps the entire signed
face correction. The original integral span consumes this same bank's
retained geometry, pairing and normal form, preserving every physical
coordinate. Six numerical banks share the same original face-domain bank
and read every saved face/sheet occurrence in its actual circuit order.
The original triangle factory consumes each normalized bank and preserves
every actual routed increment, including all six odd-power channels.
The separate waist identity
identifies the moving-zero branch pair with
the actual corrected canonical words, without identifying the signed
detour trace with that branch pair or deleting a physical boundary.
-/
private theorem retainedPaired_waist {degreeBound : Nat}
    (execution : Execution.Cache initial secondInput thirdInput fourthInput)
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (clearances : AxisClearances elimination) (frame : Paths.Frame parameter)
    {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    (bank : FramedBranchCellBank (Fibre.frameCurve frame) branches higher)
    (real : parameter.im = 0) (positive : 0 < parameter.re) (unit : parameter.re < 1) (primitiveIndex : Nat) :
    let signed := Execution.Cache.prepareSignedDetour execution elimination clearances frame bank.toBranchCellBank
    let acquired := Execution.Cache.prepareFaces execution elimination clearances frame bank signed.1 signed.2
    let incidence := acquired.incidence
    let labels := Fibre.branchLabels frame incidence.val.toBranchCellBank
    let base := FramedPuncturedGrid.ofBank incidence.val
    let lifted := acquired.mesh
    let loops := BasedBranchBank.build lifted
    let ordered := loops.ordered 0
    let paired := OrderedBranchPairs.Ordered.paired ordered
    let prepared := Paired.PeriodPrograms.prepare paired
    let waist := loops.pair (labels.val.backward 1) (labels.val.backward 0) 0
    let geometry := LiftedPuncturedGrid.Cut.build lifted
    let cut := ReferenceCutBank.build loops (labels.val.backward 0) 0 geometry
    let routed := acquired.assignments.boundaryRoute cut.retraction
    let coordinates := acquired.assignments.coordinates routed cut.geometry
    let span := acquired.assignments.spanning routed coordinates cut.geometry cut.integral cut.normal.normal
    let domains := FaceDomainBank.build lifted.frames base.faces.regulars
    let forms := Table.forms parameter
    let banks := FacePrimitiveBank.ofForms (⟨0⟩ : Hyperelliptic.Differentials.Basic.Differential 1)
      primitiveIndex domains forms
    let channelValues : Fin 6 → List Canonical := fun channel =>
      let bank := banks.get channel
      acquired.assignments.values (fun _ route => bank.edgeIncrement route)
    let readings := vectorOfFn channelValues
    let triangles := DependentVector.ofFn fun channel =>
      TrianglePrimitiveReadings.TriangleReadings.build (banks.get channel).normalize lifted.mesh
    PathEndpoints OrientedEdge.start OrientedEdge.finish acquired.assignments.word
      acquired.assignments.first.firstVertex acquired.assignments.first.firstVertex ∧
    PathEndpoints OrientedEdge.start OrientedEdge.finish routed.path
      acquired.assignments.first.firstVertex acquired.assignments.first.firstVertex ∧
    (∀ channel : Fin 6, (readings channel).length = acquired.assignments.word.length) ∧
    (∀ (channel : Fin 6) {edge : OrientedEdge lifted.vertices.count}
        (route : MeshPathWalks.EdgeRoute lifted.mesh edge),
      route.sourceEdge.increment (triangles.get channel).values = (banks.get channel).edgeIncrement route) ∧
    ∀ (value : OrientedEdge lifted.vertices.count → Canonical)
      (_anti : ∀ edge, value edge.reverse = -value edge),
      (wordValue value acquired.assignments.word = wordValue value routed.path +
        faceValue lifted.mesh.triangulation.faces value routed.correction) ∧
      (wordValue value acquired.assignments.word =
        WordCoordinates.combine span.coefficients (fun index =>
          WordCoordinates.combine (cut.integral.paired index)
            (fun column => value (VertexSewing.OrientedEdge.map
              lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column)))) +
        WordCoordinates.combine span.physical (fun column =>
          value (VertexSewing.OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
            (lifted.cutBoundaryWord.alphabet.generators column))) +
        faceValue lifted.mesh.triangulation.faces value routed.correction) ∧
      ∃ hole ∈ base.faces.holes,
        wordValue value waist.closed.indexed = wordValue value (prepared.bWord 0) -
          wordValue value (prepared.aWord 0) -
            wordValue value (hole.liftedBoundary lifted.vertices lifted.edges) := by
  intro signed acquired incidence labels base lifted loops ordered paired prepared waist geometry cut routed
    coordinates span domains forms banks channelValues readings triangles
  refine ⟨acquired.assignments.closed, acquired.assignments.boundaryRoute_closed cut.retraction, ?_, ?_, ?_⟩
  · intro channel
    exact (congrArg List.length (vectorOfFn_apply channelValues channel)).trans
      (acquired.assignments.values_length (fun _ route => (banks.get channel).edgeIncrement route))
  · intro channel edge route
    exact ((triangles.get channel).route_increment route).trans
      ((banks.get channel).normalize_edgeIncrement route)
  · intro value anti
    refine ⟨acquired.assignments.boundaryRoute_value cut.retraction value anti,
      acquired.assignments.spanning_value routed coordinates span value anti, ?_⟩
    let repeated := loops.pair (labels.val.backward 1) (labels.val.backward 1) 0
    exact Fibre.BranchLabels.waist_physical_value (base := base) (lifted := lifted) (bank := loops)
      (sheet := 0) (ordered := ordered) labels real positive unit prepared waist repeated value anti

section ConnectorHandoff

open Purelib.Geometry.Rational (Box)
open Purelib.Geometry.Rational.Box
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Clearance.Box.Region (RegionClearance)
open Purelib.Polynomial.Winding.Polygon.Basic (chainRaw)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.RootContinuation
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

section RetainedBlock

open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Geometry.Grid

variable {unitQuarter : UnitCircuitQuarter} {radiusPositive : (0 : Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 unitQuarter radiusPositive}
variable {regular : parameter ≠ criticalValue site} {current target : Endpoint}
variable {reading : ReadingAt actual current}
variable {queried : {retained : ReadingAt actual target // QueryCache actual target retained}}
variable {payment : (target.parameter - current.parameter) ^ 2 ≤
  Approximation.Rational.Geometric.Basic.quarterRadius 1 7}
variable {geometry : Geometry reading queried.val regular payment}
variable {root : OwnerAt site parameter unitQuarter radiusPositive current}
variable {agreed : InitialAgreement current reading root}
variable (block : Block queried geometry root agreed)
variable {degreeBound : Nat} {ambient : Box}
variable {elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound}
variable {clearances : AxisClearances elimination}
variable {firstAmbient : (Geometry.neighborhood site parameter regular
  (coordinate site parameter 2 unitQuarter radiusPositive current.parameter)).Refines ambient}
variable {lastAmbient : (Geometry.neighborhood site parameter regular
  (coordinate site parameter 2 unitQuarter radiusPositive target.parameter)).Refines ambient}
variable {source : Geometry.Lines elimination clearances regular
  (coordinate site parameter 2 unitQuarter radiusPositive current.parameter) firstAmbient}
variable {targetLines : Geometry.Lines elimination clearances regular
  (coordinate site parameter 2 unitQuarter radiusPositive target.parameter) lastAmbient}
variable {grid : ClearGrid (Paths.polynomial parameter) ambient}
variable {sourceOn : FromStates.ContainsVertex grid source.point}
variable {targetOn : FromStates.ContainsVertex grid targetLines.point}
variable {reference : WindingOneLoop (Paths.polynomial parameter)
    (coordinate site parameter 2 unitQuarter radiusPositive current.parameter) ⊕
  WindingOneLoop (Paths.polynomial parameter) source.point}
variable {walk : {value : Walks.Walk grid
    (Geometry.move elimination regular (coordinate site parameter 2 unitQuarter radiusPositive current.parameter))
    (Geometry.move elimination regular (coordinate site parameter 2 unitQuarter radiusPositive target.parameter)) //
  value = geometry.detourWalk elimination clearances source targetLines grid sourceOn targetOn}}
variable {supplied : Option (Block.Start root)}

/-- Retained selections in the same moved-vertex frame have equal actual sheets after the connector handoff.

Both supplied selections and both actual endpoint Owners remain inputs.
Only the derived connector comparison and the original frame's certified
distinguishability are used; no new selection is computed.
-/
private theorem retainedBlock_return_entry_sheet
    (cached : Block.DetourCache block source targetLines reference walk supplied)
    (nextClearance : RegionClearance (Paths.polynomial parameter)
      (box site parameter unitQuarter target.parameter regular))
    (targetReference : WindingOneLoop (Paths.polynomial parameter) targetLines.point)
    (enteredOwner : OwnerAt site parameter unitQuarter radiusPositive target)
    (handoff : NamedEquivalent (ownerName cached.finishOwner) (ownerName enteredOwner))
    (entered : CoveredTracedPath
      (ClearBoxPaths.Route.build nextClearance
        (coordinate site parameter 2 unitQuarter radiusPositive target.parameter) targetLines.point
        (source_inside (positive := radiusPositive) regular) targetLines.point_in_source).path
      enteredOwner)
    (frame : RootOwnerFrames.OwnerFrame ((Paths.polynomial parameter).eval targetLines.point))
    (before : RootOwnerFrames.OwnerSelection frame.owners cached.val.2.1.val.traced.finishOwner)
    (after : RootOwnerFrames.OwnerSelection frame.owners entered.traced.finishOwner) :
    after.index = before.index := by
  let related := Block.DetourCache.returnEntryEquivalent cached nextClearance targetReference
    enteredOwner handoff entered frame before after
  exact frame.distinguish _ _ (after.equivalent.symm.trans (related.trans before.equivalent))

/-- The actual cached middle joins an original following block chain through the retained endpoint tails.

The two terminal tails come from the literal stored owner paths. The original
join pays its comparison once, and the existing handoff keeps both endpoint
Owners. The original return and entry remain in the retained detour cache;
this middle-path comparison view does not identify their physical integrals.
-/
private def retainedBlock_middle_tail
    (cached : Block.DetourCache block source targetLines reference walk supplied)
    (nextClearance : RegionClearance (Paths.polynomial parameter)
      (box site parameter unitQuarter target.parameter regular))
    (targetReference : WindingOneLoop (Paths.polynomial parameter) targetLines.point)
    (enteredOwner : OwnerAt site parameter unitQuarter radiusPositive target)
    (handoff : NamedEquivalent (ownerName cached.finishOwner) (ownerName enteredOwner))
    (entered : CoveredTracedPath
      (ClearBoxPaths.Route.build nextClearance
        (coordinate site parameter 2 unitQuarter radiusPositive target.parameter) targetLines.point
        (source_inside (positive := radiusPositive) regular) targetLines.point_in_source).path
      enteredOwner)
    (frame : RootOwnerFrames.OwnerFrame ((Paths.polynomial parameter).eval targetLines.point))
    (before : RootOwnerFrames.OwnerSelection frame.owners cached.val.2.1.val.traced.finishOwner)
    (after : RootOwnerFrames.OwnerSelection frame.owners entered.traced.finishOwner)
    (middleSourceTail : OwnerTraceReadings.OwnerTail cached.val.1.val.traced.finishOwner)
    (entrySourceTail : OwnerTraceReadings.OwnerTail enteredOwner)
    {finish : Canonical} {finalOwner : Owner ((Paths.polynomial parameter).eval finish)}
    (following : CoveredTracedPath.Blocks (Paths.polynomial parameter)
      targetLines.point entered.traced.finishOwner finish finalOwner) :
    CoveredTracedPath.Blocks (Paths.polynomial parameter)
      source.point cached.val.1.val.traced.finishOwner finish finalOwner :=
  let related := Block.DetourCache.returnEntryEquivalent cached nextClearance targetReference
    enteredOwner handoff entered frame before after
  let middleTail := cached.val.2.1.val.traced.trace.get.terminalTail middleSourceTail
  let entryTail := entered.traced.trace.get.terminalTail entrySourceTail
  let joined := OwnerTraceReadings.OwnerJoin.ofTails middleTail entryTail related.symm
  .cons cached.val.2.1.val (.handoff ⟨entered.traced.finishOwner, joined⟩ following)

end RetainedBlock

end ConnectorHandoff

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid
  (OwnerWalkFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments
  (Comparisons)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels.PreparedPath.CoveredSegments
  (ParentCaches)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Polynomial.Geometry.Grid.FromStates (ContainsVertex)
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)

section RetainedMiddle

open Purelib.Riemann.RootContinuation

variable {frame : Paths.Frame parameter}
  {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
  {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
  {base : FramedPuncturedGrid (Fibre.frameCurve frame) branches higher}
  (lifted : LiftedPuncturedGrid base)
  {first last : Canonical} (walk : Walk base.bank.grid first last)
  (firstOn : ContainsVertex base.bank.grid first)
  {owner : Owner ((Fibre.frameCurve frame).polynomial.eval first)}
  (middle : CoveredTracedPath walk.path owner)

/-- Select the actual incoming middle Owner once and lift the retained anchor connector on its computed sheet.

The canonical ambient anchor and the moved source vertex remain distinct.
The backward cached target computes the anchor sheet; the original inverse
transport law proves that the same connector finishes at the actual retained
selection. No fixed starting sheet or root-identity assertion is supplied.
-/
private def retainedMiddle_anchor :
    Σ selected : RootOwnerFrames.OwnerSelection
        (lifted.frames.frameAt first firstOn).owners owner,
      Σ anchorSheet : Fin 2,
        RootIsolation.SquareRoot.Grid.RootEdgeBank.LiftedWalk lifted.edges
          (Cuts.Ambient (Fibre.frameCurve frame)).anchor anchorSheet first selected.index :=
  let selected := (lifted.frames.frameAt first firstOn).select owner
  let connector := LoopMonodromy.Grid.connect base.bank.grid
    (Cuts.Ambient (Fibre.frameCurve frame)).anchor first
    (BasedBranchTours.FramedBranchCellBank.baseMember base.bank) firstOn
  let anchorSheet := RootIsolation.SquareRoot.Grid.EdgeBank.RootEdgeBank.target
    lifted.edges connector.reverse selected.index
  ⟨selected, anchorSheet, connector,
    BasedBranchTours.FramedBranchCellBank.baseMember base.bank, firstOn,
    lifted.edges.target_reverse_right
      (fun point member => (LoopMonodromy.BranchCellBank.referenceAt base.bank.toBranchCellBank point member).toLoop)
      connector selected.index⟩

/-- The actual incoming middle Owner determines the canonical paired sheet without deleting the moving-hole term.

The retained selection and its root-grid connector determine the anchor
sheet internally. Original branch, paired-word and period factories consume
the same framed bank on that sheet; this formula does not yet identify the
whole signed detour word with the moving-zero pair.
-/
private theorem retainedMiddle_computed_waist
    (real : parameter.im = 0) (positive : 0 < parameter.re) (unit : parameter.re < 1) :
    let anchor := retainedMiddle_anchor (owner := owner) lifted firstOn
    let loops := BasedBranchBank.build lifted
    let labels := Fibre.branchLabels frame base.bank.toBranchCellBank
    let ordered := loops.ordered anchor.2.1
    let paired := OrderedBranchPairs.Ordered.paired ordered
    let prepared := Paired.PeriodPrograms.prepare paired
    let waist := loops.pair (labels.val.backward 1) (labels.val.backward 0) anchor.2.1
    ∀ (value : OrientedEdge lifted.vertices.count → Canonical)
      (_anti : ∀ edge, value edge.reverse = -value edge),
      ∃ hole ∈ base.faces.holes,
        wordValue value waist.closed.indexed = wordValue value (prepared.bWord 0) -
          wordValue value (prepared.aWord 0) -
            wordValue value (hole.liftedBoundary lifted.vertices lifted.edges) := by
  intro anchor loops labels ordered paired prepared waist value anti
  let repeated := loops.pair (labels.val.backward 1) (labels.val.backward 1) anchor.2.1
  exact Fibre.BranchLabels.waist_physical_value (base := base) (lifted := lifted) (bank := loops)
    (sheet := anchor.2.1) (ordered := ordered) labels real positive unit prepared waist repeated value anti

/-- The literal retained middle cover supplies the indexed canonical word and its actual incoming-owner alignment. -/
private theorem retainedMiddle_indexed :
    let faces := OwnerWalkFaces.build lifted.mesh walk firstOn owner
    let pieces := PreparedPathDecomposition.CoveredTracedPath.segments middle
    (faces.assign pieces).indexed = lifted.edges.indexedEdges lifted.vertices walk faces.sheet ∧
      (faces.assign pieces).OwnersAligned := by
  intro faces pieces
  exact ⟨(faces.assign_indexed pieces).trans faces.indexed_eq, faces.ownersAligned pieces⟩

/-- Actual middle comparisons consume the supplied parent caches and one shared canonical face-domain bank. -/
private theorem retainedMiddle_parents
    (domains : FaceDomainBank lifted.frames base.faces.regulars)
    (differential : Hyperelliptic.Differentials.Basic.Differential 1) (parentSheet : Fin 2) :
    let faces := OwnerWalkFaces.build lifted.mesh walk firstOn owner
    let pieces := PreparedPathDecomposition.CoveredTracedPath.segments middle
    ∀ caches : ParentCaches differential parentSheet pieces,
      let compared := faces.comparisons pieces domains differential parentSheet caches
      Comparisons.UsesDomains domains differential parentSheet (faces.assign pieces) compared ∧
        Comparisons.parentCaches differential parentSheet (faces.assign pieces) compared = caches ∧
        Comparisons.parents differential parentSheet (faces.assign pieces) compared =
          ParentCaches.parents caches := by
  intro faces pieces caches compared
  exact ⟨faces.comparisons_shared pieces domains differential parentSheet caches,
    faces.comparisons_parentCaches pieces domains differential parentSheet caches,
    faces.comparisons_parents pieces domains differential parentSheet caches⟩

section RectangularSource

open Purelib.Curves.Legendre.Periods.Jets.Source.Cell (PreparedParents)
open Purelib.Curves.Legendre.Periods.Jets.Source (Cell)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named RootChain)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents (RectangularSplits)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.Normalization.RectangularInverseModels renaming Geometry → RectangularGeometry
open Purelib.Riemann.Normalization.RegularFaceInverseModels (Clearance Bounds)
open Purelib.Riemann.Meshes.RectangularFaceModels (RectangularPatch)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment (FragmentAccuracy)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Approximation.Rational
open Purelib.Data.Rat.Fraction.Cast.Order (natCast_le_direct)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Approximation.Rational.Budget.Aggregate (countCoordinate)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBudgets (Budgets)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Branches
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts SegmentPiece)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Geometry.Rational (Box)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Data.Gaussian
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh (SegmentComparison)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh (SegmentFace)
open Purelib.Riemann.Paths.PreparedPathDecomposition (CoveredSegment)
open Purelib.Riemann.Readings
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial
open Purelib.Riemann.Normalization.TransportedFaceInverseModels (TransportedCell)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.Integration.PreparedParentSplitting (prepared_point_eq)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (traced_parent_reached)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths (EnteredPath)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

variable {basis : Hyperelliptic.Differentials.Basic.Differential 1} {parentSheet : Fin 2}
variable (cache : ParentCache middle basis parentSheet)
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish}
variable {sourceStage sourceFloor : Nat} {targets : CellEndpoints.Targets original sourceStage}

/-- The actual middle comparisons retain one saved global source product with its complete original cell list.

The original covered path supplies the segment provenance. Each comparison
keeps its exact supplied parent cache; equality transport puts the same
source preparations on those actual stored caches without another query.
-/
private theorem retainedMiddle_segment_sources
    (domains : FaceDomainBank lifted.frames base.faces.regulars)
    (saved : PreparedParents cache.covered sourceFloor targets) (channel : Fin 6) :
    let faces := OwnerWalkFaces.build lifted.mesh walk firstOn owner
    let pieces := PreparedPathDecomposition.CoveredTracedPath.segments middle
    let same := cache.parents_eq.trans
      (PreparedSegmentParentBanks.PreparedPath.CoveredSegments.parents_eq basis parentSheet pieces).symm
    let caches := ParentCaches.build basis parentSheet pieces cache.parents same cache.covered
    let compared := faces.comparisons pieces domains basis parentSheet caches
    let retained := Comparisons.parentCaches basis parentSheet (faces.assign pieces) compared
    let views := PreparedParents.segmentSources pieces cache.parents same cache.covered saved
    let transported := views.castCaches (faces.comparisons_parentCaches pieces domains basis parentSheet caches).symm
    HEq transported views ∧
      (PreparedParents.segmentCells pieces retained transported channel).flatten =
        (PreparedParents.sources cache.covered saved cache.centeredChain).cells channel := by
  intro faces pieces same caches compared retained views transported
  refine ⟨PreparedParents.OnSegments.castCaches_heq views
    (faces.comparisons_parentCaches pieces domains basis parentSheet caches).symm, ?_⟩
  exact (congrArg List.flatten (PreparedParents.OnSegments.castCaches_cells views
    (faces.comparisons_parentCaches pieces domains basis parentSheet caches).symm channel)).trans
    ((PreparedParents.segmentSources_cells pieces cache.parents same cache.covered saved channel).trans
      (PreparedParents.sources_cells cache.covered saved cache.centeredChain channel).symm)

/-- Six computed fragment requests pay the actual middle's corner sums against one original saved source bank.

The original parent and segment counts select the local allowance, then
the retained budgets select one grid index and source floor for all forms.
One saved source bank supplies the exact comparison-indexed products. The
complete cell readback retains its original sample in every strict bound.
-/
private theorem retainedMiddle_source_accuracy
    (domains : FaceDomainBank lifted.frames base.faces.regulars)
    (requests : Data.Vector {value : Rational // 0 < value} 6) (minimum : Nat) :
    let forms := Table.forms parameter
    let faces := OwnerWalkFaces.build lifted.mesh walk firstOn owner
    let pieces := PreparedPathDecomposition.CoveredTracedPath.segments middle
    let same := cache.parents_eq.trans
      (PreparedSegmentParentBanks.PreparedPath.CoveredSegments.parents_eq basis parentSheet pieces).symm
    let caches := ParentCaches.build basis parentSheet pieces cache.parents same cache.covered
    let compared := faces.comparisons pieces domains basis parentSheet caches
    let parentCount := (ParentCaches.parents
      (Comparisons.parentCaches basis parentSheet (faces.assign pieces) compared)).length
    let budgets := DependentVector.ofFn (fun channel : Fin 6 =>
      Budgets.build basis parentSheet
        (PreparedParents.CornerComparison.localTarget (requests channel).val parentCount pieces.count)
        (PreparedParents.CornerComparison.localTarget_positive (requests channel).property parentCount pieces.count)
        (faces.assign pieces) compared (some (forms channel)))
    let primitiveIndex := max minimum (budgets.maximum
      (fun _ row => Budgets.maximum basis parentSheet (faces.assign pieces) compared row))
    ∀ saved : PreparedParents cache.covered (primitiveIndex + 1) targets,
    let numerics := FacePrimitiveBank.ofForms basis primitiveIndex domains forms
    ∀ channel : Fin 6,
    Norm.Basic.normSq
        (Norm.Sum.Basic.gaussianSum
          (Cut.CornerRequests.AssignedSegments.cornerIncrements (numerics.get channel) (faces.assign pieces)) -
          (PathModel.mk ((PreparedParents.sources cache.covered saved cache.centeredChain).cells
            channel)).integralSample) < (requests channel).val := by
  intro forms faces pieces same caches compared parentCount budgets primitiveIndex saved numerics
  let views := PreparedParents.segmentSources pieces cache.parents same cache.covered saved
  let transported := views.castCaches (faces.comparisons_parentCaches pieces domains basis parentSheet caches).symm
  have below (channel : Fin 6) :
      Budgets.IndicesBelow basis parentSheet primitiveIndex (faces.assign pieces) compared (budgets.get channel) := by
    apply Budgets.indicesBelow_of_maximum_le basis parentSheet primitiveIndex (faces.assign pieces) compared
      (budgets.get channel)
    exact (budgets.get_le_maximum
      (fun _ row => Budgets.maximum basis parentSheet (faces.assign pieces) compared row) channel).trans
        (Data.Nat.Order.le_max_right _ _)
  let comparison := PreparedParents.CornerComparison.ofSources (minimum := minimum)
    (faces.comparisons_shared pieces domains basis parentSheet caches) budgets primitiveIndex
    (Data.Nat.Order.le_max_left _ _) below transported numerics
  intro channel
  have estimate := comparison.accurate channel
  change Norm.Basic.normSq
    (Norm.Sum.Basic.gaussianSum
      (Cut.CornerRequests.AssignedSegments.cornerIncrements (numerics.get channel) (faces.assign pieces)) -
        (PathModel.mk (PreparedParents.segmentCells pieces
          (Comparisons.parentCaches basis parentSheet (faces.assign pieces) compared)
          transported channel).flatten).integralSample) < (requests channel).val at estimate
  have lists := (retainedMiddle_segment_sources (lifted := lifted) (walk := walk) (firstOn := firstOn)
    (middle := middle) (cache := cache) domains saved channel).2
  change (PreparedParents.segmentCells pieces
    (Comparisons.parentCaches basis parentSheet (faces.assign pieces) compared)
    transported channel).flatten = _ at lists
  rewrite [lists] at estimate
  exact estimate

/-- The same retained geometric path produces six Stage-backed comparisons through either actual completion route.

All six fragment budgets choose one grid index before one global source
preparation and one endpoint-bank attempt. Successful old checks reuse
that Stage; otherwise the genuine closed root chain derives positional
admissions at the original occurrence keys. Both branches pass their same
saved sources and whole Stage to the shared corner attachment.
-/
private def retainedMiddle_stage_corners
    {sourceParent : CenteredEdge (Fibre.frameCurve frame) basis}
    {sourceParents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents 1 (sourceParent :: sourceParents))
    (chain : CenteredPathChain (sourceParent :: sourceParents)
      (start := Cell.PreparedParent.startPoint sourceParent)
      (finish := Cell.PreparedParent.startPoint sourceParent))
    (same : sourceParent :: sourceParents = PreparedSegmentParentBanks.PreparedPath.CoveredSegments.parents
      basis parentSheet (PreparedPathDecomposition.CoveredTracedPath.segments middle))
    (domains : FaceDomainBank lifted.frames base.faces.regulars)
    (requests : Data.Vector {value : Rational // 0 < value} 6) (minimum sourceIndex rootStage : Nat)
    {root : Named} (roots : RootChain (sourceParent :: sourceParents) root root) :
    let forms := Table.forms parameter
    let faces := OwnerWalkFaces.build lifted.mesh walk firstOn owner
    let pieces := PreparedPathDecomposition.CoveredTracedPath.segments middle
    let caches := ParentCaches.build basis parentSheet pieces (sourceParent :: sourceParents) same covered
    let compared := faces.comparisons pieces domains basis parentSheet caches
    let parentCount := (ParentCaches.parents
      (Comparisons.parentCaches basis parentSheet (faces.assign pieces) compared)).length
    let budgets := DependentVector.ofFn (fun channel : Fin 6 =>
      Budgets.build basis parentSheet
        (PreparedParents.CornerComparison.localTarget (requests channel).val parentCount pieces.count)
        (PreparedParents.CornerComparison.localTarget_positive (requests channel).property parentCount pieces.count)
        (faces.assign pieces) compared (some (forms channel)))
    let gridIndex := max minimum (budgets.maximum
      (fun _ row => Budgets.maximum basis parentSheet (faces.assign pieces) compared row))
    let targets := CellEndpoints.Targets.build chain.path sourceIndex
    let saved := Cell.prepareCovered covered (gridIndex + 1) targets
    let attempt := PreparedParents.StageAttempt.ofPrepared covered chain targets rfl saved rootStage
    (original : {actual : Jets.Source.Stage parameter
        ⟨Cell.PreparedParent.startPoint sourceParent, chain.path⟩ sourceIndex //
      actual.sources = PreparedParents.sources covered attempt.preparations chain}) ×
      {corners : PreparedParents.CornerComparison (domains := domains) (targets := targets)
          requests minimum (faces.assign pieces) compared //
        ∀ channel : Fin 6,
          Norm.Basic.normSq
            (Norm.Sum.Basic.gaussianSum (Cut.CornerRequests.AssignedSegments.cornerIncrements
                (corners.numerics.get channel) (faces.assign pieces)) -
              (PathModel.mk (original.val.sources.cells channel)).integralSample) < (requests channel).val} := by
  intro forms faces pieces caches compared parentCount budgets gridIndex targets saved attempt
  have below (channel : Fin 6) :
      Budgets.IndicesBelow basis parentSheet gridIndex (faces.assign pieces) compared (budgets.get channel) := by
    apply Budgets.indicesBelow_of_maximum_le basis parentSheet gridIndex (faces.assign pieces) compared
      (budgets.get channel)
    exact (budgets.get_le_maximum
      (fun _ row => Budgets.maximum basis parentSheet (faces.assign pieces) compared row) channel).trans
        (Data.Nat.Order.le_max_right _ _)
  let numerics := FacePrimitiveBank.ofForms basis gridIndex domains forms
  have attach (originalStage : Jets.Source.Stage parameter
      ⟨Cell.PreparedParent.startPoint sourceParent, chain.path⟩ sourceIndex)
      (exactSources : originalStage.sources = PreparedParents.sources covered attempt.preparations chain) :
      (original : {actual : Jets.Source.Stage parameter
          ⟨Cell.PreparedParent.startPoint sourceParent, chain.path⟩ sourceIndex //
        actual.sources = PreparedParents.sources covered attempt.preparations chain}) ×
        {corners : PreparedParents.CornerComparison (domains := domains) (targets := targets)
            requests minimum (faces.assign pieces) compared //
          ∀ channel : Fin 6,
            Norm.Basic.normSq
              (Norm.Sum.Basic.gaussianSum (Cut.CornerRequests.AssignedSegments.cornerIncrements
                  (corners.numerics.get channel) (faces.assign pieces)) -
                (PathModel.mk (original.val.sources.cells channel)).integralSample) < (requests channel).val} := by
    let retained := PreparedParents.CornerComparison.ofStage covered chain same
      (faces.comparisons_parentCaches pieces domains basis parentSheet caches).symm
      (faces.comparisons_shared pieces domains basis parentSheet caches)
      budgets gridIndex (Data.Nat.Order.le_max_left _ _) below attempt.preparations originalStage exactSources numerics
    exact ⟨⟨retained.1.val, (congrArg (fun stage => stage.sources) retained.1.property).trans exactSources⟩,
      ⟨retained.2.val, retained.2.property.2⟩⟩
  cases attempt.2.2.2.2.2.1 with
  | isTrue paid =>
      let completed := PreparedParents.StageAttempt.Completed.ofReady attempt paid
      have retained := PreparedParents.StageAttempt.Completion.stage_sources completed.1 completed.2
      have sameAttempt := PreparedParents.StageAttempt.Completed.ofReady_attempt attempt paid
      have sourceEq := congrArg (fun actual => PreparedParents.sources covered actual.preparations chain) sameAttempt
      exact attach completed.2.2.val (retained.trans sourceEq)
  | isFalse _ =>
      rcases attempt.completeOccurrences roots with ⟨retained, completed, sameAttempt⟩
      subst retained
      exact attach completed.stage (completed.stage_sources.trans attempt.preparations_sources.symm)

/-- The actual middle's original source bank compares with one cached rectangular splitting of its retained parents.

The same ParentCache supplies its original traced lineage, covering spine
and centered chain. Split construction reads those actual parents once;
the comparison retains all six source channels, every piece payment and
both original count factors without requesting a new source sample.
-/
private theorem retainedMiddle_rectangular_source
    (sources : PreparedParents cache.covered sourceFloor targets)
    {box prefixAmbient : Box}
    {clearance : Clearance (Paths.polynomial parameter) box} {comparisonBounds : Bounds clearance}
    {prefixPath : ClearPath (Paths.polynomial parameter) prefixAmbient first box.anchor}
    {entered : TracedPath prefixPath owner} (prefixInside : ClearPath.InBox box prefixPath)
    (reference : WindingOneLoop (Paths.polynomial parameter) first)
    (inside : ClearPath.InBox box walk.path)
    {columns rows : Nat} {geometry : RectangularGeometry columns rows} (cuts : GridCuts geometry)
    (common : RectangularPatch comparisonBounds entered.finishOwner geometry)
    (covered : ∀ position : Fin cache.parents.length,
      RectangularSegmentSplitting.Geometry.Covers geometry
        ((cache.parents[position.val]'position.isLt).edge.point 0) ∧
      RectangularSegmentSplitting.Geometry.Covers geometry
        ((cache.parents[position.val]'position.isLt).edge.point 1))
    (channel : Fin 6) (index : Nat)
    (primitives : Primitives (RectangularSheetGauge.Transitions.oriented (common.sheets.refine index).transitions
      (common.sheets.refine index).gauge)
      ((Table.forms parameter channel).numerator.scale
        (Table.forms parameter channel).scale)
      (Table.forms parameter channel).denominatorPairs)
    (overlaps : ∀ position : Fin cache.parents.length,
      ∀ piece : SegmentPiece geometry ((cache.parents[position.val]'position.isLt).edge.point 0)
        ((cache.parents[position.val]'position.isLt).edge.point 1),
      PrimitiveOverlapBounds (clearance.restrict (common.cell_refines piece.column piece.row))
        ((Table.forms parameter channel).numerator.scale
          (Table.forms parameter channel).scale)) :
    let splits := RectangularSplits.build cuts cache.parents covered
    Norm.Basic.normSq (splits.integral primitives.value -
      (PathModel.mk ((PreparedParents.sources cache.covered sources cache.centeredChain).cells
        channel)).integralSample) ≤
      splits.error (fun position piece =>
        12 * (((common.transported.cell piece.column piece.row).model.refine (index + 2)).bound +
          (((cache.covered.entry position).1.neighborhood 1).base.refine
            (sources.entry position).preparation.attached.source.selection.stage).bound) *
          (overlaps position piece).weight (Table.forms parameter channel).denominatorPairs *
            Norm.Basic.normSq (piece.lastPoint - piece.firstPoint)) := by
  intro splits
  apply PreparedParents.rectangular_integral_le cache.covered sources cache.centeredChain prefixInside reference
    common splits channel index ?_ primitives overlaps
  intro position piece _member
  let parent := cache.parents[position.val]'position.isLt
  have member : parent ∈ (CenteredPathChain.ofPreparedPath (Fibre.frameCurve frame) basis parentSheet
      middle.traced.prepared).parents := by
    rewrite [← cache.parents_eq]
    exact List.getElem_mem position.isLt
  have reached := traced_parent_reached clearance basis parentSheet middle.traced inside parent member
  have degreePositive : 0 < (Fibre.frameCurve frame).polynomial.natDegree := by
    rewrite [Fibre.frameCurve_polynomial, Paths.polynomial_natDegree]
    exact (of_decide_eq_true rfl : 0 < 3)
  have firstEq : piece.firstPoint = parent.edge.point piece.interval.lower :=
    piece.first_eq.trans (prepared_point_eq parent _).symm
  have firstInside : 0 ≤ piece.interval.lower ∧ piece.interval.lower ≤ 1 :=
    ⟨piece.within.1, piece.interval.ordered.le.trans piece.within.2⟩
  have aligned : RootAligned
      ((Model.overlapRefine (common.transported.cell piece.column piece.row).model) index)
      (parent.edge.point piece.interval.lower) (parent.edge.rootName piece.interval.lower firstInside) := by
    intro otherCount otherPatch otherInside otherSample roots otherIndex
    exact Riemann.Normalization.TransportedFaceInverseModels.TransportedCell.prepared_query_aligned
      (curve := Fibre.frameCurve frame) (entered := entered)
      (cell := common.transported.cell piece.column piece.row)
      prefixInside basis degreePositive reference parent reached piece.interval.lower firstInside
      (firstEq ▸ piece.first_inside) index otherPatch otherInside otherSample roots otherIndex
  exact @Eq.mpr _ _ (congrArg (fun point => RootAligned
    ((Model.overlapRefine (common.transported.cell piece.column piece.row).model) index)
    point (parent.edge.rootName piece.interval.lower firstInside)) firstEq) @aligned

/-- A retained entered path compares its whole six-channel source with the same saved face-split bank.

The original domain equality transports the supplied numerical cache without
rebuilding it. A positional view reads the actual mesh's split payloads, and
the retained per-parent reachability derives every local root alignment.
Both count factors and the original source stages remain in the error sum.
-/
private theorem retainedFace_source
    (domains : FaceDomainBank lifted.frames base.faces.regulars)
    (facePosition : Fin base.faces.regulars.length)
    (entered : EnteredPath (domains.get facePosition).models middle basis parentSheet)
    (domainEq : entered.domain = (domains.get facePosition).domain entered.entry.sheet)
    (sources : PreparedParents entered.cache.covered sourceFloor targets) (channel : Fin 6) (index : Nat) :
    let form := Table.forms parameter channel
    ∀ (data : DomainPrimitives ((domains.get facePosition).domain entered.entry.sheet) basis index
        (form.numerator.scale form.scale) form.denominatorPairs)
      (overlaps : ∀ position : Fin entered.cache.parents.length,
        ∀ piece : SegmentPiece entered.domain.geometry
          ((entered.cache.parents[position.val]'position.isLt).edge.point 0)
          ((entered.cache.parents[position.val]'position.isLt).edge.point 1),
        PrimitiveOverlapBounds
          ((base.faces.regulars[facePosition.val]'facePosition.isLt).clearance.restrict
            (entered.domain.patch.cell_refines piece.column piece.row)) (form.numerator.scale form.scale)),
    let shared := data.castDomain domainEq.symm
    let splits : RectangularSplits entered.domain.cuts entered.cache.parents :=
      PreparedParentSplitSelection.indexed entered.mesh.splits
    (∀ position, splits.get position = (PreparedParentSplitSelection.select entered.mesh.splits position).split) ∧
    Norm.Basic.normSq (splits.integral shared.primitives.value -
      (PathModel.mk ((PreparedParents.sources entered.cache.covered sources entered.cache.centeredChain).cells
        channel)).integralSample) ≤
      splits.error (fun position piece =>
        12 * (((entered.domain.patch.transported.cell piece.column piece.row).model.refine (index + 2)).bound +
          (((entered.cache.covered.entry position).1.neighborhood 1).base.refine
            (sources.entry position).preparation.attached.source.selection.stage).bound) *
          (overlaps position piece).weight form.denominatorPairs *
            Norm.Basic.normSq (piece.lastPoint - piece.firstPoint)) := by
  intro form data overlaps shared splits
  refine ⟨PreparedParentSplitSelection.indexed_get entered.mesh.splits, ?_⟩
  let face := base.faces.regulars[facePosition.val]'facePosition.isLt
  let anchorTrace := TracedPath.build
    (ClearPath.nil (polynomial := (Fibre.frameCurve frame).polynomial) (ambient := face.cell.box) face.cell.box.anchor)
    (.nil face.cell.box.anchor) ((domains.get facePosition).models.frame.owners entered.entry.sheet)
  apply PreparedParents.rectangular_integral_le entered.cache.covered sources entered.cache.centeredChain
    (entered := anchorTrace) face.cell.box.contains_anchor
    (LoopMonodromy.BranchCellBank.referenceAt base.bank.toBranchCellBank _
      (face.cell.anchor_mem face.member)).toLoop entered.domain.patch splits channel index ?_ shared.primitives overlaps
  intro position piece _member otherCount otherPatch otherInside otherSample roots otherIndex
  exact entered.parent_piece_aligned position piece index otherPatch otherInside otherSample roots otherIndex

/-- The actual source sample compares with mesh endpoints read from the same retained odd-power face bank.

The original four-corner bank is retained by the mesh adapter. Its saved
split sums telescope at the original path endpoints, while the existing
grid and source bounds pay their two distinct discrepancies. All six
channels use their actual numerator, inverse power and source stages.
-/
private theorem retainedFace_source_mesh
    (domains : FaceDomainBank lifted.frames base.faces.regulars)
    (facePosition : Fin base.faces.regulars.length)
    (entered : EnteredPath (domains.get facePosition).models middle basis parentSheet)
    (domainEq : entered.domain = (domains.get facePosition).domain entered.entry.sheet)
    (sources : PreparedParents entered.cache.covered sourceFloor targets) (channel : Fin 6) :
    let form := Table.forms parameter channel
    let face := base.faces.regulars[facePosition.val]'facePosition.isLt
    ∀ {target : Data.Rat.Fraction.Rational}
      {bounds : PrimitiveOverlapBounds face.clearance (form.numerator.scale form.scale)}
      (request : GridPrimitiveAccuracy bounds entered.domain.steps target form.denominatorPairs)
      (data : DomainPrimitives ((domains.get facePosition).domain entered.entry.sheet) basis request.index
        (form.numerator.scale form.scale) form.denominatorPairs)
      (overlaps : ∀ position : Fin entered.cache.parents.length,
        ∀ piece : SegmentPiece entered.domain.geometry
          ((entered.cache.parents[position.val]'position.isLt).edge.point 0)
          ((entered.cache.parents[position.val]'position.isLt).edge.point 1),
        PrimitiveOverlapBounds (face.clearance.restrict
          (entered.domain.patch.cell_refines piece.column piece.row)) (form.numerator.scale form.scale)),
    let shared := data.castDomain domainEq.symm
    let readings := PointReadings.OnMesh.build shared.corners entered.mesh.mesh.surface
    let splits : RectangularSplits entered.domain.cuts entered.cache.parents :=
      PreparedParentSplitSelection.indexed entered.mesh.splits
    readings.original = shared.corners ∧
    Norm.Basic.normSq ((readings.shared.values entered.last - readings.shared.values entered.first) -
      (PathModel.mk ((PreparedParents.sources entered.cache.covered sources entered.cache.centeredChain).cells
        channel)).integralSample) ≤
      2 * (splits.error (fun _ _ => 16 * request.globalBound) +
        splits.error (fun position piece =>
          12 * (((entered.domain.patch.transported.cell piece.column piece.row).model.refine
              (request.index + 2)).bound +
            (((entered.cache.covered.entry position).1.neighborhood 1).base.refine
              (sources.entry position).preparation.attached.source.selection.stage).bound) *
            (overlaps position piece).weight form.denominatorPairs *
              Norm.Basic.normSq (piece.lastPoint - piece.firstPoint))) := by
  intro form face target bounds request data overlaps shared readings splits
  refine ⟨readings.original_eq, ?_⟩
  let anchorTrace := TracedPath.build
    (ClearPath.nil (polynomial := (Fibre.frameCurve frame).polynomial) (ambient := face.cell.box) face.cell.box.anchor)
    (.nil face.cell.box.anchor) ((domains.get facePosition).models.frame.owners entered.entry.sheet)
  apply PreparedParents.rectangular_endpoint_le entered.cache.covered sources entered.cache.centeredChain
    (entered := anchorTrace) face.cell.box.contains_anchor
    (LoopMonodromy.BranchCellBank.referenceAt base.bank.toBranchCellBank _
      (face.cell.anchor_mem face.member)).toLoop entered.domain.patch entered.mesh splits
    (PreparedParentSplitSelection.indexed_get entered.mesh.splits) channel request ?_ shared.primitives
    readings.shared entered.first entered.last entered.first_eq entered.last_eq overlaps
  intro position piece _member otherCount otherPatch otherInside otherSample roots otherIndex
  exact entered.parent_piece_aligned position piece request.index otherPatch otherInside otherSample roots otherIndex

/-- An actual retained source parent compares with the cached primitive on its supplied face-entry sheet.

The original source neighborhood identifies its retained point with the
parent's operational root. The actual Entry supplies the face alignment;
its sheet certificate only transports the original cell index. The same
six-channel source preparation and supplied numerical primitive remain
unchanged, without requiring the complete middle path to lie in this face.
-/
private theorem retainedMiddle_face_source
    (sources : PreparedParents cache.covered sourceFloor targets)
    (position : Fin cache.parents.length)
    (domains : FaceDomainBank lifted.frames base.faces.regulars)
    (facePosition : Fin base.faces.regulars.length) (sheet : Fin 2) (channel : Fin 6) (index : Nat) :
    let parent := cache.parents[position.val]'position.isLt
    let sourcePatch := (cache.covered.entry position).1
    let prepared := sources.entry position
    let face := base.faces.regulars[facePosition.val]'facePosition.isLt
    let faceDomains := domains.get facePosition
    let domain := faceDomains.domain sheet
    let form := Table.forms parameter channel
    ∀ (piece : SegmentPiece domain.geometry (parent.edge.point 0) (parent.edge.point 1))
      (_inside : (sourcePatch.neighborhood 1).box.Contains piece.firstPoint)
      (sample : ContinuedNeighborhood.Point (sourcePatch.neighborhood 1) piece.firstPoint)
      (entry : Entry faceDomains.models piece.firstPoint sample.owner)
      (_sameSheet : entry.sheet = sheet)
      (data : DomainPrimitives domain basis index (form.numerator.scale form.scale) form.denominatorPairs)
      (overlap : PrimitiveOverlapBounds (face.clearance.restrict (domain.patch.cell_refines piece.column piece.row))
        (form.numerator.scale form.scale)),
      Norm.Basic.normSq ((data.primitives.value piece.column piece.row piece.lastPoint -
        data.primitives.value piece.column piece.row piece.firstPoint) -
        ((prepared.preparation.attached.source.primitive channel).primitive.value.eval piece.lastPoint -
          (prepared.preparation.attached.source.primitive channel).primitive.value.eval piece.firstPoint)) ≤
        12 * (((domain.patch.transported.cell piece.column piece.row).model.refine (index + 2)).bound +
          ((sourcePatch.neighborhood 1).base.refine prepared.preparation.attached.source.selection.stage).bound) *
            overlap.weight form.denominatorPairs * Norm.Basic.normSq (piece.lastPoint - piece.firstPoint) := by
  intro parent sourcePatch prepared face faceDomains domain form piece inside sample entry sameSheet data overlap
  have firstEq : piece.firstPoint = parent.edge.point piece.interval.lower :=
    piece.first_eq.trans (prepared_point_eq parent _).symm
  have firstInside : 0 ≤ piece.interval.lower ∧ piece.interval.lower ≤ 1 :=
    ⟨piece.within.1, piece.interval.ordered.le.trans piece.within.2⟩
  let names (point : Canonical) :=
    ∀ observed : ContinuedNeighborhood.Point (sourcePatch.neighborhood 1) point,
      NamedEquivalent (parent.edge.rootName piece.interval.lower firstInside) observed.certificate.value.name
  have sourceInside : (sourcePatch.neighborhood 1).box.Contains (parent.edge.point piece.interval.lower) :=
    Eq.mp (congrArg (sourcePatch.neighborhood 1).box.Contains firstEq) inside
  have atParent : names (parent.edge.point piece.interval.lower) := by
    intro observed
    exact sourcePatch.point_equivalent 1 piece.interval.lower firstInside sourceInside observed
  have atPoint : names piece.firstPoint := Eq.mpr (congrArg names firstEq) atParent
  have roots := atPoint sample
  have fromEntry : ∀ {selected : Fin 2}, entry.sheet = selected →
      (cell : TransportedCell faceDomains.models.bounds (faceDomains.models.frame.owners selected)
        (domain.geometry.box piece.column piece.row)) →
      RootAligned ((Model.overlapRefine cell.model) index) piece.firstPoint
        (OwnerTraceReadings.ownerName sample.owner) := by
    intro selected equal
    cases equal
    intro cell otherCount otherPatch otherInside otherSample otherRoots otherIndex
    exact Face.ContinuedComparison.entry_aligned entry cell basis piece.first_inside index
      otherPatch otherInside otherSample otherRoots otherIndex
  have aligned : RootAligned
      ((Model.overlapRefine (domain.patch.transported.cell piece.column piece.row).model) index)
      piece.firstPoint (parent.edge.rootName piece.interval.lower firstInside) := by
    intro otherCount otherPatch otherInside otherSample otherRoots otherIndex
    exact fromEntry sameSheet (domain.patch.transported.cell piece.column piece.row)
      otherPatch otherInside otherSample (roots.symm.trans otherRoots) otherIndex
  let entered := TracedPath.build
    (ClearPath.nil (polynomial := (Fibre.frameCurve frame).polynomial) (ambient := face.cell.box) face.cell.box.anchor)
    (.nil face.cell.box.anchor) (faceDomains.models.frame.owners sheet)
  exact prepared.rectangular_fragment_le (entered := entered) face.cell.box.contains_anchor
    (LoopMonodromy.BranchCellBank.referenceAt base.bank.toBranchCellBank _
      (face.cell.anchor_mem face.member)).toLoop domain.patch piece channel index @aligned data.primitives overlap

/-- Every original six-form segment computes an odd-power budget at a synchronized grid stage.

The actual form selects its numerator, scale and denominator power. Raising
the computed request preserves its allocation and analytic minimum while
paying both ownership and residual bounds at the retained common stage.
-/
example {segmentAmbient : Box} {segmentStart segmentFinish : Canonical}
    {segment : ClearPath.ClearSegment (Paths.polynomial parameter) segmentAmbient segmentStart segmentFinish}
    {segmentOwner : Owner ((Paths.polynomial parameter).eval segmentStart)}
    (placement : SegmentFace lifted.mesh segment) (piece : CoveredSegment segment segmentOwner)
    (compared : SegmentComparison placement piece basis parentSheet) (channel : Fin 6)
    (target : Data.Rat.Fraction.Rational) (positive : 0 < target) (minimum : Nat) :
    let form := Table.forms parameter channel
    let bounds := PrimitiveOverlapBounds.build placement.face.clearance (form.numerator.scale form.scale)
    let budget := FragmentAccuracy.build bounds compared.entered.domain.steps
      compared.entered.mesh.splits.pieceCount target positive form.denominatorPairs
    let common := max minimum budget.grid.index
    let actual := budget.atGridIndex common (Data.Nat.Order.le_max_right _ _)
    actual.grid.index = common ∧ actual.perFragment = budget.perFragment ∧
      actual.residualScale = budget.residualScale ∧ actual.minimumIndex = budget.minimumIndex ∧
      32 * actual.grid.globalBound < actual.perFragment / 2 ∧
      48 * quarterRadius (1 / 16) actual.minimumIndex * bounds.weight form.denominatorPairs *
        placement.face.cell.box.diagonalSq < actual.perFragment / 2 ∧
      countCoordinate compared.entered.mesh.splits.pieceCount *
        (countCoordinate compared.entered.mesh.splits.pieceCount * actual.perFragment) < target ∧
      ∀ position : Fin compared.entered.cache.parents.length,
        ∀ fragment : SegmentPiece compared.entered.domain.geometry
          ((compared.entered.cache.parents[position.val]'position.isLt).edge.point 0)
          ((compared.entered.cache.parents[position.val]'position.isLt).edge.point 1),
        let localBounds := bounds.restrict
          (compared.entered.domain.patch.cell_refines fragment.column fragment.row)
        localBounds.inverseUpper = bounds.inverseUpper ∧
          localBounds.weight form.denominatorPairs ≤ bounds.weight form.denominatorPairs := by
  intro form bounds budget common actual
  exact ⟨budget.atGridIndex_index common (Data.Nat.Order.le_max_right _ _), rfl, rfl, rfl,
    actual.ownership_accurate, actual.analytic_accurate, actual.full_count_accurate,
    fun _ fragment => ⟨bounds.restrict_inverseUpper _, bounds.restrict_weight_le _ form.denominatorPairs⟩⟩

/-- All six forms construct paid corner/source banks at one stage from the same original middle-path caches.

The constructor retains the actual six form budgets, one source product
and each original numerical bank. Their common stage respects the initial
floor, and each requested target is paid by the same saved observations.
-/
example (domains : FaceDomainBank lifted.frames base.faces.regulars)
    (caches : ParentCaches basis parentSheet (PreparedPathDecomposition.CoveredTracedPath.segments middle))
    (requests : Data.Vector {value : Rational // 0 < value} 6) (minimum : Nat) :
    let faces := OwnerWalkFaces.build lifted.mesh walk firstOn owner
    let pieces := PreparedPathDecomposition.CoveredTracedPath.segments middle
    let compared := faces.comparisons pieces domains basis parentSheet caches
    let actual := PreparedParents.CornerComparison.build (targets := targets) requests minimum
      (faces.assign pieces) compared (faces.comparisons_shared pieces domains basis parentSheet caches)
    minimum ≤ actual.index ∧
      (∀ channel : Fin 6, Budgets.IndicesBelow basis parentSheet actual.index (faces.assign pieces)
        compared (actual.budgets.get channel)) ∧
      ∀ channel : Fin 6,
        Norm.Basic.normSq
          (Norm.Sum.Basic.gaussianSum (Cut.CornerRequests.AssignedSegments.cornerIncrements
            (actual.numerics.get channel) (faces.assign pieces)) -
              (PathModel.mk (PreparedParents.segmentCells pieces
                (Comparisons.parentCaches basis parentSheet (faces.assign pieces) compared)
                actual.saved channel).flatten).integralSample) < (requests channel).val := by
  intro faces pieces compared actual
  exact ⟨actual.minimum_le_index, actual.indicesBelow, actual.accurate⟩

/-- An actual retained segment request constructs its ordered local source-payment certificate.

The fragment budget determines the shared bank's index and the saved source
floor. Its analytic and count bounds pay the actual residual without a
separate local estimate. The paired list retains the same original segment
occurrence and its parent-count factor for aggregate assembly.
-/
private theorem retainedSegment_payment
    {segmentAmbient : Box} {segmentStart segmentFinish : Canonical}
    {segment : ClearPath.ClearSegment (Paths.polynomial parameter) segmentAmbient segmentStart segmentFinish}
    {segmentOwner : Owner ((Paths.polynomial parameter).eval segmentStart)}
    (placement : SegmentFace lifted.mesh segment) (piece : CoveredSegment segment segmentOwner)
    (compared : SegmentComparison placement piece basis parentSheet)
    (domains : FaceDomainBank lifted.frames base.faces.regulars)
    (same : compared.domains = domains.atRoute placement.location)
    (channel : Fin 6) :
    let form := Table.forms parameter channel
    ∀ {target : Data.Rat.Fraction.Rational}
      {bounds : PrimitiveOverlapBounds placement.face.clearance (form.numerator.scale form.scale)}
      (budget : FragmentAccuracy bounds compared.entered.domain.steps
        compared.entered.mesh.splits.pieceCount target form.denominatorPairs)
      (sources : PreparedParents compared.entered.cache.covered (budget.grid.index + 1) targets)
      (bank : FacePrimitiveBank basis budget.grid.index domains
        (form.numerator.scale form.scale) form.denominatorPairs),
    List.Forall₂ (fun error payment => Norm.Basic.normSq error ≤ payment)
      [bank.edgeIncrement placement.location -
        (PathModel.mk ((PreparedParents.sources compared.entered.cache.covered sources
          compared.entered.cache.centeredChain).cells channel)).integralSample]
      [2 * ((compared.entered.cache.parents.length : Data.Rat.Fraction.Rational) + 1) * target] := by
  intro form target bounds budget sources bank
  exact List.Forall₂.cons
    (PreparedParents.segment_integral_le_accuracy placement piece compared domains same sources channel budget
      (Nat.le_refl _) bank)
    List.Forall₂.nil

end RectangularSource

end RetainedMiddle

end Steps.Acquisition.Quarter.Circuit

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
