module
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Realization
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.DetourSpine.Faces
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Spatial.Acquisition.DetourSpine.Faces
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider
import Purelib.Geometry.Gaussian.UnitCircle.Quarter
import Purelib.Data.Gaussian.Basic
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Chain.PathBoundary
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

/-! # Original face assignments of either actual retained quarter

The shared input selects its existing Steps or fine-piece face carrier.
Both branches consume the identical original paid realization, numeric
head cache and signed spine. Exact grid equality transports only their
indices; no substitute word or root owner is built.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.Quarter.Input.Realization.DetourSpine

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks (EdgeRoute)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Polynomial.Geometry.Grid.FromStates (ContainsVertex)
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Polynomial.Dense.Gaussian.Bounds
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider (AxisClearances)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerSelection NameSelection)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName_castOwnerParameter)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Spatial
  renaming Acquisition → LayerAcquisition

variable {site : Fin 2} {parameter : Canonical} {unitQuarter : UnitCircuitQuarter}
variable {leg : Transport.Leg site parameter unitQuarter}
variable {frame : Paths.Frame parameter} {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
variable {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
variable {base : FramedPuncturedGrid (Fibre.frameCurve frame) branches higher}
variable (lifted : LiftedPuncturedGrid base)
variable {degreeBound : Nat}
variable (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
variable (clearances : AxisClearances elimination)

attribute [local irreducible] coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- The exact original Steps or fine-piece face carrier on this same retained quarter and signed spine.

The original branch uses its intrinsic nonempty target certificate. The
fine branch retains the same original Piece indices and inherited signed
start. Both carriers keep their actual endpoint selections, ordered face
assignment and cached-edge terminal-index certificate. The supplied grid
identity reindexes those same caches to the retained lifted mesh.
-/
@[expose] def Faces
    (grid : ClearGrid (Paths.polynomial parameter) (RootRadius.Box.largeSquareBox (Paths.polynomial parameter)))
    (sameGrid : grid = base.bank.grid)
    (reference : ∀ point, ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point) :
    (input : Input leg) →
    (sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint) →
    (agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner) →
    (retained : Realization input sourceOwner agreement) →
    (lines : Lines retained elimination clearances) →
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := leg.regular) lines,
      ContainsVertex grid point) →
    (cached : DetourWalkCache elimination clearances grid retained lines onGrid) →
    (supplied : Option (Block.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances grid reference input sourceOwner agreement
      retained lines onGrid cached supplied) → Type := by
  subst grid
  exact fun
    | .inl _original, _sourceOwner, _agreement, retained, lines, onGrid, cached, supplied, prepared =>
        Steps.Acquisition.DetourSpine.Faces (frame := frame) (base := base)
          (branches := branches) (higher := higher) (actual := leg.actual) (regular := leg.regular)
          (elimination := elimination) (clearances := clearances) lifted reference
          (Quarter.originalQuarter retained).cache.val _original.current _original.reading _original.owner
          (Quarter.originalQuarter retained).steps _sourceOwner _agreement
          retained.receipt lines onGrid
          (cached.steps elimination clearances base.bank.grid retained lines onGrid) supplied prepared
          (Quarter.targets_nonempty retained)
    | .inr fine, _sourceOwner, _agreement, retained, lines, onGrid, cached, supplied, prepared =>
        LayerAcquisition.DetourSpine.Faces (frame := frame) (base := base)
          (branches := branches) (higher := higher) (actual := leg.actual) (regular := leg.regular)
          (elimination := elimination) (clearances := clearances) lifted reference
          fine.numerical.parts.remaining fine.numerical.parts.first
          (fun piece member => fine.numerical.layer.queried_of_factory fine.numerical.layer_eq
            fine.numerical.queried piece (fine.numerical.parts.remaining_member piece member))
          (fine.numerical.parts.startOwner _sourceOwner fine.numerical.layer_eq)
          (fine.numerical.parts.startAgreement _sourceOwner fine.numerical.layer_eq fine.numerical.queried _agreement)
          retained.paid lines onGrid
          (cached.numerical elimination clearances base.bank.grid retained lines onGrid)
          (Numerical.Realization.detourStart fine.numerical _sourceOwner supplied) prepared

/-- Construct the original ordered face assignment of this same actual signed quarter.

Each input branch runs its existing face fold once on the same retained
head bank. The original paid source, entry/return paths, endpoint roots
and stored selections remain in that branch's original carrier. The grid
identity reindexes those same retained inputs.
-/
def faces
    (grid : ClearGrid (Paths.polynomial parameter) (RootRadius.Box.largeSquareBox (Paths.polynomial parameter)))
    (sameGrid : grid = base.bank.grid)
    (reference : ∀ point, ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point) :
    (input : Input leg) →
    (sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint) →
    (agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner) →
    (retained : Realization input sourceOwner agreement) →
    (lines : Lines retained elimination clearances) →
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := leg.regular) lines,
      ContainsVertex grid point) →
    (cached : DetourWalkCache elimination clearances grid retained lines onGrid) →
    (supplied : Option (Block.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances grid reference input sourceOwner agreement
      retained lines onGrid cached supplied) →
    Faces lifted elimination clearances grid sameGrid reference input sourceOwner agreement
      retained lines onGrid cached supplied prepared := by
  subst grid
  exact fun
    | .inl _original, _sourceOwner, _agreement, retained, lines, onGrid, cached, supplied, prepared =>
        Steps.Acquisition.DetourSpine.faces (frame := frame) (base := base)
          (branches := branches) (higher := higher) (actual := leg.actual) (regular := leg.regular)
          (elimination := elimination) (clearances := clearances) lifted reference
          (Quarter.originalQuarter retained).cache.val _original.current _original.reading _original.owner
          (Quarter.originalQuarter retained).steps _sourceOwner _agreement
          retained.receipt lines onGrid
          (cached.steps elimination clearances base.bank.grid retained lines onGrid) supplied prepared
          (Quarter.targets_nonempty retained)
    | .inr fine, _sourceOwner, _agreement, retained, lines, onGrid, cached, supplied, prepared =>
        LayerAcquisition.DetourSpine.faces (frame := frame) (base := base)
          (branches := branches) (higher := higher) (actual := leg.actual) (regular := leg.regular)
          (elimination := elimination) (clearances := clearances) lifted reference
          fine.numerical.parts.remaining fine.numerical.parts.first
          (fun piece member => fine.numerical.layer.queried_of_factory fine.numerical.layer_eq
            fine.numerical.queried piece (fine.numerical.parts.remaining_member piece member))
          (fine.numerical.parts.startOwner _sourceOwner fine.numerical.layer_eq)
          (fine.numerical.parts.startAgreement _sourceOwner fine.numerical.layer_eq fine.numerical.queried _agreement)
          retained.paid lines onGrid
          (cached.numerical elimination clearances base.bank.grid retained lines onGrid)
          (Numerical.Realization.detourStart fine.numerical _sourceOwner supplied) prepared

namespace Faces

open Steps.Acquisition.DetourSpine renaming Faces → StepFaces
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement
open Layer.Spatial.Acquisition.DetourSpine renaming Faces → PieceFaces
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid (OwnerWalkFaces)
open Purelib.Topology.Polygon.Stokes (OrientedEdge triangleEdgeOccurrences)
open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Topology.Surface.Cut.JumpPaths

variable {lifted elimination clearances}
variable {grid : ClearGrid (Paths.polynomial parameter) (RootRadius.Box.largeSquareBox (Paths.polynomial parameter))}
variable {sameGrid : grid = base.bank.grid}
variable {reference : ∀ point, ContainsVertex grid point → WindingOneLoop (Paths.polynomial parameter) point}
variable {input : Input leg}
variable {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint}
variable {agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner}
variable {retained : Realization input sourceOwner agreement}
variable {lines : Lines retained elimination clearances}
variable {onGrid : ∀ point ∈ Geometry.Lines.Bank.points
  (elimination := elimination) (clearances := clearances) (regular := leg.regular) lines,
  ContainsVertex grid point}
variable {cached : DetourWalkCache elimination clearances grid retained lines onGrid}
variable {supplied : Option (Block.Start sourceOwner)}
variable {prepared : DetourSpine elimination clearances grid reference input sourceOwner agreement
  retained lines onGrid cached supplied}
variable (value : Faces lifted elimination clearances grid sameGrid reference input sourceOwner agreement
  retained lines onGrid cached supplied prepared)

/-- The original selected source-frame index retained by this actual quarter face assignment. -/
@[expose] def sourceIndex : Fin 2 := by
  subst grid
  cases input with
  | inl original =>
      exact (StepFaces.sourceSelection (frame := frame) (base := base) value).index
  | inr fine =>
      exact (PieceFaces.sourceSelection (frame := frame) (base := base) value).index

/-- The actual terminal-root frame index cached by the same original quarter fold. -/
@[expose] def terminalIndex : Fin 2 := by
  subst grid
  cases input with
  | inl original =>
      exact (StepFaces.terminalSelection (frame := frame) (base := base) value).index
  | inr fine =>
      exact (PieceFaces.terminalSelection (frame := frame) (base := base) value).index

/-- The complete unchanged ordered indexed word of this original quarter face assignment. -/
@[expose] def word : List (OrientedEdge lifted.vertices.count) := by
  subst grid
  cases input with
  | inl original =>
      exact (StepFaces.assignment (frame := frame) (base := base) value).geometry.indexed
  | inr fine =>
      exact (PieceFaces.assignment (frame := frame) (base := base) value).geometry.indexed

/-- Read the actual saved face route of every quarter occurrence in its original order.

The callback receives the same indexed edge and retained face/sheet route.
No edge lookup, path preparation or root selection is repeated, and route
choices remain available to numerical primitive-bank consumers.
-/
@[expose] def values {α : Type} (read : (edge : OrientedEdge lifted.vertices.count) → EdgeRoute lifted.mesh edge → α) :
    List α := by
  subst grid
  cases input with
  | inl original =>
      exact (StepFaces.assignment (frame := frame) (base := base) value).geometry.values read
  | inr fine =>
      exact (PieceFaces.assignment (frame := frame) (base := base) value).geometry.values read

/-- Every original indexed quarter occurrence contributes one retained face-route reading. -/
theorem values_length {α : Type}
    (read : (edge : OrientedEdge lifted.vertices.count) → EdgeRoute lifted.mesh edge → α) :
    (value.values read).length = value.word.length := by
  subst grid
  cases input with
  | inl original =>
      exact (StepFaces.assignment (frame := frame) (base := base) value).geometry.values_length read
  | inr fine =>
      exact (PieceFaces.assignment (frame := frame) (base := base) value).geometry.values_length read

/-- Every original directed occurrence of the retained quarter face word lies on the same lifted triangulation. -/
theorem supported : CutPath.Supported (triangleEdgeOccurrences
    lifted.mesh.triangulation.faces) value.word := by
  subst grid
  cases input with
  | inl original =>
      exact OwnerWalkFaces.supported (StepFaces.assignment (frame := frame) (base := base) value)
  | inr fine =>
      exact OwnerWalkFaces.supported (PieceFaces.assignment (frame := frame) (base := base) value)

/-- The actual cached last point with its original physical moved-endpoint certificate. -/
@[expose] def finishPoint : { point : Canonical // point = Geometry.move elimination leg.regular
    (Transport.Spatial.coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl)
      retained.finishEndpoint.parameter) } := by
  subst grid
  cases input with
  | inl original =>
      exact StepFaces.finishPoint (frame := frame) (base := base) value
  | inr fine =>
      exact PieceFaces.finishPoint (frame := frame) (base := base) value

/-- The original initial lifted vertex of the same retained ordered quarter word. -/
@[expose] def firstVertex : Fin lifted.vertices.count := by
  subst grid
  cases input with
  | inl original =>
      let assigned := StepFaces.assignment (frame := frame) (base := base) value
      let source := Geometry.Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := leg.regular) lines
      exact lifted.vertices.index source.point assigned.first assigned.sheet
  | inr fine =>
      let assigned := PieceFaces.assignment (frame := frame) (base := base) value
      let source := Geometry.Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := leg.regular) lines
      exact lifted.vertices.index source.point assigned.first assigned.sheet

/-- The original cached terminal point belongs to the same retained numeric grid. -/
theorem finishPoint_onGrid : ContainsVertex grid value.finishPoint.val :=
  Eq.mpr (congrArg (ContainsVertex grid) value.finishPoint.property)
    (Input.Realization.prepareDetourOn retained elimination clearances lines grid onGrid).2.property

/-- The original final lifted vertex on the same cached terminal root selection. -/
@[expose] def lastVertex : Fin lifted.vertices.count := by
  subst grid
  exact lifted.vertices.index value.finishPoint.val value.finishPoint_onGrid value.terminalIndex

/-- The same retained quarter word runs from its actual initial vertex to its cached terminal-root vertex.

The original owner-walk endpoint certificate supplies the indexed path.
Its saved terminal-index equality replaces the edge target by the same
retained final selection, preserving every directed edge occurrence.
-/
theorem endpoints : PathEndpoints OrientedEdge.start OrientedEdge.finish value.word
    value.firstVertex value.lastVertex := by
  subst grid
  cases input with
  | inl original =>
      let assigned := StepFaces.assignment (frame := frame) (base := base) value
      let point := StepFaces.finishPoint (frame := frame) (base := base) value
      have member : ContainsVertex base.bank.grid point.val := value.finishPoint_onGrid
      have actual := OwnerWalkFaces.endpoints assigned member
      exact actual.castFinish (congrArg (lifted.vertices.index point.val member)
        (StepFaces.terminal_eq (frame := frame) (base := base) value))
  | inr fine =>
      let assigned := PieceFaces.assignment (frame := frame) (base := base) value
      let point := PieceFaces.finishPoint (frame := frame) (base := base) value
      have member : ContainsVertex base.bank.grid point.val := value.finishPoint_onGrid
      have actual := OwnerWalkFaces.endpoints assigned member
      exact actual.castFinish (congrArg (lifted.vertices.index point.val member)
        (PieceFaces.terminal_eq (frame := frame) (base := base) value))

/-- The original cached source-line point of the same actual quarter face assignment. -/
@[expose] def sourcePoint : Canonical := by
  cases input with
  | inl original =>
      exact (Geometry.Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := leg.regular) lines).point
  | inr fine =>
      exact (Geometry.Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := leg.regular) lines).point

/-- The cached source point belongs to the same retained framed grid as its face word. -/
theorem sourcePoint_onGrid : ContainsVertex base.bank.grid value.sourcePoint := by
  subst grid
  cases input with
  | inl original => exact onGrid _ (List.Mem.head _)
  | inr fine => exact onGrid _ (List.Mem.head _)

/-- The original cached first point is the moved physical source of this same paid quarter. -/
theorem sourcePoint_eq : value.sourcePoint = Geometry.move elimination leg.regular
    (Transport.Spatial.coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl)
      input.sourceEndpoint.parameter) := by
  cases input with
  | inl original =>
      exact (Geometry.Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := leg.regular) lines).point_eq
  | inr fine =>
      exact (Geometry.Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := leg.regular) lines).point_eq.trans
        (congrArg (fun time => Geometry.move elimination leg.regular
          (Transport.Spatial.coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) time))
          (fine.numerical.parts.start_time fine.numerical.layer_eq))

/-- Read the original source selection at its cached grid point with the same moved-root name.

The existing parameter-cast readback laws transport only the queried name.
The actual saved index and operational equivalence remain unchanged;
no frame classification or root acquisition is performed.
-/
@[expose] def sourceSelection :
    { selected : NameSelection
        (fun index => ownerName ((lifted.frames.frameAt value.sourcePoint value.sourcePoint_onGrid).owners index))
        (ownerName (middleSource elimination clearances grid reference input sourceOwner agreement
          retained lines onGrid cached supplied prepared)) // selected.index = value.sourceIndex } := by
  subst grid
  cases input with
  | inl original =>
      let selected := StepFaces.sourceSelection (frame := frame) (base := base) value
      have nameEq := Steps.Acquisition.DetourSpine.middleSource_name
        elimination clearances base.bank.grid reference
        (Quarter.originalQuarter retained).cache.val original.current original.reading original.owner
        (Quarter.originalQuarter retained).steps sourceOwner agreement retained.receipt lines onGrid
        (cached.steps elimination clearances base.bank.grid retained lines onGrid) supplied prepared
        (Quarter.targets_nonempty retained)
      exact ⟨⟨selected.index, NamedEquivalent.transport nameEq.symm rfl selected.equivalent⟩, (rfl)⟩
  | inr fine =>
      let selected := PieceFaces.sourceSelection (frame := frame) (base := base) value
      have nameEq := LayerAcquisition.DetourSpine.middleSource_name
        elimination clearances base.bank.grid reference
        fine.numerical.parts.remaining fine.numerical.parts.first
        (fun piece member => fine.numerical.layer.queried_of_factory fine.numerical.layer_eq
          fine.numerical.queried piece (fine.numerical.parts.remaining_member piece member))
        (fine.numerical.parts.startOwner sourceOwner fine.numerical.layer_eq)
        (fine.numerical.parts.startAgreement sourceOwner fine.numerical.layer_eq fine.numerical.queried agreement)
        retained.paid lines onGrid
        (cached.numerical elimination clearances base.bank.grid retained lines onGrid)
        (Numerical.Realization.detourStart fine.numerical sourceOwner supplied) prepared
      let original := LayerAcquisition.DetourSpine.middleSource
        elimination clearances base.bank.grid reference
        fine.numerical.parts.remaining fine.numerical.parts.first
        (fun piece member => fine.numerical.layer.queried_of_factory fine.numerical.layer_eq
          fine.numerical.queried piece (fine.numerical.parts.remaining_member piece member))
        (fine.numerical.parts.startOwner sourceOwner fine.numerical.layer_eq)
        (fine.numerical.parts.startAgreement sourceOwner fine.numerical.layer_eq fine.numerical.queried agreement)
        retained.paid lines onGrid
        (cached.numerical elimination clearances base.bank.grid retained lines onGrid)
        (Numerical.Realization.detourStart fine.numerical sourceOwner supplied) prepared
      let parameterEq := congrArg (fun time : Rational => (Paths.polynomial parameter).eval
        (Geometry.move elimination leg.regular
          (Transport.Spatial.coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) time)))
        (fine.numerical.parts.start_time fine.numerical.layer_eq)
      have castName : ownerName (middleSource elimination clearances base.bank.grid reference
          (.inr fine) sourceOwner agreement retained lines onGrid cached supplied prepared) =
          ownerName original := by
        with_unfolding_all exact ownerRootName_castOwnerParameter parameterEq original
      exact ⟨⟨selected.index,
        NamedEquivalent.transport (castName.trans nameEq).symm rfl selected.equivalent⟩, (rfl)⟩

/-- Reading the source selection preserves the same originally cached frame index. -/
theorem sourceSelection_index : value.sourceSelection.val.index = value.sourceIndex :=
  value.sourceSelection.property

/-- The actual first lifted vertex uses the original source point and saved source-selection index. -/
theorem firstVertex_eq : value.firstVertex =
    lifted.vertices.index value.sourcePoint value.sourcePoint_onGrid value.sourceIndex := by
  subst grid
  cases input with
  | inl original =>
      exact congrArg (lifted.vertices.index _ _)
        (StepFaces.assignment_sheet (frame := frame) (base := base) value)
  | inr fine =>
      exact congrArg (lifted.vertices.index _ _)
        (PieceFaces.assignment_sheet (frame := frame) (base := base) value)

/-- The original terminal point belongs to the framed mesh through its retained grid identity. -/
theorem finishPoint_inMesh : ContainsVertex base.bank.grid value.finishPoint.val :=
  Eq.mp (congrArg (fun grid => ContainsVertex grid value.finishPoint.val) sameGrid) value.finishPoint_onGrid

/-- Read the saved terminal selection on the actual original quarter return's middle-root name.

The whole original return view supplies that same name in each input
branch. The cached terminal point, frame, index and operational comparison
are the original values of the existing face carrier.
-/
@[expose] def terminalSelection : NameSelection
    (fun index => ownerName ((lifted.frames.frameAt value.finishPoint.val value.finishPoint_inMesh).owners index))
    (ownerName (lastReturn elimination clearances grid reference input sourceOwner agreement
      retained lines onGrid cached supplied prepared).2.1) := by
  subst grid
  cases input with
  | inl original => exact StepFaces.terminalSelection (frame := frame) (base := base) value
  | inr fine => exact PieceFaces.terminalSelection (frame := frame) (base := base) value

/-- Reading the terminal selection keeps its original cached terminal frame index. -/
theorem terminalSelection_index : value.terminalSelection.index = value.terminalIndex := by
  subst grid
  cases input <;> rfl

/-- The actual terminal and next-entry face vertices agree through the same retained seam and connector comparison.

Both face words keep their original root selections. The actual start
handoff and the two saved connector windings compare those names in one
retained grid frame, whose distinguishing law forces their saved indices
to agree. Exact point transport then identifies the actual lifted vertices.
-/
theorem nextVertex_eq
    {nextQuarter : UnitCircuitQuarter} {nextLeg : Transport.Leg site parameter nextQuarter}
    (next : Input nextLeg) (directions : Waist.direction unitQuarter 1 = Waist.direction nextQuarter 0)
    (stored : Transport.Seam leg nextLeg)
    (seam : Transport.Seam.Receipt (left := leg) (right := nextLeg) retained.finishReading next.sourceReading
      retained.finishOwner retained.finishEquivalent retained.finish_time next.source_time directions stored)
    (nextOwner : OwnerAt site parameter nextQuarter (of_decide_eq_true rfl) next.sourceEndpoint)
    (nextAgreement : InitialAgreement next.sourceEndpoint next.sourceReading nextOwner)
    (nextRetained : Realization next nextOwner nextAgreement)
    (nextLines : Lines nextRetained elimination clearances)
    (nextOnGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := nextLeg.regular) nextLines,
      ContainsVertex grid point)
    (nextCached : DetourWalkCache elimination clearances grid nextRetained nextLines nextOnGrid)
    (nextSupplied : Option (Block.Start nextOwner))
    (nextPrepared : DetourSpine elimination clearances grid reference next nextOwner nextAgreement
      nextRetained nextLines nextOnGrid nextCached nextSupplied)
    (handoff : NamedEquivalent
      (ownerName (nextStart elimination clearances grid reference retained lines onGrid cached supplied
        prepared next directions stored seam).1)
      (ownerName (Block.Start.owner (site := site) (parameter := parameter) (unitQuarter := nextQuarter)
        (positive := of_decide_eq_true rfl) (current := next.sourceEndpoint) nextOwner nextSupplied)))
    (following : Faces lifted elimination clearances grid sameGrid reference next nextOwner nextAgreement
      nextRetained nextLines nextOnGrid nextCached nextSupplied nextPrepared) :
    value.lastVertex = following.firstVertex := by
  subst grid
  let returned := nextReturn elimination clearances base.bank.grid reference retained lines onGrid cached supplied
    prepared next directions stored seam
  have pointEq := Transport.Seam.point_eq (site := site) (parameter := parameter)
    (leftQuarter := unitQuarter) (rightQuarter := nextQuarter)
    retained.finish_time next.source_time directions
  have terminalAtReturn : value.finishPoint.val = returned.1.val :=
    value.finishPoint.property.trans
      ((congrArg (Geometry.move elimination leg.regular) pointEq).trans returned.1.property.symm)
  have sourceAtReturn : following.sourcePoint = returned.1.val :=
    following.sourcePoint_eq.trans returned.1.property.symm
  have member : ContainsVertex base.bank.grid returned.1.val :=
    Eq.mp (congrArg (ContainsVertex base.bank.grid) terminalAtReturn) value.finishPoint_inMesh
  let common := lifted.frames.frameAt returned.1.val member
  let before : OwnerSelection common.owners returned.2.1 :=
    ⟨value.terminalSelection.index,
      NamedEquivalent.transport rfl
        (StandardTours.frameNames_eq (base := base) lifted.frames terminalAtReturn
          value.finishPoint_inMesh member value.terminalSelection.index) value.terminalSelection.equivalent⟩
  let after : NameSelection (fun index => ownerName (common.owners index))
      (ownerName (middleSource elimination clearances base.bank.grid reference next nextOwner nextAgreement
        nextRetained nextLines nextOnGrid nextCached nextSupplied nextPrepared)) :=
    ⟨following.sourceSelection.val.index,
      NamedEquivalent.transport rfl
        (StandardTours.frameNames_eq (base := base) lifted.frames sourceAtReturn
          following.sourcePoint_onGrid member following.sourceSelection.val.index)
        following.sourceSelection.val.equivalent⟩
  have compared := nextEntryEquivalent elimination clearances base.bank.grid reference retained lines onGrid cached
    supplied prepared next directions stored seam nextOwner nextAgreement nextRetained nextLines nextOnGrid
    nextCached nextSupplied nextPrepared handoff common before after
  have selected : value.terminalSelection.index = following.sourceSelection.val.index :=
    (common.distinguish after.index before.index
      ((after.equivalent.symm.trans compared).trans before.equivalent)).symm
  have sheets : value.terminalIndex = following.sourceIndex :=
    value.terminalSelection_index.symm.trans (selected.trans following.sourceSelection_index)
  have points : (⟨value.finishPoint.val, value.finishPoint_inMesh⟩ :
      { point : Canonical // ContainsVertex base.bank.grid point }) =
      ⟨following.sourcePoint, following.sourcePoint_onGrid⟩ :=
    Subtype.ext (terminalAtReturn.trans sourceAtReturn.symm)
  have verticesEq := congrArg₂
    (fun (point : { point : Canonical // ContainsVertex base.bank.grid point }) (sheet : Fin 2) =>
      lifted.vertices.index point.val point.property sheet) points sheets
  exact verticesEq.trans following.firstVertex_eq.symm

end Faces

end Steps.Acquisition.Quarter.Input.Realization.DetourSpine

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
