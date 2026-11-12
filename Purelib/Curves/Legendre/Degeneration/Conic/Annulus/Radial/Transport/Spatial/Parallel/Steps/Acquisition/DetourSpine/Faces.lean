module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition
public import Purelib.Curves.Legendre.Periods.Fibre
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Geometry.Gaussian.UnitCircle.Quarter
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial

/-! # Ordered face assignments on an actual nonempty signed Steps spine

The actual retained numeric heads and signed entry/return caches supply
one ordered face assignment. Their original selected owners and
physical connectors remain indexed by the same supplied spine.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.DetourSpine

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid (OwnerWalkFaces)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider (AxisClearances)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.RootContinuation
open Purelib.RootIsolation.SquareRoot.Grid
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint finalTarget)

variable {site : Fin 2} {parameter : Canonical} {unitQuarter : UnitCircuitQuarter}
variable {radiusPositive : (0 : Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 unitQuarter radiusPositive}
variable {regular : parameter ≠ criticalValue site}
variable {frame : Paths.Frame parameter}
variable {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
variable {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
variable {base : FramedPuncturedGrid (Fibre.frameCurve frame) branches higher}
variable {degreeBound : Nat}
variable {elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound}
variable {clearances : AxisClearances elimination}
variable (lifted : LiftedPuncturedGrid base)

/-- The complete retained word view of an original signed spine with its actual nonempty target certificate.

The first and terminal actual root selections, final point and complete
owner-walk assignment are cached values. The terminal index equals the
original cached-edge transport. Only defining indices mention the
aggregate factory; construction consumes the same head and tail Walks.
-/
@[expose] def Faces
    (pointReferences : ∀ point, FromStates.ContainsVertex base.bank.grid point →
      WindingOneLoop (Paths.polynomial parameter) point)
    (targets : List Endpoint) (current : Endpoint)
    (reading : ReadingAt actual current)
    (originalOwner : OwnerAt site parameter unitQuarter radiusPositive current)
    (original : Steps actual regular current reading originalOwner targets)
    (sourceOwner : OwnerAt site parameter unitQuarter radiusPositive current)
    (agreement : InitialAgreement current reading sourceOwner)
    (paid : Acquisition original sourceOwner agreement)
    (lines : Lines paid elimination clearances)
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      FromStates.ContainsVertex base.bank.grid point)
    (heads : DetourWalkCache elimination clearances base.bank.grid paid lines onGrid)
    (supplied : Option (Block.Start sourceOwner))
    (prepared : DetourSpine elimination clearances base.bank.grid pointReferences
      targets current reading originalOwner original sourceOwner agreement
        paid lines onGrid heads supplied)
    (nonempty : targets ≠ []) :=
  let source := Geometry.Lines.Bank.head
    (elimination := elimination) (clearances := clearances) (regular := regular) lines
  let incoming := entryOwner elimination clearances base.bank.grid pointReferences
    targets current reading originalOwner original sourceOwner agreement
    paid lines onGrid heads supplied prepared nonempty
  let returned := lastReturn elimination clearances base.bank.grid pointReferences
    targets current reading originalOwner original sourceOwner agreement
    paid lines onGrid heads supplied prepared nonempty
  Σ selected : RootOwnerFrames.OwnerSelection
      (lifted.frames.frameAt source.point (onGrid source.point (List.Mem.head _))).owners incoming,
  Σ last : { value : Canonical // value = Geometry.move elimination regular
      (coordinate site parameter 2 unitQuarter radiusPositive (finalTarget current targets).parameter) },
  Σ assigned : { faces : OwnerWalkFaces lifted.mesh
        ((prepareDetourOn elimination clearances paid lines base.bank.grid onGrid).2.val.castEndpoints
          source.point_eq.symm last.property.symm) incoming //
      faces.sheet = selected.index },
    let lastOn := Eq.mpr (congrArg (FromStates.ContainsVertex base.bank.grid) last.property)
      (prepareDetourOn elimination clearances paid lines base.bank.grid onGrid).2.property
    { terminal : RootOwnerFrames.NameSelection
        (fun index => ownerName ((lifted.frames.frameAt last.val lastOn).owners index))
        (ownerName returned.2.1) //
      EdgeBank.RootEdgeBank.target lifted.edges
        ((prepareDetourOn elimination clearances paid lines base.bank.grid onGrid).2.val.castEndpoints
          source.point_eq.symm last.property.symm) assigned.val.sheet = terminal.index }

/-- The exact retained singleton signed spine is assigned once, including its true terminal Owner. -/
private def faces_single
    (pointReferences : ∀ point, FromStates.ContainsVertex base.bank.grid point →
      WindingOneLoop (Paths.polynomial parameter) point)
    (first current : Endpoint)
    (reading : ReadingAt actual current)
    (originalOwner : OwnerAt site parameter unitQuarter radiusPositive current)
    (original : Steps actual regular current reading originalOwner (first :: []))
    (sourceOwner : OwnerAt site parameter unitQuarter radiusPositive current)
    (agreement : InitialAgreement current reading sourceOwner)
    (paid : Acquisition original sourceOwner agreement)
    (lines : Lines paid elimination clearances)
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      FromStates.ContainsVertex base.bank.grid point)
    (heads : DetourWalkCache elimination clearances base.bank.grid paid lines onGrid)
    (supplied : Option (Block.Start sourceOwner))
    (prepared : DetourSpine elimination clearances base.bank.grid pointReferences
      (first :: []) current reading originalOwner original sourceOwner agreement
        paid lines onGrid heads supplied) :
    Faces lifted pointReferences [first] current reading originalOwner original
      sourceOwner agreement paid lines onGrid heads supplied prepared (by intro equal; cases equal) := by
  let source := Geometry.Lines.Bank.head
    (elimination := elimination) (clearances := clearances) (regular := regular) lines
  let suffix := Geometry.Lines.Bank.tail
    (elimination := elimination) (clearances := clearances) (regular := regular) lines
  let next := Geometry.Lines.Bank.head
    (elimination := elimination) (clearances := clearances) (regular := regular) suffix
  let cached := prepared.1
  let actualWalk := (headDetourWalk elimination clearances base.bank.grid paid lines onGrid heads).val.castEndpoints
    source.point_eq.symm next.point_eq.symm
  let selected := (lifted.frames.frameAt source.point (onGrid source.point (List.Mem.head _))).select
    (Block.DetourCache.entryOwner cached)
  let before := (lifted.frames.frameAt next.point
    (onGrid next.point (List.Mem.tail _ (List.Mem.head _)))).select
      cached.val.2.1.val.traced.finishOwner
  let left := OwnerWalkFaces.ofSelection lifted.mesh actualWalk
    (onGrid source.point (List.Mem.head _)) selected
  let right := OwnerWalkFaces.ofSelection lifted.mesh (Walks.Walk.nil next.point)
    (onGrid next.point (List.Mem.tail _ (List.Mem.head _))) before
  let related : Nonempty (NamedEquivalent (ownerName cached.val.2.1.val.traced.finishOwner)
    (ownerName cached.val.2.1.val.traced.finishOwner)) := ⟨NamedEquivalent.refl _⟩
  let joined := left.append right cached.val.2.1.val related
  have empty := prepareDetourOn_nil elimination clearances base.bank.grid paid.tail suffix
    (fun point member => onGrid point (List.Mem.tail _ member))
  have emptyCast :
      (prepareDetourOn elimination clearances paid.tail suffix base.bank.grid
        (fun point member => onGrid point (List.Mem.tail _ member))).2.val.castEndpoints
        next.point_eq.symm next.point_eq.symm = Walks.Walk.nil next.point :=
    (congrArg (fun value => value.castEndpoints next.point_eq.symm next.point_eq.symm) empty).trans
      (Walks.Walk.castEndpoints_cancel (Walks.Walk.nil next.point) next.point_eq next.point_eq)
  have same :
      (prepareDetourOn elimination clearances paid lines base.bank.grid onGrid).2.val.castEndpoints
        source.point_eq.symm next.point_eq.symm = actualWalk.append (Walks.Walk.nil next.point) :=
    (congrArg (fun value => value.castEndpoints source.point_eq.symm next.point_eq.symm)
      (prepareDetourOn_cons elimination clearances base.bank.grid paid lines onGrid heads)).trans
        ((Walks.Walk.castEndpoints_append _ _ source.point_eq.symm next.point_eq.symm
          next.point_eq.symm).trans (congrArg actualWalk.append emptyCast))
  have sheet_transport : ∀ {one two : Walks.Walk base.bank.grid source.point next.point}
      (equal : one = two) (faces : OwnerWalkFaces lifted.mesh one (Block.DetourCache.entryOwner cached)),
      (Eq.mp (congrArg (fun value => OwnerWalkFaces lifted.mesh value (Block.DetourCache.entryOwner cached))
        equal) faces).sheet =
        faces.sheet := by
    intro one two equal faces
    cases equal
    rfl
  let assigned := Eq.mp
    (congrArg (fun value => OwnerWalkFaces lifted.mesh value (Block.DetourCache.entryOwner cached)) same.symm) joined
  have assignedSheet : assigned.sheet = selected.index :=
    (sheet_transport same.symm joined).trans (left.append_sheet right cached.val.2.1.val related)
  refine ⟨selected, ⟨⟨next.point, next.point_eq⟩, ⟨⟨assigned, assignedSheet⟩, ⟨before, ?_⟩⟩⟩⟩
  have transported := congrArg₂
    (fun walk sheet => EdgeBank.RootEdgeBank.target lifted.edges walk sheet) same assignedSheet
  have appended := EdgeBank.RootEdgeBank.target_append lifted.edges actualWalk (Walks.Walk.nil next.point)
    selected.index
  exact transported.trans (appended.trans (left.target_eq right cached.val.2.1.val related))

/-- Join one literal signed head to its already retained whole tail without another assignment. -/
private def faces_cons
    (pointReferences : ∀ point, FromStates.ContainsVertex base.bank.grid point →
      WindingOneLoop (Paths.polynomial parameter) point)
    (targets : List Endpoint) (first following current : Endpoint)
    (reading : ReadingAt actual current)
    (originalOwner : OwnerAt site parameter unitQuarter radiusPositive current)
    (original : Steps actual regular current reading originalOwner (first :: following :: targets))
    (sourceOwner : OwnerAt site parameter unitQuarter radiusPositive current)
    (agreement : InitialAgreement current reading sourceOwner)
    (paid : Acquisition original sourceOwner agreement)
    (lines : Lines paid elimination clearances)
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      FromStates.ContainsVertex base.bank.grid point)
    (heads : DetourWalkCache elimination clearances base.bank.grid paid lines onGrid)
    (supplied : Option (Block.Start sourceOwner))
    (prepared : DetourSpine elimination clearances base.bank.grid pointReferences
      (first :: following :: targets) current reading originalOwner original sourceOwner agreement
        paid lines onGrid heads supplied)
    (tail : Faces lifted pointReferences (following :: targets) first original.nextReading
      original.headCovered.finishOwner original.tail paid.head.finishOwner paid.head.nextAgreement
      paid.tail (Geometry.Lines.Bank.tail
        (elimination := elimination) (clearances := clearances) (regular := regular) lines)
      (fun point member => onGrid point (List.Mem.tail _ member))
      (tailDetourWalks elimination clearances base.bank.grid paid lines onGrid heads)
      (some ⟨prepared.1.finishOwner, prepared.1.equivalent⟩) prepared.2
      (by intro equal; cases equal)) :
    Faces lifted pointReferences (first :: following :: targets) current reading originalOwner original
      sourceOwner agreement paid lines onGrid heads supplied prepared (by intro equal; cases equal) := by
  let source := Geometry.Lines.Bank.head
    (elimination := elimination) (clearances := clearances) (regular := regular) lines
  let suffix := Geometry.Lines.Bank.tail
    (elimination := elimination) (clearances := clearances) (regular := regular) lines
  let next := Geometry.Lines.Bank.head
    (elimination := elimination) (clearances := clearances) (regular := regular) suffix
  let cached := prepared.1
  let actualWalk := (headDetourWalk elimination clearances base.bank.grid paid lines onGrid heads).val.castEndpoints
    source.point_eq.symm next.point_eq.symm
  let selected := (lifted.frames.frameAt source.point (onGrid source.point (List.Mem.head _))).select
    (Block.DetourCache.entryOwner cached)
  let before := (lifted.frames.frameAt next.point
    (onGrid next.point (List.Mem.tail _ (List.Mem.head _)))).select
      cached.val.2.1.val.traced.finishOwner
  let left := OwnerWalkFaces.ofSelection lifted.mesh actualWalk
    (onGrid source.point (List.Mem.head _)) selected
  let right := tail.2.2.1.val
  let targetReference := (LoopMonodromy.BranchCellBank.referenceAt base.bank.toBranchCellBank next.point
    (onGrid next.point (List.Mem.tail _ (List.Mem.head _)))).toLoop
  let related := cached.returnEntryEquivalent original.tail.headGeometry.clearance targetReference
    cached.finishOwner (NamedEquivalent.refl (ownerName cached.finishOwner)) prepared.2.1.val.1.val
    (lifted.frames.frameAt next.point (onGrid next.point (List.Mem.tail _ (List.Mem.head _))))
      before tail.1
  let joined := left.append right cached.val.2.1.val ⟨related.symm⟩
  have same :
      (prepareDetourOn elimination clearances paid lines base.bank.grid onGrid).2.val.castEndpoints
        source.point_eq.symm tail.2.1.property.symm =
      actualWalk.append
        ((prepareDetourOn elimination clearances paid.tail suffix base.bank.grid
          (fun point member => onGrid point (List.Mem.tail _ member))).2.val.castEndpoints
            next.point_eq.symm tail.2.1.property.symm) :=
    (congrArg (fun value => value.castEndpoints source.point_eq.symm tail.2.1.property.symm)
      (prepareDetourOn_cons elimination clearances base.bank.grid paid lines onGrid heads)).trans
        (Walks.Walk.castEndpoints_append _ _ source.point_eq.symm next.point_eq.symm
          tail.2.1.property.symm)
  have sheet_transport : ∀ {one two : Walks.Walk base.bank.grid source.point tail.2.1.val}
      (equal : one = two) (faces : OwnerWalkFaces lifted.mesh one (Block.DetourCache.entryOwner cached)),
      (Eq.mp (congrArg (fun value => OwnerWalkFaces lifted.mesh value (Block.DetourCache.entryOwner cached))
        equal) faces).sheet =
        faces.sheet := by
    intro one two equal faces
    cases equal
    rfl
  let assigned := Eq.mp
    (congrArg (fun value => OwnerWalkFaces lifted.mesh value (Block.DetourCache.entryOwner cached)) same.symm) joined
  have assignedSheet : assigned.sheet = selected.index :=
    (sheet_transport same.symm joined).trans (left.append_sheet right cached.val.2.1.val ⟨related.symm⟩)
  refine ⟨selected, ⟨tail.2.1, ⟨⟨assigned, assignedSheet⟩, ⟨tail.2.2.2.val, ?_⟩⟩⟩⟩
  have transported := congrArg₂
    (fun walk sheet => EdgeBank.RootEdgeBank.target lifted.edges walk sheet) same assignedSheet
  let tailWalk := (prepareDetourOn elimination clearances paid.tail suffix base.bank.grid
    (fun point member => onGrid point (List.Mem.tail _ member))).2.val.castEndpoints
      next.point_eq.symm tail.2.1.property.symm
  have appended := EdgeBank.RootEdgeBank.target_append lifted.edges actualWalk tailWalk selected.index
  have handoff := left.target_eq right cached.val.2.1.val ⟨related.symm⟩
  have afterHandoff := congrArg (EdgeBank.RootEdgeBank.target lifted.edges tailWalk) handoff
  exact transported.trans (appended.trans (afterHandoff.trans tail.2.2.2.property))

namespace Faces

variable {lifted}
variable
    {pointReferences : ∀ point, FromStates.ContainsVertex base.bank.grid point →
      WindingOneLoop (Paths.polynomial parameter) point}
    {targets : List Endpoint} {current : Endpoint}
    {reading : ReadingAt actual current}
    {originalOwner : OwnerAt site parameter unitQuarter radiusPositive current}
    {original : Steps actual regular current reading originalOwner targets}
    {sourceOwner : OwnerAt site parameter unitQuarter radiusPositive current}
    {agreement : InitialAgreement current reading sourceOwner}
    {paid : Acquisition original sourceOwner agreement}
    {lines : Lines paid elimination clearances}
    {onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      FromStates.ContainsVertex base.bank.grid point}
    {heads : DetourWalkCache elimination clearances base.bank.grid paid lines onGrid}
    {supplied : Option (Block.Start sourceOwner)}
    {prepared : DetourSpine elimination clearances base.bank.grid pointReferences
      targets current reading originalOwner original sourceOwner agreement
        paid lines onGrid heads supplied}
    {nonempty : targets ≠ []}
variable (retained : Faces lifted pointReferences targets current reading originalOwner original
  sourceOwner agreement paid lines onGrid heads supplied prepared nonempty)

/-- Read the unchanged selected starting occurrence of this actual signed spine. -/
@[expose] def sourceSelection := retained.1

/-- Read the actual cached terminal point and its original moved-coordinate identity. -/
@[expose] def finishPoint := retained.2.1

/-- Read the complete retained ordered face assignment, including all original directed occurrences. -/
@[expose] def assignment := retained.2.2.1.val

/-- Read the cached classification of the actual terminal middle root in its retained grid frame. -/
@[expose] def terminalSelection := retained.2.2.2.val

/-- The retained face assignment starts on the original selected source index. -/
theorem assignment_sheet : retained.assignment.sheet = retained.sourceSelection.index :=
  retained.2.2.1.property

/-- The saved grid-edge transport reaches the retained actual terminal root's selected frame index. -/
theorem terminal_eq :
    EdgeBank.RootEdgeBank.target lifted.edges
      ((prepareDetourOn elimination clearances paid lines base.bank.grid onGrid).2.val.castEndpoints
        (Geometry.Lines.Bank.head
          (elimination := elimination) (clearances := clearances) (regular := regular) lines).point_eq.symm
        retained.finishPoint.property.symm) retained.assignment.sheet = retained.terminalSelection.index :=
  retained.2.2.2.property

end Faces

attribute [local irreducible] Faces Steps.Acquisition Block Geometry coordinate
  Block.DetourCache DetourWalkCache

/-- Assign the actual nonempty signed spine by its retained singleton and cons operations. -/
private def faces_consList
    (pointReferences : ∀ point, FromStates.ContainsVertex base.bank.grid point →
      WindingOneLoop (Paths.polynomial parameter) point) :
    (targets : List Endpoint) → (first current : Endpoint) →
    (reading : ReadingAt actual current) →
    (originalOwner : OwnerAt site parameter unitQuarter radiusPositive current) →
    (original : Steps actual regular current reading originalOwner (first :: targets)) →
    (sourceOwner : OwnerAt site parameter unitQuarter radiusPositive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) → (lines : Lines paid elimination clearances) →
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      FromStates.ContainsVertex base.bank.grid point) →
    (heads : DetourWalkCache elimination clearances base.bank.grid paid lines onGrid) →
    (supplied : Option (Block.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances base.bank.grid pointReferences
      (first :: targets) current reading originalOwner original sourceOwner agreement
        paid lines onGrid heads supplied) →
    Faces lifted pointReferences (first :: targets) current reading originalOwner original
      sourceOwner agreement paid lines onGrid heads supplied prepared (by intro equal; cases equal) := by
  intro targets
  induction targets with
  | nil => exact faces_single lifted pointReferences
  | cons following remaining inductionHypothesis =>
    intro first current reading originalOwner original sourceOwner agreement paid lines onGrid heads supplied prepared
    exact faces_cons lifted pointReferences remaining first following current reading originalOwner original
      sourceOwner agreement paid lines onGrid heads supplied prepared
      (inductionHypothesis following first original.nextReading
        original.headCovered.finishOwner original.tail paid.head.finishOwner paid.head.nextAgreement
        paid.tail (Geometry.Lines.Bank.tail
          (elimination := elimination) (clearances := clearances) (regular := regular) lines)
        (fun point member => onGrid point (List.Mem.tail _ member))
        (tailDetourWalks elimination clearances base.bank.grid paid lines onGrid heads)
        (some ⟨prepared.1.finishOwner, prepared.1.equivalent⟩) prepared.2)

/-- Assign a retained original Steps spine using its actual nonempty target-list certificate.

The original singleton and recursive construction consume the same paid
spine, numerical head bank and supplied signed start. The input list is
used directly; its certificate excludes only the empty case. Both saved
endpoint selections and their edge-transport law remain in the result.
-/
def faces
    (pointReferences : ∀ point, FromStates.ContainsVertex base.bank.grid point →
      WindingOneLoop (Paths.polynomial parameter) point)
    (targets : List Endpoint) (current : Endpoint)
    (reading : ReadingAt actual current)
    (originalOwner : OwnerAt site parameter unitQuarter radiusPositive current)
    (original : Steps actual regular current reading originalOwner targets)
    (sourceOwner : OwnerAt site parameter unitQuarter radiusPositive current)
    (agreement : InitialAgreement current reading sourceOwner)
    (paid : Acquisition original sourceOwner agreement)
    (lines : Lines paid elimination clearances)
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      FromStates.ContainsVertex base.bank.grid point)
    (heads : DetourWalkCache elimination clearances base.bank.grid paid lines onGrid)
    (supplied : Option (Block.Start sourceOwner))
    (prepared : DetourSpine elimination clearances base.bank.grid pointReferences
      targets current reading originalOwner original sourceOwner agreement
        paid lines onGrid heads supplied)
    (nonempty : targets ≠ []) :
    Faces lifted pointReferences targets current reading originalOwner original
      sourceOwner agreement paid lines onGrid heads supplied prepared nonempty := by
  cases targets with
  | nil => exact False.elim (nonempty rfl)
  | cons first targets =>
      exact faces_consList lifted pointReferences targets first current reading originalOwner original
        sourceOwner agreement paid lines onGrid heads supplied prepared

end Steps.Acquisition.DetourSpine

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
