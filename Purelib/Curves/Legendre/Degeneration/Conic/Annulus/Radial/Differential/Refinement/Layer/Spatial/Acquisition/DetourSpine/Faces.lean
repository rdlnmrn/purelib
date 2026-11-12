module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Spatial.Acquisition
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
import Purelib.Approximation.AccuracyRequest
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Piece
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Bounds

/-! # Ordered face assignments on an actual signed fine-piece spine

The actual retained numeric heads and signed entry/return caches supply
one ordered face assignment. Their original selected owners and
physical connectors remain indexed by the same supplied spine.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer

namespace Spatial.Acquisition.DetourSpine

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

open Purelib.Approximation (AccuracyRequest)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint)
open Transport.Spatial
open Transport.Spatial.Parallel
open Transport.Spatial.Parallel.Steps.Acquisition renaming Block → StepBlock
open Purelib.Polynomial.Geometry

variable {radicand : CoefficientPolynomial}
variable {site : Fin 2} {parameter : Canonical} {differential : OddPowerDifferential radicand}
variable {data : Waist.Differential.Bounds.Data site parameter differential}
variable {quarter : UnitCircuitQuarter} {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive} {accuracy : AccuracyRequest}
variable {regular : parameter ≠ criticalValue site} {finish : Endpoint}
variable {finishQuery : { reading : ReadingAt actual finish // QueryCache actual finish reading }}
variable {degreeBound : Nat}
variable {elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound}
variable {clearances : AxisClearances elimination}
variable {frame : Paths.Frame parameter} {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
variable {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
variable {base : FramedPuncturedGrid (Fibre.frameCurve frame) branches higher}
variable (lifted : LiftedPuncturedGrid base)

/-- An ordered fine-spine face assignment retains its actual source and terminal root selections.

The same supplied signed spine and numerical head bank determine every
occurrence. The final classification is stored once on the actual returned
middle owner, with its index equal to the original cached-edge transport.
-/
@[expose] def Faces
    (pointReferences : ∀ point, Grid.FromStates.ContainsVertex base.bank.grid point →
      WindingOneLoop (Paths.polynomial parameter) point)
    (remaining : List (Piece data actual accuracy)) (first : Piece data actual accuracy)
    (queried : ∀ piece ∈ remaining, piece.Queried)
    (sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint)
    (agreement : Parallel.Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner)
    (paid : Acquisition regular finishQuery remaining first queried sourceOwner agreement)
    (lines : Lines paid elimination clearances)
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex base.bank.grid point)
    (heads : DetourWalkCache elimination clearances base.bank.grid paid lines onGrid)
    (supplied : Option (StepBlock.Start sourceOwner))
    (prepared : DetourSpine elimination clearances base.bank.grid pointReferences
      remaining first queried sourceOwner agreement paid lines onGrid heads supplied) :=
  let source := Geometry.Lines.Bank.head
    (elimination := elimination) (clearances := clearances) (regular := regular) lines
  let incoming := entryOwner elimination clearances base.bank.grid pointReferences
    remaining first queried sourceOwner agreement paid lines onGrid heads supplied prepared
  let returned := lastReturn elimination clearances base.bank.grid pointReferences
    remaining first queried sourceOwner agreement paid lines onGrid heads supplied prepared
  Σ selected : RootOwnerFrames.OwnerSelection
      (lifted.frames.frameAt source.point (onGrid source.point (List.Mem.head _))).owners incoming,
  Σ last : { value : Canonical // value = Geometry.move elimination regular
      (Transport.Spatial.coordinate site parameter 2 quarter positive finish.parameter) },
  Σ assigned : { faces : OwnerWalkFaces lifted.mesh
        ((prepareDetourOn elimination clearances paid lines base.bank.grid onGrid).2.val.castEndpoints
          source.point_eq.symm last.property.symm) incoming // faces.sheet = selected.index },
    let lastOn := Eq.mpr (congrArg (Grid.FromStates.ContainsVertex base.bank.grid) last.property)
      (prepareDetourOn elimination clearances paid lines base.bank.grid onGrid).2.property
    { terminal : RootOwnerFrames.NameSelection
        (fun index => ownerName ((lifted.frames.frameAt last.val lastOn).owners index))
        (ownerName returned.2.1) //
      EdgeBank.RootEdgeBank.target lifted.edges
        ((prepareDetourOn elimination clearances paid lines base.bank.grid onGrid).2.val.castEndpoints
          source.point_eq.symm last.property.symm) assigned.val.sheet = terminal.index }

/-- Assign the original fine singleton's literal saved final head on its actual selected incoming sheet. -/
private def faces_single
    (pointReferences : ∀ point, Grid.FromStates.ContainsVertex base.bank.grid point →
      WindingOneLoop (Paths.polynomial parameter) point)
    (first : Piece data actual accuracy) (queried : ∀ piece ∈ ([] : List (Piece data actual accuracy)), piece.Queried)
    (sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint)
    (agreement : Parallel.Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner)
    (paid : Acquisition regular finishQuery [] first queried sourceOwner agreement)
    (lines : Lines paid elimination clearances)
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex base.bank.grid point)
    (heads : DetourWalkCache elimination clearances base.bank.grid paid lines onGrid)
    (supplied : Option (StepBlock.Start sourceOwner))
    (prepared : DetourSpine elimination clearances base.bank.grid pointReferences
      [] first queried sourceOwner agreement paid lines onGrid heads supplied) :
    Faces lifted pointReferences [] first queried sourceOwner agreement paid lines onGrid
      heads supplied prepared := by
  let source := Geometry.Lines.Bank.head
    (elimination := elimination) (clearances := clearances) (regular := regular) lines
  let suffix := Geometry.Lines.Bank.tail
    (elimination := elimination) (clearances := clearances) (regular := regular) lines
  let last := Geometry.Lines.Bank.head
    (elimination := elimination) (clearances := clearances) (regular := regular) suffix
  let incoming := StepBlock.DetourCache.entryOwner prepared
  let selected := (lifted.frames.frameAt source.point (onGrid source.point (List.Mem.head _))).select incoming
  let actualWalk := (lastDetourWalk elimination clearances base.bank.grid paid lines onGrid heads).val.castEndpoints
    source.point_eq.symm last.point_eq.symm
  let faces := OwnerWalkFaces.ofSelection lifted.mesh actualWalk
    (onGrid source.point (List.Mem.head _)) selected
  have same : (prepareDetourOn elimination clearances paid lines base.bank.grid onGrid).2.val.castEndpoints
      source.point_eq.symm last.point_eq.symm = actualWalk :=
    congrArg (fun value => value.castEndpoints source.point_eq.symm last.point_eq.symm)
      (prepareDetourOn_last elimination clearances base.bank.grid paid lines onGrid heads)
  have sheet_transport : ∀ {one two : Grid.Walks.Walk base.bank.grid source.point last.point}
      (equal : one = two) (old : OwnerWalkFaces lifted.mesh one incoming),
      (Eq.mp (congrArg (fun value => OwnerWalkFaces lifted.mesh value incoming) equal) old).sheet = old.sheet := by
    intro one two equal old
    cases equal
    rfl
  let terminal := (lifted.frames.frameAt last.point
    (onGrid last.point (List.Mem.tail _ (List.Mem.head _)))).select prepared.val.2.1.val.traced.finishOwner
  let assigned := Eq.mp (congrArg (fun value => OwnerWalkFaces lifted.mesh value incoming) same.symm) faces
  have assignedSheet : assigned.sheet = selected.index := sheet_transport same.symm faces
  refine ⟨selected, ⟨⟨last.point, last.point_eq⟩, ⟨⟨assigned, assignedSheet⟩, ⟨terminal, ?_⟩⟩⟩⟩
  have transported := congrArg₂
    (fun walk sheet => EdgeBank.RootEdgeBank.target lifted.edges walk sheet) same assignedSheet
  apply transported.trans
  obtain ⟨aligned⟩ := faces.finishAligned
    (onGrid last.point (List.Mem.tail _ (List.Mem.head _))) prepared.val.2.1.val
  exact (lifted.frames.frameAt last.point
    (onGrid last.point (List.Mem.tail _ (List.Mem.head _)))).distinguish _ _
      (aligned.symm.trans terminal.equivalent)

/-- Join one actual fine signed head to its already assigned whole retained tail.

The original return and actual next-entry traces select the same shared
frame index. The existing cached comparison gives their directional
relation; the complete original tail assignment is then appended once.
-/
private def faces_cons
    (pointReferences : ∀ point, Grid.FromStates.ContainsVertex base.bank.grid point →
      WindingOneLoop (Paths.polynomial parameter) point)
    (remaining : List (Piece data actual accuracy)) (next first : Piece data actual accuracy)
    (queried : ∀ piece ∈ (next :: remaining), piece.Queried)
    (sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint)
    (agreement : Parallel.Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner)
    (paid : Acquisition regular finishQuery (next :: remaining) first queried sourceOwner agreement)
    (lines : Lines paid elimination clearances)
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex base.bank.grid point)
    (heads : DetourWalkCache elimination clearances base.bank.grid paid lines onGrid)
    (supplied : Option (StepBlock.Start sourceOwner))
    (prepared : DetourSpine elimination clearances base.bank.grid pointReferences
      (next :: remaining) first queried sourceOwner agreement paid lines onGrid heads supplied)
    (tail : Faces lifted pointReferences remaining next
      (fun piece member => queried piece (List.Mem.tail next member))
      paid.head.finishOwner paid.head.nextAgreement paid.tail
      (Geometry.Lines.Bank.tail
        (elimination := elimination) (clearances := clearances) (regular := regular) lines)
      (fun point member => onGrid point (List.Mem.tail _ member))
      (tailDetourWalks elimination clearances base.bank.grid paid lines onGrid heads)
      (some ⟨prepared.1.finishOwner, prepared.1.equivalent⟩) prepared.2) :
    Faces lifted pointReferences (next :: remaining) first queried sourceOwner agreement paid lines onGrid
      heads supplied prepared := by
  let source := Geometry.Lines.Bank.head
    (elimination := elimination) (clearances := clearances) (regular := regular) lines
  let suffix := Geometry.Lines.Bank.tail
    (elimination := elimination) (clearances := clearances) (regular := regular) lines
  let targetLines := Geometry.Lines.Bank.head
    (elimination := elimination) (clearances := clearances) (regular := regular) suffix
  let cached := prepared.1
  let incoming := StepBlock.DetourCache.entryOwner cached
  let selected := (lifted.frames.frameAt source.point (onGrid source.point (List.Mem.head _))).select incoming
  let actualWalk := (headDetourWalk elimination clearances base.bank.grid paid lines onGrid heads).val.castEndpoints
    source.point_eq.symm targetLines.point_eq.symm
  let left := OwnerWalkFaces.ofSelection lifted.mesh actualWalk
    (onGrid source.point (List.Mem.head _)) selected
  let before := (lifted.frames.frameAt targetLines.point
    (onGrid targetLines.point (List.Mem.tail _ (List.Mem.head _)))).select
      cached.val.2.1.val.traced.finishOwner
  let right := tail.2.2.1.val
  let targetReference :=
    (LoopMonodromy.BranchCellBank.referenceAt
      base.bank.toBranchCellBank targetLines.point
        (onGrid targetLines.point (List.Mem.tail _ (List.Mem.head _)))).toLoop
  have related : Nonempty (NamedEquivalent (ownerName cached.val.2.1.val.traced.finishOwner)
      (ownerName (entryOwner elimination clearances base.bank.grid pointReferences remaining next
        (fun piece member => queried piece (List.Mem.tail next member))
        paid.head.finishOwner paid.head.nextAgreement paid.tail suffix
        (fun point member => onGrid point (List.Mem.tail _ member))
        (tailDetourWalks elimination clearances base.bank.grid paid lines onGrid heads)
        (some ⟨cached.finishOwner, cached.equivalent⟩) prepared.2))) := by
    cases remaining with
    | nil =>
      exact ⟨(cached.returnEntryEquivalent paid.tail.head.geometry.clearance targetReference
        cached.finishOwner (NamedEquivalent.refl (ownerName cached.finishOwner)) prepared.2.val.1.val
        (lifted.frames.frameAt targetLines.point
          (onGrid targetLines.point (List.Mem.tail _ (List.Mem.head _)))) before tail.1).symm⟩
    | cons following rest =>
      exact ⟨(cached.returnEntryEquivalent paid.tail.head.geometry.clearance targetReference
        cached.finishOwner (NamedEquivalent.refl (ownerName cached.finishOwner)) prepared.2.1.val.1.val
        (lifted.frames.frameAt targetLines.point
          (onGrid targetLines.point (List.Mem.tail _ (List.Mem.head _)))) before tail.1).symm⟩
  let joined := left.append right cached.val.2.1.val related
  have same :
      (prepareDetourOn elimination clearances paid lines base.bank.grid onGrid).2.val.castEndpoints
        source.point_eq.symm tail.2.1.property.symm = actualWalk.append
          ((prepareDetourOn elimination clearances paid.tail suffix base.bank.grid
            (fun point member => onGrid point (List.Mem.tail _ member))).2.val.castEndpoints
              targetLines.point_eq.symm tail.2.1.property.symm) :=
    (congrArg (fun value => value.castEndpoints source.point_eq.symm tail.2.1.property.symm)
      (prepareDetourOn_cons elimination clearances base.bank.grid paid lines onGrid heads)).trans
        (Grid.Walks.Walk.castEndpoints_append _ _ source.point_eq.symm targetLines.point_eq.symm
          tail.2.1.property.symm)
  have sheet_transport : ∀ {one two : Grid.Walks.Walk base.bank.grid source.point tail.2.1.val}
      (equal : one = two) (old : OwnerWalkFaces lifted.mesh one incoming),
      (Eq.mp (congrArg (fun value => OwnerWalkFaces lifted.mesh value incoming) equal) old).sheet = old.sheet := by
    intro one two equal old
    cases equal
    rfl
  let assigned := Eq.mp
    (congrArg (fun value => OwnerWalkFaces lifted.mesh value incoming) same.symm) joined
  have assignedSheet : assigned.sheet = selected.index :=
    (sheet_transport same.symm joined).trans (left.append_sheet right cached.val.2.1.val related)
  refine ⟨selected, ⟨tail.2.1, ⟨⟨assigned, assignedSheet⟩, ⟨tail.2.2.2.val, ?_⟩⟩⟩⟩
  have transported := congrArg₂
    (fun walk sheet => EdgeBank.RootEdgeBank.target lifted.edges walk sheet) same assignedSheet
  let tailWalk := (prepareDetourOn elimination clearances paid.tail suffix base.bank.grid
    (fun point member => onGrid point (List.Mem.tail _ member))).2.val.castEndpoints
      targetLines.point_eq.symm tail.2.1.property.symm
  have appended := EdgeBank.RootEdgeBank.target_append lifted.edges actualWalk tailWalk selected.index
  have handoff := left.target_eq right cached.val.2.1.val related
  have afterHandoff := congrArg (EdgeBank.RootEdgeBank.target lifted.edges tailWalk) handoff
  exact transported.trans (appended.trans (afterHandoff.trans tail.2.2.2.property))

namespace Faces

variable {lifted}
variable
    {pointReferences : ∀ point, Grid.FromStates.ContainsVertex base.bank.grid point →
      WindingOneLoop (Paths.polynomial parameter) point}
    {remaining : List (Piece data actual accuracy)} {first : Piece data actual accuracy}
    {queried : ∀ piece ∈ remaining, piece.Queried}
    {sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint}
    {agreement : Parallel.Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner}
    {paid : Acquisition regular finishQuery remaining first queried sourceOwner agreement}
    {lines : Lines paid elimination clearances}
    {onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex base.bank.grid point}
    {heads : DetourWalkCache elimination clearances base.bank.grid paid lines onGrid}
    {supplied : Option (StepBlock.Start sourceOwner)}
    {prepared : DetourSpine elimination clearances base.bank.grid pointReferences
      remaining first queried sourceOwner agreement paid lines onGrid heads supplied}
variable (retained : Faces lifted pointReferences remaining first queried sourceOwner agreement
  paid lines onGrid heads supplied prepared)

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

attribute [local irreducible] Faces Block Parallel.Geometry Transport.Spatial.coordinate
attribute [local irreducible] StepBlock.DetourCache DetourWalkCache

/-- Assign the complete original fine signed spine in its unchanged Piece order on the computed first sheet. -/
def faces
    (pointReferences : ∀ point, Grid.FromStates.ContainsVertex base.bank.grid point →
      WindingOneLoop (Paths.polynomial parameter) point) :
    (remaining : List (Piece data actual accuracy)) → (first : Piece data actual accuracy) →
    (queried : ∀ piece ∈ remaining, piece.Queried) →
    (sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint) →
    (agreement : Parallel.Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner) →
    (paid : Acquisition regular finishQuery remaining first queried sourceOwner agreement) →
    (lines : Lines paid elimination clearances) →
    (onGrid : ∀ point ∈ Parallel.Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex base.bank.grid point) →
    (heads : DetourWalkCache elimination clearances base.bank.grid paid lines onGrid) →
    (supplied : Option (StepBlock.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances base.bank.grid pointReferences
      remaining first queried sourceOwner agreement
      paid lines onGrid heads supplied) →
    Faces lifted pointReferences remaining first queried sourceOwner agreement paid lines onGrid
      heads supplied prepared := by
  intro remaining
  induction remaining with
  | nil => exact faces_single lifted pointReferences
  | cons next rest inductionHypothesis =>
    intro first queried sourceOwner agreement paid lines onGrid heads supplied prepared
    exact faces_cons lifted pointReferences rest next first queried sourceOwner agreement
      paid lines onGrid heads supplied prepared
      (inductionHypothesis next (fun piece member => queried piece (List.Mem.tail next member))
        paid.head.finishOwner paid.head.nextAgreement paid.tail
        (Geometry.Lines.Bank.tail
          (elimination := elimination) (clearances := clearances) (regular := regular) lines)
        (fun point member => onGrid point (List.Mem.tail _ member))
        (tailDetourWalks elimination clearances base.bank.grid paid lines onGrid heads)
        (some ⟨prepared.1.finishOwner, prepared.1.equivalent⟩) prepared.2)

end Spatial.Acquisition.DetourSpine

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer

end
