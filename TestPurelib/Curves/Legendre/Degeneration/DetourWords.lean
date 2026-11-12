module
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.DetourSpine.Faces
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Spatial.Acquisition.DetourSpine.Faces
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Realization
import all Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Realization.Preparation
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Spatial.Acquisition

import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Block
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Clearance.Box.Region
import Purelib.Approximation.Gaussian.Equivalence

/-! # Quantified signed-word agreement on retained detours

The import-all Preparation owner supplies the unexposed cache-transport
bodies reduced by these whole-value regressions.
-/

open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Geometry

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid (OwnerWalkFaces)
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider (AxisClearances)
open Purelib.Polynomial.Clearance.Box.Region (RegionClearance)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint finalTarget)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.RootContinuation
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {site : Fin 2} {parameter : Canonical} {unitQuarter : UnitCircuitQuarter}
variable {radiusPositive : (0 : Rational) < 2}
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
variable {frame : Paths.Frame parameter}
variable {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
variable {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
variable {base : FramedPuncturedGrid (Fibre.frameCurve frame) branches higher}
variable (lifted : LiftedPuncturedGrid base)
variable {degreeBound : Nat}
variable {elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound}
variable {clearances : AxisClearances elimination}
variable {firstAmbient : (Geometry.neighborhood site parameter regular
  (coordinate site parameter 2 unitQuarter radiusPositive current.parameter)).Refines
    (Cuts.Ambient (Fibre.frameCurve frame))}
variable {lastAmbient : (Geometry.neighborhood site parameter regular
  (coordinate site parameter 2 unitQuarter radiusPositive target.parameter)).Refines
    (Cuts.Ambient (Fibre.frameCurve frame))}
variable {source : Geometry.Lines elimination clearances regular
  (coordinate site parameter 2 unitQuarter radiusPositive current.parameter) firstAmbient}
variable {targetLines : Geometry.Lines elimination clearances regular
  (coordinate site parameter 2 unitQuarter radiusPositive target.parameter) lastAmbient}
variable {sourceOn : FromStates.ContainsVertex base.bank.grid source.point}
variable {targetOn : FromStates.ContainsVertex base.bank.grid targetLines.point}
variable {reference : WindingOneLoop (Paths.polynomial parameter)
    (coordinate site parameter 2 unitQuarter radiusPositive current.parameter) ⊕
  WindingOneLoop (Paths.polynomial parameter) source.point}
variable {walk : {value : Walks.Walk base.bank.grid
    (Geometry.move elimination regular (coordinate site parameter 2 unitQuarter radiusPositive current.parameter))
    (Geometry.move elimination regular (coordinate site parameter 2 unitQuarter radiusPositive target.parameter)) //
  value = geometry.detourWalk elimination clearances source targetLines base.bank.grid sourceOn targetOn}}
variable {supplied : Option (Block.Start root)}

/-- The literal cached middle word joins the next retained numerical word on the computed common sheet.

The return and next entry remain in their actual cached paths. The same
branch bank supplies the point reference, and the original comparison derives the needed sheet equality; the face words
reuse the supplied selections and both original numerical walks. No word
identity, sheet choice or cancellation of physical connectors is assumed.
-/
private theorem retainedMiddle_words_append
    (cached : Block.DetourCache block source targetLines reference walk supplied)
    (nextClearance : RegionClearance (Paths.polynomial parameter)
      (box site parameter unitQuarter target.parameter regular))
    (enteredOwner : OwnerAt site parameter unitQuarter radiusPositive target)
    (handoff : NamedEquivalent (ownerName cached.finishOwner) (ownerName enteredOwner))
    (entered : CoveredTracedPath
      (Riemann.Paths.ClearBoxPaths.Route.build nextClearance
        (coordinate site parameter 2 unitQuarter radiusPositive target.parameter) targetLines.point
        (source_inside (positive := radiusPositive) regular) targetLines.point_in_source).path
      enteredOwner)
    {last : Canonical} (nextWalk : Walks.Walk base.bank.grid targetLines.point last)
    (firstSelection : RootOwnerFrames.OwnerSelection (lifted.frames.frameAt source.point sourceOn).owners
      cached.val.1.val.traced.finishOwner)
    (before : RootOwnerFrames.OwnerSelection (lifted.frames.frameAt targetLines.point targetOn).owners
      cached.val.2.1.val.traced.finishOwner)
    (after : RootOwnerFrames.OwnerSelection (lifted.frames.frameAt targetLines.point targetOn).owners
      entered.traced.finishOwner) :
    let actualWalk := walk.val.castEndpoints source.point_eq.symm targetLines.point_eq.symm
    let left := OwnerWalkFaces.ofSelection lifted.mesh actualWalk sourceOn firstSelection
    let right := OwnerWalkFaces.ofSelection lifted.mesh nextWalk targetOn after
    left.geometry.indexed ++ right.geometry.indexed =
      lifted.edges.indexedEdges lifted.vertices (actualWalk.append nextWalk) firstSelection.index := by
  intro actualWalk left right
  let targetReference :=
    (LoopMonodromy.BranchCellBank.referenceAt
      base.bank.toBranchCellBank targetLines.point targetOn).toLoop
  let related := cached.returnEntryEquivalent nextClearance targetReference enteredOwner handoff entered
    (lifted.frames.frameAt targetLines.point targetOn) before after
  exact left.append_indexed right cached.val.2.1.val ⟨related.symm⟩

section Consecutive

variable (cached : Block.DetourCache block source targetLines reference walk supplied)
variable {nextTarget : Endpoint}
variable {nextQueried : {retained : ReadingAt actual nextTarget // QueryCache actual nextTarget retained}}
variable {nextPayment : (nextTarget.parameter - target.parameter) ^ 2 ≤
  Approximation.Rational.Geometric.Basic.quarterRadius 1 7}
variable {nextGeometry : Geometry queried.val nextQueried.val regular nextPayment}
variable (nextBlock : Block nextQueried nextGeometry block.finishOwner block.nextAgreement)
variable {nextAmbient : (Geometry.neighborhood site parameter regular
  (coordinate site parameter 2 unitQuarter radiusPositive nextTarget.parameter)).Refines
    (Cuts.Ambient (Fibre.frameCurve frame))}
variable {nextLines : Geometry.Lines elimination clearances regular
  (coordinate site parameter 2 unitQuarter radiusPositive nextTarget.parameter) nextAmbient}
variable {nextOn : FromStates.ContainsVertex base.bank.grid nextLines.point}
variable {nextReference : WindingOneLoop (Paths.polynomial parameter)
    (coordinate site parameter 2 unitQuarter radiusPositive target.parameter) ⊕
  WindingOneLoop (Paths.polynomial parameter) targetLines.point}
variable {nextWalk : {value : Walks.Walk base.bank.grid
    (Geometry.move elimination regular (coordinate site parameter 2 unitQuarter radiusPositive target.parameter))
    (Geometry.move elimination regular (coordinate site parameter 2 unitQuarter radiusPositive nextTarget.parameter)) //
  value = nextGeometry.detourWalk elimination clearances targetLines nextLines base.bank.grid targetOn nextOn}}
variable (following : Block.DetourCache nextBlock targetLines nextLines nextReference nextWalk
  (some ⟨cached.finishOwner, cached.equivalent⟩))

/-- The actual consecutive signed heads retain their three selections and two ordered face words. -/
private abbrev ConsecutiveWords :=
  let firstWalk := walk.val.castEndpoints source.point_eq.symm targetLines.point_eq.symm
  let followingWalk := nextWalk.val.castEndpoints targetLines.point_eq.symm nextLines.point_eq.symm
  Σ firstSelection : RootOwnerFrames.OwnerSelection (lifted.frames.frameAt source.point sourceOn).owners
    cached.entryOwner,
  Σ _finishSelection : RootOwnerFrames.OwnerSelection (lifted.frames.frameAt targetLines.point targetOn).owners
    cached.val.2.1.val.traced.finishOwner,
  Σ followingSelection : RootOwnerFrames.OwnerSelection (lifted.frames.frameAt targetLines.point targetOn).owners
    following.entryOwner,
  Σ left : OwnerWalkFaces lifted.mesh firstWalk cached.entryOwner,
    { right : OwnerWalkFaces lifted.mesh followingWalk following.entryOwner //
      left = OwnerWalkFaces.ofSelection lifted.mesh firstWalk sourceOn firstSelection ∧
      right = OwnerWalkFaces.ofSelection lifted.mesh followingWalk targetOn followingSelection ∧
      left.geometry.indexed ++ right.geometry.indexed =
        lifted.edges.indexedEdges lifted.vertices (firstWalk.append followingWalk) firstSelection.index }

/-- Construct the actual signed cons-pair words from their literal inherited start and cached comparisons.

The following entry starts at the previous return's actual finish Owner.
Its supplied comparison is exactly the preceding cached relation to the old
paid Owner. The three frame selections are retained once; the original
same-box winding argument and face-word append theorem derive the ordered
word equality without another root acquisition, comparison request or
handoff premise. Entry and return paths remain in their original caches;
no primitive-integral cancellation or closed-cut incidence is asserted.
-/
private def retainedConsecutive_words : ConsecutiveWords block lifted cached nextBlock following := by
  let firstSelection := (lifted.frames.frameAt source.point sourceOn).select cached.entryOwner
  let finishSelection := (lifted.frames.frameAt targetLines.point targetOn).select
    cached.val.2.1.val.traced.finishOwner
  let followingSelection := (lifted.frames.frameAt targetLines.point targetOn).select following.entryOwner
  let firstWalk := walk.val.castEndpoints source.point_eq.symm targetLines.point_eq.symm
  let followingWalk := nextWalk.val.castEndpoints targetLines.point_eq.symm nextLines.point_eq.symm
  let left := OwnerWalkFaces.ofSelection lifted.mesh firstWalk sourceOn firstSelection
  let right := OwnerWalkFaces.ofSelection lifted.mesh followingWalk targetOn followingSelection
  refine ⟨firstSelection, finishSelection, followingSelection, left, ⟨right, rfl, rfl, ?_⟩⟩
  exact retainedMiddle_words_append block lifted cached nextGeometry.clearance cached.finishOwner
    (NamedEquivalent.refl (ownerName cached.finishOwner)) following.val.1.val followingWalk
    firstSelection finishSelection followingSelection

/-- Join the two actual consecutive cached face assignments without assigning either path again.

The three retained selections are read from the original cons-pair cache.
The saved return and entry comparisons determine the sheet join in erased
proofs. The result retains both whole original assignments and their
ordered concatenation, with the original first selected sheet.
-/
private def retainedConsecutive_faces :
    let firstWalk := walk.val.castEndpoints source.point_eq.symm targetLines.point_eq.symm
    let followingWalk := nextWalk.val.castEndpoints targetLines.point_eq.symm nextLines.point_eq.symm
    Σ words : ConsecutiveWords block lifted cached nextBlock following,
      { joined : OwnerWalkFaces lifted.mesh (firstWalk.append followingWalk) cached.entryOwner //
        joined.geometry.indexed = words.2.2.2.1.geometry.indexed ++ words.2.2.2.2.val.geometry.indexed ∧
        joined.sheet = words.2.2.2.1.sheet } := by
  let words := retainedConsecutive_words block lifted cached nextBlock following
  let left := words.2.2.2.1
  let right := words.2.2.2.2.val
  let targetReference :=
    (LoopMonodromy.BranchCellBank.referenceAt
      base.bank.toBranchCellBank targetLines.point targetOn).toLoop
  let related := cached.returnEntryEquivalent nextGeometry.clearance targetReference cached.finishOwner
    (NamedEquivalent.refl (ownerName cached.finishOwner)) following.val.1.val
      (lifted.frames.frameAt targetLines.point targetOn) words.2.1 words.2.2.1
  refine ⟨words, ⟨left.append right cached.val.2.1.val ⟨related.symm⟩, ?_, ?_⟩⟩
  · exact left.append_geometry_indexed right cached.val.2.1.val ⟨related.symm⟩
  · exact left.append_sheet right cached.val.2.1.val ⟨related.symm⟩

end Consecutive

section PaidSpine

variable {followingTarget : Endpoint} {remaining : List Endpoint}
variable {originalOwner : OwnerAt site parameter unitQuarter radiusPositive current}
variable {original : Steps actual regular current reading originalOwner (target :: followingTarget :: remaining)}
variable (paid : Acquisition original root agreed)
variable (lines : Lines paid elimination clearances)
variable (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
  (elimination := elimination) (clearances := clearances) (regular := regular) lines,
  FromStates.ContainsVertex base.bank.grid point)
variable (heads : DetourWalkCache elimination clearances base.bank.grid paid lines onGrid)
variable (pointReferences : ∀ point, FromStates.ContainsVertex base.bank.grid point →
  WindingOneLoop (Paths.polynomial parameter) point)
variable (prepared : DetourSpine elimination clearances base.bank.grid pointReferences
  (target :: followingTarget :: remaining) current reading originalOwner original root agreed
    paid lines onGrid heads supplied)

/-- The actual original signed spine's first two retained heads satisfy the derived ordered face-word law.

The dependent tail is consumed directly. Its start is the first cached
return Owner, and its source comparison is the identical saved first-head
relation. The real ordered numeric head bank, original paid tail and signed
head caches determine both words and all selections; no external endpoint
relation or canonical-word equality is supplied.
-/
private def retainedSpine_pair :
    ConsecutiveWords paid.head lifted prepared.1 paid.tail.head prepared.2.1 :=
  retainedConsecutive_words paid.head lifted prepared.1 paid.tail.head prepared.2.1

end PaidSpine

section WholeSpine

attribute [local irreducible] DetourSpine.Faces Steps.Acquisition Block Geometry coordinate
  Block.DetourCache DetourWalkCache

/-- Retain the complete original signed spine beside its derived whole numerical-middle face assignment.

Every original entry, middle and return cover, exact inherited start and
cached comparison remains in the identical supplied spine. Its new face
assignment consumes the same head bank in order; no physical connectors
are discarded by returning the numerical middle word alone.
-/
private def retainedSpine_wordCache
    (pointReferences : ∀ point, FromStates.ContainsVertex base.bank.grid point →
      WindingOneLoop (Paths.polynomial parameter) point)
    (targets : List Endpoint) (first current : Endpoint)
    (reading : ReadingAt actual current)
    (originalOwner : OwnerAt site parameter unitQuarter radiusPositive current)
    (original : Steps actual regular current reading originalOwner (first :: targets))
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
      (first :: targets) current reading originalOwner original sourceOwner agreement
        paid lines onGrid heads supplied) :
    { value : DetourSpine elimination clearances base.bank.grid pointReferences
      (first :: targets) current reading originalOwner original sourceOwner agreement
        paid lines onGrid heads supplied // value = prepared } ×
      DetourSpine.Faces lifted pointReferences (first :: targets) current reading originalOwner original
        sourceOwner agreement paid lines onGrid heads supplied prepared (by intro equal; cases equal) :=
  ⟨⟨prepared, rfl⟩,
    DetourSpine.faces lifted pointReferences (first :: targets) current reading originalOwner original
      sourceOwner agreement paid lines onGrid heads supplied prepared (by intro equal; cases equal)⟩

end WholeSpine

section OriginalTerminal

namespace DetourSpine

open Purelib.Polynomial.Geometry

variable (elimination clearances)
variable (grid : Polynomial.Geometry.Grid.ClearGrid (Paths.polynomial parameter)
  (Polynomial.Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Paths.polynomial parameter)))

section FormerOriginal

attribute [local irreducible] Block Geometry coordinate
attribute [local irreducible] Block.DetourCache DetourWalkCache

/-- The complete historical original-Steps final-Owner fold for whole-value verification. -/
private def formerOriginalFinishOwner
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point) : (targets : List Endpoint) → (current : Endpoint) →
    (reading : ReadingAt actual current) → (originalOwner : OwnerAt site parameter unitQuarter radiusPositive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter radiusPositive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) → (lines : Lines paid elimination clearances) →
    (onGrid : ∀ value ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid value) →
    (cached : DetourWalkCache elimination clearances grid paid lines onGrid) →
    (supplied : Option (Block.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances grid reference targets current reading originalOwner original
      sourceOwner agreement paid lines onGrid cached supplied) →
    OwnerAt site parameter unitQuarter radiusPositive (finalTarget current targets)
  | [], _current, _reading, _originalOwner, _original, sourceOwner, _agreement,
      _paid, _lines, _onGrid, _cached, supplied, _prepared => Block.Start.owner sourceOwner supplied
  | target :: targets, _current, _reading, _originalOwner, original, _sourceOwner, _agreement,
      paid, lines, onGrid, cached, _supplied, prepared =>
      let suffix := Geometry.Lines.Bank.tail
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      formerOriginalFinishOwner reference targets target original.nextReading original.headCovered.finishOwner
        original.tail paid.head.finishOwner paid.head.nextAgreement paid.tail suffix
        (fun point member => onGrid point (List.Mem.tail _ member))
        (tailDetourWalks elimination clearances grid paid lines onGrid cached)
        (some ⟨Block.DetourCache.finishOwner prepared.1, Block.DetourCache.equivalent prepared.1⟩) prepared.2

/-- The original empty/default and all nonempty final Owners agree with their complete historical fold. -/
private theorem original_finishOwner_former
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point) : (targets : List Endpoint) → (current : Endpoint) →
    (reading : ReadingAt actual current) → (originalOwner : OwnerAt site parameter unitQuarter radiusPositive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter radiusPositive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) → (lines : Lines paid elimination clearances) →
    (onGrid : ∀ value ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid value) →
    (cached : DetourWalkCache elimination clearances grid paid lines onGrid) →
    (supplied : Option (Block.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances grid reference targets current reading originalOwner original
      sourceOwner agreement paid lines onGrid cached supplied) →
    finishOwner elimination clearances grid reference targets current reading originalOwner original
      sourceOwner agreement paid lines onGrid cached supplied prepared =
      formerOriginalFinishOwner elimination clearances grid reference targets current reading originalOwner original
        sourceOwner agreement paid lines onGrid cached supplied prepared := by
  intro targets
  induction targets with
  | nil => intros; rfl
  | cons target targets induction =>
    intros current reading originalOwner original sourceOwner agreement paid lines onGrid cached supplied prepared
    exact (finishOwner_cons elimination clearances grid reference targets target current reading originalOwner
      original sourceOwner agreement paid lines onGrid cached supplied prepared).trans
      (induction target original.nextReading original.headCovered.finishOwner
        original.tail paid.head.finishOwner paid.head.nextAgreement paid.tail
        (Geometry.Lines.Bank.tail (elimination := elimination) (clearances := clearances) (regular := regular) lines)
        (fun point member => onGrid point (List.Mem.tail _ member))
        (tailDetourWalks elimination clearances grid paid lines onGrid cached)
        (some ⟨Block.DetourCache.finishOwner prepared.1, Block.DetourCache.equivalent prepared.1⟩) prepared.2)

end FormerOriginal

/-- The complete previous nonempty terminal return, for all-field preservation verification only. -/
private def formerLastReturn
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point)
    : (targets : List Endpoint) → (target current : Endpoint) →
    (reading : ReadingAt actual current) → (originalOwner : OwnerAt site parameter unitQuarter radiusPositive current) →
    (original : Steps actual regular current reading originalOwner (target :: targets)) →
    (sourceOwner : OwnerAt site parameter unitQuarter radiusPositive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) → (lines : Lines paid elimination clearances) →
    (onGrid : ∀ value ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid value) →
    (cached : DetourWalkCache elimination clearances grid paid lines onGrid) →
    (supplied : Option (Block.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances grid reference (target :: targets) current reading
      originalOwner original
      sourceOwner agreement paid lines onGrid cached supplied) →
    LastReturn (site := site) (parameter := parameter) (unitQuarter := unitQuarter) (positive := radiusPositive)
      (regular := regular) (finish := finalTarget target targets) elimination :=
  fun targets target current reading originalOwner original sourceOwner agreement
      paid lines onGrid cached supplied prepared =>
    withLast (actual := actual) (regular := regular)
      (Result := fun finish => LastReturn (site := site) (parameter := parameter) (unitQuarter := unitQuarter)
        (positive := radiusPositive) (regular := regular) (finish := finish) elimination)
      elimination clearances grid reference
      (fun _target _current _reading _originalOwner _original _sourceOwner _agreement
        _paid terminalLines _onGrid _cached _supplied terminal =>
        let suffix := Geometry.Lines.Bank.tail
          (elimination := elimination) (clearances := clearances) (regular := regular) terminalLines
        let targetLines := Geometry.Lines.Bank.head
          (elimination := elimination) (clearances := clearances) (regular := regular) suffix
        ⟨⟨targetLines.point, targetLines.point_eq⟩, terminal.1.val.2.1.val.traced.finishOwner,
          terminal.1.val.2.2.1.val.traced.finishOwner, terminal.1.val.2.2.1.val.traced.trace.get⟩)
      targets target current reading originalOwner original sourceOwner agreement
      paid lines onGrid cached supplied prepared

/-- The generalized readback retains every original nonempty terminal field and its exact saved path. -/
private theorem lastReturn_whole_former
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point)
    : (targets : List Endpoint) → (target current : Endpoint) →
    (reading : ReadingAt actual current) → (originalOwner : OwnerAt site parameter unitQuarter radiusPositive current) →
    (original : Steps actual regular current reading originalOwner (target :: targets)) →
    (sourceOwner : OwnerAt site parameter unitQuarter radiusPositive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) → (lines : Lines paid elimination clearances) →
    (onGrid : ∀ value ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid value) →
    (cached : DetourWalkCache elimination clearances grid paid lines onGrid) →
    (supplied : Option (Block.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances grid reference (target :: targets) current reading
      originalOwner original
      sourceOwner agreement paid lines onGrid cached supplied) →
    lastReturn elimination clearances grid reference (target :: targets) current reading originalOwner original
      sourceOwner agreement paid lines onGrid cached supplied prepared
      (by intro empty; exact Nat.succ_ne_zero _ (congrArg List.length empty)) =
      formerLastReturn elimination clearances grid reference targets target current reading originalOwner original
        sourceOwner agreement paid lines onGrid cached supplied prepared := by
  intros
  rfl

/-- Retain the complete original signed spine with its literal terminal return and same paid endpoint relation. -/
private def retainedOriginal_returnCache
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point)
    : (targets : List Endpoint) → (target current : Endpoint) →
    (reading : ReadingAt actual current) → (originalOwner : OwnerAt site parameter unitQuarter radiusPositive current) →
    (original : Steps actual regular current reading originalOwner (target :: targets)) →
    (sourceOwner : OwnerAt site parameter unitQuarter radiusPositive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) → (lines : Lines paid elimination clearances) →
    (onGrid : ∀ value ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid value) →
    (cached : DetourWalkCache elimination clearances grid paid lines onGrid) →
    (supplied : Option (Block.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances grid reference (target :: targets) current reading
      originalOwner original
      sourceOwner agreement paid lines onGrid cached supplied) →
    Σ retained : DetourSpine elimination clearances grid reference (target :: targets) current reading originalOwner
        original sourceOwner agreement paid lines onGrid cached supplied,
      Σ returned : { value : LastReturn (site := site) (parameter := parameter) (unitQuarter := unitQuarter)
          (positive := radiusPositive) (regular := regular) (finish := finalTarget target targets) elimination //
        value.2.2.1 = finishOwner elimination clearances grid reference (target :: targets) current reading
          originalOwner original sourceOwner agreement paid lines onGrid cached supplied retained },
        NamedEquivalent (ownerName returned.val.2.2.1) (ownerName paid.finishOwner) := by
  intro targets target current reading originalOwner original sourceOwner agreement paid lines onGrid cached supplied
    prepared
  let returned := lastReturn elimination clearances grid reference (target :: targets) current reading
    originalOwner original sourceOwner agreement paid lines onGrid cached supplied prepared
    (by intro empty; exact Nat.succ_ne_zero _ (congrArg List.length empty))
  have same := lastReturn_finishOwner elimination clearances grid reference (target :: targets) current reading
    originalOwner original sourceOwner agreement paid lines onGrid cached supplied prepared
    (by intro empty; exact Nat.succ_ne_zero _ (congrArg List.length empty))
  refine ⟨prepared, ⟨⟨returned, same⟩, ?_⟩⟩
  exact NamedEquivalent.transport (congrArg ownerName same.symm) rfl
    (equivalent elimination clearances grid reference (target :: targets) current reading originalOwner original
      sourceOwner agreement paid lines onGrid cached supplied prepared)

end DetourSpine

end OriginalTerminal

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer
namespace Spatial.Acquisition.DetourSpine

open Transport.Spatial.Parallel.Steps.Acquisition.DetourSpine (LastReturn)

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Integration.Partition
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Transport.Spatial
open Transport.Spatial.Parallel.Steps.Acquisition renaming Block → StepBlock

open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider (AxisClearances)
open Purelib.Polynomial.Dense.Gaussian.Bounds
open Purelib.Polynomial.Geometry

variable {radicand : CoefficientPolynomial}
variable {site : Fin 2} {parameter : Canonical} {differential : OddPowerDifferential radicand}
variable {data : Waist.Differential.Bounds.Data site parameter differential}
variable {quarter : UnitCircuitQuarter} {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive} {accuracy : AccuracyRequest}

variable {regular : parameter ≠ criticalValue site} {finish : Endpoint}
variable (finishQuery : { reading : ReadingAt actual finish // QueryCache actual finish reading })
variable {degreeBound : Nat}
variable (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
variable (clearances : AxisClearances elimination)
variable (grid : Polynomial.Geometry.Grid.ClearGrid (Paths.polynomial parameter)
  (Polynomial.Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Paths.polynomial parameter)))

variable {finishQuery}

section FormerValue

attribute [local irreducible] Acquisition Block Parallel.Geometry Transport.Spatial.coordinate
attribute [local irreducible] StepBlock.DetourCache DetourWalkCache

/-- The complete former moved-coordinate Owner readback, retained only for quantified preservation verification. -/
private def formerMiddleSource
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point) :
    (remaining : List (Piece data actual accuracy)) → (first : Piece data actual accuracy) →
    (queried : ∀ piece ∈ remaining, piece.Queried) →
    (sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint) →
    (agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner) →
    (paid : Acquisition regular finishQuery remaining first queried sourceOwner agreement) →
    (lines : Lines paid elimination clearances) →
    (onGrid : ∀ point ∈ Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid point) →
    (cached : DetourWalkCache elimination clearances grid paid lines onGrid) →
    (supplied : Option (StepBlock.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances grid reference remaining first queried sourceOwner agreement
      paid lines onGrid cached supplied) → Riemann.Topology.SquareRootContinuationChain.Owner
      ((Paths.polynomial parameter).eval (Parallel.Geometry.move elimination regular
        (Transport.Spatial.coordinate site parameter 2 quarter positive first.span.lower)))
  | [], _first, _queried, _sourceOwner, _agreement, _paid, lines, _onGrid, _cached, _supplied, prepared =>
      let source := Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      RootIsolation.SquareRoot.Owner.Transport.castOwnerParameter
        (congrArg (Paths.polynomial parameter).eval source.point_eq) (StepBlock.DetourCache.entryOwner prepared)
  | _next :: _remaining, _first, _queried, _sourceOwner, _agreement, _paid, lines, _onGrid,
      _cached, _supplied, prepared =>
      let source := Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      RootIsolation.SquareRoot.Owner.Transport.castOwnerParameter
        (congrArg (Paths.polynomial parameter).eval source.point_eq) (StepBlock.DetourCache.entryOwner prepared.1)

/-- The shared original entry getter preserves the complete former moved-coordinate Owner for every fine spine. -/
private theorem middleSource_former
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point) :
    (remaining : List (Piece data actual accuracy)) → (first : Piece data actual accuracy) →
    (queried : ∀ piece ∈ remaining, piece.Queried) →
    (sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint) →
    (agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner) →
    (paid : Acquisition regular finishQuery remaining first queried sourceOwner agreement) →
    (lines : Lines paid elimination clearances) →
    (onGrid : ∀ point ∈ Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid point) →
    (cached : DetourWalkCache elimination clearances grid paid lines onGrid) →
    (supplied : Option (StepBlock.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances grid reference remaining first queried sourceOwner agreement
      paid lines onGrid cached supplied) →
    middleSource elimination clearances grid reference remaining first queried sourceOwner agreement
      paid lines onGrid cached supplied prepared =
      formerMiddleSource elimination clearances grid reference remaining first queried sourceOwner agreement
        paid lines onGrid cached supplied prepared := by
  intro remaining
  cases remaining with
  | nil => intros; rfl
  | cons next rest => intros; rfl

end FormerValue

section FormerFinish

attribute [local irreducible] Block Parallel.Geometry Transport.Spatial.coordinate
attribute [local irreducible] StepBlock.DetourCache DetourWalkCache

/-- The complete historical final-Owner fold, retained only for whole-value preservation. -/
private def formerFinishOwner
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point) :
    (remaining : List (Piece data actual accuracy)) → (first : Piece data actual accuracy) →
    (queried : ∀ piece ∈ remaining, piece.Queried) →
    (sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint) →
    (agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner) →
    (paid : Acquisition regular finishQuery remaining first queried sourceOwner agreement) →
    (lines : Lines paid elimination clearances) →
    (onGrid : ∀ point ∈ Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid point) →
    (cached : DetourWalkCache elimination clearances grid paid lines onGrid) →
    (supplied : Option (StepBlock.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances grid reference remaining first queried sourceOwner agreement
      paid lines onGrid cached supplied) → OwnerAt site parameter quarter positive finish
  | [], _first, _queried, _sourceOwner, _agreement, _paid, _lines, _onGrid, _cached, _supplied, prepared =>
      StepBlock.DetourCache.finishOwner prepared
  | next :: remaining, _first, queried, _sourceOwner, _agreement, paid, lines, onGrid, cached, _supplied, prepared =>
      let suffix := Lines.Bank.tail
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      formerFinishOwner reference remaining next (fun piece member => queried piece (List.Mem.tail next member))
        paid.head.finishOwner paid.head.nextAgreement paid.tail suffix
        (fun point member => onGrid point (List.Mem.tail _ member))
        (tailDetourWalks elimination clearances grid paid lines onGrid cached)
        (some ⟨StepBlock.DetourCache.finishOwner prepared.1,
          StepBlock.DetourCache.equivalent prepared.1⟩) prepared.2

/-- Terminal continuation specialization preserves the complete old result for every retained spine. -/
private theorem finishOwner_former
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point) :
    (remaining : List (Piece data actual accuracy)) → (first : Piece data actual accuracy) →
    (queried : ∀ piece ∈ remaining, piece.Queried) →
    (sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint) →
    (agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner) →
    (paid : Acquisition regular finishQuery remaining first queried sourceOwner agreement) →
    (lines : Lines paid elimination clearances) →
    (onGrid : ∀ point ∈ Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid point) →
    (cached : DetourWalkCache elimination clearances grid paid lines onGrid) →
    (supplied : Option (StepBlock.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances grid reference remaining first queried sourceOwner agreement
      paid lines onGrid cached supplied) →
    finishOwner elimination clearances grid reference remaining first queried sourceOwner agreement
      paid lines onGrid cached supplied prepared =
      formerFinishOwner elimination clearances grid reference remaining first queried sourceOwner agreement
        paid lines onGrid cached supplied prepared := by
  intro remaining
  induction remaining with
  | nil => intros; rfl
  | cons next remaining induction =>
    intros first queried sourceOwner agreement paid lines onGrid cached supplied prepared
    exact induction next (fun piece member => queried piece (List.Mem.tail next member))
      paid.head.finishOwner paid.head.nextAgreement paid.tail
      (Lines.Bank.tail
        (elimination := elimination) (clearances := clearances) (regular := regular) lines)
      (fun point member => onGrid point (List.Mem.tail _ member))
      (tailDetourWalks elimination clearances grid paid lines onGrid cached)
      (some ⟨StepBlock.DetourCache.finishOwner prepared.1,
        StepBlock.DetourCache.equivalent prepared.1⟩) prepared.2

end FormerFinish

section WholeWords

open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid (OwnerWalkFaces)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation

variable {elimination clearances grid}
variable {frame : Paths.Frame parameter} {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
variable {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
variable {base : FramedPuncturedGrid (Fibre.frameCurve frame) branches higher}
variable (lifted : LiftedPuncturedGrid base)

attribute [local irreducible] Faces Block Parallel.Geometry Transport.Spatial.coordinate
attribute [local irreducible] StepBlock.DetourCache DetourWalkCache

/-- Retain the complete original fine signed spine beside its derived numerical-middle word.

Every saved entry and return connector, Owner, query receipt and signed
comparison remains in the identical supplied cofold. The new assignment
consumes the same stored numeric heads; it does not replace the physical
trace or assert cancellation of its connectors.
-/
private def retainedFine_wordCache
    (pointReferences : ∀ point, Grid.FromStates.ContainsVertex base.bank.grid point →
      WindingOneLoop (Paths.polynomial parameter) point)
    (remaining : List (Piece data actual accuracy)) (first : Piece data actual accuracy)
    (queried : ∀ piece ∈ remaining, piece.Queried)
    (sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint)
    (agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner)
    (paid : Acquisition regular finishQuery remaining first queried sourceOwner agreement)
    (lines : Lines paid elimination clearances)
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex base.bank.grid point)
    (heads : DetourWalkCache elimination clearances base.bank.grid paid lines onGrid)
    (supplied : Option (StepBlock.Start sourceOwner))
    (prepared : DetourSpine elimination clearances base.bank.grid pointReferences
      remaining first queried sourceOwner agreement paid lines onGrid heads supplied) :
    { value : DetourSpine elimination clearances base.bank.grid pointReferences
      remaining first queried sourceOwner agreement paid lines onGrid heads supplied // value = prepared } ×
      Faces lifted pointReferences remaining first queried sourceOwner agreement paid lines onGrid
        heads supplied prepared :=
  ⟨⟨prepared, rfl⟩,
    faces lifted pointReferences remaining first queried sourceOwner agreement
      paid lines onGrid heads supplied prepared⟩

/-- Retain the actual whole fine signed spine beside its literal terminal return and original paid relation.

Both actual terminal Owners and their saved path remain dependent inputs.
The saved endpoint comparison is transported along an erased equality; the
operation adds no continuation, numeric factory or classification request.
-/
private def retainedFine_returnCache
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point) :
    (remaining : List (Piece data actual accuracy)) → (first : Piece data actual accuracy) →
    (queried : ∀ piece ∈ remaining, piece.Queried) →
    (sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint) →
    (agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner) →
    (paid : Acquisition regular finishQuery remaining first queried sourceOwner agreement) →
    (lines : Lines paid elimination clearances) →
    (onGrid : ∀ point ∈ Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid point) →
    (cached : DetourWalkCache elimination clearances grid paid lines onGrid) →
    (supplied : Option (StepBlock.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances grid reference remaining first queried sourceOwner agreement
      paid lines onGrid cached supplied) →
    Σ retained : DetourSpine elimination clearances grid reference remaining first queried
        sourceOwner agreement paid lines onGrid cached supplied,
      Σ returned : { value : LastReturn (site := site) (parameter := parameter) (unitQuarter := quarter)
          (positive := positive) (regular := regular) (finish := finish) elimination //
        value.2.2.1 = finishOwner elimination clearances grid reference remaining first queried
          sourceOwner agreement paid lines onGrid cached supplied retained },
        NamedEquivalent (ownerName returned.val.2.2.1) (ownerName paid.finishOwner) := by
  intro remaining first queried sourceOwner agreement paid lines onGrid cached supplied prepared
  let returned := lastReturn elimination clearances grid reference remaining first queried
    sourceOwner agreement paid lines onGrid cached supplied prepared
  have same := lastReturn_finishOwner elimination clearances grid reference remaining first queried
    sourceOwner agreement paid lines onGrid cached supplied prepared
  refine ⟨prepared, ⟨⟨returned, same⟩, ?_⟩⟩
  exact NamedEquivalent.transport (congrArg ownerName same.symm) rfl
    (equivalent elimination clearances grid reference remaining first queried
      sourceOwner agreement paid lines onGrid cached supplied prepared)

end WholeWords

end Spatial.Acquisition.DetourSpine
end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
namespace Steps.Acquisition.Quarter.Input.Realization.DetourSpine

open Purelib
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Spatial
  renaming Acquisition → LayerAcquisition
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Geometry
open Purelib.Data.Rat
open Purelib.Polynomial.Dense.Gaussian.Bounds
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider (AxisClearances)
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {site : Fin 2} {parameter : Data.Gaussian.Basic.Canonical} {unitQuarter : UnitCircuitQuarter}
variable {leg : Transport.Leg site parameter unitQuarter} {input : Input leg}
variable {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint}
variable {agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner}
variable {degreeBound : Nat}
variable (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
variable (clearances : AxisClearances elimination)
variable (grid : ClearGrid (Paths.polynomial parameter)
  (RootRadius.Box.largeSquareBox (Paths.polynomial parameter)))

/-- Retain the complete actual mixed quarter beside its exact cached terminal return and saved old-owner comparison.

The original and fine branches both consume the same supplied signed
cofold. Only erased endpoint equality transports its saved comparison;
no route, query, root selection or numerical preparation is repeated.
-/
private def retainedQuarter_returnCache
    (reference : ∀ point, FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point)
    (retained : Realization input sourceOwner agreement)
    (lines : Lines retained elimination clearances)
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := leg.regular) lines,
      FromStates.ContainsVertex grid point)
    (cached : DetourWalkCache elimination clearances grid retained lines onGrid)
    (supplied : Option (Block.Start sourceOwner))
    (prepared : DetourSpine elimination clearances grid reference input sourceOwner agreement
      retained lines onGrid cached supplied) :=
  let returned := lastReturn elimination clearances grid reference input sourceOwner agreement
    retained lines onGrid cached supplied prepared
  have same := lastReturn_finishOwner elimination clearances grid reference input sourceOwner agreement
    retained lines onGrid cached supplied prepared
  let related := NamedEquivalent.transport (congrArg ownerName same.symm) rfl
    (equivalent elimination clearances grid reference input sourceOwner agreement
      retained lines onGrid cached supplied prepared)
  ((⟨prepared, rfl⟩ : {value : DetourSpine elimination clearances grid reference input sourceOwner agreement
      retained lines onGrid cached supplied // value = prepared}), returned, related)

section FormerQuarter

attribute [local irreducible] coordinate
attribute [local irreducible] DetourWalkCache.steps DetourWalkCache.numerical

/-- The complete historical mixed-quarter first-middle operation, retained only for whole-value verification. -/
private def formerQuarterMiddleSource
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point) :
    (input : Input leg) →
    (sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint) →
    (agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner) →
    (retained : Realization input sourceOwner agreement) →
    (lines : Lines retained elimination clearances) →
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := leg.regular) lines,
      Grid.FromStates.ContainsVertex grid point) →
    (cached : DetourWalkCache elimination clearances grid retained lines onGrid) →
    (supplied : Option (Block.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances grid reference input sourceOwner agreement
      retained lines onGrid cached supplied) →
    Riemann.Topology.SquareRootContinuationChain.Owner ((Paths.polynomial parameter).eval
      (Geometry.move elimination leg.regular
        (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint.parameter)))
  | .inl _original, _sourceOwner, _agreement, retained, lines, onGrid, cached, supplied, prepared =>
      Steps.Acquisition.DetourSpine.middleSource elimination clearances grid reference _ _ _ _ _ _ _
        retained.receipt lines onGrid
        (cached.steps elimination clearances grid retained lines onGrid) supplied prepared (by
          intro empty
          have count := Quarter.target_count retained
          have wrong : (128 : Nat) = 0 := count.symm.trans (congrArg List.length empty)
          exact (of_decide_eq_true rfl : (128 : Nat) ≠ 0) wrong)
  | .inr fine, _sourceOwner, _agreement, retained, lines, onGrid, cached, supplied, prepared =>
      let original := LayerAcquisition.DetourSpine.middleSource elimination clearances grid reference _ _ _ _ _
        retained.paid lines onGrid
        (cached.numerical elimination clearances grid retained lines onGrid)
        (Numerical.Realization.detourStart fine.numerical _sourceOwner supplied) prepared
      RootIsolation.SquareRoot.Owner.Transport.castOwnerParameter
        (congrArg (fun time : Fraction.Rational => (Paths.polynomial parameter).eval
          (Geometry.move elimination leg.regular
            (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) time)))
          (fine.numerical.parts.start_time fine.numerical.layer_eq)) original

/-- Factoring the retained quarter's nonempty proof preserves its whole historical first-middle Owner. -/
private theorem middleSource_whole_former
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point) :
    (input : Input leg) →
    (sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint) →
    (agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner) →
    (retained : Realization input sourceOwner agreement) →
    (lines : Lines retained elimination clearances) →
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := leg.regular) lines,
      Grid.FromStates.ContainsVertex grid point) →
    (cached : DetourWalkCache elimination clearances grid retained lines onGrid) →
    (supplied : Option (Block.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances grid reference input sourceOwner agreement
      retained lines onGrid cached supplied) →
    middleSource elimination clearances grid reference input sourceOwner agreement
      retained lines onGrid cached supplied prepared =
      formerQuarterMiddleSource elimination clearances grid reference input sourceOwner agreement
        retained lines onGrid cached supplied prepared := by
  intro input
  cases input with
  | inl original => intros; rfl
  | inr fine => intros; rfl

end FormerQuarter

variable {nextQuarter : UnitCircuitQuarter} {nextLeg : Transport.Leg site parameter nextQuarter}

/-- Consume the actual saved quarter return and its original following seam start without identifying middle paths. -/
private def retainedQuarter_seamCache
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point)
    (retained : Realization input sourceOwner agreement)
    (lines : Lines retained elimination clearances)
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := leg.regular) lines,
      Grid.FromStates.ContainsVertex grid point)
    (cached : DetourWalkCache elimination clearances grid retained lines onGrid)
    (supplied : Option (Block.Start sourceOwner))
    (prepared : DetourSpine elimination clearances grid reference input sourceOwner agreement
      retained lines onGrid cached supplied)
    (next : Input nextLeg) (directions : Waist.direction unitQuarter 1 = Waist.direction nextQuarter 0)
    (stored : Transport.Seam leg nextLeg)
    (seam : Transport.Seam.Receipt (left := leg) (right := nextLeg) retained.finishReading next.sourceReading
      retained.finishOwner retained.finishEquivalent retained.finish_time next.source_time directions stored) :=
  let terminal := lastReturn elimination clearances grid reference input sourceOwner agreement
    retained lines onGrid cached supplied prepared
  let following := nextStart elimination clearances grid reference retained lines onGrid cached supplied
    prepared next directions stored seam
  have same := lastReturn_nextStart elimination clearances grid reference retained lines onGrid cached supplied
    prepared next directions stored seam
  ((⟨prepared, rfl⟩ : {value : DetourSpine elimination clearances grid reference input sourceOwner agreement
      retained lines onGrid cached supplied // value = prepared}), terminal,
    (⟨following, same⟩ : {value : Block.Start seam.owner // value.1 =
      Transport.Seam.castOwner (site := site) (parameter := parameter)
        (leftQuarter := unitQuarter) (rightQuarter := nextQuarter)
        retained.finish_time next.source_time directions terminal.2.2.1}))

end Steps.Acquisition.Quarter.Input.Realization.DetourSpine
end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
