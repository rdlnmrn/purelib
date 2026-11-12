module

import Purelib.RootIsolation.SquareRoot.Owner.Transport

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Spine
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.RootContinuation.ClearBoxRootTransport
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Polynomial.Clearance.Box.Region
import Purelib.Data.List.DependentProduct
import Purelib.Data.List.Map
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.Walks

/-! # Readbacks and final returns on retained paid acquisition spines

The existing Steps receipt supplies every original QueryCache and Geometry.
New paid blocks follow that same target-list spine. Each tail retains the
identical original next Reading and the literal preceding paid finishOwner,
with its actual cached next-source comparison. Old headCovered values are
used solely to navigate the original receipt's indices; no equality with
those old executions is asserted. Complete paid cover and comparison caches
are retained at each new node.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
  (ownerRootName ownerRootName_castOwnerParameter)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint finalTarget)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.RootIsolation.SquareRoot
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Riemann.Paths.ClearBoxPathWinding.ClearBoxPaths (windingPotential)
open Purelib.Polynomial.Winding.Polygon.Basic (chainRaw)
open Purelib.Polynomial.Clearance.Box.Region (RegionClearance)

variable {site : Fin 2} {parameter : Canonical} {unitQuarter : UnitCircuitQuarter}
variable {positive : (0 : Data.Rat.Fraction.Rational) < 2}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

namespace Steps.Acquisition

variable {actual : Transport.Quarter site parameter 2 unitQuarter positive} {regular : parameter ≠ criticalValue site}
variable {targets : List Endpoint} {current : Endpoint} {reading : ReadingAt actual current}
variable {originalOwner sourceOwner : OwnerAt site parameter unitQuarter positive current}
variable {original : Steps actual regular current reading originalOwner targets}
variable {agreement : InitialAgreement current reading sourceOwner}

open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider (AxisClearances)
open Purelib.Polynomial.Geometry
open Purelib.Polynomial.Dense.Gaussian.Bounds
open Purelib.Geometry.Rational.Box.Refinement
open Purelib.Data.List (DependentProduct)

section Detour

variable {degreeBound : Nat}
variable (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
variable (clearances : AxisClearances elimination)
variable (grid : Grid.ClearGrid (Paths.polynomial parameter)
  (RootRadius.Box.largeSquareBox (Paths.polynomial parameter)))

namespace DetourSpine

section TerminalFold

attribute [local irreducible] Block Geometry coordinate
attribute [local irreducible] Block.DetourCache DetourWalkCache

/-- An exact consumer of the actual last nonempty original Steps context.

The complete singleton retains its old receipt, paid Block, selected line
bank, numerical cache and signed head/tail. Both source Owners remain
original indices; the result may depend on the exact final target.
-/
abbrev LastAction (Result : Endpoint → Type u)
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point) :=
    (target current : Endpoint) →
    (reading : ReadingAt actual current) → (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner [target]) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) → (lines : Lines paid elimination clearances) →
    (onGrid : ∀ value ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid value) →
    (cached : DetourWalkCache elimination clearances grid paid lines onGrid) →
    (supplied : Option (Block.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances grid reference [target] current reading originalOwner original
      sourceOwner agreement paid lines onGrid cached supplied) → Result target

/-- Consume the actual final signed head of an original nonempty Steps spine.

Only the original stored paid, selected-line, numerical and signed tails
are followed. The final singleton is passed intact to the consumer; no
head, route, query, root selection or comparison is prepared again.
-/
@[expose, specialize] def withLast {Result : Endpoint → Type u}
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point)
    (consume : LastAction (actual := actual) (regular := regular)
      (elimination := elimination) (clearances := clearances) (grid := grid) Result reference) :
    (targets : List Endpoint) → (target current : Endpoint) →
    (reading : ReadingAt actual current) → (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner (target :: targets)) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) → (lines : Lines paid elimination clearances) →
    (onGrid : ∀ value ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid value) →
    (cached : DetourWalkCache elimination clearances grid paid lines onGrid) →
    (supplied : Option (Block.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances grid reference (target :: targets) current reading
      originalOwner original
      sourceOwner agreement paid lines onGrid cached supplied) → Result (finalTarget target targets)
  | [], target, current, reading, originalOwner, original, sourceOwner, agreement,
      paid, lines, onGrid, cached, supplied, prepared =>
      consume target current reading originalOwner original sourceOwner agreement
        paid lines onGrid cached supplied prepared
  | next :: targets, target, _current, _reading, _originalOwner, original, _sourceOwner, _agreement,
      paid, lines, onGrid, cached, _supplied, prepared =>
      let suffix := Geometry.Lines.Bank.tail
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      withLast reference consume targets next target original.nextReading original.headCovered.finishOwner
        original.tail paid.head.finishOwner paid.head.nextAgreement paid.tail suffix
        (fun point member => onGrid point (List.Mem.tail _ member))
        (tailDetourWalks elimination clearances grid paid lines onGrid cached)
        (some ⟨prepared.1.finishOwner, prepared.1.equivalent⟩) prepared.2

end TerminalFold

section CachedReadbacks

attribute [local irreducible] Steps.Acquisition Block Geometry coordinate
attribute [local irreducible] Block.DetourCache DetourWalkCache

/-- Read the literal actual final Owner from the retained signed preparation spine. -/
@[expose] def finishOwner
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point) : (targets : List Endpoint) → (current : Endpoint) →
    (reading : ReadingAt actual current) → (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) → (lines : Lines paid elimination clearances) →
    (onGrid : ∀ value ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid value) →
    (cached : DetourWalkCache elimination clearances grid paid lines onGrid) →
    (supplied : Option (Block.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances grid reference targets current reading originalOwner original
      sourceOwner agreement paid lines onGrid cached supplied) →
    OwnerAt site parameter unitQuarter positive (finalTarget current targets)
  | [], _current, _reading, _originalOwner, _original, sourceOwner, _agreement,
      _paid, _lines, _onGrid, _cached, supplied, _prepared => Block.Start.owner sourceOwner supplied
  | target :: targets, current, reading, originalOwner, original, sourceOwner, agreement,
      paid, lines, onGrid, cached, supplied, prepared =>
      withLast (actual := actual) (regular := regular) elimination clearances grid reference
        (fun _target _current _reading _originalOwner _original _sourceOwner _agreement
          _paid _lines _onGrid _cached _supplied terminal => Block.DetourCache.finishOwner terminal.1)
        targets target current reading originalOwner original sourceOwner agreement
        paid lines onGrid cached supplied prepared

/-- The shared terminal specialization retains the exact original head/tail finish equation. -/
theorem finishOwner_cons
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point)
    : (targets : List Endpoint) → (target current : Endpoint) →
    (reading : ReadingAt actual current) → (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner (target :: targets)) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
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
    finishOwner elimination clearances grid reference (target :: targets) current reading originalOwner original
      sourceOwner agreement paid lines onGrid cached supplied prepared =
      finishOwner elimination clearances grid reference targets target original.nextReading
        original.headCovered.finishOwner
        original.tail paid.head.finishOwner paid.head.nextAgreement paid.tail
        (Geometry.Lines.Bank.tail (elimination := elimination) (clearances := clearances) (regular := regular) lines)
        (fun point member => onGrid point (List.Mem.tail _ member))
        (tailDetourWalks elimination clearances grid paid lines onGrid cached)
        (some ⟨Block.DetourCache.finishOwner prepared.1, Block.DetourCache.equivalent prepared.1⟩) prepared.2 := by
  intro targets
  cases targets with
  | nil =>
    intros target current reading originalOwner original sourceOwner agreement paid lines onGrid cached supplied
      prepared
    change Block.DetourCache.finishOwner prepared.1 =
      Block.Start.owner paid.head.finishOwner
        (some ⟨Block.DetourCache.finishOwner prepared.1, Block.DetourCache.equivalent prepared.1⟩)
    rfl
  | cons next rest => intros; rfl

end CachedReadbacks

/-- The original last numerical middle and its actual retained return trace.

The selected point keeps its exact moved-coordinate equation. Both Owners
are literal cached endpoints; the path is read from the already prepared
return, so this view creates no route, root track, comparison or payment.
-/
abbrev LastReturn (finish : Endpoint) :=
  Σ last : { value : Canonical // value = Parallel.Geometry.move elimination regular
      (Transport.Spatial.coordinate site parameter 2 unitQuarter positive finish.parameter) },
  Σ middle : Riemann.Topology.SquareRootContinuationChain.Owner ((Paths.polynomial parameter).eval last.val),
  Σ returned : OwnerAt site parameter unitQuarter positive finish,
    OwnerPath (Paths.polynomial parameter) last.val middle
      (Transport.Spatial.coordinate site parameter 2 unitQuarter positive finish.parameter) returned

namespace LastReturn

open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame OwnerSelection NameSelection)
open Purelib.RootIsolation.SquareRoot.Owner.Transport (castOwnerParameter castOwnerParameter_heq)

/-- Reindex the same retained return at a geometrically equal endpoint and its identical transported owner.

The original moved point, middle owner and complete return path are kept.
The endpoint equality derives its new moved-point certificate internally;
the supplied heterogeneous owner identity transports only the return's
terminal index. No geometry search or root acquisition is performed.
-/
@[expose] def atEndpoint {finish : Endpoint}
    (retained : LastReturn (site := site) (parameter := parameter) (unitQuarter := unitQuarter)
      (positive := positive) (regular := regular) (finish := finish) elimination)
    {nextQuarter : UnitCircuitQuarter} (endpoint : Endpoint)
    (pointEq : Transport.Spatial.coordinate site parameter 2 unitQuarter positive finish.parameter =
      Transport.Spatial.coordinate site parameter 2 nextQuarter positive endpoint.parameter)
    (nextOwner : OwnerAt site parameter nextQuarter positive endpoint)
    (ownerEq : HEq retained.2.2.1 nextOwner) :
    LastReturn (site := site) (parameter := parameter) (unitQuarter := nextQuarter)
      (positive := positive) (regular := regular) (finish := endpoint) elimination :=
  ⟨⟨retained.1.val, retained.1.property.trans
      (congrArg (Geometry.move elimination regular) pointEq)⟩,
    retained.2.1, nextOwner,
    OwnerPath.castEndpoints (polynomial := Paths.polynomial parameter) rfl pointEq HEq.rfl ownerEq
      retained.2.2.2⟩

/-- Exact endpoint reindexing preserves the complete retained return's original ordered vertex list. -/
theorem atEndpoint_vertices {finish : Endpoint}
    (retained : LastReturn (site := site) (parameter := parameter) (unitQuarter := unitQuarter)
      (positive := positive) (regular := regular) (finish := finish) elimination)
    {nextQuarter : UnitCircuitQuarter} (endpoint : Endpoint)
    (pointEq : Transport.Spatial.coordinate site parameter 2 unitQuarter positive finish.parameter =
      Transport.Spatial.coordinate site parameter 2 nextQuarter positive endpoint.parameter)
    (nextOwner : OwnerAt site parameter nextQuarter positive endpoint)
    (ownerEq : HEq retained.2.2.1 nextOwner) :
    (atEndpoint elimination retained endpoint pointEq nextOwner ownerEq).2.2.2.vertices =
      retained.2.2.2.vertices := by
  dsimp only [atEndpoint]
  exact OwnerPath.castEndpoints_vertices rfl pointEq HEq.rfl ownerEq retained.2.2.2

/-- Compare a retained terminal middle with the actual entry after its saved return connector.

The same cached return path and both original endpoint owners remain
inputs. The following entry supplies its actual owner path, exact physical-point
identity and geometric winding payment. Endpoint transport preserves its
saved vertex list and both original names. The same frame selections
supply the operational comparison without another root classification.
-/
def entryEquivalent {finish : Endpoint}
    (retained : LastReturn (site := site) (parameter := parameter) (unitQuarter := unitQuarter)
      (positive := positive) (regular := regular) (finish := finish) elimination)
    (enteredOwner : OwnerAt site parameter unitQuarter positive finish)
    (handoff : NamedEquivalent (ownerName retained.2.2.1) (ownerName enteredOwner))
    {finishPoint : Canonical} {last : Owner ((Paths.polynomial parameter).eval finishPoint)}
    (entered : OwnerPath (Paths.polynomial parameter)
      (Transport.Spatial.coordinate site parameter 2 unitQuarter positive finish.parameter)
      enteredOwner finishPoint last)
    (samePoint : finishPoint = retained.1.val)
    (reference : WindingOneLoop (Paths.polynomial parameter) retained.1.val)
    (frame : OwnerFrame ((Paths.polynomial parameter).eval retained.1.val))
    (before : OwnerSelection frame.owners retained.2.1)
    (after : NameSelection (fun index => ownerName (frame.owners index)) (ownerName last))
    (turns : Int)
    (winding : chainRaw (Paths.polynomial parameter) retained.1.val retained.2.2.2.vertices +
      chainRaw (Paths.polynomial parameter)
        (Transport.Spatial.coordinate site parameter 2 unitQuarter positive finish.parameter)
        entered.vertices = 8 * turns) :
    NamedEquivalent (ownerName last) (ownerName retained.2.1) := by
  let parameterEq := congrArg (Paths.polynomial parameter).eval samePoint
  let castOwner := castOwnerParameter parameterEq last
  let shifted : OwnerPath (Paths.polynomial parameter)
      (Transport.Spatial.coordinate site parameter 2 unitQuarter positive finish.parameter)
      enteredOwner retained.1.val castOwner :=
    OwnerPath.castEndpoints rfl samePoint HEq.rfl (castOwnerParameter_heq parameterEq last).symm entered
  have castName : ownerName castOwner = ownerName last := by
    with_unfolding_all exact ownerRootName_castOwnerParameter parameterEq last
  let selectedAfter : OwnerSelection frame.owners castOwner :=
    ⟨after.index, NamedEquivalent.transport castName.symm rfl after.equivalent⟩
  have vertices := OwnerPath.castEndpoints_vertices (polynomial := Paths.polynomial parameter)
    rfl samePoint HEq.rfl (castOwnerParameter_heq parameterEq last).symm entered
  have paid : chainRaw (Paths.polynomial parameter) retained.1.val retained.2.2.2.vertices +
      chainRaw (Paths.polynomial parameter)
        (Transport.Spatial.coordinate site parameter 2 unitQuarter positive finish.parameter)
        shifted.vertices = 8 * turns :=
    (congrArg (fun points : List Canonical =>
      chainRaw (Paths.polynomial parameter) retained.1.val retained.2.2.2.vertices +
        chainRaw (Paths.polynomial parameter)
          (Transport.Spatial.coordinate site parameter 2 unitQuarter positive finish.parameter) points)
      vertices).trans winding
  let compared := ClearBoxRootTransport.equivalentOfReturnSelections (polynomial := Paths.polynomial parameter)
    (start := retained.1.val)
    (middle := Transport.Spatial.coordinate site parameter 2 unitQuarter positive finish.parameter)
    (first := retained.2.1) (returnedOwner := retained.2.2.1) (enteredOwner := enteredOwner) (last := castOwner)
    reference retained.2.2.2 handoff shifted frame before selectedAfter turns paid
  exact NamedEquivalent.transport castName rfl compared

end LastReturn

namespace LastAction

/-- Read the supplied last singleton's actual point, Owners and cached return trace.

Only the retained line bank and signed singleton are projected. The
original return trace is forced once without preparing another path,
root selection or comparison.
-/
@[expose] def lastReturn
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point) :
    LastAction (actual := actual) (regular := regular) (elimination := elimination)
      (clearances := clearances) (grid := grid)
      (fun finish => LastReturn (site := site) (parameter := parameter) (unitQuarter := unitQuarter)
        (positive := positive) (regular := regular) (finish := finish) elimination) reference :=
  fun _target _current _reading _originalOwner _original _sourceOwner _agreement
      _paid terminalLines _onGrid _cached _supplied terminal =>
    let suffix := Geometry.Lines.Bank.tail
      (elimination := elimination) (clearances := clearances) (regular := regular) terminalLines
    let targetLines := Geometry.Lines.Bank.head
      (elimination := elimination) (clearances := clearances) (regular := regular) suffix
    ⟨⟨targetLines.point, targetLines.point_eq⟩, terminal.1.val.2.1.val.traced.finishOwner,
      terminal.1.val.2.2.1.val.traced.finishOwner, terminal.1.val.2.2.1.val.traced.trace.get⟩

end LastAction

section LastReading

attribute [local irreducible] Steps.Acquisition Block Geometry coordinate
attribute [local irreducible] Block.DetourCache DetourWalkCache
attribute [local irreducible] DetourSpine

/-- Read the actual final original head's middle and return using its shared terminal continuation.

The existing dependent return view retains both literal cached Owners and
the original saved return trace. The original signed singleton is consumed
once; no route, comparison, root selection or numerical factory is run.
-/
@[expose] def lastReturn
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point) : (targets : List Endpoint) → (current : Endpoint) →
    (reading : ReadingAt actual current) → (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) → (lines : Lines paid elimination clearances) →
    (onGrid : ∀ value ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid value) →
    (cached : DetourWalkCache elimination clearances grid paid lines onGrid) →
    (supplied : Option (Block.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances grid reference targets current reading originalOwner original
      sourceOwner agreement paid lines onGrid cached supplied) → (nonempty : targets ≠ []) →
    LastReturn (site := site) (parameter := parameter) (unitQuarter := unitQuarter) (positive := positive)
      (regular := regular) (finish := finalTarget current targets) elimination
  | [], _current, _reading, _originalOwner, _original, _sourceOwner, _agreement,
      _paid, _lines, _onGrid, _cached, _supplied, _prepared, nonempty => False.elim (nonempty rfl)
  | target :: targets, current, reading, originalOwner, original, sourceOwner, agreement,
      paid, lines, onGrid, cached, supplied, prepared, _nonempty =>
    withLast (actual := actual) (regular := regular)
      (Result := fun finish => LastReturn (site := site) (parameter := parameter) (unitQuarter := unitQuarter)
        (positive := positive) (regular := regular) (finish := finish) elimination)
      elimination clearances grid reference
      (LastAction.lastReturn (actual := actual) (regular := regular)
        elimination clearances grid reference)
      targets target current reading originalOwner original sourceOwner agreement
      paid lines onGrid cached supplied prepared

end LastReading

/-- The literal retained original return finishes at the original shared signed-spine Owner. -/
theorem lastReturn_finishOwner
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point) : (targets : List Endpoint) → (current : Endpoint) →
    (reading : ReadingAt actual current) → (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) → (lines : Lines paid elimination clearances) →
    (onGrid : ∀ value ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid value) →
    (cached : DetourWalkCache elimination clearances grid paid lines onGrid) →
    (supplied : Option (Block.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances grid reference targets current reading originalOwner original
      sourceOwner agreement paid lines onGrid cached supplied) → (nonempty : targets ≠ []) →
    (lastReturn elimination clearances grid reference targets current reading originalOwner original
      sourceOwner agreement paid lines onGrid cached supplied prepared nonempty).2.2.1 =
      finishOwner elimination clearances grid reference targets current reading originalOwner original
        sourceOwner agreement paid lines onGrid cached supplied prepared := by
  intro targets
  induction targets with
  | nil =>
    intros current reading originalOwner original sourceOwner agreement paid lines onGrid cached supplied
      prepared nonempty
    exact False.elim (nonempty rfl)
  | cons target targets induction =>
    intros current reading originalOwner original sourceOwner agreement paid lines onGrid cached supplied
      prepared nonempty
    cases targets with
    | nil => rfl
    | cons next rest =>
      exact induction target original.nextReading original.headCovered.finishOwner
        original.tail paid.head.finishOwner paid.head.nextAgreement paid.tail
        (Geometry.Lines.Bank.tail (elimination := elimination) (clearances := clearances) (regular := regular) lines)
        (fun point member => onGrid point (List.Mem.tail _ member))
        (tailDetourWalks elimination clearances grid paid lines onGrid cached)
        (some ⟨Block.DetourCache.finishOwner prepared.1, Block.DetourCache.equivalent prepared.1⟩) prepared.2
        (by intro empty; exact Nat.succ_ne_zero _ (congrArg List.length empty))

/-- The actual terminal return of a nonempty signed spine has its sharp-square endpoint winding.

Structural traversal follows the same retained paid, line, numerical and
signed tails. The final cached connector supplies its own potential law
inside the original target square. No return path, root classification or
winding certificate is acquired along the fold.
-/
theorem lastReturn_winding
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point) : (targets : List Endpoint) → (current : Endpoint) →
    (reading : ReadingAt actual current) → (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) → (lines : Lines paid elimination clearances) →
    (onGrid : ∀ value ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid value) →
    (cached : DetourWalkCache elimination clearances grid paid lines onGrid) →
    (supplied : Option (Block.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances grid reference targets current reading originalOwner original
      sourceOwner agreement paid lines onGrid cached supplied) → (nonempty : targets ≠ []) →
    (clearance : RegionClearance (Paths.polynomial parameter)
      (box site parameter unitQuarter (finalTarget current targets).parameter regular)) →
    let returned := lastReturn elimination clearances grid reference targets current reading originalOwner original
      sourceOwner agreement paid lines onGrid cached supplied prepared nonempty
    chainRaw (Paths.polynomial parameter) returned.1.val returned.2.2.2.vertices =
      windingPotential (Paths.polynomial parameter)
        (box site parameter unitQuarter (finalTarget current targets).parameter regular)
        (coordinate site parameter 2 unitQuarter positive (finalTarget current targets).parameter) -
      windingPotential (Paths.polynomial parameter)
        (box site parameter unitQuarter (finalTarget current targets).parameter regular) returned.1.val := by
  intro targets
  induction targets with
  | nil =>
    intros current reading originalOwner original sourceOwner agreement paid lines onGrid cached supplied
      prepared nonempty clearance
    exact False.elim (nonempty rfl)
  | cons target targets induction =>
    intros current reading originalOwner original sourceOwner agreement paid lines onGrid cached supplied
      prepared nonempty clearance
    cases targets with
    | nil => exact prepared.1.return_winding clearance
    | cons next rest =>
      exact induction target original.nextReading original.headCovered.finishOwner
        original.tail paid.head.finishOwner paid.head.nextAgreement paid.tail
        (Geometry.Lines.Bank.tail (elimination := elimination) (clearances := clearances) (regular := regular) lines)
        (fun point member => onGrid point (List.Mem.tail _ member))
        (tailDetourWalks elimination clearances grid paid lines onGrid cached)
        (some ⟨Block.DetourCache.finishOwner prepared.1, Block.DetourCache.equivalent prepared.1⟩) prepared.2
        (by intro empty; exact Nat.succ_ne_zero _ (congrArg List.length empty)) clearance

section CachedReadbacks

attribute [local irreducible] Steps.Acquisition Block Geometry coordinate
attribute [local irreducible] Block.DetourCache DetourWalkCache

/-- Read the existing cached final relation to the unchanged original paid finish Owner. -/
def equivalent
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point) : (targets : List Endpoint) → (current : Endpoint) →
    (reading : ReadingAt actual current) → (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) → (lines : Lines paid elimination clearances) →
    (onGrid : ∀ value ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid value) →
    (cached : DetourWalkCache elimination clearances grid paid lines onGrid) →
    (supplied : Option (Block.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances grid reference targets current reading originalOwner original
      sourceOwner agreement paid lines onGrid cached supplied) →
    NamedEquivalent (ownerName (finishOwner elimination clearances grid reference targets current reading
      originalOwner original sourceOwner agreement paid lines onGrid cached supplied prepared))
      (ownerName paid.finishOwner)
  | [], _current, _reading, _originalOwner, _original, sourceOwner, _agreement,
      _paid, _lines, _onGrid, _cached, supplied, _prepared => Block.Start.equivalent sourceOwner supplied
  | target :: targets, _current, _reading, _originalOwner, original, _sourceOwner, _agreement,
      paid, lines, onGrid, cached, _supplied, prepared =>
      let suffix := Geometry.Lines.Bank.tail
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      let retained := equivalent reference targets target original.nextReading original.headCovered.finishOwner
        original.tail paid.head.finishOwner paid.head.nextAgreement paid.tail suffix
        (fun point member => onGrid point (List.Mem.tail _ member))
        (tailDetourWalks elimination clearances grid paid lines onGrid cached)
        (some ⟨prepared.1.finishOwner, prepared.1.equivalent⟩) prepared.2
      let restored := Eq.mp (congrArg (fun owner => NamedEquivalent
        (ownerName (finishOwner elimination clearances grid reference targets target original.nextReading
          original.headCovered.finishOwner original.tail paid.head.finishOwner paid.head.nextAgreement paid.tail suffix
          (fun point member => onGrid point (List.Mem.tail _ member))
          (tailDetourWalks elimination clearances grid paid lines onGrid cached)
          (some ⟨prepared.1.finishOwner, prepared.1.equivalent⟩) prepared.2))
        (ownerName owner)) paid.finishOwner_tail) retained
      NamedEquivalent.transport
        (congrArg ownerName (finishOwner_cons elimination clearances grid reference targets target _current _reading
          _originalOwner original _sourceOwner _agreement paid lines onGrid cached _supplied prepared).symm)
        rfl restored

/-- Read the complete ordered chain of the literal retained signed covers. -/
@[expose] def blocks
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point) : (targets : List Endpoint) → (current : Endpoint) →
    (reading : ReadingAt actual current) → (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) → (lines : Lines paid elimination clearances) →
    (onGrid : ∀ value ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid value) →
    (cached : DetourWalkCache elimination clearances grid paid lines onGrid) →
    (supplied : Option (Block.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances grid reference targets current reading originalOwner original
      sourceOwner agreement paid lines onGrid cached supplied) →
    CoveredTracedPath.Blocks (Paths.polynomial parameter)
      (coordinate site parameter 2 unitQuarter positive current.parameter) (Block.Start.owner sourceOwner supplied)
      (coordinate site parameter 2 unitQuarter positive (finalTarget current targets).parameter)
      (finishOwner elimination clearances grid reference targets current reading originalOwner original
        sourceOwner agreement paid lines onGrid cached supplied prepared)
  | [], _current, _reading, _originalOwner, _original, sourceOwner, _agreement,
      _paid, _lines, _onGrid, _cached, supplied, _prepared => .nil _ (Block.Start.owner sourceOwner supplied)
  | target :: targets, _current, _reading, _originalOwner, original, _sourceOwner, _agreement,
      paid, lines, onGrid, cached, _supplied, prepared =>
      let suffix := Geometry.Lines.Bank.tail
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      let joined := (Block.DetourCache.blocks prepared.1).append
        (blocks reference targets target original.nextReading original.headCovered.finishOwner
          original.tail paid.head.finishOwner paid.head.nextAgreement paid.tail suffix
          (fun point member => onGrid point (List.Mem.tail _ member))
          (tailDetourWalks elimination clearances grid paid lines onGrid cached)
          (some ⟨prepared.1.finishOwner, prepared.1.equivalent⟩) prepared.2)
      Eq.mp (congrArg (fun owner => CoveredTracedPath.Blocks (Paths.polynomial parameter)
        (coordinate site parameter 2 unitQuarter positive _current.parameter)
        (Block.Start.owner _sourceOwner _supplied)
        (coordinate site parameter 2 unitQuarter positive (finalTarget target targets).parameter) owner)
        (finishOwner_cons elimination clearances grid reference targets target _current _reading
          _originalOwner original _sourceOwner _agreement paid lines onGrid cached _supplied prepared).symm) joined

/-- Read the literal first entry-finish Owner of an actual nonempty signed Steps spine.

The selected source point is the original retained head-line point. The
cached Block supplies its entire Owner without a parameter cast, another
root acquisition or a new selection. The actual target-list certificate
excludes the empty branch.
-/
@[expose] def entryOwner
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point) : (targets : List Endpoint) → (current : Endpoint) →
    (reading : ReadingAt actual current) → (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) → (lines : Lines paid elimination clearances) →
    (onGrid : ∀ value ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid value) →
    (cached : DetourWalkCache elimination clearances grid paid lines onGrid) →
    (supplied : Option (Block.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances grid reference targets current reading originalOwner original
      sourceOwner agreement paid lines onGrid cached supplied) →
    (nonempty : targets ≠ []) →
    let source := Geometry.Lines.Bank.head
      (elimination := elimination) (clearances := clearances) (regular := regular) lines
    Riemann.Topology.SquareRootContinuationChain.Owner ((Paths.polynomial parameter).eval source.point)
  | [], _current, _reading, _originalOwner, _original, _sourceOwner, _agreement,
      _paid, _lines, _onGrid, _cached, _supplied, _prepared, nonempty => False.elim (nonempty rfl)
  | _target :: _targets, _current, _reading, _originalOwner, _original, _sourceOwner, _agreement,
      _paid, _lines, _onGrid, _cached, _supplied, prepared, _nonempty =>
      Block.DetourCache.entryOwner prepared.1

/-- Read the first actual middle Owner from a retained nonempty original Steps signed spine.

The original source-line equality transports only the parameter index of
the cached entry finish. The complete Owner and track remain unchanged;
the empty branch is excluded by the actual target-list witness.
-/
@[expose] def middleSource
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point) : (targets : List Endpoint) → (current : Endpoint) →
    (reading : ReadingAt actual current) → (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) → (lines : Lines paid elimination clearances) →
    (onGrid : ∀ value ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid value) →
    (cached : DetourWalkCache elimination clearances grid paid lines onGrid) →
    (supplied : Option (Block.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances grid reference targets current reading originalOwner original
      sourceOwner agreement paid lines onGrid cached supplied) →
    (nonempty : targets ≠ []) →
    Riemann.Topology.SquareRootContinuationChain.Owner ((Paths.polynomial parameter).eval
      (Geometry.move elimination regular (coordinate site parameter 2 unitQuarter positive current.parameter)))
  | [], _current, _reading, _originalOwner, _original, _sourceOwner, _agreement,
      _paid, _lines, _onGrid, _cached, _supplied, _prepared, nonempty => False.elim (nonempty rfl)
  | _target :: _targets, _current, _reading, _originalOwner, _original, _sourceOwner, _agreement,
      _paid, lines, _onGrid, _cached, _supplied, prepared, _nonempty =>
      let source := Geometry.Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      RootIsolation.SquareRoot.Owner.Transport.castOwnerParameter
        (congrArg (Paths.polynomial parameter).eval source.point_eq) (entryOwner (actual := actual) (regular := regular)
          elimination clearances grid reference (_target :: _targets) _current _reading _originalOwner _original
          _sourceOwner _agreement _paid lines _onGrid _cached _supplied prepared _nonempty)

/-- The moved-source view retains the literal original first entry root name.

Only the certified cached source-point equality changes the Owner's
parameter. The retained name and entire original track remain unchanged.
-/
theorem middleSource_name
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point)
    (targets : List Endpoint) (current : Endpoint) (reading : ReadingAt actual current)
    (originalOwner : OwnerAt site parameter unitQuarter positive current)
    (original : Steps actual regular current reading originalOwner targets)
    (sourceOwner : OwnerAt site parameter unitQuarter positive current)
    (agreement : InitialAgreement current reading sourceOwner)
    (paid : Acquisition original sourceOwner agreement) (lines : Lines paid elimination clearances)
    (onGrid : ∀ value ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid value)
    (cached : DetourWalkCache elimination clearances grid paid lines onGrid)
    (supplied : Option (Block.Start sourceOwner))
    (prepared : DetourSpine elimination clearances grid reference targets current reading originalOwner original
      sourceOwner agreement paid lines onGrid cached supplied)
    (nonempty : targets ≠ []) :
    ownerName (middleSource elimination clearances grid reference targets current reading originalOwner original
      sourceOwner agreement paid lines onGrid cached supplied prepared nonempty) =
      ownerName (entryOwner elimination clearances grid reference targets current reading originalOwner original
      sourceOwner agreement paid lines onGrid cached supplied prepared nonempty) := by
  cases targets with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest =>
      with_unfolding_all exact ownerRootName_castOwnerParameter _ _

/-- Read the same cached first entry path at the original moved-source index of a nonempty signed spine.

The retained line equality changes only the path's final coordinate index
and that identical cached Owner's parameter. The supplied start, original
entry links and numerical head remain unchanged.
-/
@[expose] def entryTrace
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point) : (targets : List Endpoint) → (current : Endpoint) →
    (reading : ReadingAt actual current) → (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) → (lines : Lines paid elimination clearances) →
    (onGrid : ∀ value ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid value) →
    (cached : DetourWalkCache elimination clearances grid paid lines onGrid) →
    (supplied : Option (Block.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances grid reference targets current reading originalOwner original
      sourceOwner agreement paid lines onGrid cached supplied) →
    (nonempty : targets ≠ []) →
    OwnerPath (Paths.polynomial parameter)
      (coordinate site parameter 2 unitQuarter positive current.parameter) (Block.Start.owner sourceOwner supplied)
      (Geometry.move elimination regular (coordinate site parameter 2 unitQuarter positive current.parameter))
      (middleSource elimination clearances grid reference targets current reading originalOwner original
        sourceOwner agreement paid lines onGrid cached supplied prepared nonempty)
  | [], _current, _reading, _originalOwner, _original, _sourceOwner, _agreement,
      _paid, _lines, _onGrid, _cached, _supplied, _prepared, nonempty => False.elim (nonempty rfl)
  | _target :: _targets, _current, _reading, _originalOwner, _original, _sourceOwner, _agreement,
      _paid, lines, _onGrid, _cached, _supplied, prepared, _nonempty =>
      let source := Geometry.Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      OwnerPath.castEndpoints rfl source.point_eq HEq.rfl
        (Owner.Transport.castOwnerParameter_heq
          (congrArg (Paths.polynomial parameter).eval source.point_eq) (Block.DetourCache.entryOwner prepared.1)).symm
        prepared.1.entryTrace

/-- The original signed spine's cached first entry has its sharp-source-square endpoint winding.

Exact endpoint transport preserves the complete saved vertex list. The
original first Block supplies the winding formula, and the stored line
readback gives the same moved-source coordinate used by `middleSource`.
-/
theorem entryTrace_winding
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point) : (targets : List Endpoint) → (current : Endpoint) →
    (reading : ReadingAt actual current) → (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) → (lines : Lines paid elimination clearances) →
    (onGrid : ∀ value ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid value) →
    (cached : DetourWalkCache elimination clearances grid paid lines onGrid) →
    (supplied : Option (Block.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances grid reference targets current reading originalOwner original
      sourceOwner agreement paid lines onGrid cached supplied) →
    (nonempty : targets ≠ []) →
    chainRaw (Paths.polynomial parameter) (coordinate site parameter 2 unitQuarter positive current.parameter)
      (entryTrace elimination clearances grid reference targets current reading originalOwner original
        sourceOwner agreement paid lines onGrid cached supplied prepared nonempty).vertices =
      windingPotential (Paths.polynomial parameter) (box site parameter unitQuarter current.parameter regular)
        (Geometry.move elimination regular (coordinate site parameter 2 unitQuarter positive current.parameter)) -
      windingPotential (Paths.polynomial parameter) (box site parameter unitQuarter current.parameter regular)
        (coordinate site parameter 2 unitQuarter positive current.parameter) := by
  intro targets
  cases targets with
  | nil =>
    intros current reading originalOwner original sourceOwner agreement paid lines onGrid cached supplied
      prepared nonempty
    exact False.elim (nonempty rfl)
  | cons target targets =>
    intros current reading originalOwner original sourceOwner agreement paid lines onGrid cached supplied
      prepared nonempty
    let source := Geometry.Lines.Bank.head
      (elimination := elimination) (clearances := clearances) (regular := regular) lines
    have vertices := OwnerPath.castEndpoints_vertices rfl source.point_eq HEq.rfl
      (Owner.Transport.castOwnerParameter_heq
        (congrArg (Paths.polynomial parameter).eval source.point_eq) (Block.DetourCache.entryOwner prepared.1)).symm
      prepared.1.entryTrace
    exact (congrArg (chainRaw (Paths.polynomial parameter)
      (coordinate site parameter 2 unitQuarter positive current.parameter)) vertices).trans
        (prepared.1.entry_winding.trans (congrArg (fun point =>
          windingPotential (Paths.polynomial parameter) (box site parameter unitQuarter current.parameter regular)
            point -
          windingPotential (Paths.polynomial parameter) (box site parameter unitQuarter current.parameter regular)
            (coordinate site parameter 2 unitQuarter positive current.parameter)) source.point_eq))

end CachedReadbacks

end DetourSpine

end Detour

end Steps.Acquisition

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
