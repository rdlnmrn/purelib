module

import Purelib.RootIsolation.SquareRoot.Owner.Transport

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Spatial.Block
public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Blocks
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition
import Purelib.Data.List.Membership
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Polynomial.Clearance.Box.Region

/-! # Actual paid Blocks following the SAME original numerical pieces

Every actual old numerical source is read from its retained piece. One
supplied complete final query ends the chain. No time query, initial Source
attachment or unpaid cover is acquired by this fold. Each original paid
Block hands its literal finishOwner and cached target agreement onward.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer

open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Geometry

namespace Spatial

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
open Purelib.Riemann.Paths.ClearBoxPathWinding.ClearBoxPaths (windingPotential)
open Purelib.Polynomial.Winding.Polygon.Basic (chainRaw)
open Purelib.Polynomial.Clearance.Box.Region (RegionClearance)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.RootIsolation.SquareRoot
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
  (ownerRootName ownerRootName_castOwnerParameter)
open Transport.Spatial
open Transport.Spatial.Parallel.Steps.Acquisition renaming Block → StepBlock

variable {radicand : CoefficientPolynomial}
variable {site : Fin 2} {parameter : Canonical} {differential : OddPowerDifferential radicand}
variable {data : Waist.Differential.Bounds.Data site parameter differential}
variable {quarter : UnitCircuitQuarter} {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive} {accuracy : AccuracyRequest}

attribute [local irreducible] Transport.Spatial.coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- A paid ordered realization of the SAME old numerical piece list with one supplied final target cache.

The original first piece is separate from its actual remaining list, so
structural recursion never discards or replaces its old source/Model. Each
head stores its complete original paid Block. Its literal finishOwner and
cached next agreement index the actual tail on the SAME next piece.source.
-/
@[expose] def Acquisition (regular : parameter ≠ criticalValue site)
    {finish : Endpoint} (finishQuery : { reading : ReadingAt actual finish // QueryCache actual finish reading }) :
    (remaining : List (Piece data actual accuracy)) → (first : Piece data actual accuracy) →
    (queried : ∀ piece ∈ remaining, piece.Queried) →
    (sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint) →
    (agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner) → Type 1
  | [] => fun first _ sourceOwner agreement => Block (regular := regular) first finishQuery sourceOwner agreement
  | next :: remaining => fun first queried sourceOwner agreement =>
      let nextQuery := next.sourceQuery (queried next (List.Mem.head remaining))
      Σ block : Block (regular := regular) first nextQuery sourceOwner agreement,
        Acquisition regular finishQuery remaining next
          (fun piece member => queried piece (List.Mem.tail next member)) block.finishOwner block.nextAgreement
termination_by structural remaining => remaining

namespace Acquisition

variable {regular : parameter ≠ criticalValue site}
variable {finish : Endpoint}
variable (finishQuery : { reading : ReadingAt actual finish // QueryCache actual finish reading })

/-- Build the actual paid chain from exact old span incidence, widths and original cached query receipts.

The Chain and width certificates are intrinsic to the supplied original
Layer. They pay each actual head internally. Later source readings and
agreements are literal retained target caches; no desired terminal root
relation or final error bound is an input to this construction.
-/
def build : (remaining : List (Piece data actual accuracy)) → (first : Piece data actual accuracy) →
    (queried : ∀ piece ∈ remaining, piece.Queried) →
    (sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint) →
    (agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner) →
    (chain : Interval.Chain first.span.lower finish.parameter (Piece.chartIntervals (first :: remaining))) →
    (widths : ∀ piece ∈ first :: remaining, piece.span.width ^ 2 ≤ Geometric.Basic.quarterRadius 1 7) →
      Acquisition regular finishQuery remaining first queried sourceOwner agreement
  | [] => fun first _ sourceOwner agreement chain widths =>
      have incidence : finish.parameter = first.span.upper :=
        (Interval.Chain.finish_eq chain 0
          (by change 0 < 1; exact of_decide_eq_true rfl) rfl).symm
      Block.build first finishQuery sourceOwner agreement incidence (widths first (List.Mem.head []))
  | next :: remaining => fun first queried sourceOwner agreement chain widths =>
      have incidence : next.lowerEndpoint.parameter = first.span.upper :=
        (Interval.Chain.adjacent chain 0
          (by
            rewrite [Piece.chartIntervals, Data.List.Map.length_map]
            exact Nat.zero_lt_succ _)
          (by
            rewrite [Piece.chartIntervals, Data.List.Map.length_map]
            exact Nat.succ_lt_succ (Nat.zero_lt_succ _))).symm
      let nextQuery := next.sourceQuery (queried next (List.Mem.head remaining))
      let block := Block.build first nextQuery sourceOwner agreement incidence
        (widths first (List.Mem.head (next :: remaining)))
      have tailChain : Interval.Chain next.span.lower finish.parameter (Piece.chartIntervals (next :: remaining)) := by
        have removeHead : ∀ {left middle right : Fraction.Rational} {intervals : List Integration.Partition.Interval},
            Interval.Chain left right (⟨left, middle⟩ :: intervals) → Interval.Chain middle right intervals := by
          intro left middle right intervals retained
          cases retained with
          | cons rest => exact rest
        have rest : Interval.Chain first.span.upper finish.parameter
            (Piece.chartIntervals (next :: remaining)) := removeHead chain
        have same : first.span.upper = next.span.lower := incidence.symm
        exact (congrArg (fun left => Interval.Chain left finish.parameter
          (Piece.chartIntervals (next :: remaining))) same).mp rest
      let tail := build remaining next
        (fun piece member => queried piece (List.Mem.tail next member)) block.finishOwner block.nextAgreement tailChain
        (fun piece member => widths piece (List.Mem.tail first member))
      ⟨block, tail⟩
termination_by structural remaining => remaining

variable {finishQuery}

/-- Read the actual original head Block without rebuilding any Geometry, source observation or paid preparation. -/
@[expose] def head : {remaining : List (Piece data actual accuracy)} → {first : Piece data actual accuracy} →
    {queried : ∀ piece ∈ remaining, piece.Queried} →
    {sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint} →
    {agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner} →
    (paid : Acquisition regular finishQuery remaining first queried sourceOwner agreement) →
      match remaining with
      | [] => Block (regular := regular) first finishQuery sourceOwner agreement
      | next :: rest => Block (regular := regular) first
          (next.sourceQuery (queried next (List.Mem.head rest))) sourceOwner agreement
  | [], _, _, _, _, paid => paid
  | _ :: _, _, _, _, _, paid => paid.1

/-- Read the exact dependent tail on the SAME next piece.source and literal preceding paid finishOwner/agreement. -/
@[expose] def tail {next : Piece data actual accuracy} {remaining : List (Piece data actual accuracy)}
    {first : Piece data actual accuracy} {queried : ∀ piece ∈ next :: remaining, piece.Queried}
    {sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint}
    {agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner}
    (paid : Acquisition regular finishQuery (next :: remaining) first queried sourceOwner agreement) :
    Acquisition regular finishQuery remaining next
      (fun piece member => queried piece (List.Mem.tail next member)) paid.head.finishOwner paid.head.nextAgreement :=
  paid.2

/-- Read the actual final Owner by following only literal stored paid finishOwner handoffs. -/
@[expose] def finishOwner : {remaining : List (Piece data actual accuracy)} → {first : Piece data actual accuracy} →
    {queried : ∀ piece ∈ remaining, piece.Queried} →
    {sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint} →
    {agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner} →
    (paid : Acquisition regular finishQuery remaining first queried sourceOwner agreement) →
      OwnerAt site parameter quarter positive finish
  | [], _first, _queried, _sourceOwner, _agreement, paid => Block.finishOwner paid
  | _ :: _, _first, _queried, _sourceOwner, _agreement, paid => finishOwner paid.2

/-- Removing the actual first fine paid Block preserves the complete retained final Owner. -/
theorem finishOwner_tail {next : Piece data actual accuracy} {remaining : List (Piece data actual accuracy)}
    {first : Piece data actual accuracy} {queried : ∀ piece ∈ next :: remaining, piece.Queried}
    {sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint}
    {agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner}
    (paid : Acquisition regular finishQuery (next :: remaining) first queried sourceOwner agreement) :
    paid.tail.finishOwner = paid.finishOwner := (rfl)

/-- The actual final paid Owner agrees with the SAME independently retained original final target Lift. -/
def finishEquivalent : {remaining : List (Piece data actual accuracy)} → {first : Piece data actual accuracy} →
    {queried : ∀ piece ∈ remaining, piece.Queried} →
    {sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint} →
    {agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner} →
    (paid : Acquisition regular finishQuery remaining first queried sourceOwner agreement) →
      NamedEquivalent (ownerRootName paid.finishOwner.parameterNonzero paid.finishOwner) finishQuery.val.lift.value.name
  | [], _first, _queried, _sourceOwner, _agreement, paid =>
      Steps.Acquisition.Block.finishEquivalent paid.paid
  | _ :: _, _first, _queried, _sourceOwner, _agreement, paid => finishEquivalent paid.2

/-- The whole varying-box covered chain retains every original actual paid cover and exact terminal-owner index. -/
@[expose] def blocks : {remaining : List (Piece data actual accuracy)} → {first : Piece data actual accuracy} →
    {queried : ∀ piece ∈ remaining, piece.Queried} →
    {sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint} →
    {agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner} →
    (paid : Acquisition regular finishQuery remaining first queried sourceOwner agreement) →
      CoveredTracedPath.Blocks (Paths.polynomial parameter)
        (Transport.Spatial.coordinate site parameter 2 quarter positive first.span.lower) sourceOwner
        (Transport.Spatial.coordinate site parameter 2 quarter positive finish.parameter) paid.finishOwner
  | [], _first, _queried, _sourceOwner, _agreement, paid =>
      CoveredTracedPath.Blocks.singleton paid.paid.paid.covered
  | _ :: _, _first, _queried, _sourceOwner, _agreement, paid =>
      .cons paid.1.paid.paid.covered (blocks paid.2)

/-- Read the SAME original complete covered-path trace with all actual signed stationary/moving occurrences. -/
@[expose] def trace {remaining : List (Piece data actual accuracy)} {first : Piece data actual accuracy}
    {queried : ∀ piece ∈ remaining, piece.Queried}
    {sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint}
    {agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner}
    (paid : Acquisition regular finishQuery remaining first queried sourceOwner agreement) :
    OwnerPath (Paths.polynomial parameter)
      (Transport.Spatial.coordinate site parameter 2 quarter positive first.span.lower) sourceOwner
      (Transport.Spatial.coordinate site parameter 2 quarter positive finish.parameter) paid.finishOwner :=
  paid.blocks.trace

/-- Count the actual retained paid Blocks on the SAME original numerical piece list. -/
@[expose] def blockCount : {remaining : List (Piece data actual accuracy)} → {first : Piece data actual accuracy} →
    {queried : ∀ piece ∈ remaining, piece.Queried} →
    {sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint} →
    {agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner} →
    Acquisition regular finishQuery remaining first queried sourceOwner agreement → Nat
  | [], _first, _queried, _sourceOwner, _agreement, _paid => 1
  | _ :: _, _first, _queried, _sourceOwner, _agreement, paid => 1 + blockCount paid.2

/-- The actual ordered paid Block count is exactly the original numerical piece count, including the final span. -/
theorem blockCount_eq : {remaining : List (Piece data actual accuracy)} → {first : Piece data actual accuracy} →
    {queried : ∀ piece ∈ remaining, piece.Queried} →
    {sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint} →
    {agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner} →
    (paid : Acquisition regular finishQuery remaining first queried sourceOwner agreement) →
      paid.blockCount = remaining.length + 1
  | [], _first, _queried, _sourceOwner, _agreement, _paid => rfl
  | _ :: remaining, _first, _queried, _sourceOwner, _agreement, paid => by
      change 1 + blockCount paid.2 = (remaining.length + 1) + 1
      rewrite [blockCount_eq paid.2]
      exact Nat.add_comm _ _

/-- Every SAME retained actual head Route pays the common physical request before fine factor/arithmetic queries. -/
@[expose] def PointPayments (physical : AccuracyRequest) :
    {remaining : List (Piece data actual accuracy)} → {first : Piece data actual accuracy} →
    {queried : ∀ piece ∈ remaining, piece.Queried} →
    {sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint} →
    {agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner} →
    Acquisition regular finishQuery remaining first queried sourceOwner agreement → Prop
  | [], first, _queried, _sourceOwner, _agreement, paid =>
      Polynomial.Geometry.ClearPath.PointBound
        (Transport.Spatial.coordinate site parameter 2 quarter positive first.span.lower)
        physical.tolerance paid.geometry.route.path
  | _ :: _, first, _queried, _sourceOwner, _agreement, paid =>
      Polynomial.Geometry.ClearPath.PointBound
        (Transport.Spatial.coordinate site parameter 2 quarter positive first.span.lower)
        physical.tolerance paid.1.geometry.route.path ∧ PointPayments physical paid.2

/-- Original finite width certificates derive PointBound on every actual retained paid head and dependent tail. -/
theorem pointPayments (physical : AccuracyRequest) :
    {remaining : List (Piece data actual accuracy)} → {first : Piece data actual accuracy} →
    {queried : ∀ piece ∈ remaining, piece.Queried} →
    {sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint} →
    {agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner} →
    (paid : Acquisition regular finishQuery remaining first queried sourceOwner agreement) →
    (widths : ∀ piece ∈ first :: remaining, piece.span.width ^ 2 ≤
      Geometric.Basic.quarterRadius 1 (Geometry.widthMinimum site parameter physical)) →
      PointPayments physical paid
  | [], first, _queried, _sourceOwner, _agreement, paid, widths =>
      paid.pointBound physical (widths first (List.Mem.head []))
  | next :: remaining, first, _queried, _sourceOwner, _agreement, paid, widths =>
      ⟨paid.1.pointBound physical (widths first (List.Mem.head (next :: remaining))),
        pointPayments physical paid.2 (fun piece member => widths piece (List.Mem.tail first member))⟩

open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider (AxisClearances)
open Purelib.Polynomial.Dense.Gaussian.Bounds
open Purelib.Polynomial.Geometry

/-- The unchanged lower endpoints of the actual numerical pieces, followed by the literal final-query endpoint. -/
@[expose] def endpointList {remaining : List (Piece data actual accuracy)} {first : Piece data actual accuracy}
    {queried : ∀ piece ∈ remaining, piece.Queried}
    {sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint}
    {agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner}
    (_paid : Acquisition regular finishQuery remaining first queried sourceOwner agreement) : List Endpoint :=
  first.lowerEndpoint :: (remaining.map Piece.lowerEndpoint ++ [finish])

/-- The shared numerical line bank follows the literal endpoints of this SAME retained fine-piece realization. -/
abbrev Lines {degreeBound : Nat}
    {remaining : List (Piece data actual accuracy)} {first : Piece data actual accuracy}
    {queried : ∀ piece ∈ remaining, piece.Queried}
    {sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint}
    {agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner}
    (paid : Acquisition regular finishQuery remaining first queried sourceOwner agreement)
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (clearances : AxisClearances elimination) :=
  Lines.Bank elimination clearances regular actual.data.bound paid.endpointList
    (fun endpoint : Endpoint => Transport.Spatial.coordinate site parameter 2 quarter positive endpoint.parameter)
    (fun endpoint => Transport.Spatial.coordinate_inside site parameter 2 quarter
      positive actual.data.lower actual.data.upper actual.data.bound endpoint.parameter)

section Detour

variable {degreeBound : Nat}
variable (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
variable (clearances : AxisClearances elimination)
variable (grid : Grid.ClearGrid (Paths.polynomial parameter)
  (RootRadius.Box.largeSquareBox (Paths.polynomial parameter)))

attribute [local irreducible] Parallel.Geometry

/-- The same original target-occurrence product retains one Walk per actual fine piece.

The final supplied query remains the last target; every preceding target
is the unchanged next piece's lower endpoint. The family is the original
Steps acquisition's exact consecutive-endpoint view.
-/
abbrev DetourWalks (first : Piece data actual accuracy) (remaining : List (Piece data actual accuracy)) :=
  Steps.Acquisition.DetourWalks (site := site) (unitQuarter := quarter)
    (positive := positive) (regular := regular) elimination grid first.lowerEndpoint
      (remaining.map Piece.lowerEndpoint ++ [finish])

/-- Split the retained fine-piece sharp geometries on the same grid without acquiring any replacement Steps. -/
private def detourSpine : (remaining : List (Piece data actual accuracy)) → (first : Piece data actual accuracy) →
    (queried : ∀ piece ∈ remaining, piece.Queried) →
    (sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint) →
    (agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner) →
    (paid : Acquisition regular finishQuery remaining first queried sourceOwner agreement) →
    (lines : Lines paid elimination clearances) →
    (onGrid : ∀ point ∈ Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid point) →
    DetourWalks (regular := regular) (finish := finish) elimination grid first remaining ×
    {_walk : Grid.Walks.Walk grid
      (Parallel.Geometry.move elimination regular
        (Transport.Spatial.coordinate site parameter 2 quarter positive first.span.lower))
      (Parallel.Geometry.move elimination regular
        (Transport.Spatial.coordinate site parameter 2 quarter positive finish.parameter)) //
      Grid.FromStates.ContainsVertex grid (Parallel.Geometry.move elimination regular
        (Transport.Spatial.coordinate site parameter 2 quarter positive finish.parameter))}
  | [], first, _queried, _sourceOwner, _agreement, paid, lines, onGrid =>
      let source := Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      let suffix := Lines.Bank.tail
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      let target := Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := regular) suffix
      let head := paid.head
      let walk := Parallel.Geometry.detourWalk (actual := actual)
        (first := first.span.lower) (last := finish.parameter)
        (firstInside := first.lowerEndpoint.inside) (lastInside := finish.inside)
        (reading := first.source) (targetReading := finishQuery.val)
        (regular := regular) (payment := head.payment)
        head.geometry elimination clearances source target grid
        (onGrid source.point (List.Mem.head _))
        (onGrid target.point (List.Mem.tail _ (List.Mem.head _)))
      ⟨⟨walk, PUnit.unit⟩, ⟨walk, Eq.mp (congrArg (Grid.FromStates.ContainsVertex grid) target.point_eq)
        (onGrid target.point (List.Mem.tail _ (List.Mem.head _)))⟩⟩
  | next :: remaining, first, queried, _sourceOwner, _agreement, paid, lines, onGrid =>
      let source := Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      let suffix := Lines.Bank.tail
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      let target := Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := regular) suffix
      let head := paid.head
      let walk := Parallel.Geometry.detourWalk (actual := actual)
        (first := first.span.lower) (last := next.lowerEndpoint.parameter)
        (firstInside := first.lowerEndpoint.inside) (lastInside := next.lowerEndpoint.inside)
        (reading := first.source) (targetReading := (next.sourceQuery (queried next (List.Mem.head remaining))).val)
        (regular := regular) (payment := head.payment)
        head.geometry elimination clearances source target grid
        (onGrid source.point (List.Mem.head _))
        (onGrid target.point (List.Mem.tail _ (List.Mem.head _)))
      let rest := detourSpine remaining next
        (fun piece member => queried piece (List.Mem.tail next member))
        head.finishOwner head.nextAgreement paid.tail suffix
        (fun point member => onGrid point (List.Mem.tail _ member))
      ⟨⟨walk, rest.1⟩, ⟨walk.append rest.2.val, rest.2.property⟩⟩

/-- Retain the same fine-piece head Walks and their aggregate in one original paid-spine traversal. -/
def prepareDetourOn {remaining : List (Piece data actual accuracy)} {first : Piece data actual accuracy}
    {queried : ∀ piece ∈ remaining, piece.Queried}
    {sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint}
    {agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner}
    (paid : Acquisition regular finishQuery remaining first queried sourceOwner agreement)
    (lines : Lines paid elimination clearances)
    (grid : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter)))
    (onGrid : ∀ point ∈ Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid point) :
    DetourWalks (regular := regular) (finish := finish) elimination grid first remaining ×
    {_walk : Grid.Walks.Walk grid
      (Parallel.Geometry.move elimination regular
        (Transport.Spatial.coordinate site parameter 2 quarter positive first.span.lower))
      (Parallel.Geometry.move elimination regular
        (Transport.Spatial.coordinate site parameter 2 quarter positive finish.parameter)) //
      Grid.FromStates.ContainsVertex grid (Parallel.Geometry.move elimination regular
        (Transport.Spatial.coordinate site parameter 2 quarter positive finish.parameter))} :=
  detourSpine elimination clearances grid remaining first queried sourceOwner agreement paid lines onGrid

/-- Split this SAME fine-piece realization on a supplied grid containing its actual retained moved occurrences. -/
def detourOn {remaining : List (Piece data actual accuracy)} {first : Piece data actual accuracy}
    {queried : ∀ piece ∈ remaining, piece.Queried}
    {sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint}
    {agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner}
    (paid : Acquisition regular finishQuery remaining first queried sourceOwner agreement)
    (lines : Lines paid elimination clearances)
    (grid : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter)))
    (onGrid : ∀ point ∈ Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid point) :
    {_walk : Grid.Walks.Walk grid
      (Parallel.Geometry.move elimination regular
        (Transport.Spatial.coordinate site parameter 2 quarter positive first.span.lower))
      (Parallel.Geometry.move elimination regular
        (Transport.Spatial.coordinate site parameter 2 quarter positive finish.parameter)) //
      Grid.FromStates.ContainsVertex grid (Parallel.Geometry.move elimination regular
        (Transport.Spatial.coordinate site parameter 2 quarter positive finish.parameter))} :=
  (prepareDetourOn elimination clearances paid lines grid onGrid).2

/-- Construct the numeric detour of the SAME fine numerical piece realization on its own extended grid.

Every head reads its literal retained Geometry and every recursive call
consumes the actual paid tail on the SAME original next Piece. The line
bank is shared with the original Steps branch; no alternate quarter,
Reading, source attachment or paid Block is constructed here.
-/
def detour {remaining : List (Piece data actual accuracy)} {first : Piece data actual accuracy}
    {queried : ∀ piece ∈ remaining, piece.Queried}
    {sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint}
    {agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner}
    (paid : Acquisition regular finishQuery remaining first queried sourceOwner agreement)
    (lines : Lines paid elimination clearances)
    (base : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter))) :
    let pairs := Lines.Bank.pairs
      (elimination := elimination) (clearances := clearances) (regular := regular) lines
    {_walk : Grid.Walks.Walk (Grid.Extension.extend base (pairs.map Prod.fst) (pairs.map Prod.snd))
      (Parallel.Geometry.move elimination regular
        (Transport.Spatial.coordinate site parameter 2 quarter positive first.span.lower))
      (Parallel.Geometry.move elimination regular
        (Transport.Spatial.coordinate site parameter 2 quarter positive finish.parameter)) //
      Grid.FromStates.ContainsVertex (Grid.Extension.extend base (pairs.map Prod.fst) (pairs.map Prod.snd))
        (Parallel.Geometry.move elimination regular
          (Transport.Spatial.coordinate site parameter 2 quarter positive finish.parameter))} :=
  detourOn elimination clearances paid lines _
    (Lines.Bank.onExtended
      (elimination := elimination) (clearances := clearances) (regular := regular) lines base)

/-- The literal retained fine-piece Walk product and its exact original numeric factory equation. -/
@[expose] def DetourWalkCache {remaining : List (Piece data actual accuracy)} {first : Piece data actual accuracy}
    {queried : ∀ piece ∈ remaining, piece.Queried}
    {sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint}
    {agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner}
    (paid : Acquisition regular finishQuery remaining first queried sourceOwner agreement)
    (lines : Lines paid elimination clearances)
    (onGrid : ∀ point ∈ Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid point) :=
  {value // value = (prepareDetourOn elimination clearances paid lines grid onGrid).1}

/-- Read the literal stored final fine-piece Walk with its original Geometry factory certificate. -/
def lastDetourWalk
    {first : Piece data actual accuracy}
    {queried : ∀ piece ∈ ([] : List (Piece data actual accuracy)), piece.Queried}
    {sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint}
    {agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner}
    (paid : Acquisition regular finishQuery [] first queried sourceOwner agreement)
    (lines : Lines paid elimination clearances)
    (onGrid : ∀ point ∈ Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid point)
    (cached : DetourWalkCache elimination clearances grid paid lines onGrid) :
    let source := Lines.Bank.head
      (elimination := elimination) (clearances := clearances) (regular := regular) lines
    let suffix := Lines.Bank.tail
      (elimination := elimination) (clearances := clearances) (regular := regular) lines
    let target := Lines.Bank.head
      (elimination := elimination) (clearances := clearances) (regular := regular) suffix
    {value : Grid.Walks.Walk grid
        (Parallel.Geometry.move elimination regular
          (Transport.Spatial.coordinate site parameter 2 quarter positive first.span.lower))
        (Parallel.Geometry.move elimination regular
          (Transport.Spatial.coordinate site parameter 2 quarter positive finish.parameter)) //
      value = Parallel.Geometry.detourWalk (actual := actual)
        (first := first.span.lower) (last := finish.parameter)
        (firstInside := first.lowerEndpoint.inside) (lastInside := finish.inside)
        (reading := first.source) (targetReading := finishQuery.val)
        (regular := regular) (payment := paid.head.payment)
        paid.head.geometry elimination clearances source target grid
        (onGrid source.point (List.Mem.head _))
        (onGrid target.point (List.Mem.tail _ (List.Mem.head _)))} :=
  ⟨cached.val.1, congrArg Prod.fst cached.property⟩

/-- Read the literal stored first fine-piece Walk with its original Geometry factory certificate. -/
def headDetourWalk
    {remaining : List (Piece data actual accuracy)} {next : Piece data actual accuracy}
    {first : Piece data actual accuracy}
    {queried : ∀ piece ∈ ((next :: remaining)), piece.Queried}
    {sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint}
    {agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner}
    (paid : Acquisition regular finishQuery (next :: remaining) first queried sourceOwner agreement)
    (lines : Lines paid elimination clearances)
    (onGrid : ∀ point ∈ Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid point)
    (cached : DetourWalkCache elimination clearances grid paid lines onGrid) :
    let source := Lines.Bank.head
      (elimination := elimination) (clearances := clearances) (regular := regular) lines
    let suffix := Lines.Bank.tail
      (elimination := elimination) (clearances := clearances) (regular := regular) lines
    let target := Lines.Bank.head
      (elimination := elimination) (clearances := clearances) (regular := regular) suffix
    {value : Grid.Walks.Walk grid
        (Parallel.Geometry.move elimination regular
          (Transport.Spatial.coordinate site parameter 2 quarter positive first.span.lower))
        (Parallel.Geometry.move elimination regular
          (Transport.Spatial.coordinate site parameter 2 quarter positive next.lowerEndpoint.parameter)) //
      value = Parallel.Geometry.detourWalk (actual := actual)
        (first := first.span.lower) (last := next.lowerEndpoint.parameter)
        (firstInside := first.lowerEndpoint.inside) (lastInside := next.lowerEndpoint.inside)
        (reading := first.source) (targetReading := (next.sourceQuery (queried next (List.Mem.head remaining))).val)
        (regular := regular) (payment := paid.head.payment)
        paid.head.geometry elimination clearances source target grid
        (onGrid source.point (List.Mem.head _))
        (onGrid target.point (List.Mem.tail _ (List.Mem.head _)))} :=
  ⟨cached.val.1, congrArg Prod.fst cached.property⟩

/-- Read the literal remaining fine-piece Walks with their same original paid-tail factory equation. -/
def tailDetourWalks
    {remaining : List (Piece data actual accuracy)} {next : Piece data actual accuracy}
    {first : Piece data actual accuracy}
    {queried : ∀ piece ∈ ((next :: remaining)), piece.Queried}
    {sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint}
    {agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner}
    (paid : Acquisition regular finishQuery (next :: remaining) first queried sourceOwner agreement)
    (lines : Lines paid elimination clearances)
    (onGrid : ∀ point ∈ Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid point)
    (cached : DetourWalkCache elimination clearances grid paid lines onGrid) :
    let suffix := Lines.Bank.tail
      (elimination := elimination) (clearances := clearances) (regular := regular) lines
    DetourWalkCache elimination clearances grid paid.tail suffix
      (fun point member => onGrid point (List.Mem.tail _ member)) :=
  ⟨cached.val.2, congrArg Prod.snd cached.property⟩

/-- The singleton fine aggregate is the identical retained final head Walk. -/
theorem prepareDetourOn_last
    {first : Piece data actual accuracy}
    {queried : ∀ piece ∈ ([] : List (Piece data actual accuracy)), piece.Queried}
    {sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint}
    {agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner}
    (paid : Acquisition regular finishQuery [] first queried sourceOwner agreement)
    (lines : Lines paid elimination clearances)
    (onGrid : ∀ point ∈ Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid point)
    (cached : DetourWalkCache elimination clearances grid paid lines onGrid) :
    (prepareDetourOn elimination clearances paid lines grid onGrid).2.val =
      (lastDetourWalk elimination clearances grid paid lines onGrid cached).val := by
  exact (congrArg Prod.fst cached.property).symm

/-- The fine cons aggregate appends its literal saved head to its unchanged actual paid tail.

Only the retained numeric factory equality supplies the head readback.
Both original paid and selected-line suffixes are preserved in order.
-/
theorem prepareDetourOn_cons
    {remaining : List (Piece data actual accuracy)} {next : Piece data actual accuracy}
    {first : Piece data actual accuracy}
    {queried : ∀ piece ∈ ((next :: remaining)), piece.Queried}
    {sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint}
    {agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner}
    (paid : Acquisition regular finishQuery (next :: remaining) first queried sourceOwner agreement)
    (lines : Lines paid elimination clearances)
    (onGrid : ∀ point ∈ Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid point)
    (cached : DetourWalkCache elimination clearances grid paid lines onGrid) :
    let suffix := Lines.Bank.tail
      (elimination := elimination) (clearances := clearances) (regular := regular) lines
    (prepareDetourOn elimination clearances paid lines grid onGrid).2.val =
      (headDetourWalk elimination clearances grid paid lines onGrid cached).val.append
        (prepareDetourOn elimination clearances paid.tail suffix grid
          (fun point member => onGrid point (List.Mem.tail _ member))).2.val := by
  have same := congrArg Prod.fst cached.property
  change _ = cached.val.1.append _
  rewrite [same]
  rfl

section CachedSpine

attribute [local irreducible] StepBlock.DetourCache DetourWalkCache
attribute [local irreducible] lastDetourWalk headDetourWalk tailDetourWalks

/-- The original fine-piece spine retains the actual three-cover factory at every stored numeric head.

The supplied final query remains the final block. Each actual result
retains both old/new Owners and its cached comparison; the literal
returned finish Owner indexes the next supplied-start request.
-/
@[expose] def DetourSpine
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
    (supplied : Option (StepBlock.Start sourceOwner)) → Type
  | [], _first, _queried, _sourceOwner, _agreement, paid, lines, onGrid, cached, supplied =>
      let source := Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      let suffix := Lines.Bank.tail
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      let target := Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := regular) suffix
      StepBlock.DetourCache paid.head.paid source target
        (.inr (reference source.point (onGrid source.point (List.Mem.head _))))
        (lastDetourWalk elimination clearances grid paid lines onGrid cached) supplied
  | next :: remaining, _first, queried, _sourceOwner, _agreement, paid, lines, onGrid, cached, supplied =>
      let source := Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      let suffix := Lines.Bank.tail
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      let target := Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := regular) suffix
      Σ head : StepBlock.DetourCache paid.head.paid source target
          (.inr (reference source.point (onGrid source.point (List.Mem.head _))))
          (headDetourWalk elimination clearances grid paid lines onGrid cached) supplied,
        DetourSpine reference remaining next (fun piece member => queried piece (List.Mem.tail next member))
          paid.head.finishOwner paid.head.nextAgreement paid.tail suffix
          (fun point member => onGrid point (List.Mem.tail _ member))
          (tailDetourWalks elimination clearances grid paid lines onGrid cached)
          (some ⟨head.finishOwner, head.equivalent⟩)

/-- Build each original fine-piece detour once from the same stored numeric head and actual preceding finish. -/
private def buildDetourSpine
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
    DetourSpine elimination clearances grid reference remaining first queried sourceOwner agreement
      paid lines onGrid cached supplied
  | [], _first, _queried, _sourceOwner, _agreement, paid, lines, onGrid, cached, supplied =>
      let source := Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      let suffix := Lines.Bank.tail
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      let target := Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := regular) suffix
      paid.head.paid.prepareDetourOn source target
        (.inr (reference source.point (onGrid source.point (List.Mem.head _))))
        (lastDetourWalk elimination clearances grid paid lines onGrid cached) supplied
  | next :: remaining, _first, queried, _sourceOwner, _agreement, paid, lines, onGrid, cached, supplied =>
      let source := Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      let suffix := Lines.Bank.tail
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      let target := Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := regular) suffix
      let head := paid.head.paid.prepareDetourOn source target
        (.inr (reference source.point (onGrid source.point (List.Mem.head _))))
        (headDetourWalk elimination clearances grid paid lines onGrid cached) supplied
      let tail := buildDetourSpine reference remaining next
        (fun piece member => queried piece (List.Mem.tail next member))
        paid.head.finishOwner paid.head.nextAgreement paid.tail suffix
        (fun point member => onGrid point (List.Mem.tail _ member))
        (tailDetourWalks elimination clearances grid paid lines onGrid cached)
        (some ⟨head.finishOwner, head.equivalent⟩)
      ⟨head, tail⟩

/-- Prepare the actual fine signed detours from the same retained numeric head bank and paid Piece spine.

The original final query remains the final block. Every actual head keeps
its complete original three-cover factory and cached endpoint relation;
the literal returned finish Owner indexes the next supplied-start request.
-/
def prepareDetour
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point)
    {remaining : List (Piece data actual accuracy)} {first : Piece data actual accuracy}
    {queried : ∀ piece ∈ remaining, piece.Queried}
    {sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint}
    {agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner}
    (paid : Acquisition regular finishQuery remaining first queried sourceOwner agreement)
    (lines : Lines paid elimination clearances)
    (onGrid : ∀ point ∈ Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid point)
    (cached : DetourWalkCache elimination clearances grid paid lines onGrid)
    (supplied : Option (StepBlock.Start sourceOwner) := none) :
    DetourSpine elimination clearances grid reference remaining first queried sourceOwner agreement
      paid lines onGrid cached supplied :=
  buildDetourSpine elimination clearances grid reference remaining first queried sourceOwner agreement
    paid lines onGrid cached supplied

end CachedSpine

namespace DetourSpine

open Parallel.Steps.Acquisition.DetourSpine (LastReturn)

section TerminalFold

attribute [local irreducible] StepBlock.DetourCache DetourWalkCache
attribute [local irreducible] lastDetourWalk headDetourWalk tailDetourWalks

/-- An exact consumer of the original final singleton context and its complete retained signed head.

Every input is the actual terminal Piece, paid singleton, selected line
bank, numerical head cache and signed three-cover cache. The consumer may
read those values; no context, Owner or preparation is reconstructed.
-/
abbrev LastAction (Result : Type u)
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point) :=
    (first : Piece data actual accuracy) →
    (queried : ∀ piece ∈ ([] : List (Piece data actual accuracy)), piece.Queried) →
    (sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint) →
    (agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner) →
    (paid : Acquisition regular finishQuery [] first queried sourceOwner agreement) →
    (lines : Lines paid elimination clearances) →
    (onGrid : ∀ point ∈ Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid point) →
    (cached : DetourWalkCache elimination clearances grid paid lines onGrid) →
    (supplied : Option (StepBlock.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances grid reference [] first queried sourceOwner agreement
      paid lines onGrid cached supplied) → Result

/-- Consume the actual final signed singleton in one traversal of the original dependent spine.

The identical paid, selected-line, numerical and signed tails are passed
onward. Only the final context invokes the supplied consumer, so selecting
one terminal readback does not prepare any other terminal value or cache.
-/
@[expose, specialize] def withLast {Result : Type u}
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point)
    (consume : LastAction (data := data) (actual := actual) (accuracy := accuracy)
      (regular := regular) (finishQuery := finishQuery)
      (elimination := elimination) (clearances := clearances) (grid := grid) Result reference) :
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
      paid lines onGrid cached supplied) → Result
  | [], first, queried, sourceOwner, agreement, paid, lines, onGrid, cached, supplied, prepared =>
      consume first queried sourceOwner agreement paid lines onGrid cached supplied prepared
  | next :: remaining, _first, queried, _sourceOwner, _agreement, paid, lines, onGrid, cached, _supplied, prepared =>
      let suffix := Lines.Bank.tail
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      withLast reference consume remaining next (fun piece member => queried piece (List.Mem.tail next member))
        paid.head.finishOwner paid.head.nextAgreement paid.tail suffix
        (fun point member => onGrid point (List.Mem.tail _ member))
        (tailDetourWalks elimination clearances grid paid lines onGrid cached)
        (some ⟨StepBlock.DetourCache.finishOwner prepared.1,
          StepBlock.DetourCache.equivalent prepared.1⟩) prepared.2

/-- Read the literal actual final Owner from the retained fine signed preparation spine. -/
@[expose] def finishOwner
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
      paid lines onGrid cached supplied) → OwnerAt site parameter quarter positive finish :=
  fun remaining first queried sourceOwner agreement paid lines onGrid cached supplied prepared =>
    withLast (data := data) (actual := actual) (accuracy := accuracy)
      (regular := regular) (finishQuery := finishQuery)
      elimination clearances grid reference
      (fun _first _queried _sourceOwner _agreement _paid _lines _onGrid _cached _supplied terminal =>
        StepBlock.DetourCache.finishOwner terminal)
      remaining first queried sourceOwner agreement paid lines onGrid cached supplied prepared

end TerminalFold

/-- Read the actual final middle endpoint and retained return in the original signed order.

One traversal consumes the exact final singleton cache. The original whole
signed spine remains its owner and retains all three actual covered paths;
this root-path view does not assert an integral or finite-reading equality.
-/
@[expose] def lastReturn
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
    LastReturn (site := site) (parameter := parameter) (unitQuarter := quarter) (positive := positive)
      (regular := regular) (finish := finish) elimination :=
  fun remaining first queried sourceOwner agreement paid lines onGrid cached supplied prepared =>
    withLast (data := data) (actual := actual) (accuracy := accuracy)
      (regular := regular) (finishQuery := finishQuery)
      elimination clearances grid reference
      (fun _first _queried _sourceOwner _agreement _paid terminalLines _onGrid _cached _supplied terminal =>
        let suffix := Lines.Bank.tail
          (elimination := elimination) (clearances := clearances) (regular := regular) terminalLines
        let target := Lines.Bank.head
          (elimination := elimination) (clearances := clearances) (regular := regular) suffix
        ⟨⟨target.point, target.point_eq⟩, terminal.val.2.1.val.traced.finishOwner,
          terminal.val.2.2.1.val.traced.finishOwner, terminal.val.2.2.1.val.traced.trace.get⟩)
      remaining first queried sourceOwner agreement paid lines onGrid cached supplied prepared

/-- The retained return view ends at the exact original signed-spine finish Owner. -/
theorem lastReturn_finishOwner
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
    (lastReturn elimination clearances grid reference remaining first queried sourceOwner agreement
      paid lines onGrid cached supplied prepared).2.2.1 =
      finishOwner elimination clearances grid reference remaining first queried sourceOwner agreement
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

/-- The retained fine-piece terminal return has its original sharp-square endpoint winding.

Structural traversal follows the same numerical pieces, paid acquisitions,
line bank and signed caches. The actual final singleton supplies its cached
connector's potential law without preparing another path or root owner.
-/
theorem lastReturn_winding
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
    (clearance : RegionClearance (Paths.polynomial parameter)
      (Parallel.box site parameter quarter finish.parameter regular)) →
    let returned := lastReturn elimination clearances grid reference remaining first queried sourceOwner agreement
      paid lines onGrid cached supplied prepared
    chainRaw (Paths.polynomial parameter) returned.1.val returned.2.2.2.vertices =
      windingPotential (Paths.polynomial parameter) (Parallel.box site parameter quarter finish.parameter regular)
        (Transport.Spatial.coordinate site parameter 2 quarter positive finish.parameter) -
      windingPotential (Paths.polynomial parameter) (Parallel.box site parameter quarter finish.parameter regular)
        returned.1.val := by
  intro remaining
  induction remaining with
  | nil =>
    intros first queried sourceOwner agreement paid lines onGrid cached supplied prepared clearance
    exact StepBlock.DetourCache.return_winding
      (actual := actual) (regular := regular) (current := first.lowerEndpoint) (target := finish)
      (reading := first.source) (queried := finishQuery) (sourceOwner := sourceOwner) (sourceAgreement := agreement)
      (geometry := paid.head.geometry) (block := paid.head.paid) prepared clearance
  | cons next remaining induction =>
    intros first queried sourceOwner agreement paid lines onGrid cached supplied prepared clearance
    exact induction next (fun piece member => queried piece (List.Mem.tail next member))
      paid.head.finishOwner paid.head.nextAgreement paid.tail
      (Lines.Bank.tail
        (elimination := elimination) (clearances := clearances) (regular := regular) lines)
      (fun point member => onGrid point (List.Mem.tail _ member))
      (tailDetourWalks elimination clearances grid paid lines onGrid cached)
      (some ⟨StepBlock.DetourCache.finishOwner prepared.1,
        StepBlock.DetourCache.equivalent prepared.1⟩) prepared.2 clearance

section CachedReadbacks

attribute [local irreducible] StepBlock.DetourCache DetourWalkCache
attribute [local irreducible] lastDetourWalk headDetourWalk tailDetourWalks

/-- Read the retained final comparison to the unchanged original fine paid finish Owner. -/
def equivalent
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
    NamedEquivalent (ownerName (finishOwner elimination clearances grid reference remaining first queried
      sourceOwner agreement paid lines onGrid cached supplied prepared)) (ownerName paid.finishOwner)
  | [], _first, _queried, _sourceOwner, _agreement, _paid, _lines, _onGrid, _cached, _supplied, prepared =>
      StepBlock.DetourCache.equivalent prepared
  | next :: remaining, _first, queried, _sourceOwner, _agreement, paid, lines, onGrid, cached, _supplied, prepared =>
      let suffix := Lines.Bank.tail
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      let retained := equivalent reference remaining next
        (fun piece member => queried piece (List.Mem.tail next member))
        paid.head.finishOwner paid.head.nextAgreement paid.tail suffix
        (fun point member => onGrid point (List.Mem.tail _ member))
        (tailDetourWalks elimination clearances grid paid lines onGrid cached)
        (some ⟨StepBlock.DetourCache.finishOwner prepared.1,
          StepBlock.DetourCache.equivalent prepared.1⟩) prepared.2
      Eq.mp (congrArg (fun owner => NamedEquivalent
        (ownerName (finishOwner elimination clearances grid reference (next :: remaining) _first queried
          _sourceOwner _agreement paid lines onGrid cached _supplied prepared))
        (ownerName owner)) paid.finishOwner_tail) retained

/-- Read the complete ordered chain of the literal retained signed covers. -/
@[expose] def blocks
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
    CoveredTracedPath.Blocks (Paths.polynomial parameter)
      (Transport.Spatial.coordinate site parameter 2 quarter positive first.span.lower)
      (StepBlock.Start.owner (site := site) (parameter := parameter) (unitQuarter := quarter)
        (positive := positive) (current := first.lowerEndpoint) sourceOwner supplied)
      (Transport.Spatial.coordinate site parameter 2 quarter positive finish.parameter)
      (finishOwner elimination clearances grid reference remaining first queried sourceOwner agreement
        paid lines onGrid cached supplied prepared)
  | [], _first, _queried, _sourceOwner, _agreement, _paid, _lines, _onGrid, _cached, _supplied, prepared =>
      StepBlock.DetourCache.blocks prepared
  | next :: remaining, _first, queried, _sourceOwner, _agreement, paid, lines, onGrid, cached, _supplied, prepared =>
      let suffix := Lines.Bank.tail
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      (StepBlock.DetourCache.blocks prepared.1).append
        (blocks reference remaining next (fun piece member => queried piece (List.Mem.tail next member))
          paid.head.finishOwner paid.head.nextAgreement paid.tail suffix
          (fun point member => onGrid point (List.Mem.tail _ member))
          (tailDetourWalks elimination clearances grid paid lines onGrid cached)
          (some ⟨StepBlock.DetourCache.finishOwner prepared.1,
            StepBlock.DetourCache.equivalent prepared.1⟩) prepared.2)

/-- Read the literal first entry-finish Owner on the retained selected source point.

The singleton and cons cases read the same actual first Block cache.
There is no parameter transport, track reconstruction or new selection;
the moved-coordinate view derives from this original retained Owner.
-/
@[expose] def entryOwner
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
    let source := Lines.Bank.head
      (elimination := elimination) (clearances := clearances) (regular := regular) lines
    Riemann.Topology.SquareRootContinuationChain.Owner ((Paths.polynomial parameter).eval source.point)
  | [], _first, _queried, _sourceOwner, _agreement, _paid, _lines, _onGrid, _cached, _supplied, prepared =>
      StepBlock.DetourCache.entryOwner prepared
  | _next :: _remaining, _first, _queried, _sourceOwner, _agreement, _paid, _lines, _onGrid,
      _cached, _supplied, prepared => StepBlock.DetourCache.entryOwner prepared.1

/-- Read the first actual middle Owner from the retained fine-piece signed spine.

A fine spine always retains its first piece, including its final singleton
case. Only the cached source-line equality transports the parameter of the
actual entry finish; no numerical piece, query or Owner is reconstructed.
-/
@[expose] def middleSource
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
        (Transport.Spatial.coordinate site parameter 2 quarter positive first.span.lower))) :=
  fun remaining first queried sourceOwner agreement paid lines onGrid cached supplied prepared =>
    let source := Lines.Bank.head
      (elimination := elimination) (clearances := clearances) (regular := regular) lines
    RootIsolation.SquareRoot.Owner.Transport.castOwnerParameter
      (congrArg (Paths.polynomial parameter).eval source.point_eq)
      (entryOwner elimination clearances grid reference remaining first queried sourceOwner agreement
        paid lines onGrid cached supplied prepared)

/-- The fine moved-source view keeps the same original cached entry root name.

The source-line equality changes only the dependent parameter index;
no root acquisition or new frame classification is used.
-/
theorem middleSource_name
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point)
    (remaining : List (Piece data actual accuracy)) (first : Piece data actual accuracy)
    (queried : ∀ piece ∈ remaining, piece.Queried)
    (sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint)
    (agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner)
    (paid : Acquisition regular finishQuery remaining first queried sourceOwner agreement)
    (lines : Lines paid elimination clearances)
    (onGrid : ∀ point ∈ Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid point)
    (cached : DetourWalkCache elimination clearances grid paid lines onGrid)
    (supplied : Option (StepBlock.Start sourceOwner))
    (prepared : DetourSpine elimination clearances grid reference remaining first queried sourceOwner agreement
      paid lines onGrid cached supplied) :
    ownerName (middleSource elimination clearances grid reference remaining first queried sourceOwner agreement
      paid lines onGrid cached supplied prepared) =
      ownerName (entryOwner elimination clearances grid reference remaining first queried sourceOwner agreement
      paid lines onGrid cached supplied prepared) := by
  with_unfolding_all exact ownerRootName_castOwnerParameter _ _

/-- Read the retained fine spine's actual first entry at its existing moved-source Owner index.

Both the final singleton and nonterminal cases consume their saved entry
cover. Exact endpoint transport preserves the original path and supplied
start while retaining the same `middleSource` owner and numerical piece.
-/
@[expose] def entryTrace
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
    OwnerPath (Paths.polynomial parameter)
      (Transport.Spatial.coordinate site parameter 2 quarter positive first.span.lower)
      (StepBlock.Start.owner (site := site) (parameter := parameter) (unitQuarter := quarter)
        (positive := positive) (current := first.lowerEndpoint) sourceOwner supplied)
      (Parallel.Geometry.move elimination regular
        (Transport.Spatial.coordinate site parameter 2 quarter positive first.span.lower))
      (middleSource elimination clearances grid reference remaining first queried sourceOwner agreement
        paid lines onGrid cached supplied prepared) := by
  intro remaining
  cases remaining with
  | nil =>
    intros first queried sourceOwner agreement paid lines onGrid cached supplied prepared
    let source := Lines.Bank.head
      (elimination := elimination) (clearances := clearances) (regular := regular) lines
    let cachedOwner := entryOwner elimination clearances grid reference
      [] first queried sourceOwner agreement paid lines onGrid cached supplied prepared
    let cachedPath := StepBlock.DetourCache.entryTrace
      (actual := actual) (regular := regular) (current := first.lowerEndpoint) (target := finish)
      (reading := first.source) (queried := finishQuery) (sourceOwner := sourceOwner) (sourceAgreement := agreement)
      (geometry := paid.head.geometry) (block := paid.head.paid) prepared
    exact OwnerPath.castEndpoints rfl source.point_eq HEq.rfl
      (Owner.Transport.castOwnerParameter_heq
        (congrArg (Paths.polynomial parameter).eval source.point_eq) cachedOwner).symm
      cachedPath
  | cons next remaining =>
    intros first queried sourceOwner agreement paid lines onGrid cached supplied prepared
    let source := Lines.Bank.head
      (elimination := elimination) (clearances := clearances) (regular := regular) lines
    let cachedOwner := entryOwner elimination clearances grid reference
      (next :: remaining) first queried sourceOwner agreement
      paid lines onGrid cached supplied prepared
    let cachedPath := StepBlock.DetourCache.entryTrace
      (actual := actual) (regular := regular) (current := first.lowerEndpoint) (target := next.lowerEndpoint)
      (reading := first.source) (queried := next.sourceQuery (queried next (List.Mem.head remaining)))
      (sourceOwner := sourceOwner) (sourceAgreement := agreement)
      (geometry := paid.head.geometry) (block := paid.head.paid) prepared.1
    exact OwnerPath.castEndpoints rfl source.point_eq HEq.rfl
      (Owner.Transport.castOwnerParameter_heq
        (congrArg (Paths.polynomial parameter).eval source.point_eq) cachedOwner).symm
      cachedPath

/-- The literal fine-spine entry has its sharp-source-square endpoint winding in either list case.

The original Block's entry formula and the retained source-line equality
pay the same cached vertex list. No independent winding or sheet comparison
is supplied for either the singleton or nonterminal piece.
-/
theorem entryTrace_winding
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
    chainRaw (Paths.polynomial parameter)
      (Transport.Spatial.coordinate site parameter 2 quarter positive first.span.lower)
      (entryTrace elimination clearances grid reference remaining first queried sourceOwner agreement
        paid lines onGrid cached supplied prepared).vertices =
      windingPotential (Paths.polynomial parameter) (Parallel.box site parameter quarter first.span.lower regular)
        (Parallel.Geometry.move elimination regular
        (Transport.Spatial.coordinate site parameter 2 quarter positive first.span.lower)) -
      windingPotential (Paths.polynomial parameter) (Parallel.box site parameter quarter first.span.lower regular)
        (Transport.Spatial.coordinate site parameter 2 quarter positive first.span.lower) := by
  intro remaining
  cases remaining with
  | nil =>
    intros first queried sourceOwner agreement paid lines onGrid cached supplied prepared
    let source := Lines.Bank.head
      (elimination := elimination) (clearances := clearances) (regular := regular) lines
    let cachedOwner := entryOwner elimination clearances grid reference
      [] first queried sourceOwner agreement paid lines onGrid cached supplied prepared
    let cachedPath := StepBlock.DetourCache.entryTrace
      (actual := actual) (regular := regular) (current := first.lowerEndpoint) (target := finish)
      (reading := first.source) (queried := finishQuery) (sourceOwner := sourceOwner) (sourceAgreement := agreement)
      (geometry := paid.head.geometry) (block := paid.head.paid) prepared
    have vertices := OwnerPath.castEndpoints_vertices rfl source.point_eq HEq.rfl
      (Owner.Transport.castOwnerParameter_heq
        (congrArg (Paths.polynomial parameter).eval source.point_eq) cachedOwner).symm
      cachedPath
    have original := StepBlock.DetourCache.entry_winding
      (actual := actual) (regular := regular) (current := first.lowerEndpoint) (target := finish)
      (reading := first.source) (queried := finishQuery) (sourceOwner := sourceOwner) (sourceAgreement := agreement)
      (geometry := paid.head.geometry) (block := paid.head.paid) prepared
    exact (congrArg (chainRaw (Paths.polynomial parameter)
      (Transport.Spatial.coordinate site parameter 2 quarter positive first.span.lower)) vertices).trans
      (original.trans (congrArg (fun point =>
        windingPotential (Paths.polynomial parameter) (Parallel.box site parameter quarter first.span.lower regular)
          point -
        windingPotential (Paths.polynomial parameter) (Parallel.box site parameter quarter first.span.lower regular)
          (Transport.Spatial.coordinate site parameter 2 quarter positive first.span.lower)) source.point_eq))
  | cons next remaining =>
    intros first queried sourceOwner agreement paid lines onGrid cached supplied prepared
    let source := Lines.Bank.head
      (elimination := elimination) (clearances := clearances) (regular := regular) lines
    let cachedOwner := entryOwner elimination clearances grid reference
      (next :: remaining) first queried sourceOwner agreement
      paid lines onGrid cached supplied prepared
    let cachedPath := StepBlock.DetourCache.entryTrace
      (actual := actual) (regular := regular) (current := first.lowerEndpoint) (target := next.lowerEndpoint)
      (reading := first.source) (queried := next.sourceQuery (queried next (List.Mem.head remaining)))
      (sourceOwner := sourceOwner) (sourceAgreement := agreement)
      (geometry := paid.head.geometry) (block := paid.head.paid) prepared.1
    have vertices := OwnerPath.castEndpoints_vertices rfl source.point_eq HEq.rfl
      (Owner.Transport.castOwnerParameter_heq
        (congrArg (Paths.polynomial parameter).eval source.point_eq) cachedOwner).symm
      cachedPath
    have original := StepBlock.DetourCache.entry_winding
      (actual := actual) (regular := regular) (current := first.lowerEndpoint) (target := next.lowerEndpoint)
      (reading := first.source) (queried := next.sourceQuery (queried next (List.Mem.head remaining)))
      (sourceOwner := sourceOwner) (sourceAgreement := agreement)
      (geometry := paid.head.geometry) (block := paid.head.paid) prepared.1
    exact (congrArg (chainRaw (Paths.polynomial parameter)
      (Transport.Spatial.coordinate site parameter 2 quarter positive first.span.lower)) vertices).trans
      (original.trans (congrArg (fun point =>
        windingPotential (Paths.polynomial parameter) (Parallel.box site parameter quarter first.span.lower regular)
          point -
        windingPotential (Paths.polynomial parameter) (Parallel.box site parameter quarter first.span.lower regular)
          (Transport.Spatial.coordinate site parameter 2 quarter positive first.span.lower)) source.point_eq))

end CachedReadbacks

end DetourSpine

end Detour

end Acquisition

end Spatial

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer

end
