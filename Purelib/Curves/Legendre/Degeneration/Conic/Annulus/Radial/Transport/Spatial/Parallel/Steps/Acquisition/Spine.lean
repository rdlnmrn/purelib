module

import Purelib.RootIsolation.SquareRoot.Owner.Transport

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Block
public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Blocks
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

/-! # Paid realization of an unchanged original-quarter spatial step chain

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

/-- The paid spine follows only the original target list while retaining both the old receipt and new actual Owner.

The original receipt supplies its identical target QueryCache and Geometry
at each node. A new whole Block is retained with its complete factory
identity, and its literal stored finishOwner and nextAgreement index the
dependent tail. The original Covered owner is used only to access that
unchanged original tail, never as the new paid source.
-/
@[expose] def Spine (actual : Transport.Quarter site parameter 2 unitQuarter positive)
    (regular : parameter ≠ criticalValue site) : (targets : List Endpoint) → (current : Endpoint) →
    (reading : ReadingAt actual current) → (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (_original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (_agreement : InitialAgreement current reading sourceOwner) → Type 1
  | [] => fun _ _ _ _ _ _ => PUnit
  | target :: targets => fun _ _ _ original sourceOwner agreement =>
      Σ block : { retained : Block original.2.1 original.headGeometry sourceOwner agreement //
          retained = Block.build original.2.1 original.headGeometry sourceOwner agreement },
        Spine actual regular targets target original.nextReading original.headCovered.finishOwner original.tail
          block.val.finishOwner block.val.nextAgreement

end Steps.Acquisition

/-- A complete new paid realization indexed by the unchanged original Steps receipt and actual supplied initial Owner.

The exact spine preserves all original target queries and Geometries, all
new paid Covered and comparison caches, and the literal paid Owner and
Type-valued agreement passed between neighboring blocks.
-/
@[expose] def Steps.Acquisition
    {actual : Transport.Quarter site parameter 2 unitQuarter positive} {regular : parameter ≠ criticalValue site}
    {targets : List Endpoint} {current : Endpoint} {reading : ReadingAt actual current}
    {originalOwner : OwnerAt site parameter unitQuarter positive current}
    (original : Steps actual regular current reading originalOwner targets)
    (sourceOwner : OwnerAt site parameter unitQuarter positive current)
    (agreement : Steps.Acquisition.InitialAgreement current reading sourceOwner) : Type 1 :=
  Steps.Acquisition.Spine actual regular targets current reading originalOwner original sourceOwner agreement

namespace Steps.Acquisition

variable {actual : Transport.Quarter site parameter 2 unitQuarter positive} {regular : parameter ≠ criticalValue site}
variable {targets : List Endpoint} {current : Endpoint} {reading : ReadingAt actual current}
variable {originalOwner sourceOwner : OwnerAt site parameter unitQuarter positive current}
variable {original : Steps actual regular current reading originalOwner targets}
variable {agreement : InitialAgreement current reading sourceOwner}

/-- The stationary paid realization retains the same original Reading, nominal Owner and input comparison. -/
@[expose] def nil (original : Steps actual regular current reading originalOwner [])
    (sourceOwner : OwnerAt site parameter unitQuarter positive current)
    (agreement : InitialAgreement current reading sourceOwner) : Acquisition original sourceOwner agreement :=
  PUnit.unit

/-- Retain one completed new Block and its exact factory identity, with the unchanged original dependent tail. -/
@[expose] def cons {target : Endpoint}
    {original : Steps actual regular current reading originalOwner (target :: targets)}
    (block : Block original.2.1 original.headGeometry sourceOwner agreement)
    (block_eq : block = Block.build original.2.1 original.headGeometry sourceOwner agreement)
    (remaining : Acquisition original.tail block.finishOwner block.nextAgreement) :
    Acquisition original sourceOwner agreement := ⟨⟨block, block_eq⟩, remaining⟩

/-- Read the identical complete paid Block retained at the first original query/Geometry pair. -/
@[expose] def head {target : Endpoint}
    {original : Steps actual regular current reading originalOwner (target :: targets)}
    (paid : Acquisition original sourceOwner agreement) :
    Block original.2.1 original.headGeometry sourceOwner agreement := paid.1.val

/-- The whole first paid Block is the factory on the same stored original query, Geometry and source witness. -/
theorem head_eq {target : Endpoint}
    {original : Steps actual regular current reading originalOwner (target :: targets)}
    (paid : Acquisition original sourceOwner agreement) :
    paid.head = Block.build original.2.1 original.headGeometry sourceOwner agreement := paid.1.property

/-- Read the unchanged paid tail on the literal stored finishOwner and exact cached next-source agreement. -/
@[expose] def tail {target : Endpoint}
    {original : Steps actual regular current reading originalOwner (target :: targets)}
    (paid : Acquisition original sourceOwner agreement) :
    Acquisition original.tail paid.head.finishOwner paid.head.nextAgreement := paid.2

/-- Retaining a completed head preserves its exact whole Block and every original observation and factory cache. -/
theorem cons_head {target : Endpoint}
    {original : Steps actual regular current reading originalOwner (target :: targets)}
    (block : Block original.2.1 original.headGeometry sourceOwner agreement)
    (block_eq : block = Block.build original.2.1 original.headGeometry sourceOwner agreement)
    (remaining : Acquisition original.tail block.finishOwner block.nextAgreement) :
    (cons block block_eq remaining).head = block := rfl

/-- Retaining a completed head preserves the actual paid tail and its exact Owner/comparison indices. -/
theorem cons_tail {target : Endpoint}
    {original : Steps actual regular current reading originalOwner (target :: targets)}
    (block : Block original.2.1 original.headGeometry sourceOwner agreement)
    (block_eq : block = Block.build original.2.1 original.headGeometry sourceOwner agreement)
    (remaining : Acquisition original.tail block.finishOwner block.nextAgreement) :
    (cons block block_eq remaining).tail = remaining := rfl

/-- The actual next source witness is the cached preceding Endpoint's symmetry on the same original next Reading. -/
theorem head_nextAgreement_eq {target : Endpoint}
    {original : Steps actual regular current reading originalOwner (target :: targets)}
    (paid : Acquisition original sourceOwner agreement) :
    paid.head.nextAgreement = paid.head.endpoint.finish.symm := paid.head.nextAgreement_eq

/-- Reuse each original stored query and Geometry while building only the new paid realization. -/
private def buildSpine (actual : Transport.Quarter site parameter 2 unitQuarter positive)
    (regular : parameter ≠ criticalValue site) : (targets : List Endpoint) → (current : Endpoint) →
    (reading : ReadingAt actual current) → (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) → Acquisition original sourceOwner agreement
  | [] => fun _ _ _ original sourceOwner agreement => nil original sourceOwner agreement
  | target :: targets => fun _ _ _ original sourceOwner agreement =>
      let block := Block.build original.2.1 original.headGeometry sourceOwner agreement
      let remaining := buildSpine actual regular targets target original.nextReading
        original.headCovered.finishOwner original.tail block.finishOwner block.nextAgreement
      cons block rfl remaining

/-- Totally realize the unchanged original Steps chain with internally paid new routes and derived Owner handoffs.

All original Queries and Geometries are read from the supplied whole Steps
cache. Each sufficient width is computed by the original total paid route
acquisition. Every later source agreement comes from the preceding stored
Endpoint; neither a desired terminal equivalence nor another Source
attachment is supplied or acquired.
-/
def build (original : Steps actual regular current reading originalOwner targets)
    (sourceOwner : OwnerAt site parameter unitQuarter positive current)
    (agreement : InitialAgreement current reading sourceOwner) : Acquisition original sourceOwner agreement :=
  buildSpine actual regular targets current reading originalOwner original sourceOwner agreement

namespace Spine

/-- Read the actual new final Owner along the original endpoint list and stored paid finishOwner handoffs. -/
@[expose] def finishOwner : (targets : List Endpoint) → (current : Endpoint) →
    (reading : ReadingAt actual current) → (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) → Acquisition original sourceOwner agreement →
      OwnerAt site parameter unitQuarter positive (finalTarget current targets)
  | [] => fun _ _ _ _ sourceOwner _ _ => sourceOwner
  | target :: targets => fun _ _ _ original _ _ paid =>
      finishOwner targets target original.nextReading original.headCovered.finishOwner original.tail
        paid.head.finishOwner paid.head.nextAgreement paid.tail

/-- Derive final agreement with the unchanged final Reading, reading the last actual Endpoint on nonempty chains. -/
def finishEquivalent : (targets : List Endpoint) → (current : Endpoint) →
    (reading : ReadingAt actual current) → (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) →
      NamedEquivalent
        (ownerRootName
          (finishOwner targets current reading originalOwner original sourceOwner agreement paid).parameterNonzero
          (finishOwner targets current reading originalOwner original sourceOwner agreement paid))
        original.finishReading.lift.value.name
  | [] => fun _ _ _ _ _ agreement _ => agreement.symm
  | _target :: [] => fun _ _ _ _ _ _ paid => paid.head.finishEquivalent
  | target :: following :: targets => fun _ _ _ original _ _ paid =>
      finishEquivalent (following :: targets) target original.nextReading
        original.headCovered.finishOwner original.tail paid.head.finishOwner paid.head.nextAgreement paid.tail

/-- Retain the actual new covered blocks in order with literal stored Owner handoffs and unchanged original caches. -/
@[expose] def blocks : (targets : List Endpoint) → (current : Endpoint) →
    (reading : ReadingAt actual current) → (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) →
      CoveredTracedPath.Blocks (Paths.polynomial parameter)
        (coordinate site parameter 2 unitQuarter positive current.parameter) sourceOwner
        (coordinate site parameter 2 unitQuarter positive (finalTarget current targets).parameter)
        (finishOwner targets current reading originalOwner original sourceOwner agreement paid)
  | [] => fun _ _ _ _ sourceOwner _ _ => .nil _ sourceOwner
  | target :: targets => fun _ _ _ original _ _ paid =>
      .cons paid.head.paid.covered
        (blocks targets target original.nextReading original.headCovered.finishOwner original.tail
          paid.head.finishOwner paid.head.nextAgreement paid.tail)

/-- Count the actual new retained paid Blocks on the original target-list spine. -/
@[expose] def blockCount : (targets : List Endpoint) → (current : Endpoint) →
    (reading : ReadingAt actual current) → (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) → Acquisition original sourceOwner agreement → Nat
  | [] => fun _ _ _ _ _ _ _ => 0
  | target :: targets => fun _ _ _ original _ _ paid =>
      (blockCount targets target original.nextReading original.headCovered.finishOwner original.tail
        paid.head.finishOwner paid.head.nextAgreement paid.tail) + 1

/-- The actual new paid spine has precisely one retained Block for every original target entry. -/
theorem blockCount_eq : (targets : List Endpoint) → (current : Endpoint) →
    (reading : ReadingAt actual current) → (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) → (paid : Acquisition original sourceOwner agreement) →
    blockCount targets current reading originalOwner original sourceOwner agreement paid = targets.length
  | [] => fun _ _ _ _ _ _ _ => rfl
  | target :: targets => fun _ _ _ original _ _ paid =>
      congrArg (fun count => count + 1)
        (blockCount_eq targets target original.nextReading original.headCovered.finishOwner original.tail
          paid.head.finishOwner paid.head.nextAgreement paid.tail)

end Spine

/-- Read this new paid execution's actual final Owner; the original Steps' old final Owner stays distinct. -/
@[expose] def finishOwner (paid : Acquisition original sourceOwner agreement) :
    OwnerAt site parameter unitQuarter positive (finalTarget current targets) :=
  Spine.finishOwner targets current reading originalOwner original sourceOwner agreement paid

/-- Removing the actual first paid Block preserves the complete retained final Owner. -/
theorem finishOwner_tail {target : Endpoint}
    {original : Steps actual regular current reading originalOwner (target :: targets)}
    (paid : Acquisition original sourceOwner agreement) : paid.tail.finishOwner = paid.finishOwner := (rfl)

/-- The actual new paid finishOwner agrees with the unchanged complete final original-quarter Reading cache. -/
def finishEquivalent (paid : Acquisition original sourceOwner agreement) :
    NamedEquivalent (ownerRootName paid.finishOwner.parameterNonzero paid.finishOwner)
      original.finishReading.lift.value.name :=
  Spine.finishEquivalent targets current reading originalOwner original sourceOwner agreement paid

/-- Compose the exact new covered blocks through their existing Blocks owner without rebuilding a primitive cover. -/
@[expose] def blocks (paid : Acquisition original sourceOwner agreement) :
    CoveredTracedPath.Blocks (Paths.polynomial parameter)
      (coordinate site parameter 2 unitQuarter positive current.parameter) sourceOwner
      (coordinate site parameter 2 unitQuarter positive (finalTarget current targets).parameter) paid.finishOwner :=
  Spine.blocks targets current reading originalOwner original sourceOwner agreement paid

/-- Read the original complete OwnerPath assembled from those same stored new covered blocks. -/
@[expose] def trace (paid : Acquisition original sourceOwner agreement) :
    OwnerPath (Paths.polynomial parameter)
      (coordinate site parameter 2 unitQuarter positive current.parameter) sourceOwner
      (coordinate site parameter 2 unitQuarter positive (finalTarget current targets).parameter) paid.finishOwner :=
  paid.blocks.trace

/-- Read the actual new covered-preparation moving-vertex caches in their unchanged block order. -/
@[expose] def movingVertices (paid : Acquisition original sourceOwner agreement) : List Canonical :=
  paid.blocks.movingVertices

/-- The new retained covered moving chain terminates at the actual original finalTarget coordinate. -/
theorem moving_terminal (paid : Acquisition original sourceOwner agreement) :
    Geometry.Rational.Polygon.Chain.terminal (coordinate site parameter 2 unitQuarter positive current.parameter)
      paid.movingVertices = coordinate site parameter 2 unitQuarter positive (finalTarget current targets).parameter :=
  paid.blocks.moving_terminal

/-- The new actual Owner trace has the winding of the identical retained new moving-vertex caches. -/
theorem trace_winding_eq (paid : Acquisition original sourceOwner agreement) :
    Polynomial.Winding.Polygon.Basic.chainRaw (Paths.polynomial parameter)
      (coordinate site parameter 2 unitQuarter positive current.parameter) paid.trace.vertices =
    Polynomial.Winding.Polygon.Basic.chainRaw (Paths.polynomial parameter)
      (coordinate site parameter 2 unitQuarter positive current.parameter) paid.movingVertices :=
  paid.blocks.trace_winding_eq

/-- Count the actual complete paid Blocks retained by this realization. -/
@[expose] def blockCount (paid : Acquisition original sourceOwner agreement) : Nat :=
  Spine.blockCount targets current reading originalOwner original sourceOwner agreement paid

/-- There is exactly one stored complete new paid Block per original target entry. -/
theorem blockCount_eq (paid : Acquisition original sourceOwner agreement) : paid.blockCount = targets.length :=
  Spine.blockCount_eq targets current reading originalOwner original sourceOwner agreement paid

/-- The paid realization reads the identical complete original query-cache sequence without querying a node again. -/
@[expose] def nodes (_paid : Acquisition original sourceOwner agreement) : List (Node actual) := original.nodes

/-- The shared original query caches retain exactly their original source and target endpoint sequence. -/
theorem nodes_endpoints (paid : Acquisition original sourceOwner agreement) :
    (paid.nodes.map fun node => node.1) = current :: targets := original.nodes_endpoints

/-- The shared original query-cache sequence contains the unchanged source and one original cache per target. -/
theorem nodes_length (paid : Acquisition original sourceOwner agreement) : paid.nodes.length = targets.length + 1 :=
  original.nodes_length

open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider (AxisClearances)
open Purelib.Polynomial.Geometry
open Purelib.Polynomial.Dense.Gaussian.Bounds
open Purelib.Geometry.Rational.Box.Refinement
open Purelib.Data.List (DependentProduct)

/-- The shared numerical line bank at the SAME original paid endpoint occurrences. -/
abbrev Lines {degreeBound : Nat} (_paid : Acquisition original sourceOwner agreement)
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (clearances : AxisClearances elimination) :=
  Geometry.Lines.Bank elimination clearances regular actual.data.bound (current :: targets)
    (fun endpoint : Endpoint => coordinate site parameter 2 unitQuarter positive endpoint.parameter)
    (fun endpoint => coordinate_inside site parameter 2 unitQuarter
      positive actual.data.lower actual.data.upper actual.data.bound endpoint.parameter)

section Detour

variable {degreeBound : Nat}
variable (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
variable (clearances : AxisClearances elimination)
variable (grid : Grid.ClearGrid (Paths.polynomial parameter)
  (RootRadius.Box.largeSquareBox (Paths.polynomial parameter)))

section CachedDetours

attribute [local irreducible] Steps.Acquisition Block Geometry
attribute [local irreducible] coordinate

/-- One retained moved Walk at each original bounded target occurrence.

The original dependent product stores the literal consecutive source and
target indices, including duplicates. No new numeric path is computed
by this exact container view.
-/
abbrev DetourWalks (current : Endpoint) (targets : List Endpoint) :=
  DependentProduct targets (fun index => Grid.Walks.Walk grid
    (Geometry.move elimination regular (coordinate site parameter 2 unitQuarter positive
      ((current :: targets)[index.val]'(Nat.lt_succ_of_lt index.isLt)).parameter))
    (Geometry.move elimination regular (coordinate site parameter 2 unitQuarter positive
      (targets[index.val]'index.isLt).parameter)))

/-- Split the moved original geometry blocks on one retained clear grid, consuming the actual paid spine in order. -/
private def detourSpine : (targets : List Endpoint) → (current : Endpoint) →
    (reading : ReadingAt actual current) → (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) → (lines : Lines paid elimination clearances) →
    (onGrid : ∀ value ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid value) →
    DetourWalks (site := site) (unitQuarter := unitQuarter)
      (positive := positive) (regular := regular) elimination grid current targets ×
    {_walk : Grid.Walks.Walk grid
      (Geometry.move elimination regular (coordinate site parameter 2 unitQuarter positive current.parameter))
      (Geometry.move elimination regular
        (coordinate site parameter 2 unitQuarter positive (finalTarget current targets).parameter)) //
      Grid.FromStates.ContainsVertex grid (Geometry.move elimination regular
        (coordinate site parameter 2 unitQuarter positive (finalTarget current targets).parameter))}
  | [], _current, _reading, _originalOwner, _original, _sourceOwner, _agreement, _paid, lines, onGrid =>
      let source := Geometry.Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      ⟨PUnit.unit, ⟨(Grid.Walks.Walk.nil source.point).castEndpoints source.point_eq source.point_eq,
        Eq.mp (congrArg (Grid.FromStates.ContainsVertex grid) source.point_eq)
          (onGrid source.point (List.Mem.head _))⟩⟩
  | target :: targets, current, reading, _originalOwner, original, _sourceOwner, _agreement, paid,
      lines, onGrid =>
      let source := Geometry.Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      let suffix := Geometry.Lines.Bank.tail
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      let next := Geometry.Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := regular) suffix
      let moved := Geometry.detourWalk (actual := actual) (first := current.parameter) (last := target.parameter)
        (firstInside := current.inside) (lastInside := target.inside) (reading := reading)
        (targetReading := original.nextReading) (regular := regular) (payment := original.1)
        original.headGeometry elimination clearances source next grid
        (onGrid source.point (List.Mem.head _))
        (onGrid next.point (List.Mem.tail _ (List.Mem.head _)))
      let remaining : DetourWalks (site := site) (unitQuarter := unitQuarter)
          (positive := positive) (regular := regular) elimination grid target targets ×
          {_walk : Grid.Walks.Walk grid
          (Geometry.move elimination regular (coordinate site parameter 2 unitQuarter positive target.parameter))
          (Geometry.move elimination regular
            (coordinate site parameter 2 unitQuarter positive (finalTarget target targets).parameter)) //
          Grid.FromStates.ContainsVertex grid (Geometry.move elimination regular
            (coordinate site parameter 2 unitQuarter positive (finalTarget target targets).parameter))} :=
        detourSpine targets target original.nextReading original.headCovered.finishOwner
        original.tail paid.head.finishOwner paid.head.nextAgreement paid.tail suffix
        (fun value member => onGrid value (List.Mem.tail _ member))
      ⟨⟨moved, remaining.1⟩, ⟨moved.append remaining.2.val, remaining.2.property⟩⟩

/-- Retain each actual head Walk and its aggregate on the same supplied grid in one original spine traversal. -/
def prepareDetourOn (paid : Acquisition original sourceOwner agreement)
    (lines : Lines paid elimination clearances)
    (grid : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter)))
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid point) :
    DetourWalks (site := site) (unitQuarter := unitQuarter)
      (positive := positive) (regular := regular) elimination grid current targets ×
    {_walk : Grid.Walks.Walk grid
      (Geometry.move elimination regular (coordinate site parameter 2 unitQuarter positive current.parameter))
      (Geometry.move elimination regular
        (coordinate site parameter 2 unitQuarter positive (finalTarget current targets).parameter)) //
      Grid.FromStates.ContainsVertex grid (Geometry.move elimination regular
        (coordinate site parameter 2 unitQuarter positive (finalTarget current targets).parameter))} :=
  detourSpine elimination clearances grid targets current reading originalOwner original sourceOwner agreement
    paid lines onGrid

/-- Split this SAME paid realization on a supplied grid containing its actual retained moved-point occurrences. -/
def detourOn (paid : Acquisition original sourceOwner agreement)
    (lines : Lines paid elimination clearances)
    (grid : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter)))
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid point) :
    {_walk : Grid.Walks.Walk grid
      (Geometry.move elimination regular (coordinate site parameter 2 unitQuarter positive current.parameter))
      (Geometry.move elimination regular
        (coordinate site parameter 2 unitQuarter positive (finalTarget current targets).parameter)) //
      Grid.FromStates.ContainsVertex grid (Geometry.move elimination regular
        (coordinate site parameter 2 unitQuarter positive (finalTarget current targets).parameter))} :=
  (prepareDetourOn elimination clearances paid lines grid onGrid).2

/-- Construct the actual finite paid-quarter detour on the original grid extended by its own selected line payloads.

The same retained endpoint bank supplies the numeric points and all grid
membership witnesses internally. The fold reads each original Geometry
and the unchanged actual paid tail; it performs no Reading, root, paid
Block or source acquisition. Signed root and integral comparison is separate.
-/
def detour (paid : Acquisition original sourceOwner agreement)
    (lines : Lines paid elimination clearances)
    (base : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter))) :
    let pairs := Geometry.Lines.Bank.pairs
      (elimination := elimination) (clearances := clearances) (regular := regular) lines
    {_walk : Grid.Walks.Walk (Grid.Extension.extend base (pairs.map Prod.fst) (pairs.map Prod.snd))
      (Geometry.move elimination regular (coordinate site parameter 2 unitQuarter positive current.parameter))
      (Geometry.move elimination regular
        (coordinate site parameter 2 unitQuarter positive (finalTarget current targets).parameter)) //
      Grid.FromStates.ContainsVertex (Grid.Extension.extend base (pairs.map Prod.fst) (pairs.map Prod.snd))
        (Geometry.move elimination regular
          (coordinate site parameter 2 unitQuarter positive (finalTarget current targets).parameter))} :=
  detourOn elimination clearances paid lines _ (Geometry.Lines.Bank.onExtended
      (elimination := elimination) (clearances := clearances) (regular := regular) lines base)

/-- The numerical detour bank follows the identical original retained query-node occurrences.

This is ordered endpoint readback through the original whole-node list.
It does not identify root owners or replace the actual paid comparison.
-/
theorem detour_points (paid : Acquisition original sourceOwner agreement)
    (lines : Lines paid elimination clearances) :
    Geometry.Lines.Bank.points (elimination := elimination) (clearances := clearances) (regular := regular) lines =
      paid.nodes.map (fun node => Geometry.move elimination regular
        (coordinate site parameter 2 unitQuarter positive node.1.parameter)) :=
  (Geometry.Lines.Bank.points_eq
    (elimination := elimination) (clearances := clearances) (regular := regular) lines).trans
    ((congrArg (fun endpoints : List Endpoint => endpoints.map (fun endpoint => Geometry.move elimination regular
      (coordinate site parameter 2 unitQuarter positive endpoint.parameter))) paid.nodes_endpoints).symm.trans
        (Data.List.Map.map_map
          (fun endpoint : Endpoint => Geometry.move elimination regular
            (coordinate site parameter 2 unitQuarter positive endpoint.parameter))
          (fun node : Node actual => node.1) paid.nodes))

/-- The actual retained occurrence product with its whole original numeric factory equation.

Only the proof mentions the producer. Lookup consumes the stored head or
tail directly; no numeric Walk is reconstructed by this cache view.
-/
@[expose] def DetourWalkCache (paid : Acquisition original sourceOwner agreement)
    (lines : Lines paid elimination clearances)
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid point) :=
  {value // value = (prepareDetourOn elimination clearances paid lines grid onGrid).1}

/-- Read the literal stored head Walk with its original Geometry factory certificate. -/
def headDetourWalk {target : Endpoint}
    {original : Steps actual regular current reading originalOwner (target :: targets)}
    (paid : Acquisition original sourceOwner agreement) (lines : Lines paid elimination clearances)
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid point)
    (cached : DetourWalkCache elimination clearances grid paid lines onGrid) :
    let source := Geometry.Lines.Bank.head
      (elimination := elimination) (clearances := clearances) (regular := regular) lines
    let suffix := Geometry.Lines.Bank.tail
      (elimination := elimination) (clearances := clearances) (regular := regular) lines
    let next := Geometry.Lines.Bank.head
      (elimination := elimination) (clearances := clearances) (regular := regular) suffix
    {value : Grid.Walks.Walk grid
        (Geometry.move elimination regular (coordinate site parameter 2 unitQuarter positive current.parameter))
        (Geometry.move elimination regular (coordinate site parameter 2 unitQuarter positive target.parameter)) //
      value = Geometry.detourWalk (actual := actual) (first := current.parameter) (last := target.parameter)
        (firstInside := current.inside) (lastInside := target.inside) (reading := reading)
        (targetReading := original.nextReading) (regular := regular) (payment := original.1)
        original.headGeometry elimination clearances source next grid
        (onGrid source.point (List.Mem.head _))
        (onGrid next.point (List.Mem.tail _ (List.Mem.head _)))} :=
  ⟨cached.val.1, congrArg Prod.fst cached.property⟩

/-- Read the literal stored tail product with the unchanged actual paid-tail numeric factory equation. -/
def tailDetourWalks {target : Endpoint}
    {original : Steps actual regular current reading originalOwner (target :: targets)}
    (paid : Acquisition original sourceOwner agreement) (lines : Lines paid elimination clearances)
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid point)
    (cached : DetourWalkCache elimination clearances grid paid lines onGrid) :
    let suffix := Geometry.Lines.Bank.tail
      (elimination := elimination) (clearances := clearances) (regular := regular) lines
    DetourWalkCache elimination clearances grid paid.tail suffix
      (fun point member => onGrid point (List.Mem.tail _ member)) :=
  ⟨cached.val.2, congrArg Prod.snd cached.property⟩

/-- The empty original numeric fold retains the identical selected source point as its empty Walk.

Only the original producer equation is read. The actual selected line
cache and both exact endpoint transports are unchanged.
-/
theorem prepareDetourOn_nil
    {original : Steps actual regular current reading originalOwner []}
    (paid : Acquisition original sourceOwner agreement) (lines : Lines paid elimination clearances)
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid point) :
    let source := Geometry.Lines.Bank.head
      (elimination := elimination) (clearances := clearances) (regular := regular) lines
    (prepareDetourOn elimination clearances paid lines grid onGrid).2.val =
      (Grid.Walks.Walk.nil source.point).castEndpoints source.point_eq source.point_eq := (rfl)

/-- The original numeric cons aggregate appends its literal retained head to its unchanged actual paid tail.

The supplied head cache is consumed only through its whole original
factory equality. This equation does not evaluate the producer or retain
a second numeric traversal at runtime.
-/
theorem prepareDetourOn_cons {target : Endpoint}
    {original : Steps actual regular current reading originalOwner (target :: targets)}
    (paid : Acquisition original sourceOwner agreement) (lines : Lines paid elimination clearances)
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid point)
    (cached : DetourWalkCache elimination clearances grid paid lines onGrid) :
    let suffix := Geometry.Lines.Bank.tail
      (elimination := elimination) (clearances := clearances) (regular := regular) lines
    (prepareDetourOn elimination clearances paid lines grid onGrid).2.val =
      (headDetourWalk elimination clearances grid paid lines onGrid cached).val.append
        (prepareDetourOn elimination clearances paid.tail suffix grid
          (fun point member => onGrid point (List.Mem.tail _ member))).2.val := by
  have same := congrArg Prod.fst cached.property
  change _ = cached.val.1.append _
  rewrite [same]
  rfl

attribute [local irreducible] Block.DetourCache DetourWalkCache headDetourWalk tailDetourWalks

/-- The actual signed preparations at the original ordered numeric head occurrences.

The original dependent Sigma spine retains each complete three-cover
factory and its endpoint comparison. Its actual returned finish Owner,
with that same stored relation, indexes the next supplied-start request.
The retained numeric head/tail banks are consumed without recomputation.
-/
@[expose] def DetourSpine
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
    (supplied : Option (Block.Start sourceOwner)) → Type
  | [], _current, _reading, _originalOwner, _original, _sourceOwner, _agreement,
      _paid, _lines, _onGrid, _cached, _supplied => PUnit
  | target :: targets, _current, _reading, _originalOwner, original, _sourceOwner, _agreement,
      paid, lines, onGrid, cached, supplied =>
      let source := Geometry.Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      let suffix := Geometry.Lines.Bank.tail
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      let next := Geometry.Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := regular) suffix
      let walk := headDetourWalk elimination clearances grid paid lines onGrid cached
      Σ head : Block.DetourCache paid.head source next
          (.inr (reference source.point (onGrid source.point (List.Mem.head _)))) walk supplied,
        DetourSpine reference targets target original.nextReading original.headCovered.finishOwner
          original.tail paid.head.finishOwner paid.head.nextAgreement paid.tail suffix
          (fun point member => onGrid point (List.Mem.tail _ member))
          (tailDetourWalks elimination clearances grid paid lines onGrid cached)
          (some ⟨head.finishOwner, head.equivalent⟩)

/-- Build each actual signed head once and retain its literal returned Owner in the dependent tail. -/
private def buildDetourSpine
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
      DetourSpine elimination clearances grid reference targets current reading originalOwner original
        sourceOwner agreement paid lines onGrid cached supplied
  | [], _current, _reading, _originalOwner, _original, _sourceOwner, _agreement,
      _paid, _lines, _onGrid, _cached, _supplied => PUnit.unit
  | target :: targets, _current, _reading, _originalOwner, original, _sourceOwner, _agreement,
      paid, lines, onGrid, cached, supplied =>
      let source := Geometry.Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      let suffix := Geometry.Lines.Bank.tail
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      let next := Geometry.Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := regular) suffix
      let walk := headDetourWalk elimination clearances grid paid lines onGrid cached
      let head := paid.head.prepareDetourOn source next
        (.inr (reference source.point (onGrid source.point (List.Mem.head _)))) walk supplied
      let tail := buildDetourSpine reference targets target original.nextReading original.headCovered.finishOwner
        original.tail paid.head.finishOwner paid.head.nextAgreement paid.tail suffix
        (fun point member => onGrid point (List.Mem.tail _ member))
        (tailDetourWalks elimination clearances grid paid lines onGrid cached)
        (some ⟨head.finishOwner, head.equivalent⟩)
      ⟨head, tail⟩

/-- Prepare the actual signed detours from the same retained numeric head bank and paid spine.

Every head keeps its complete original three-cover factory. The next
preparation consumes that head's literal finish Owner and cached relation;
no original numeric Walk, query, Reading or old paid Block is recomputed.
-/
def prepareDetour
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point)
    (paid : Acquisition original sourceOwner agreement) (lines : Lines paid elimination clearances)
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid point)
    (cached : DetourWalkCache elimination clearances grid paid lines onGrid)
    (supplied : Option (Block.Start sourceOwner) := none) :
    DetourSpine elimination clearances grid reference targets current reading originalOwner original
      sourceOwner agreement paid lines onGrid cached supplied :=
  buildDetourSpine elimination clearances grid reference targets current reading originalOwner original
    sourceOwner agreement paid lines onGrid cached supplied

end CachedDetours

end Detour

end Steps.Acquisition

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
