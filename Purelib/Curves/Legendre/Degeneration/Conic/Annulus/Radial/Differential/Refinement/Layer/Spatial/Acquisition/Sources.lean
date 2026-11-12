module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Spatial.Acquisition.Entry
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.Spine.Assembly
import Purelib.Data.List.Append
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

/-! # Shared original source preparations on a genuinely finer paid Layer

Each actual old Layer piece owns its own paid Block, Geometry and physical
acquisitions. One source family prepares each such retained acquisition
once, independently of the primitive or differential row subsequently read.
Assembly consumes only those SAME preparations, preserving literal paid
finishOwner handoffs and every actual physical Segment/child occurrence.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer

namespace Spatial.Acquisition

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Transport.Spatial
open Transport.Spatial.Parallel
open Transport.Spatial.Factors.Segment.Reading.Payment (widthRequest)

variable {radicand : CoefficientPolynomial}
variable {site : Fin 2} {parameter : Canonical} {differential : OddPowerDifferential radicand}
variable {data : Waist.Differential.Bounds.Data site parameter differential}
variable {quarter : UnitCircuitQuarter} {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive} {accuracy : AccuracyRequest}
variable {regular : parameter ≠ criticalValue site}
variable {finish : Endpoint}
variable (finishQuery : { reading : ReadingAt actual finish // QueryCache actual finish reading })
variable {frame : Paths.Frame parameter} {basis : Differential 1} {count floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {sourceTargets : CellEndpoints.Targets sourcePath stage}

attribute [local irreducible] Transport.Spatial.coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- One complete original physical source family per SAME actual paid Layer Block, shared by all selected rows.

This family follows the original remaining-piece list. Its dependent tail
uses the literal stored head finishOwner and original next agreement.
No old Steps execution or new source/root owner is used as a substitute.
-/
@[expose] def Sources : (remaining : List (Piece data actual accuracy)) → (first : Piece data actual accuracy) →
    (queried : ∀ piece ∈ remaining, piece.Queried) →
    (sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint) →
    (agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner) →
    Acquisition regular finishQuery remaining first queried sourceOwner agreement → Type 1
  | [] => fun _first _queried sourceOwner _agreement retained =>
      Spine.Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
        (sheet := sheet) (targets := sourceTargets)
        (fun {_start _finish} segment => widthRequest retained.paid.anchor segment)
        retained.geometry.route.path retained.geometry.route.within sourceOwner retained.paid.paid.spine
  | next :: remaining => fun _first queried _sourceOwner _agreement retained =>
      Spine.Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
        (sheet := sheet) (targets := sourceTargets)
        (fun {_start _finish} segment => widthRequest retained.1.paid.anchor segment)
        retained.1.geometry.route.path retained.1.geometry.route.within _sourceOwner retained.1.paid.paid.spine ×
        Sources remaining next
          (fun piece member => queried piece (List.Mem.tail next member))
          retained.1.finishOwner retained.1.nextAgreement retained.2
termination_by structural remaining => remaining

namespace Sources

/-- Prepare the original center/cover/source family once on each SAME actual acquired physical Route.

Only the source preparation factories run here. The original fine Layer,
source Readings, paid Blocks, factor folds and physical subdivisions are
already supplied and remain unchanged. All six scalar model channels share
this one retained source family.
-/
def build : (remaining : List (Piece data actual accuracy)) → (first : Piece data actual accuracy) →
    (queried : ∀ piece ∈ remaining, piece.Queried) →
    (sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint) →
    (agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner) →
    (retained : Acquisition regular finishQuery remaining first queried sourceOwner agreement) →
      Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
        (sourceTargets := sourceTargets) finishQuery remaining first queried sourceOwner agreement retained
  | [] => fun _first _queried sourceOwner _agreement retained =>
      Spine.Sources.build (frame := frame) (basis := basis) (count := count) (floor := floor)
        (sheet := sheet) (targets := sourceTargets)
        (fun {_start _finish} segment => widthRequest retained.paid.anchor segment)
        retained.geometry.route.path retained.geometry.route.within sourceOwner retained.paid.paid.spine
  | next :: remaining => fun _first queried sourceOwner _agreement retained =>
      let head := Spine.Sources.build (frame := frame) (basis := basis) (count := count) (floor := floor)
        (sheet := sheet) (targets := sourceTargets)
        (fun {_start _finish} segment => widthRequest retained.1.paid.anchor segment)
        retained.1.geometry.route.path retained.1.geometry.route.within sourceOwner retained.1.paid.paid.spine
      let following := build remaining next
        (fun piece member => queried piece (List.Mem.tail next member))
        retained.1.finishOwner retained.1.nextAgreement retained.2
      ⟨head, following⟩
termination_by structural remaining => remaining

/-- Assemble only the SAME existing physical source parents in the original fine-Layer piece order.

The complete source families retain their original Parents, canonical
center states, covers and six-channel preparation products. Appending
them preserves the exact actual physical endpoints and cache owners.
-/
def assemble : (remaining : List (Piece data actual accuracy)) → (first : Piece data actual accuracy) →
    (queried : ∀ piece ∈ remaining, piece.Queried) →
    (sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint) →
    (agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner) →
    (retained : Acquisition regular finishQuery remaining first queried sourceOwner agreement) →
    Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) finishQuery remaining first queried sourceOwner agreement retained →
    Spine.Sources.Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := sourceTargets)
      (Transport.Spatial.coordinate site parameter 2 quarter positive first.span.lower)
      (Transport.Spatial.coordinate site parameter 2 quarter positive finish.parameter)
  | [] => fun _first _queried sourceOwner _agreement retained sources =>
      Spine.Sources.assemble
        (fun {_start _finish} segment => widthRequest retained.paid.anchor segment)
        retained.geometry.route.path retained.geometry.route.within sourceOwner retained.paid.paid.spine sources
  | next :: remaining => fun _first queried sourceOwner _agreement retained sources =>
      let head := Spine.Sources.assemble
        (fun {_start _finish} segment => widthRequest retained.1.paid.anchor segment)
        retained.1.geometry.route.path retained.1.geometry.route.within sourceOwner retained.1.paid.paid.spine sources.1
      let following := assemble remaining next
        (fun piece member => queried piece (List.Mem.tail next member))
        retained.1.finishOwner retained.1.nextAgreement retained.2 sources.2
      head.append following
termination_by structural remaining => remaining

/-- Read one exact assembled physical parent word per original paid Layer Block, retaining empty Routes in order. -/
@[expose] def parentWords : (remaining : List (Piece data actual accuracy)) → (first : Piece data actual accuracy) →
    (queried : ∀ piece ∈ remaining, piece.Queried) →
    (sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint) →
    (agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner) →
    (retained : Acquisition regular finishQuery remaining first queried sourceOwner agreement) →
    Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) finishQuery remaining first queried sourceOwner agreement retained →
    List (List (CenteredEdge (Curves.Legendre.Periods.Fibre.frameCurve frame) basis))
  | [] => fun _first _queried sourceOwner _agreement retained sources =>
      [(Spine.Sources.assemble
        (fun {_start _finish} segment => widthRequest retained.paid.anchor segment)
        retained.geometry.route.path retained.geometry.route.within sourceOwner
        retained.paid.paid.spine sources).geometry.parents]
  | next :: remaining => fun _first queried sourceOwner _agreement retained sources =>
      (Spine.Sources.assemble
        (fun {_start _finish} segment => widthRequest retained.1.paid.anchor segment)
        retained.1.geometry.route.path retained.1.geometry.route.within sourceOwner
          retained.1.paid.paid.spine sources.1).geometry.parents ::
        parentWords remaining next (fun piece member => queried piece (List.Mem.tail next member))
          retained.1.finishOwner retained.1.nextAgreement retained.2 sources.2
termination_by structural remaining => remaining

/-- Assembly preserves the literal block/Segment/child parent order on the SAME fine execution and source caches. -/
theorem assemble_parents : (remaining : List (Piece data actual accuracy)) → (first : Piece data actual accuracy) →
    (queried : ∀ piece ∈ remaining, piece.Queried) →
    (sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint) →
    (agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner) →
    (retained : Acquisition regular finishQuery remaining first queried sourceOwner agreement) →
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) finishQuery remaining first queried sourceOwner agreement retained) →
    (assemble finishQuery remaining first queried sourceOwner agreement retained sources).geometry.parents =
      (parentWords finishQuery remaining first queried sourceOwner agreement retained sources).flatten
  | [] => fun _first _queried _sourceOwner _agreement retained sources =>
      (Append.append_nil (Spine.Sources.assemble
        (fun {_start _finish} segment => widthRequest retained.paid.anchor segment)
        retained.geometry.route.path retained.geometry.route.within _sourceOwner
        retained.paid.paid.spine sources).geometry.parents).symm
  | next :: remaining => fun _first queried sourceOwner _agreement retained sources => by
      let head := Spine.Sources.assemble
        (fun {_start _finish} segment => widthRequest retained.1.paid.anchor segment)
        retained.1.geometry.route.path retained.1.geometry.route.within sourceOwner retained.1.paid.paid.spine sources.1
      let following := assemble finishQuery remaining next
        (fun piece member => queried piece (List.Mem.tail next member))
        retained.1.finishOwner retained.1.nextAgreement retained.2 sources.2
      change (head.append following).geometry.parents = head.geometry.parents ++ _
      rewrite [Spine.Sources.Assembled.append_parents]
      exact congrArg (List.append head.geometry.parents)
        (assemble_parents remaining next (fun piece member => queried piece (List.Mem.tail next member))
          retained.1.finishOwner retained.1.nextAgreement retained.2 sources.2)
termination_by structural remaining => remaining

/-- The SAME source family has one parent word per literal original paid Layer Block, including its final span. -/
theorem parentWords_length : (remaining : List (Piece data actual accuracy)) → (first : Piece data actual accuracy) →
    (queried : ∀ piece ∈ remaining, piece.Queried) →
    (sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint) →
    (agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner) →
    (retained : Acquisition regular finishQuery remaining first queried sourceOwner agreement) →
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) finishQuery remaining first queried sourceOwner agreement retained) →
    (parentWords finishQuery remaining first queried sourceOwner agreement retained sources).length =
      retained.blockCount
  | [] => fun _first _queried _sourceOwner _agreement _retained _sources => rfl
  | next :: remaining => fun _first queried _sourceOwner _agreement retained sources => by
      have counted := parentWords_length remaining next
        (fun piece member => queried piece (List.Mem.tail next member))
        retained.1.finishOwner retained.1.nextAgreement retained.2 sources.2
      exact (congrArg (fun size => size + 1) counted).trans (Nat.add_comm _ _)
termination_by structural remaining => remaining

section AssemblyReadbacks

variable {first : Piece data actual accuracy}
variable {sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint}
variable {agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner}

/-- The final original paid span assembles exactly its supplied complete physical source family. -/
theorem assemble_last_eq {queried : ∀ piece ∈ ([] : List (Piece data actual accuracy)), piece.Queried}
    (retained : Acquisition regular finishQuery [] first queried sourceOwner agreement)
    (kept : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) finishQuery [] first queried sourceOwner agreement retained) :
    assemble finishQuery [] first queried sourceOwner agreement retained kept =
      Spine.Sources.assemble
        (fun {_start _finish} segment => widthRequest retained.paid.anchor segment)
        retained.geometry.route.path retained.geometry.route.within sourceOwner retained.paid.paid.spine kept := by
  unfold assemble
  rfl

/-- Actual next-span assembly is the original append on the SAME complete stored head and dependent tail sources. -/
theorem assemble_next_eq {next : Piece data actual accuracy} {remaining : List (Piece data actual accuracy)}
    {queried : ∀ piece ∈ next :: remaining, piece.Queried}
    (retained : Acquisition regular finishQuery (next :: remaining) first queried sourceOwner agreement)
    (kept : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) finishQuery (next :: remaining) first queried sourceOwner agreement retained) :
    assemble finishQuery (next :: remaining) first queried sourceOwner agreement retained kept =
      (Spine.Sources.assemble
        (fun {_start _finish} segment => widthRequest retained.1.paid.anchor segment)
        retained.1.geometry.route.path retained.1.geometry.route.within sourceOwner retained.1.paid.paid.spine
        kept.1).append
        (assemble finishQuery remaining next (fun piece member => queried piece (List.Mem.tail next member))
          retained.1.finishOwner retained.1.nextAgreement retained.2 kept.2) := by
  rfl

end AssemblyReadbacks

section SignedRoots

open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Topology

/-- Read signed parent chains through the literal retained fine-Block finish-Owner handoffs.

Empty physical Routes remain empty root chains on their actual Owners.
The original Sources tail and actual acquisition tail are consumed together;
no Piece, query, source preparation or paid acquisition is executed again.
-/
private def rootChainWords : (remaining : List (Piece data actual accuracy)) →
    (first : Piece data actual accuracy) → (queried : ∀ piece ∈ remaining, piece.Queried) →
    (sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint) →
    (agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner) →
    (paid : Acquisition regular finishQuery remaining first queried sourceOwner agreement) →
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) finishQuery remaining first queried sourceOwner agreement paid) →
    RootChain (parentWords finishQuery remaining first queried sourceOwner agreement paid sources).flatten
      (ownerRootName sourceOwner.parameterNonzero sourceOwner)
      (ownerRootName paid.finishOwner.parameterNonzero paid.finishOwner)
  | [] => fun _first _queried sourceOwner _agreement paid sources =>
      PreparedBankRootChains.RootChain.castChildren (Append.append_nil _).symm
        (Spine.Sources.acquiredRootChain
          (fun {_start _finish} segment => widthRequest paid.paid.anchor segment)
          paid.geometry.route.path paid.geometry.route.within sourceOwner paid.paid.paid.paid sources)
  | next :: remaining => fun _first queried sourceOwner _agreement paid sources =>
      let first := Spine.Sources.acquiredRootChain
        (fun {_start _finish} segment => widthRequest paid.1.paid.anchor segment)
        paid.1.geometry.route.path paid.1.geometry.route.within sourceOwner paid.1.paid.paid.paid sources.1
      let following := rootChainWords remaining next
        (fun piece member => queried piece (List.Mem.tail next member))
        paid.1.finishOwner paid.1.nextAgreement paid.2 sources.2
      first.append following
termination_by structural remaining => remaining

/-- Derive the signed chain of the SAME fine-Layer assembled sources, including zero-word Block handoffs.

The literal source Owner and terminal Owner remain the original acquisition
indices. The original ordered-parent equality transports only the list;
the signed joins are those of the actual stored physical subdivisions.
-/
def rootChain (remaining : List (Piece data actual accuracy)) (first : Piece data actual accuracy)
    (queried : ∀ piece ∈ remaining, piece.Queried)
    (sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint)
    (agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner)
    (paid : Acquisition regular finishQuery remaining first queried sourceOwner agreement)
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) finishQuery remaining first queried sourceOwner agreement paid) :
    RootChain (assemble finishQuery remaining first queried sourceOwner agreement paid sources).geometry.parents
      (ownerRootName sourceOwner.parameterNonzero sourceOwner)
      (ownerRootName paid.finishOwner.parameterNonzero paid.finishOwner) :=
  PreparedBankRootChains.RootChain.castChildren
    (assemble_parents finishQuery remaining first queried sourceOwner agreement paid sources).symm
    (rootChainWords finishQuery remaining first queried sourceOwner agreement paid sources)

end SignedRoots

end Sources

end Spatial.Acquisition

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer

end
