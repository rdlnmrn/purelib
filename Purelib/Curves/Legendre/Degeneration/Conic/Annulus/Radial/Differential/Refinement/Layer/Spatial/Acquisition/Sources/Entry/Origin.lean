module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Spatial.Acquisition.Sources.Entry
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Block.Sources.Occurrence
import Purelib.Data.Fin
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Curves.Legendre.Periods.Fibre

/-! # Exact source origins below a retained genuine fine Block entry

The selected original Entry supplies its whole actual Block/source pair.
The readonly origin constructor follows the original finite Entry index,
retains its literal Piece membership and queries only the physical locator
and SourceAt getters. Original numerical/source/continuation producers are
not replayed. Every original nominal Owner and previous-corner origin stays
in the resulting SourceOccurrence.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer

namespace Spatial.Acquisition.Sources.Entry

open Purelib
open Purelib.Curves.Legendre.Periods
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
variable {frame : Paths.Frame parameter} {basis : Differential 1} {count floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {sourceTargets : CellEndpoints.Targets sourcePath stage}

attribute [local irreducible] coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- A literal fine Piece, its unchanged Block/source parents and the exact retained physical source occurrence.

Existing Sigma/subtype containers expose the selected mathematical parents
hidden by the Entry's varying Piece index. The final incidence is equality
of the entire original centered parent. No root relation, numerical bound,
replacement Owner, runtime identifier or execution callback is stored.
-/
@[expose] def Origin (pieces : List (Piece data actual accuracy))
    (parent : CenteredEdge (Fibre.frameCurve frame) basis) :=
  Σ piece : { value : Piece data actual accuracy // value ∈ pieces },
    Σ target : Endpoint,
      Σ queried : { reading : ReadingAt actual target // QueryCache actual target reading },
        Σ sourceOwner : OwnerAt site parameter quarter positive piece.val.lowerEndpoint,
          Σ agreement : Steps.Acquisition.InitialAgreement
              piece.val.lowerEndpoint piece.val.source sourceOwner,
            Σ block : Block (regular := regular) piece.val queried sourceOwner agreement,
              Σ kept : Spine.Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
                  (sheet := sheet) (targets := sourceTargets)
                  (fun {_start _finish} segment => widthRequest block.paid.anchor segment)
                  block.geometry.route.path block.geometry.route.within sourceOwner block.paid.paid.spine,
                Σ index : Fin (Spine.Sources.assemble
                    (fun {_start _finish} segment => widthRequest block.paid.anchor segment)
                    block.geometry.route.path block.geometry.route.within sourceOwner
                    block.paid.paid.spine kept).geometry.parents.length,
                  { retained : Steps.Acquisition.Block.SourceOccurrence block.paid kept index //
                    retained.parent = parent }

namespace Origin

variable {pieces : List (Piece data actual accuracy)} {parent : CenteredEdge (Fibre.frameCurve frame) basis}

/-- Retain an original fine Block occurrence with its actual Piece membership and whole parent incidence.

The supplied Block, physical source family and already materialized occurrence
are stored unchanged. This constructor performs no lookup or acquisition.
-/
def ofOccurrence (piece : Piece data actual accuracy) (member : piece ∈ pieces)
    (target : Endpoint) (queried : { reading : ReadingAt actual target // QueryCache actual target reading })
    (sourceOwner : OwnerAt site parameter quarter positive piece.lowerEndpoint)
    (agreement : Steps.Acquisition.InitialAgreement piece.lowerEndpoint piece.source sourceOwner)
    (block : Block (regular := regular) piece queried sourceOwner agreement)
    (kept : Spine.Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := sourceTargets)
      (fun {_start _finish} segment => widthRequest block.paid.anchor segment)
      block.geometry.route.path block.geometry.route.within sourceOwner block.paid.paid.spine)
    (index : Fin (Spine.Sources.assemble
      (fun {_start _finish} segment => widthRequest block.paid.anchor segment)
      block.geometry.route.path block.geometry.route.within sourceOwner
      block.paid.paid.spine kept).geometry.parents.length)
    (observed : Steps.Acquisition.Block.SourceOccurrence block.paid kept index)
    (same : observed.parent = parent) :
    Origin (regular := regular) (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (sourceTargets := sourceTargets) pieces parent :=
  ⟨⟨piece, member⟩, target, queried, sourceOwner, agreement, block, kept, index, ⟨observed, same⟩⟩

variable (retained : Origin (regular := regular) (frame := frame) (basis := basis) (count := count)
  (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) pieces parent)

/-- Read the identical original Piece selected by this exact retained fine Block occurrence. -/
@[expose] def piece : Piece data actual accuracy := retained.1.val

/-- The selected Piece belongs to the original actual head/tail list, including its final span. -/
theorem member : retained.piece ∈ pieces := retained.1.property

/-- Read the SAME original target endpoint of this selected fine Block. -/
@[expose] def target : Endpoint := retained.2.1

/-- Read the SAME target Reading and QueryCache without performing the query. -/
@[expose] def queried :
    { reading : ReadingAt actual retained.target // QueryCache actual retained.target reading } :=
  retained.2.2.1

/-- Read the exact original supplied source Owner, including prior actual finish-owner handoffs. -/
@[expose] def sourceOwner : OwnerAt site parameter quarter positive retained.piece.lowerEndpoint :=
  retained.2.2.2.1

/-- Read the SAME original source agreement attached to that literal source Owner. -/
@[expose] def agreement : Steps.Acquisition.InitialAgreement
    retained.piece.lowerEndpoint retained.piece.source retained.sourceOwner := retained.2.2.2.2.1

/-- Read the whole original Layer Block with its same Geometry, Route and paid acquisition. -/
@[expose] def block :
    Block (regular := regular) retained.piece retained.queried retained.sourceOwner retained.agreement :=
  retained.2.2.2.2.2.1

/-- Read its SAME original physical source family, including the actual previous-corner caches. -/
@[expose] def sources : Spine.Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
    (sheet := sheet) (targets := sourceTargets)
    (fun {_start _finish} segment => widthRequest retained.block.paid.anchor segment)
    retained.block.geometry.route.path retained.block.geometry.route.within
    retained.sourceOwner retained.block.paid.paid.spine := retained.2.2.2.2.2.2.1

/-- Read the literal bounded original source occurrence inside that SAME selected Block. -/
@[expose] def index : Fin (Spine.Sources.assemble
    (fun {_start _finish} segment => widthRequest retained.block.paid.anchor segment)
    retained.block.geometry.route.path retained.block.geometry.route.within
    retained.sourceOwner retained.block.paid.paid.spine retained.sources).geometry.parents.length :=
  retained.2.2.2.2.2.2.2.1

/-- Read the whole original physical locator and SourceAt cache pair acquired by the readonly origin factory. -/
@[expose] def occurrence :
    Steps.Acquisition.Block.SourceOccurrence retained.block.paid retained.sources retained.index :=
  retained.2.2.2.2.2.2.2.2.val

/-- The selected source occurrence retains the SAME entire original centered parent. -/
theorem parent_eq : retained.occurrence.parent = parent := retained.2.2.2.2.2.2.2.2.property

/-- Transport only the complete original parent index of the SAME retained source occurrence and its whole caches. -/
@[expose] def castParent {next : CenteredEdge (Fibre.frameCurve frame) basis} (same : parent = next) :
    Origin (regular := regular) (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (sourceTargets := sourceTargets) pieces next := by
  cases same
  exact retained

/-- A whole-parent index transport preserves the complete original origin cache heterogeneously. -/
theorem castParent_heq {next : CenteredEdge (Fibre.frameCurve frame) basis} (same : parent = next) :
    HEq (retained.castParent same) retained := by
  cases same
  rfl

/-- Add only the original preceding Piece to membership; all selected mathematical parents remain the SAME values. -/
@[expose] def prepend (first : Piece data actual accuracy) :
    Origin (regular := regular) (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (sourceTargets := sourceTargets) (first :: pieces) parent :=
  ⟨⟨retained.piece, List.Mem.tail first retained.member⟩, retained.2⟩

/-- Membership extension preserves the literal whole original source occurrence unchanged. -/
theorem prepend_occurrence_heq (first : Piece data actual accuracy) :
    HEq (retained.prepend first).occurrence retained.occurrence := by rfl

end Origin

variable {finish : Endpoint}
variable (finishQuery : { reading : ReadingAt actual finish // QueryCache actual finish reading })

/-- Read the actual selected fine Entry's source origin once at its SAME original physical child.

The stored whole input-pair equality transports the original child bound.
Only existing locator/source-origin getters run; the actual Block, source
family, selected parent and previous Reading/Samples remain unchanged.
-/
def origin : (remaining : List (Piece data actual accuracy)) → (first : Piece data actual accuracy) →
    (queried : ∀ piece ∈ remaining, piece.Queried) →
    (sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint) →
    (agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner) →
    (retained : Acquisition regular finishQuery remaining first queried sourceOwner agreement) →
    (kept : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) finishQuery remaining first queried sourceOwner agreement retained) →
    (outer : Fin (parentWords finishQuery remaining first queried sourceOwner agreement retained kept).length) →
    (picked : Entry finishQuery remaining first queried sourceOwner agreement retained kept outer) →
    (child : Fin ((parentWords finishQuery remaining first queried sourceOwner agreement retained kept)[outer.val]'
      outer.isLt).length) →
    Origin (regular := regular) (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (sourceTargets := sourceTargets) (first :: remaining)
      (((parentWords finishQuery remaining first queried sourceOwner agreement retained kept)[outer.val]'
        outer.isLt)[child.val]'child.isLt)
  | [] => fun first _queried sourceOwner agreement retained kept outer =>
      Data.Fin.casesDependent
        (motive := fun selectedIndex :
            Fin (parentWords finishQuery [] first _queried sourceOwner agreement retained kept).length =>
          Entry finishQuery [] first _queried sourceOwner agreement retained kept selectedIndex →
          (child : Fin ((parentWords finishQuery [] first _queried
            sourceOwner agreement retained kept)[selectedIndex.val]'selectedIndex.isLt).length) →
          Origin (regular := regular) (frame := frame) (basis := basis) (count := count) (floor := floor)
            (sheet := sheet) (sourceTargets := sourceTargets) (first :: [])
            (((parentWords finishQuery [] first _queried sourceOwner agreement
              retained kept)[selectedIndex.val]'selectedIndex.isLt)[child.val]'child.isLt))
        (fun picked child => by
          let selected := picked.val.2
          have same := congrArg (fun sources => (Spine.Sources.assemble
            (fun {_start _finish} segment => widthRequest retained.paid.anchor segment)
            retained.geometry.route.path retained.geometry.route.within sourceOwner retained.paid.paid.spine
            sources).geometry.parents) (congrArg Prod.snd picked.property)
          let index : Fin (Spine.Sources.assemble
              (fun {_start _finish} segment => widthRequest retained.paid.anchor segment)
              retained.geometry.route.path retained.geometry.route.within sourceOwner retained.paid.paid.spine
              selected).geometry.parents.length :=
            ⟨child.val, Eq.mpr (congrArg (fun parents => child.val < parents.length) same) child.isLt⟩
          let observed := Steps.Acquisition.Block.sourceOccurrence retained.paid selected index
          exact Origin.ofOccurrence first (List.Mem.head []) finish finishQuery sourceOwner agreement
            retained selected index observed (getElem_congr same rfl index.isLt))
        (fun empty => Fin.elim0 empty) outer
  | next :: remaining => fun first queried sourceOwner agreement retained kept outer =>
      Data.Fin.casesDependent
        (motive := fun selectedIndex :
            Fin (parentWords finishQuery (next :: remaining) first queried
              sourceOwner agreement retained kept).length =>
          Entry finishQuery (next :: remaining) first queried sourceOwner agreement retained kept selectedIndex →
          (child : Fin ((parentWords finishQuery (next :: remaining) first queried
            sourceOwner agreement retained kept)[selectedIndex.val]'selectedIndex.isLt).length) →
          Origin (regular := regular) (frame := frame) (basis := basis) (count := count) (floor := floor)
            (sheet := sheet) (sourceTargets := sourceTargets) (first :: (next :: remaining))
            (((parentWords finishQuery (next :: remaining) first queried sourceOwner agreement
              retained kept)[selectedIndex.val]'selectedIndex.isLt)[child.val]'child.isLt))
        (fun picked child => by
          let selected := picked.val.2
          have same := congrArg (fun sources => (Spine.Sources.assemble
            (fun {_start _finish} segment => widthRequest retained.1.paid.anchor segment)
            retained.1.geometry.route.path retained.1.geometry.route.within sourceOwner retained.1.paid.paid.spine
            sources).geometry.parents) (congrArg Prod.snd picked.property)
          let index : Fin (Spine.Sources.assemble
              (fun {_start _finish} segment => widthRequest retained.1.paid.anchor segment)
              retained.1.geometry.route.path retained.1.geometry.route.within sourceOwner retained.1.paid.paid.spine
              selected).geometry.parents.length :=
            ⟨child.val, Eq.mpr (congrArg (fun parents => child.val < parents.length) same) child.isLt⟩
          let observed := Steps.Acquisition.Block.sourceOccurrence retained.1.paid selected index
          exact Origin.ofOccurrence first (List.Mem.head (next :: remaining)) next.lowerEndpoint
            (next.sourceQuery (queried next (List.Mem.head remaining))) sourceOwner agreement retained.1
            selected index observed (getElem_congr same rfl index.isLt))
        (fun following picked child =>
          (origin remaining next (fun piece member => queried piece (List.Mem.tail next member))
            retained.1.finishOwner retained.1.nextAgreement retained.2 kept.2 following picked child).prepend first)
        outer
termination_by structural remaining => remaining

end Spatial.Acquisition.Sources.Entry

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer

end
