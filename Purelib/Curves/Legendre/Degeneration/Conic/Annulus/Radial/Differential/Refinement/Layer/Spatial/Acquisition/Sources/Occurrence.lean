module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Spatial.Acquisition.Sources.Entry
import Purelib.Data.List.Flatten.Occurrence
import Purelib.Data.Fin
import Purelib.Data.List.Append

/-! # Literal Block occurrence lookup in the SAME genuine fine-Layer source family

The original remaining-piece list selects its actual paid Block and whole
physical source cache. The exact head-pair equality and original tail
retain both input parents. Reading a source preparation pair uses only
those caches and their original ordered assembly; no query, root advance,
geometry, acquisition, center selection or source observer is replayed.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer

namespace Spatial.Acquisition

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
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

attribute [local irreducible] coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

namespace Sources

/-- Exact original aggregate/Block preparation incidence at one retained source occurrence.

This names the dependent child and global-index proposition used by both
structural branches. All original lists, positions, preparations and
flatten-prefix bounds remain its defining arguments.
-/
private def EntryIncidence
    (remaining : List (Piece data actual accuracy)) (first : Piece data actual accuracy)
    (queried : ∀ piece ∈ remaining, piece.Queried)
    (sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint)
    (agreement : Parallel.Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner)
    (retained : Acquisition regular finishQuery remaining first queried sourceOwner agreement)
    (kept : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) finishQuery remaining first queried sourceOwner agreement retained)
    (outer : Fin (parentWords finishQuery remaining first queried sourceOwner agreement retained kept).length) : Prop :=
  (child : Fin ((parentWords finishQuery remaining first queried sourceOwner agreement retained kept)[outer.val]'
    outer.isLt).length) →
  (globalIndex : Fin (assemble finishQuery remaining first queried sourceOwner agreement
    retained kept).geometry.parents.length) →
  globalIndex.val =
    ((parentWords finishQuery remaining first queried sourceOwner agreement retained kept).take
      outer.val).flatten.length + child.val →
  HEq ((assemble finishQuery remaining first queried sourceOwner agreement retained kept).prepared.entry globalIndex)
    ((Entry.sources finishQuery remaining first queried sourceOwner agreement retained kept outer
      (entry finishQuery remaining first queried sourceOwner agreement retained kept outer)).2.entry child)

/-- Exact original Block-prefix offsets preserve the complete SAME fine-source PreparedParent in aggregate assembly.

The proof follows only the actual retained piece/source/acquisition tails.
It uses original append incidence laws and the SAME retained input pair;
no prepared source, center state, Root, model, request or observer is rebuilt.
-/
theorem assemble_entry_heq : (remaining : List (Piece data actual accuracy)) → (first : Piece data actual accuracy) →
    (queried : ∀ piece ∈ remaining, piece.Queried) →
    (sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint) →
    (agreement : Parallel.Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner) →
    (retained : Acquisition regular finishQuery remaining first queried sourceOwner agreement) →
    (kept : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) finishQuery remaining first queried sourceOwner agreement retained) →
    (outer : Fin (parentWords finishQuery remaining first queried sourceOwner agreement retained kept).length) →
    (child : Fin ((parentWords finishQuery remaining first queried sourceOwner agreement retained kept)[outer.val]'
      outer.isLt).length) →
    (globalIndex : Fin (assemble finishQuery remaining first queried sourceOwner agreement
      retained kept).geometry.parents.length) →
    globalIndex.val =
      ((parentWords finishQuery remaining first queried sourceOwner agreement retained kept).take
        outer.val).flatten.length + child.val →
    HEq ((assemble finishQuery remaining first queried sourceOwner agreement retained kept).prepared.entry globalIndex)
      ((Entry.sources finishQuery remaining first queried sourceOwner agreement retained kept outer
        (entry finishQuery remaining first queried sourceOwner agreement retained kept outer)).2.entry child)
  | [] => fun _first _queried sourceOwner _agreement retained kept outer =>
      Data.Fin.casesDependent
        (motive := EntryIncidence finishQuery [] _first _queried sourceOwner _agreement retained kept)
        (fun child globalIndex offset => by
          let head := Spine.Sources.assemble
            (fun {_start _finish} segment => widthRequest retained.paid.anchor segment)
            retained.geometry.route.path retained.geometry.route.within sourceOwner retained.paid.paid.spine kept
          have values : globalIndex.val = child.val := offset.trans (Nat.zero_add child.val)
          have same := assemble_last_eq finishQuery retained kept
          let headIndex : Fin head.geometry.parents.length :=
            ⟨globalIndex.val, Eq.mp (congrArg (fun assembled => globalIndex.val < assembled.geometry.parents.length)
              same) globalIndex.isLt⟩
          exact (Spine.Sources.Assembled.entry_heq_of_eq _ head same globalIndex headIndex rfl).trans
            (PreparedParents.entry_congr head.covered head.prepared (Fin.ext values)))
        (fun empty => Fin.elim0 empty) outer
  | next :: remaining => fun _first queried sourceOwner _agreement retained kept outer =>
      Data.Fin.casesDependent
        (motive := EntryIncidence finishQuery (next :: remaining) _first queried
          sourceOwner _agreement retained kept)
        (fun child globalIndex offset => by
          let head := Spine.Sources.assemble
            (fun {_start _finish} segment => widthRequest retained.1.paid.anchor segment)
            retained.1.geometry.route.path retained.1.geometry.route.within sourceOwner retained.1.paid.paid.spine
            kept.1
          let following := assemble finishQuery remaining next
            (fun piece member => queried piece (List.Mem.tail next member))
            retained.1.finishOwner retained.1.nextAgreement retained.2 kept.2
          have values : globalIndex.val = child.val := offset.trans (Nat.zero_add child.val)
          have same := assemble_next_eq finishQuery retained kept
          let joinedIndex : Fin (head.append following).geometry.parents.length :=
            ⟨globalIndex.val, Eq.mp (congrArg (fun assembled => globalIndex.val < assembled.geometry.parents.length)
              same) globalIndex.isLt⟩
          exact (Spine.Sources.Assembled.entry_heq_of_eq _ (head.append following) same
            globalIndex joinedIndex rfl).trans (head.append_entry_left following child joinedIndex values))
        (fun following child globalIndex offset => by
          let head := Spine.Sources.assemble
            (fun {_start _finish} segment => widthRequest retained.1.paid.anchor segment)
            retained.1.geometry.route.path retained.1.geometry.route.within sourceOwner retained.1.paid.paid.spine
            kept.1
          let rest := assemble finishQuery remaining next
            (fun piece member => queried piece (List.Mem.tail next member))
            retained.1.finishOwner retained.1.nextAgreement retained.2 kept.2
          let words := parentWords finishQuery remaining next
            (fun piece member => queried piece (List.Mem.tail next member))
            retained.1.finishOwner retained.1.nextAgreement retained.2 kept.2
          have prefixLength :
              ((parentWords finishQuery (next :: remaining) _ queried sourceOwner _ retained kept).take
                following.succ.val).flatten.length =
                head.geometry.parents.length + (words.take following.val).flatten.length := by
            change (head.geometry.parents ++ (words.take following.val).flatten).length = _
            exact Append.length_append _ _
          let tailValue := (words.take following.val).flatten.length + child.val
          have values : globalIndex.val = head.geometry.parents.length + tailValue :=
            (offset.trans (congrArg (fun value => value + child.val) prefixLength)).trans (Nat.add_assoc _ _ _)
          have lengthEq : (head.append rest).geometry.parents.length =
              head.geometry.parents.length + rest.geometry.parents.length :=
            (congrArg List.length (Spine.Sources.Assembled.append_parents head rest)).trans
              (Append.length_append head.geometry.parents rest.geometry.parents)
          have same := assemble_next_eq finishQuery retained kept
          let joinedIndex : Fin (head.append rest).geometry.parents.length :=
            ⟨globalIndex.val, Eq.mp (congrArg (fun assembled => globalIndex.val < assembled.geometry.parents.length)
              same) globalIndex.isLt⟩
          have fullBound : globalIndex.val < head.geometry.parents.length + rest.geometry.parents.length :=
            Eq.mp (congrArg (fun length => globalIndex.val < length) lengthEq) joinedIndex.isLt
          have tailBound : tailValue < rest.geometry.parents.length := Nat.lt_of_add_lt_add_left
            (Eq.mp (congrArg (fun value => value < head.geometry.parents.length + rest.geometry.parents.length)
              values) fullBound)
          let tailIndex : Fin rest.geometry.parents.length := ⟨tailValue, tailBound⟩
          exact (Spine.Sources.Assembled.entry_heq_of_eq _ (head.append rest) same
            globalIndex joinedIndex rfl).trans
            ((head.append_entry_right rest tailIndex joinedIndex values).trans
            (assemble_entry_heq remaining next (fun piece member => queried piece (List.Mem.tail next member))
              retained.1.finishOwner retained.1.nextAgreement retained.2 kept.2 following child tailIndex rfl))) outer
termination_by structural remaining => remaining

section Located

variable (remaining : List (Piece data actual accuracy)) (first : Piece data actual accuracy)
variable (queried : ∀ piece ∈ remaining, piece.Queried)
variable (sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint)
variable (agreement : Parallel.Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner)
variable (retained : Acquisition regular finishQuery remaining first queried sourceOwner agreement)
variable (kept : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
  (sourceTargets := sourceTargets) finishQuery remaining first queried sourceOwner agreement retained)
variable (index : Fin (assemble finishQuery remaining first queried sourceOwner agreement
  retained kept).geometry.parents.length)

/-- Read the SAME literal fine-source natural position in its exact original Block flattening. -/
@[expose] def flattenedIndex :
    Fin (parentWords finishQuery remaining first queried sourceOwner agreement retained kept).flatten.length :=
  ⟨index.val, Eq.mp (congrArg (fun parents => index.val < parents.length)
    (assemble_parents finishQuery remaining first queried sourceOwner agreement retained kept)) index.isLt⟩

/-- Execute the original finite flatten locator once on the SAME actual aggregate fine-source occurrence. -/
def locate : Data.List.Flatten.Occurrence
    (parentWords finishQuery remaining first queried sourceOwner agreement retained kept)
    (flattenedIndex finishQuery remaining first queried sourceOwner agreement retained kept index) :=
  Data.List.Flatten.locate (parentWords finishQuery remaining first queried sourceOwner agreement retained kept)
    (flattenedIndex finishQuery remaining first queried sourceOwner agreement retained kept index)

/-- The retained fine-source location is exactly the original executable lookup result on its literal index. -/
theorem locate_eq : locate finishQuery remaining first queried sourceOwner agreement retained kept index =
    Data.List.Flatten.locate (parentWords finishQuery remaining first queried sourceOwner agreement retained kept)
      (flattenedIndex finishQuery remaining first queried sourceOwner agreement retained kept index) := by
  unfold locate
  rfl

variable (position : Data.List.Flatten.Occurrence
  (parentWords finishQuery remaining first queried sourceOwner agreement retained kept)
  (flattenedIndex finishQuery remaining first queried sourceOwner agreement retained kept index))

/-- Read the actual complete original fine Block/source pair using the SAME retained aggregate source location. -/
@[expose] def selected := entry finishQuery remaining first queried sourceOwner agreement retained kept position.1

/-- Read the SAME original selected Block covering/preparation pair, retaining its complete source caches. -/
@[expose] def selectedSources :=
  Entry.sources finishQuery remaining first queried sourceOwner agreement retained kept position.1
    (selected finishQuery remaining first queried sourceOwner agreement retained kept index position)

/-- The selected fine Block child is the literal aggregate source parent, independently of repeated point values. -/
theorem parent_eq :
    (assemble finishQuery remaining first queried sourceOwner agreement retained kept).geometry.parents[index.val]'
      index.isLt =
      ((parentWords finishQuery remaining first queried sourceOwner agreement retained kept)[position.1.val]'
        position.1.isLt)[position.2.val.val]'position.2.val.isLt :=
  (getElem_congr (assemble_parents finishQuery remaining first queried sourceOwner agreement retained kept)
    rfl index.isLt).trans position.2.property.1

/-- The aggregate fine source retains the WHOLE original selected PreparedParent, not only its point or sample value. -/
theorem prepared_heq :
    HEq ((assemble finishQuery remaining first queried sourceOwner agreement retained kept).prepared.entry index)
      ((selectedSources finishQuery remaining first queried sourceOwner agreement retained kept
        index position).2.entry position.2.val) :=
  assemble_entry_heq finishQuery remaining first queried sourceOwner agreement retained kept position.1 position.2.val
    index position.2.property.2

end Located

end Sources

end Spatial.Acquisition

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer

end
