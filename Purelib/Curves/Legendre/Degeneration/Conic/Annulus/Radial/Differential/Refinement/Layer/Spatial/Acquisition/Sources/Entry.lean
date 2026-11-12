module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Spatial.Acquisition.Sources
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

/-- The exact complete original Block/source input pair at a bounded actual fine-Layer Block occurrence.

The head keeps the SAME old Block and full physical source family plus
its whole input identity. Successors retain the original list tail and
literal finishOwner/nextAgreement. Existing Sigma/Subtype containers keep
these actual parents; no new execution context or runtime identifier is used.
-/
@[expose] def Entry : (remaining : List (Piece data actual accuracy)) → (first : Piece data actual accuracy) →
    (queried : ∀ piece ∈ remaining, piece.Queried) →
    (sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint) →
    (agreement : Parallel.Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner) →
    (retained : Acquisition regular finishQuery remaining first queried sourceOwner agreement) →
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) finishQuery remaining first queried sourceOwner agreement retained) →
    (index : Fin (parentWords finishQuery remaining first queried sourceOwner agreement retained sources).length) →
    Type 1
  | [] => fun first _queried sourceOwner agreement retained kept index =>
      Data.Fin.cases
        { input : Block (regular := regular) first finishQuery sourceOwner agreement ×
          Spine.Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
          (sheet := sheet) (targets := sourceTargets)
          (fun {_start _finish} segment => widthRequest retained.paid.anchor segment)
          retained.geometry.route.path retained.geometry.route.within sourceOwner retained.paid.paid.spine //
          input = (retained, kept) }
        (fun empty => Fin.elim0 empty) index
  | next :: remaining => fun first queried sourceOwner agreement retained kept index =>
      Data.Fin.cases
        { input : Block (regular := regular) first
            (next.sourceQuery (queried next (List.Mem.head remaining))) sourceOwner agreement ×
          Spine.Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
          (sheet := sheet) (targets := sourceTargets)
          (fun {_start _finish} segment => widthRequest retained.1.paid.anchor segment)
          retained.1.geometry.route.path retained.1.geometry.route.within sourceOwner retained.1.paid.paid.spine //
          input = (retained.1, kept.1) }
        (fun following => Entry remaining next (fun piece member => queried piece (List.Mem.tail next member))
          retained.1.finishOwner retained.1.nextAgreement retained.2 kept.2 following) index
termination_by structural remaining => remaining

/-- Read the SAME actual fine Block/source pair without running a Geometry, paid Fold, preparation or observer.

The supplied whole source family and paid fold determine every branch.
On the second physical L-edge the retained Block still owns its original
origin-sensitive Entry and previous Reading/Samples; this getter does not
replace or reindex those caches.
-/
@[expose] def entry : (remaining : List (Piece data actual accuracy)) → (first : Piece data actual accuracy) →
    (queried : ∀ piece ∈ remaining, piece.Queried) →
    (sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint) →
    (agreement : Parallel.Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner) →
    (retained : Acquisition regular finishQuery remaining first queried sourceOwner agreement) →
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) finishQuery remaining first queried sourceOwner agreement retained) →
    (index : Fin (parentWords finishQuery remaining first queried sourceOwner agreement retained sources).length) →
    Entry finishQuery remaining first queried sourceOwner agreement retained sources index
  | [] => fun _first _queried _sourceOwner _agreement retained kept index =>
      Data.Fin.casesDependent ⟨(retained, kept), rfl⟩ (fun empty => Fin.elim0 empty) index
  | next :: remaining => fun _first queried _sourceOwner _agreement retained kept index =>
      Data.Fin.casesDependent ⟨(retained.1, kept.1), rfl⟩
        (fun following => entry remaining next (fun piece member => queried piece (List.Mem.tail next member))
          retained.1.finishOwner retained.1.nextAgreement retained.2 kept.2 following) index
termination_by structural remaining => remaining

namespace Entry

/-- Read the SAME complete covering/preparation pair from an original actual fine Block occurrence.

The stored original whole-pair equality transports only the exact parent
list index of that pair. No geometry, source preparation, observation,
allocation, factor query or accepted root advance is reconstructed.
-/
@[expose] def sources : (remaining : List (Piece data actual accuracy)) → (first : Piece data actual accuracy) →
    (queried : ∀ piece ∈ remaining, piece.Queried) →
    (sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint) →
    (agreement : Parallel.Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner) →
    (retained : Acquisition regular finishQuery remaining first queried sourceOwner agreement) →
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) finishQuery remaining first queried sourceOwner agreement retained) →
    (index : Fin (parentWords finishQuery remaining first queried sourceOwner agreement retained sources).length) →
    Entry finishQuery remaining first queried sourceOwner agreement retained sources index →
    Σ covered : CoveredParents count
        ((parentWords finishQuery remaining first queried sourceOwner agreement retained sources)[index.val]'
          index.isLt),
      PreparedParents (frame := frame) (basis := basis) covered floor sourceTargets
  | [] => fun _first _queried sourceOwner _agreement retained kept index =>
      Data.Fin.casesDependent
        (motive := fun selectedIndex :
            Fin (parentWords finishQuery [] _first _queried sourceOwner _agreement retained kept).length =>
          Entry finishQuery [] _first _queried sourceOwner _agreement retained kept selectedIndex →
            Σ covered : CoveredParents count
                ((parentWords finishQuery [] _first _queried sourceOwner _agreement
                    retained kept)[selectedIndex.val]'selectedIndex.isLt),
              PreparedParents covered floor sourceTargets)
        (fun selected =>
          let actual := Spine.Sources.assemble
            (fun {_start _finish} segment => widthRequest retained.paid.anchor segment)
            retained.geometry.route.path retained.geometry.route.within sourceOwner retained.paid.paid.spine
            selected.val.2
          have same := congrArg (fun kept => (Spine.Sources.assemble
            (fun {_start _finish} segment => widthRequest retained.paid.anchor segment)
            retained.geometry.route.path retained.geometry.route.within sourceOwner retained.paid.paid.spine
            kept).geometry.parents) (congrArg Prod.snd selected.property)
          PreparedParents.castParents same actual.covered actual.prepared)
        (fun empty => Fin.elim0 empty) index
  | next :: remaining => fun _first queried sourceOwner _agreement retained kept index =>
      Data.Fin.casesDependent
        (motive := fun selectedIndex :
            Fin (parentWords finishQuery (next :: remaining) _first queried
              sourceOwner _agreement retained kept).length =>
          Entry finishQuery (next :: remaining) _first queried sourceOwner _agreement retained kept selectedIndex →
            Σ covered : CoveredParents count
                ((parentWords finishQuery (next :: remaining) _first queried sourceOwner _agreement
                    retained kept)[selectedIndex.val]'selectedIndex.isLt),
              PreparedParents covered floor sourceTargets)
        (fun selected =>
          let actual := Spine.Sources.assemble
            (fun {_start _finish} segment => widthRequest retained.1.paid.anchor segment)
            retained.1.geometry.route.path retained.1.geometry.route.within sourceOwner retained.1.paid.paid.spine
            selected.val.2
          have same := congrArg (fun kept => (Spine.Sources.assemble
            (fun {_start _finish} segment => widthRequest retained.1.paid.anchor segment)
            retained.1.geometry.route.path retained.1.geometry.route.within sourceOwner retained.1.paid.paid.spine
            kept).geometry.parents) (congrArg Prod.snd selected.property)
          PreparedParents.castParents same actual.covered actual.prepared)
        (fun following selected => Entry.sources remaining next
          (fun piece member => queried piece (List.Mem.tail next member))
          retained.1.finishOwner retained.1.nextAgreement retained.2 kept.2 following selected) index
termination_by structural remaining => remaining

end Entry

end Sources

end Spatial.Acquisition

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer

end
