module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment.Fold.Entry.Corner
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

/-! # Corner entry through the actual retained finish Owner

An original trace can retain its finishing Owner separately from the
canonical prepared finish, together with their original exact equality.
This entry preserves that actual stored Owner as the next execution's source
and transports only the derived source name. The preceding complete factor
Reading and Samples remain unchanged.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment

namespace Reading.Payment.Fold.Entry.Corner

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Owner)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.PreparedClearPathModels (CompleteSegment zeroEndpoint oneEndpoint ownerAtStart)

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {reference : Fraction.Rational} {referenceInside : FixedRootBoxPath.Inside reference}
variable {source : Transport.Reading actual reference referenceInside} {anchor : Parameter.Anchor source.lift}
variable {previousBudgets budgets : Budgets anchor} {previousStart corner finish : Canonical}
variable {previousSegment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) previousStart corner}
variable {segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) corner finish}
variable {previousWithin : previousSegment.WithinAmbient} {within : segment.WithinAmbient}
variable {previousCompleted : Segment previousBudgets previousSegment previousWithin}
variable {completed : Segment budgets segment within}
variable {previousOwner : Owner ((Paths.polynomial parameter).eval previousStart)}
variable (previous : CompleteSegment previousSegment previousWithin previousOwner)
variable (finishOwner : Owner ((Paths.polynomial parameter).eval corner))
variable (finishOwner_eq : finishOwner = previous.finishOwner)

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

include finishOwner_eq in
/-- The actual cached finish Owner has the same source root name after the original corner index transport. -/
theorem sourceName_eq_of_owner_eq :
    ownerRootName (ownerAtStart segment finishOwner).parameterNonzero (ownerAtStart segment finishOwner) =
      ownerRootName previous.subdivision.terminalOwner.parameterNonzero previous.subdivision.terminalOwner := by
  have original := congrArg
    (fun retained : Owner ((Paths.polynomial parameter).eval corner) =>
      ownerRootName (ownerAtStart segment retained).parameterNonzero (ownerAtStart segment retained)) finishOwner_eq
  exact original.trans (sourceName_eq (segment := segment) previous)

/-- Derive the next source relation from the original preceding terminal cache and exact cached Owner equation. -/
def sourceAgreementOfOwnerEq (terminal : Terminal (completed := previousCompleted) previous.subdivision) :
    NamedEquivalent terminal.1.values.value.name
      (ownerRootName (ownerAtStart segment finishOwner).parameterNonzero (ownerAtStart segment finishOwner)) :=
  NamedEquivalent.transport rfl
    (sourceName_eq_of_owner_eq (segment := segment) previous finishOwner finishOwner_eq).symm terminal.2.2.symm

variable (next : CompleteSegment segment within finishOwner)
variable (trace : PreparedTraceBudget segment zeroEndpoint oneEndpoint)
variable (fits : TraceFits trace next.subdivision) (widths : Widths (anchor := anchor) next.subdivision)

/-- Enter the next stored execution on the actual preceding cached finish Owner and unchanged terminal observations.

The original finish-owner equality pays only its name transport. The actual
new CompleteSegment remains indexed by the supplied stored finishOwner;
no substitute Owner, cast preparation or new Source attachment is built.
The physical join is derived from the original complete segment's endpoint.
-/
def fromTerminalOfOwnerEq (terminal : Terminal (completed := previousCompleted) previous.subdivision) :
    Entry.Cache (completed := completed) terminal.1 terminal.2.1 trace next.subdivision
      (point_eq (segment := segment) previous)
      (sourceAgreementOfOwnerEq (segment := segment) previous finishOwner finishOwner_eq terminal) fits widths :=
  Entry.Cache.build (completed := completed) terminal.1 terminal.2.1 trace next.subdivision
    (point_eq (segment := segment) previous)
    (sourceAgreementOfOwnerEq (segment := segment) previous finishOwner finishOwner_eq terminal) fits widths

end Reading.Payment.Fold.Entry.Corner

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment
