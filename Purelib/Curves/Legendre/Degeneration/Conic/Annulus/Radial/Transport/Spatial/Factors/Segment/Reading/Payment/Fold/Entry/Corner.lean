module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment.Fold.Entry
public import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

/-! # Derived factor entry at a displayed physical corner

The preceding complete segment supplies the actual terminal coordinate and
original finish Owner. Exact original Owner index transports supply the next
zero-parameter source name. The previous fold's whole terminal cache is read
once and passed unchanged to the next segment's entry comparison.
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

-- Exact affine coordinates remain original nominal owner indices in this interface.
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt

/-- The preceding actual terminal coordinate is the following segment's original zero-parameter point. -/
theorem point_eq : previousSegment.pointAt previous.subdivision.endpoint.parameter =
    segment.pointAt zeroEndpoint.parameter :=
  previous.finish_eq.trans segment.pointAt_zero.symm

/-- Both original endpoint index transports preserve the preceding actual terminal Owner's root name. -/
theorem sourceName_eq :
    ownerRootName (ownerAtStart segment previous.finishOwner).parameterNonzero
      (ownerAtStart segment previous.finishOwner) =
      ownerRootName previous.subdivision.terminalOwner.parameterNonzero previous.subdivision.terminalOwner := by
  calc
    _ = ownerRootName previous.finishOwner.parameterNonzero previous.finishOwner := by
      unfold ownerAtStart
      exact SquareRootTrackEquivalence.ownerRootName_castOwnerParameter _ _
    _ = _ := by
      unfold CompleteSegment.finishOwner CompleteSegment.terminalOwner
      exact SquareRootTrackEquivalence.ownerRootName_castOwnerParameter _ _

/-- The retained preceding terminal comparison derives the next source agreement without changing its factor channel. -/
def sourceAgreement (terminal : Terminal (completed := previousCompleted) previous.subdivision) :
    NamedEquivalent terminal.1.values.value.name
      (ownerRootName (ownerAtStart segment previous.finishOwner).parameterNonzero
        (ownerAtStart segment previous.finishOwner)) :=
  NamedEquivalent.transport rfl (sourceName_eq (segment := segment) previous).symm terminal.2.2.symm

variable (next : CompleteSegment segment within previous.finishOwner)
variable (trace : PreparedTraceBudget segment zeroEndpoint oneEndpoint)
variable (fits : TraceFits trace next.subdivision) (widths : Widths (anchor := anchor) next.subdivision)

/-- Enter the next actual subdivision with the preceding terminal Reading and complete Samples unchanged.

The physical-point equation and source-name transport are derived from the
same original complete segments. The next subdivision's actual request-fit
and width certificates pay its advances. No additional Source attachment,
preceding endpoint query or desired final equivalence is acquired.
-/
def fromTerminal (terminal : Terminal (completed := previousCompleted) previous.subdivision) :
    Entry.Cache (completed := completed) terminal.1 terminal.2.1 trace next.subdivision
      (point_eq (segment := segment) previous) (sourceAgreement (segment := segment) previous terminal) fits widths :=
  Entry.Cache.build (completed := completed) terminal.1 terminal.2.1 trace next.subdivision
    (point_eq (segment := segment) previous) (sourceAgreement (segment := segment) previous terminal) fits widths

variable {previousTrace : PreparedTraceBudget previousSegment zeroEndpoint oneEndpoint}
variable {first : Reading previousCompleted zeroEndpoint.parameter zeroEndpoint.inside}
variable {samples : RequestedSamples (anchor := anchor) first}
variable {agreement : SourceAgreement (current := zeroEndpoint)
  (owner := ownerAtStart previousSegment previousOwner) first}
variable {previousFits : TraceFits previousTrace previous.subdivision}
variable {previousWidths : Widths (anchor := anchor) previous.subdivision}
variable (previousCache : Fold.Cache (completed := previousCompleted) previousTrace previous.subdivision
  first samples agreement previousFits previousWidths)

/-- A complete corner result retains the original preceding terminal getter and next-segment entry cache. -/
@[expose] def Result :=
  Σ terminal : { retained : Terminal (completed := previousCompleted) previous.subdivision //
      retained = Fold.Cache.terminal (completed := previousCompleted) previousTrace previousCache },
    Entry.Cache (completed := completed) terminal.val.1 terminal.val.2.1 trace next.subdivision
      (point_eq (segment := segment) previous) (sourceAgreement (segment := segment) previous terminal.val) fits widths

/-- Read the preceding terminal cache once and construct the next entry on those exact retained inputs. -/
def build : Result (completed := completed) previous next trace fits widths previousCache :=
  let terminal := Fold.Cache.terminal (completed := previousCompleted) previousTrace previousCache
  let following := fromTerminal (completed := completed) previous next trace fits widths terminal
  ⟨⟨terminal, rfl⟩, following⟩

namespace Result

variable {previous : CompleteSegment previousSegment previousWithin previousOwner}
variable {next : CompleteSegment segment within previous.finishOwner}
variable {trace : PreparedTraceBudget segment zeroEndpoint oneEndpoint}
variable {fits : TraceFits trace next.subdivision} {widths : Widths (anchor := anchor) next.subdivision}
variable {previousFits : TraceFits previousTrace previous.subdivision}
variable {previousWidths : Widths (anchor := anchor) previous.subdivision}
variable {previousCache : Fold.Cache (completed := previousCompleted) previousTrace previous.subdivision
  first samples agreement previousFits previousWidths}
variable (result : Result (completed := completed) previous next trace fits widths previousCache)

/-- Read the identical original terminal Reading, Samples and derived previous endpoint comparison. -/
@[expose] def previousTerminal := result.1.val

/-- The retained preceding terminal is the original getter on the same complete previous fold. -/
theorem previousTerminal_eq : result.previousTerminal =
    Fold.Cache.terminal (completed := previousCompleted) previousTrace previousCache :=
  result.1.property

/-- Read the whole next-segment comparison cache, retaining its unchanged preceding terminal inputs. -/
@[expose] def following := result.2

/-- Read the actual output, including its original preceding origin when the next subdivision stops immediately. -/
@[expose] def output := Entry.Cache.output (completed := completed)
  result.previousTerminal.1 result.previousTerminal.2.1 trace
  (subdivision := next.subdivision) (point_eq := point_eq (segment := segment) previous)
  (agreement := sourceAgreement (segment := segment) previous result.previousTerminal)
  (fits := fits) (widths := widths) result.following

end Result

end Reading.Payment.Fold.Entry.Corner

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment
