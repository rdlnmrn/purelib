module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Route.Acquisition.Comparison.Endpoint
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Route.Acquisition.Comparison.Initial
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Approximation.Gaussian.Division.Prepared.Basic

/-! # Actual paid-route handoff at one retained original-quarter query

The preceding paid Endpoint supplies its actual finishing Owner's comparison
with the same original target Reading used as the next source. The complete
query-factory certificate remains retained. New physical factor entry uses
that derived comparison and the exact stored previous finishOwner, without
another Source attachment or a new quarter query. Existing earlier Samples
stay in their original cache; the next Anchor's factor observations belong
to their own original factor processes.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors

namespace Route.Acquisition.Comparison.Handoff

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint)

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {first : Fraction.Rational} {firstInside : FixedRootBoxPath.Inside first}
variable {source : Transport.Reading actual first firstInside} {anchor : Parameter.Anchor source.lift}
variable {current : Endpoint}
variable (nextSource : { reading : Parallel.ReadingAt actual current // Parallel.QueryCache actual current reading })
variable {previousPayment : (current.parameter - first) ^ 2 ≤
  Approximation.Rational.Geometric.Basic.quarterRadius 1 7}
variable {previousGeometry : Parallel.Geometry source nextSource.val anchor.regular previousPayment}
variable {previousBudgets : Budgets anchor} {previousFactors : Route previousBudgets previousGeometry}
variable {prepared : Division.Prepared source.lift.value}
variable {attachment : Spatial.Source source prepared}
variable {previousPaid : Route.Acquisition previousFactors attachment.attached.owner}
variable {previousResult : Comparison.Result attachment previousPaid}
variable (previousEndpoint : Comparison.Result.Endpoint attachment previousResult)

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- The retained endpoint comparison derives the next source relation on the exact previous paid finish Owner.

The original endpoint target and next source are the identical complete
Reading value nextSource.val. The whole retained query identity authenticates
that value's factory; no equality between independent root Owners is assumed.
-/
def sourceAgreement : NamedEquivalent nextSource.val.lift.value.name
    (ownerRootName previousPaid.finishOwner.parameterNonzero previousPaid.finishOwner) :=
  previousEndpoint.finish.symm

/-- The new source is the identical completed original-quarter query retained at the common chart node. -/
theorem source_eq : nextSource.val = Reading.build actual current.parameter current.inside :=
  Parallel.QueryCache.readback nextSource.property

/-- The source comparison retains its actual preceding Endpoint factory rather than a requested final relation. -/
@[irreducible, expose] def AgreementCache
    (retained : NamedEquivalent nextSource.val.lift.value.name
      (ownerRootName previousPaid.finishOwner.parameterNonzero previousPaid.finishOwner)) : Prop :=
  retained = sourceAgreement (previousPaid := previousPaid) nextSource previousEndpoint

variable {last : Fraction.Rational} {lastInside : FixedRootBoxPath.Inside last}
variable {targetReading : Transport.Reading actual last lastInside}
variable {nextAnchor : Parameter.Anchor nextSource.val.lift}
variable {nextPayment : (last - current.parameter) ^ 2 ≤
  Approximation.Rational.Geometric.Basic.quarterRadius 1 7}
variable {nextGeometry : Parallel.Geometry nextSource.val targetReading nextAnchor.regular nextPayment}
variable {nextBudgets : Budgets nextAnchor}
variable (nextFactors : Route nextBudgets nextGeometry)

/-- The new paid covered execution is the actual acquisition on the unchanged route and exact previous finishOwner. -/
@[irreducible, expose] def PaidCache
    (retained : Route.Acquisition nextFactors previousPaid.finishOwner) : Prop :=
  retained = Route.Acquisition.build nextFactors previousPaid.finishOwner

/-- The new complete comparison uses the same actual source witness and paid execution without re-attaching a root. -/
@[irreducible, expose] def ComparisonCache
    (agreement : NamedEquivalent nextSource.val.lift.value.name
      (ownerRootName previousPaid.finishOwner.parameterNonzero previousPaid.finishOwner))
    (paid : Route.Acquisition nextFactors previousPaid.finishOwner)
    (compared : Initial.Result (geometry := nextGeometry) (factors := nextFactors)
      (Initial.ofOwner (source := nextSource.val) previousPaid.finishOwner agreement) paid) : Prop :=
  compared = Initial.Result.build (geometry := nextGeometry) (factors := nextFactors)
    (Initial.ofOwner (source := nextSource.val) previousPaid.finishOwner agreement) paid

/-- Complete same-quarter Anchor handoff on the actual stored preceding Owner and original shared Reading cache.

The retained source witness is computed from the preceding Endpoint. One
new paid acquisition and one supplied-owner comparison are stored with their
whole factories. The original previous Result and all its observations
remain unchanged indices. This realizes a new paid continuation, without
identifying any older unpaid execution or crossing a quarter seam.
-/
@[expose] def Result :=
  Σ agreement : { retained : NamedEquivalent nextSource.val.lift.value.name
        (ownerRootName previousPaid.finishOwner.parameterNonzero previousPaid.finishOwner) //
      AgreementCache (previousPaid := previousPaid) nextSource previousEndpoint retained },
    Σ paid : { retained : Route.Acquisition nextFactors previousPaid.finishOwner //
        PaidCache (previousPaid := previousPaid) nextSource nextFactors retained },
      { compared : Initial.Result (geometry := nextGeometry) (factors := nextFactors)
          (Initial.ofOwner (source := nextSource.val) previousPaid.finishOwner agreement.val) paid.val //
        ComparisonCache (previousPaid := previousPaid) nextSource nextFactors agreement.val paid.val compared }

namespace Result

/-- Retain the completed derived source relation, paid execution and comparison without replaying their factories. -/
@[expose] def ofCompleted
    (agreement : NamedEquivalent nextSource.val.lift.value.name
      (ownerRootName previousPaid.finishOwner.parameterNonzero previousPaid.finishOwner))
    (agreement_eq : AgreementCache (previousPaid := previousPaid) nextSource previousEndpoint agreement)
    (paid : Route.Acquisition nextFactors previousPaid.finishOwner)
    (paid_eq : PaidCache (previousPaid := previousPaid) nextSource nextFactors paid)
    (compared : Initial.Result (geometry := nextGeometry) (factors := nextFactors)
      (Initial.ofOwner (source := nextSource.val) previousPaid.finishOwner agreement) paid)
    (compared_eq : ComparisonCache (previousPaid := previousPaid) nextSource nextFactors agreement paid compared) :
    Result nextSource previousEndpoint nextFactors :=
  ⟨⟨agreement, agreement_eq⟩, ⟨⟨paid, paid_eq⟩, ⟨compared, compared_eq⟩⟩⟩

/-- Derive source agreement and compare one new route acquired on the actual previous finishOwner. -/
def build : Result nextSource previousEndpoint nextFactors :=
  let agreement := Handoff.sourceAgreement (previousPaid := previousPaid) nextSource previousEndpoint
  let paid := Route.Acquisition.build nextFactors previousPaid.finishOwner
  let compared := Initial.Result.build (geometry := nextGeometry) (factors := nextFactors)
    (Initial.ofOwner (source := nextSource.val) previousPaid.finishOwner agreement) paid
  ofCompleted nextSource previousEndpoint nextFactors agreement (by unfold AgreementCache; rfl)
    paid (by unfold PaidCache; rfl) compared (by unfold ComparisonCache; rfl)

variable {nextSource previousEndpoint nextFactors}
variable (result : Handoff.Result nextSource previousEndpoint nextFactors)

/-- Read the exact retained operational source relation derived from the unchanged preceding Endpoint. -/
@[expose] def sourceAgreement := result.1.val

/-- Read the complete new paid acquisition whose nominal source is the actual previous finishOwner. -/
@[expose] def paid : Route.Acquisition nextFactors previousPaid.finishOwner := result.2.1.val

/-- Read the supplied-owner compatibility view on that identical original source and retained comparison. -/
@[expose] def initial : Initial nextSource.val :=
  Initial.ofOwner (source := nextSource.val) previousPaid.finishOwner result.sourceAgreement

/-- Read the complete actual paid comparison, including its unchanged entry and corner Samples and schedules. -/
@[expose] def comparison : Initial.Result (geometry := nextGeometry) (factors := nextFactors)
    result.initial result.paid := result.2.2.val

/-- The next source comparison is precisely the symmetry of the same retained preceding endpoint relation. -/
theorem sourceAgreement_eq : result.sourceAgreement = previousEndpoint.finish.symm := by
  have retained := result.1.property
  unfold AgreementCache at retained
  exact retained

/-- The newly acquired route stores the exact actual previous finishOwner as its nominal source without replacement. -/
theorem sourceOwner_eq : result.paid.startOwner = previousPaid.finishOwner := rfl

/-- The whole next paid execution is the acquisition factory on the unchanged supplied factors and previous Owner. -/
theorem paid_eq : result.paid = Route.Acquisition.build nextFactors previousPaid.finishOwner := by
  have retained := result.2.1.property
  unfold PaidCache at retained
  exact retained

/-- The whole new comparison is the supplied-owner factory on the identical stored witness and acquisition. -/
theorem comparison_eq : result.comparison = Initial.Result.build result.initial result.paid := by
  have retained := result.2.2.property
  unfold ComparisonCache at retained
  exact retained

/-- Read the actual full-product physical channel retained by this particular new paid route. -/
@[expose] def channel := result.comparison.channel

/-- The same stored new paid finishOwner agrees with the unchanged original physical output channel. -/
def equivalent : NamedEquivalent (ownerRootName result.paid.finishOwner.parameterNonzero result.paid.finishOwner)
    result.channel.name := result.comparison.equivalent

end Result

end Route.Acquisition.Comparison.Handoff

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors
