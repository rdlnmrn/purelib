module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment.Fold
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Entry
public import Purelib.RootIsolation.SquareRoot.Preparation.Terminal.Width.Acquisition
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.RootIsolation.SquareRoot.Owner.Transport

/-! # Initial attachment and paid actual full-cubic subdivision agreement

The existing original source attachment derives initial agreement. One
physical factor Reading/Samples pair is cached at entry. The new width-paid
acquisition supplies the original request-fit/width proofs internally, and
the retained actual-subdivision fold derives agreement with its exact stored
finish Owner. A fresh constructor computes its complete budget/acquisition
once, leaving old executions and independent target owners distinct.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment

namespace Reading.Payment.Fold.Acquisition

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.PreparedClearPathModels (zeroEndpoint ownerAtStart CompleteSegment)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (PrimitiveTraceBudget)
open Purelib.RootIsolation.SquareRoot.Preparation.Terminal.AcquiredDyadic (WidthAcquisition)

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {reference : Fraction.Rational} {referenceInside : FixedRootBoxPath.Inside reference}
variable {source : Transport.Reading actual reference referenceInside} {anchor : Parameter.Anchor source.lift}
variable {budgets : Budgets anchor} {finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor)
  (Spatial.coordinate site parameter 2 quarter positive reference) finish}
variable {within : segment.WithinAmbient} {completed : Segment budgets segment within}
variable {prepared : Division.Prepared source.lift.value} (attachment : Spatial.Source source prepared)
variable {budget : PrimitiveTraceBudget segment}
variable (paid : WidthAcquisition (within := within) (owner := attachment.attached.owner) budget
  (widthRequest anchor segment))

/-- The internally paid acquisition's exact original subdivision inherits its original trace fit. -/
theorem fits : TraceFits budget.trace paid.acquired.prepared.subdivision := by
  unfold TraceFits
  rewrite [← paid.acquired.requests_eq]
  exact paid.requestsFit

/-- The same actual subdivision inherits its internally derived physical-width certificate. -/
theorem widths : Widths (anchor := anchor) paid.acquired.prepared.subdivision := by
  unfold Widths
  rewrite [← paid.acquired.requests_eq]
  exact paid.widthsFit

/-- The entry query uses the same completed physical factor preparation and original parameter-zero endpoint. -/
@[expose] def FirstReading := Reading completed zeroEndpoint.parameter zeroEndpoint.inside

/-- The original complete entry Reading is the retained physical preparation's exact zero-parameter query. -/
@[irreducible, expose] def FirstCache (first : FirstReading (completed := completed)) : Prop :=
  first = Reading.build completed zeroEndpoint.parameter zeroEndpoint.inside

/-- The complete entry factor Samples retain the original request factory on the same actual cached Reading. -/
@[irreducible, expose] def SamplesCache (first : FirstReading (completed := completed))
    (samples : RequestedSamples (anchor := anchor) first) : Prop := samples = RequestedSamples.build first

namespace Initial

-- These exact coordinates and root names are nominal indices of the retained caches.
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

variable (suppliedOwner : Owner ((Paths.polynomial parameter).eval
  (Spatial.coordinate site parameter 2 quarter positive reference)))
/-- The original entry-comparison factory indexed by the exact supplied Owner and complete first Reading.

Keeping the factory, rather than evaluating its result before entry, lets
the shared constructor retain the original query, Samples and comparison
execution order. Its outputs are Type-valued operational source relations.
-/
@[expose] def AgreementFactory :=
  (first : FirstReading (completed := completed)) → SourceAgreement (current := zeroEndpoint)
    (owner := ownerAtStart segment suppliedOwner) first

/-- Compose the original factor-source relation with the retained source-Lift comparison at the actual first query. -/
def ownerAgreement
    (equivalent : NamedEquivalent source.lift.value.name (ownerRootName suppliedOwner.parameterNonzero suppliedOwner)) :
    AgreementFactory (completed := completed) suppliedOwner :=
  fun first => first.agrees_owner suppliedOwner equivalent

variable (suppliedAgreement : AgreementFactory (completed := completed) suppliedOwner)
variable (suppliedPaid : WidthAcquisition (within := within) (owner := suppliedOwner) budget
  (widthRequest anchor segment))

/-- The actual supplied-owner acquisition pays the original trace requests on its unchanged subdivision. -/
theorem fits : TraceFits budget.trace suppliedPaid.acquired.prepared.subdivision := by
  unfold TraceFits
  rewrite [← suppliedPaid.acquired.requests_eq]
  exact suppliedPaid.requestsFit

/-- The same acquisition's retained request spine pays the physical factor widths without a second preparation. -/
theorem widths : Widths (anchor := anchor) suppliedPaid.acquired.prepared.subdivision := by
  unfold Widths
  rewrite [← suppliedPaid.acquired.requests_eq]
  exact suppliedPaid.widthsFit

/-- The supplied-owner entry comparison is the original factor-source composition on the same cached Reading. -/
@[irreducible, expose] def AgreementCache (first : FirstReading (completed := completed))
    (agreement : SourceAgreement (current := zeroEndpoint)
      (owner := ownerAtStart segment suppliedOwner) first) : Prop :=
  agreement = suppliedAgreement first

/-- The entry fold retains the exact original supplied-owner subdivision, requests, Samples and source comparison. -/
@[irreducible, expose] def FoldCache (first : FirstReading (completed := completed))
    (samples : RequestedSamples (anchor := anchor) first)
    (agreement : SourceAgreement (current := zeroEndpoint)
      (owner := ownerAtStart segment suppliedOwner) first)
    (fold : Cache budget.trace suppliedPaid.acquired.prepared.subdivision first samples agreement
      (fits suppliedOwner suppliedPaid) (widths suppliedOwner suppliedPaid)) : Prop :=
  fold = Cache.build budget.trace suppliedPaid.acquired.prepared.subdivision first samples agreement
    (fits suppliedOwner suppliedPaid) (widths suppliedOwner suppliedPaid)

/-- Complete initial factor caches for a supplied original Owner and its retained source-Lift comparison.

The initial Reading and Samples use the original factories once. Their
source-comparison factory is evaluated next, retaining its Type-valued
output unchanged in the actual subdivision fold. Both the original
attachment entry and supplied-owner composition use this same cache.
-/
@[expose] def Result :=
  Σ first : { reading : FirstReading (completed := completed) // FirstCache reading },
    Σ samples : { retained : RequestedSamples (anchor := anchor) first.val // SamplesCache first.val retained },
      Σ agreement : { retained : SourceAgreement (current := zeroEndpoint)
          (owner := ownerAtStart segment suppliedOwner) first.val //
          AgreementCache suppliedOwner suppliedAgreement first.val retained },
        { retained : Cache budget.trace suppliedPaid.acquired.prepared.subdivision first.val samples.val agreement.val
            (fits suppliedOwner suppliedPaid) (widths suppliedOwner suppliedPaid) //
          FoldCache suppliedOwner suppliedPaid first.val samples.val agreement.val retained }

namespace Result

/-- Retain the already completed original entry query, Samples, derived source witness and whole actual fold. -/
@[expose] def ofCompleted
    (first : FirstReading (completed := completed)) (first_eq : FirstCache first)
    (samples : RequestedSamples (anchor := anchor) first) (samples_eq : SamplesCache first samples)
    (agreement : SourceAgreement (current := zeroEndpoint)
      (owner := ownerAtStart segment suppliedOwner) first)
    (agreement_eq : AgreementCache suppliedOwner suppliedAgreement first agreement)
    (fold : Cache budget.trace suppliedPaid.acquired.prepared.subdivision first samples agreement
      (fits suppliedOwner suppliedPaid) (widths suppliedOwner suppliedPaid))
    (fold_eq : FoldCache suppliedOwner suppliedPaid first samples agreement fold) :
    Result (completed := completed) suppliedOwner suppliedAgreement suppliedPaid :=
  ⟨⟨first, first_eq⟩, ⟨⟨samples, samples_eq⟩, ⟨⟨agreement, agreement_eq⟩, ⟨fold, fold_eq⟩⟩⟩⟩

/-- Construct the original initial query, Samples, source composition and actual fold once, in that order. -/
def build : Result (completed := completed) suppliedOwner suppliedAgreement suppliedPaid :=
  let first := Reading.build completed zeroEndpoint.parameter zeroEndpoint.inside
  let samples := RequestedSamples.build first
  let agreement := suppliedAgreement first
  let fold := Cache.build budget.trace suppliedPaid.acquired.prepared.subdivision first samples agreement
    (fits suppliedOwner suppliedPaid) (widths suppliedOwner suppliedPaid)
  ofCompleted suppliedOwner suppliedAgreement suppliedPaid first (by unfold FirstCache; rfl)
    samples (by unfold SamplesCache; rfl) agreement (by unfold AgreementCache; rfl)
    fold (by unfold FoldCache; rfl)

/-- Construct supplied-owner entry from the actual retained source-Lift comparison without another Source attachment. -/
def ofOwner
    (equivalent : NamedEquivalent source.lift.value.name (ownerRootName suppliedOwner.parameterNonzero suppliedOwner)) :
    Result (completed := completed) suppliedOwner (ownerAgreement suppliedOwner equivalent) suppliedPaid :=
  build suppliedOwner (ownerAgreement suppliedOwner equivalent) suppliedPaid

variable {suppliedOwner : Owner ((Paths.polynomial parameter).eval
  (Spatial.coordinate site parameter 2 quarter positive reference))}
variable {suppliedAgreement : AgreementFactory (completed := completed) suppliedOwner}
variable {suppliedPaid : WidthAcquisition (within := within) (owner := suppliedOwner) budget
  (widthRequest anchor segment)}
variable (result : Result (completed := completed) suppliedOwner suppliedAgreement suppliedPaid)

/-- Read the identical complete original physical factor Reading cached at the supplied-owner entry. -/
@[expose] def first := result.1.val

/-- Read the exact original entry Samples consumed by the same actual comparison fold. -/
@[expose] def samples : RequestedSamples (anchor := anchor) result.first := result.2.1.val

/-- Read the original source composition, including its retained executable comparison schedules. -/
@[expose] def agreement := result.2.2.1.val

/-- Read the complete original actual-subdivision fold on the same retained entry observations and source witness. -/
@[expose] def fold := result.2.2.2.val

/-- The cached whole initial Reading is the original query factory on this unchanged factor preparation. -/
theorem first_eq : result.first = Reading.build completed zeroEndpoint.parameter zeroEndpoint.inside := by
  have retained := result.1.property
  unfold FirstCache at retained
  exact retained

/-- The stored source comparison is the original composition with the supplied Owner and source-Lift relation. -/
theorem agreement_eq : result.agreement = suppliedAgreement result.first := by
  have retained := result.2.2.1.property
  unfold AgreementCache at retained
  exact retained

/-- The original actual fold factory consumes the identical cached Reading, Samples and Type-valued source witness. -/
theorem fold_eq : result.fold = Cache.build budget.trace suppliedPaid.acquired.prepared.subdivision
    result.first result.samples result.agreement (fits suppliedOwner suppliedPaid)
      (widths suppliedOwner suppliedPaid) := by
  have retained := result.2.2.2.property
  unfold FoldCache at retained
  exact retained

end Result
end Initial

/-- Initial factor agreement is derived from the same original supplied Source attachment. -/
@[irreducible, expose] def AgreementCache (first : FirstReading (completed := completed))
    (agreement : SourceAgreement (owner := ownerAtStart segment attachment.attached.owner) first) : Prop :=
  agreement = first.agrees_initial attachment

/-- The complete comparison fold belongs to the same actual subdivision, entry caches and paid geometry. -/
@[irreducible, expose] def FoldCache (first : FirstReading (completed := completed))
    (samples : RequestedSamples (anchor := anchor) first)
    (agreement : SourceAgreement (owner := ownerAtStart segment attachment.attached.owner) first)
    (fold : Cache budget.trace paid.acquired.prepared.subdivision first samples agreement
      (fits attachment paid) (widths attachment paid)) : Prop :=
  fold = Cache.build budget.trace paid.acquired.prepared.subdivision first samples agreement
    (fits attachment paid) (widths attachment paid)

/-- Completed original entry query/Samples, derived initial relation and exact actual-subdivision comparison fold.

The supplied Source attachment, physical factor preparation and complete
paid acquisition remain original indices. The stored fold consumes their
actual original subdivision and exact request/cached-advance data. Every
factory equation concerns the same complete cached inputs.
-/
@[expose] def Result :=
  Σ first : { reading : FirstReading (completed := completed) // FirstCache reading },
    Σ samples : { retained : RequestedSamples (anchor := anchor) first.val // SamplesCache first.val retained },
      Σ agreement : { retained : SourceAgreement (owner := ownerAtStart segment attachment.attached.owner) first.val //
          AgreementCache attachment first.val retained },
        { retained : Cache budget.trace paid.acquired.prepared.subdivision first.val samples.val agreement.val
            (fits attachment paid) (widths attachment paid) //
          FoldCache attachment paid first.val samples.val agreement.val retained }

namespace Result

/-- Retain complete entry, initial-agreement and actual-fold caches without querying or comparing them again. -/
@[expose] def ofCompleted
    (first : FirstReading (completed := completed)) (first_eq : FirstCache first)
    (samples : RequestedSamples (anchor := anchor) first) (samples_eq : SamplesCache first samples)
    (agreement : SourceAgreement (owner := ownerAtStart segment attachment.attached.owner) first)
    (agreement_eq : AgreementCache attachment first agreement)
    (fold : Cache budget.trace paid.acquired.prepared.subdivision first samples agreement
      (fits attachment paid) (widths attachment paid))
    (fold_eq : FoldCache attachment paid first samples agreement fold) :
    Result (completed := completed) attachment paid :=
  ⟨⟨first, first_eq⟩, ⟨⟨samples, samples_eq⟩, ⟨⟨agreement, agreement_eq⟩, ⟨fold, fold_eq⟩⟩⟩⟩

/-- Retain the complete shared initial construction in the original attachment Result without replaying a factory.

The original public Sigma type and its attachment-specific cache statements
remain unchanged. Each runtime Reading, Samples, Type-valued comparison and
fold is the exact completed input projection; only their retained proof
certificates are transported to the existing attachment statements.
-/
def ofInitial
    (retained : Initial.Result (completed := completed) attachment.attached.owner
      (fun first => first.agrees_initial attachment) paid) :
    Result (completed := completed) attachment paid :=
  ofCompleted attachment paid retained.first retained.1.property retained.samples retained.2.1.property
    retained.agreement
    (by
      unfold AgreementCache
      exact retained.agreement_eq)
    retained.fold (by unfold FoldCache; exact retained.fold_eq)

/-- Derive the attachment entry through the shared supplied-owner constructor in the original factory order. -/
def build : Result (completed := completed) attachment paid :=
  let retained := Initial.Result.build (completed := completed)
    attachment.attached.owner (fun first => first.agrees_initial attachment) paid
  ofInitial attachment paid retained

variable {attachment : Spatial.Source source prepared}
variable {paid : WidthAcquisition (within := within) (owner := attachment.attached.owner) budget
  (widthRequest anchor segment)}

/-- Read the original complete physical factor query cached at entry. -/
@[expose] def first (result : Result (completed := completed) attachment paid) := result.1.val

/-- Read the original complete entry Samples retained by the first actual advance comparison. -/
@[expose] def samples (result : Result (completed := completed) attachment paid) :
    RequestedSamples (anchor := anchor) result.first :=
  result.2.1.val

/-- Read the original initial factor-to-attached-owner comparison derived from the supplied Source. -/
@[expose] def agreement (result : Result (completed := completed) attachment paid) := result.2.2.1.val

/-- Read the entire retained actual-subdivision factor-comparison spine. -/
@[expose] def fold (result : Result (completed := completed) attachment paid) := result.2.2.2.val

/-- Specializing the shared initial construction preserves its identical complete initial Reading cache. -/
theorem ofInitial_first
    (retained : Initial.Result (completed := completed) attachment.attached.owner
      (fun first => first.agrees_initial attachment) paid) :
    (ofInitial attachment paid retained).first = retained.first := by
  rfl

/-- Specializing the shared initial construction preserves the exact original entry Samples. -/
theorem ofInitial_samples
    (retained : Initial.Result (completed := completed) attachment.attached.owner
      (fun first => first.agrees_initial attachment) paid) :
    HEq (ofInitial attachment paid retained).samples retained.samples := by
  rfl

/-- Specializing the shared initial construction preserves its complete Type-valued source comparison witness. -/
theorem ofInitial_agreement
    (retained : Initial.Result (completed := completed) attachment.attached.owner
      (fun first => first.agrees_initial attachment) paid) :
    HEq (ofInitial attachment paid retained).agreement retained.agreement := by
  rfl

/-- Specializing the shared initial construction preserves the exact whole actual-subdivision comparison fold. -/
theorem ofInitial_fold
    (retained : Initial.Result (completed := completed) attachment.attached.owner
      (fun first => first.agrees_initial attachment) paid) :
    HEq (ofInitial attachment paid retained).fold retained.fold := by
  rfl

/-- The retained complete entry Reading is the original once-computed query on the same preparation. -/
theorem first_eq (result : Result (completed := completed) attachment paid) :
    result.first = Reading.build completed zeroEndpoint.parameter zeroEndpoint.inside := by
  have cache := result.1.property
  unfold FirstCache at cache
  exact cache

/-- The initial comparison is the same original attachment comparison on that exact cached entry Reading. -/
theorem agreement_eq (result : Result (completed := completed) attachment paid) :
    result.agreement = result.first.agrees_initial attachment := by
  have cache := result.2.2.1.property
  unfold AgreementCache at cache
  exact cache

/-- The stored finishing Owner retains the same original terminal root name through endpoint index transport. -/
theorem finishName_eq : ownerRootName paid.acquired.finishOwner.parameterNonzero paid.acquired.finishOwner =
    ownerRootName paid.acquired.prepared.subdivision.terminalOwner.parameterNonzero
      paid.acquired.prepared.subdivision.terminalOwner := by
  rewrite [paid.acquired.finishOwner_eq]
  unfold CompleteSegment.finishOwner
  exact SquareRootTrackEquivalence.ownerRootName_castOwnerParameter _ _

/-- The actual cached full-cubic finishing Owner agrees with the unchanged final physical factor channel.

The original acquisition retains its finish Owner and exact finish equation.
The actual subdivision fold derives the terminal comparison; original exact
Owner index transport connects it to that same stored finish cache. Neither
an independent target Owner nor the desired final equivalence is supplied.
-/
def finishEquivalent (result : Result (completed := completed) attachment paid) :
    NamedEquivalent (ownerRootName paid.acquired.finishOwner.parameterNonzero paid.acquired.finishOwner)
      (Cache.last budget.trace result.fold).values.value.name :=
  NamedEquivalent.transport (finishName_eq (attachment := attachment) (paid := paid)).symm rfl
    (Cache.equivalent budget.trace result.fold)

end Result

/-- The complete original automatic width-paid preparation type on the unchanged physical segment and attached Owner. -/
@[expose] def Preparation :=
  Σ budget : { retained : PrimitiveTraceBudget segment // retained = PrimitiveTraceBudget.build segment },
    WidthAcquisition (within := within) (owner := attachment.attached.owner) budget.val (widthRequest anchor segment)

/-- A preparation retains the automatic admitted-input acquisition on the same Source and physical width. -/
@[irreducible, expose] def PreparationCache
    (retained : Preparation (segment := segment) (within := within) attachment) : Prop :=
  retained = WidthAcquisition.prepare segment within attachment.attached.owner (widthRequest anchor segment)

/-- Construct a new paid acquisition and its entire physical factor fold, retaining both complete factory results.

The existing Source attachment and original factor preparations are supplied
complete inputs. All sufficient finite depths and initial/source/terminal
comparisons are computed internally. The new execution remains distinct from
any old preparation and from any independent original target reading.
-/
def prepare :
    Σ retained : { value : Preparation (segment := segment) (within := within) attachment //
        PreparationCache attachment value },
      Result (completed := completed) (budget := retained.val.1.val) attachment retained.val.2 :=
  let retained := WidthAcquisition.prepare segment within attachment.attached.owner (widthRequest anchor segment)
  let result := Result.build (completed := completed) attachment retained.2
  ⟨⟨retained, by unfold PreparationCache; rfl⟩, result⟩

end Reading.Payment.Fold.Acquisition

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment
