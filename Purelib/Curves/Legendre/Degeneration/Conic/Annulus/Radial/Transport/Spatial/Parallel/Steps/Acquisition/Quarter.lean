module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Approximation.Gaussian.Division.Prepared.Basic

/-! # One actual paid quarter on its identical retained original step chain

The original Quarter supplies the exact cached depth-seven target list and
complete Steps value. One new paid realization is built on those identical
query and Geometry caches. Its full factory, actual finishOwner, original
last Reading and covered-block trace remain retained; the certified final
endpoint is transported only by its original exact list identity. This is
one quarter, without a distinct-quarter seam or a closed-cycle assertion.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint finalTarget)
open Purelib.Riemann.Meshes

variable {site : Fin 2} {parameter : Canonical} {unitQuarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 unitQuarter positive}
variable {regular : parameter ≠ criticalValue site}
variable {current : Endpoint} {reading : ReadingAt actual current}
variable {originalOwner : OwnerAt site parameter unitQuarter positive current}
variable (original : Steps.Quarter actual regular current reading originalOwner)
variable (sourceOwner : OwnerAt site parameter unitQuarter positive current)
variable (agreement : InitialAgreement current reading sourceOwner)

section Retained

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- One whole new paid-quarter realization and its exact factory on the unchanged original Quarter's cached Steps.

The existing target list and original query/Geometry caches remain indices.
Every paid block, its observations, actual source/finish Owners and endpoint
comparisons are retained by the new realization. No old covered execution
is relabelled, and no target query or Source attachment is repeated.
-/
@[expose] def Quarter :=
  Σ retained : { cache : Steps.Quarter actual regular current reading originalOwner // cache = original },
    { paid : Acquisition retained.val.steps sourceOwner agreement //
      paid = Acquisition.build retained.val.steps sourceOwner agreement }

namespace Quarter

/-- Retain an already completed actual paid-quarter realization with its whole original factory identity. -/
@[expose] def ofCompleted (paid : Acquisition original.steps sourceOwner agreement)
    (paid_eq : paid = Acquisition.build original.steps sourceOwner agreement) :
    Quarter original sourceOwner agreement :=
  ⟨⟨original, rfl⟩, ⟨paid, paid_eq⟩⟩

/-- Construct the total finite paid quarter once on the identical original target, query and Geometry caches. -/
def build : Quarter original sourceOwner agreement :=
  let paid := Acquisition.build original.steps sourceOwner agreement
  ofCompleted original sourceOwner agreement paid rfl

variable {original : Steps.Quarter actual regular current reading originalOwner}
variable {sourceOwner : OwnerAt site parameter unitQuarter positive current}
variable {agreement : InitialAgreement current reading sourceOwner}
variable (quarter : Quarter original sourceOwner agreement)

/-- Read the identical whole original Quarter cache retained beside this actual new paid realization. -/
@[expose] def originalQuarter : Steps.Quarter actual regular current reading originalOwner := quarter.1.val

/-- The retained original Quarter is exactly the supplied complete target/Steps cache. -/
theorem originalQuarter_eq : quarter.originalQuarter = original := quarter.1.property

/-- Read the complete actual new paid realization on that same stored original Quarter, without replaying a factory. -/
@[expose] def receipt : Acquisition quarter.originalQuarter.steps sourceOwner agreement := quarter.2.val

/-- Retaining completed quarter data preserves the identical whole original Quarter input cache. -/
theorem ofCompleted_originalQuarter (paid : Acquisition original.steps sourceOwner agreement)
    (paid_eq : paid = Acquisition.build original.steps sourceOwner agreement) :
    (ofCompleted original sourceOwner agreement paid paid_eq).originalQuarter = original := rfl

/-- Retaining completed quarter data preserves the same entire already constructed paid realization. -/
theorem ofCompleted_receipt (paid : Acquisition original.steps sourceOwner agreement)
    (paid_eq : paid = Acquisition.build original.steps sourceOwner agreement) :
    (ofCompleted original sourceOwner agreement paid paid_eq).receipt = paid := rfl

/-- The retained whole paid realization is the exact factory on the identical stored original Steps cache. -/
theorem receipt_eq : quarter.receipt = Acquisition.build quarter.originalQuarter.steps sourceOwner agreement :=
  quarter.2.property

/-- Read the identical stored original depth-seven target cache and its opaque complete dyadic factory certificate. -/
@[expose] def targetCache : Steps.TargetCache := quarter.originalQuarter.cache

/-- Read the actual new paid finishOwner on the same retained finalTarget endpoint. -/
@[expose] def finishOwner : OwnerAt site parameter unitQuarter positive
    (finalTarget current quarter.originalQuarter.cache.val) := quarter.receipt.finishOwner

/-- Read the unchanged original final quarter Reading from the same whole stored original cache. -/
@[expose] def finishReading : ReadingAt actual (finalTarget current quarter.originalQuarter.cache.val) :=
  quarter.originalQuarter.steps.finishReading

/-- This actual new paid finishOwner agrees with the same original retained final quarter Lift. -/
def finishEquivalent : NamedEquivalent (ownerRootName quarter.finishOwner.parameterNonzero quarter.finishOwner)
    quarter.finishReading.lift.value.name := quarter.receipt.finishEquivalent

/-- The retained original target factory has exactly one hundred twenty-eight original chart targets. -/
theorem target_count : quarter.targetCache.val.length = 128 :=
  Steps.retained_target_count quarter.targetCache.targets_eq

/-- The original depth-seven retained target bank is nonempty. -/
theorem targets_nonempty : quarter.targetCache.val ≠ [] := by
  intro empty
  have wrong : (128 : Nat) = 0 := quarter.target_count.symm.trans (congrArg List.length empty)
  exact (of_decide_eq_true rfl : (128 : Nat) ≠ 0) wrong

/-- The complete new paid quarter retains exactly one actual paid Block for each of those original targets. -/
theorem block_count : quarter.receipt.blockCount = 128 :=
  quarter.receipt.blockCount_eq.trans quarter.target_count

/-- The unchanged original shared Reading sequence has its original source plus the one hundred twenty-eight targets. -/
theorem query_count : quarter.receipt.nodes.length = 129 := by
  have retained := quarter.receipt.nodes_length
  change quarter.receipt.nodes.length = quarter.targetCache.val.length + 1 at retained
  rewrite [quarter.target_count] at retained
  exact retained

/-- The actual retained target factory ends at the certified unit endpoint from the original initial endpoint. -/
theorem finalEndpoint_eq (initial : current = UniformPrimitiveMesh.firstEndpoint) :
    finalTarget current quarter.originalQuarter.cache.val = UniformPrimitiveMesh.lastEndpoint :=
  Steps.retained_finish initial quarter.targetCache.targets_eq

/-- Transport only this actual stored paid finishOwner along an exact final endpoint identity. -/
@[expose] def finishOwnerAt (endpoint : Endpoint)
    (endpoint_eq : finalTarget current quarter.originalQuarter.cache.val = endpoint) :
    OwnerAt site parameter unitQuarter positive endpoint :=
  RootIsolation.SquareRoot.Owner.Transport.castOwnerParameter
    (congrArg (fun endpoint : Endpoint => (Paths.polynomial parameter).eval
      (coordinate site parameter 2 unitQuarter positive endpoint.parameter)) endpoint_eq) quarter.finishOwner

/-- Exact final endpoint transport retains the same complete actual paid Owner, track and clearance data. -/
theorem finishOwnerAt_heq (endpoint : Endpoint)
    (endpoint_eq : finalTarget current quarter.originalQuarter.cache.val = endpoint) :
    HEq (quarter.finishOwnerAt endpoint endpoint_eq) quarter.finishOwner :=
  RootIsolation.SquareRoot.Owner.Transport.castOwnerParameter_heq _ _

/-- Exact endpoint-index transport preserves the root name of that same original actual paid finishOwner. -/
theorem finishName_eq (endpoint : Endpoint)
    (endpoint_eq : finalTarget current quarter.originalQuarter.cache.val = endpoint) :
    ownerRootName (quarter.finishOwnerAt endpoint endpoint_eq).parameterNonzero
      (quarter.finishOwnerAt endpoint endpoint_eq) =
      ownerRootName quarter.finishOwner.parameterNonzero quarter.finishOwner := by
  unfold finishOwnerAt
  exact SquareRootTrackEquivalence.ownerRootName_castOwnerParameter _ _

/-- Reindex the unchanged complete original final Reading by the same exact endpoint identity. -/
@[expose] def finishReadingAt (endpoint : Endpoint)
    (endpoint_eq : finalTarget current quarter.originalQuarter.cache.val = endpoint) :
    ReadingAt actual endpoint := quarter.originalQuarter.steps.finishReadingAt endpoint endpoint_eq

/-- Reindexing the original final Reading preserves its entire original preparation and Lift caches. -/
theorem finishReadingAt_heq (endpoint : Endpoint)
    (endpoint_eq : finalTarget current quarter.originalQuarter.cache.val = endpoint) :
    HEq (quarter.finishReadingAt endpoint endpoint_eq) quarter.finishReading :=
  quarter.originalQuarter.steps.finishReadingAt_heq endpoint endpoint_eq

/-- Derive endpoint-indexed agreement while retaining both the actual finishOwner and original final Reading caches. -/
def finishEquivalentAt (endpoint : Endpoint)
    (endpoint_eq : finalTarget current quarter.originalQuarter.cache.val = endpoint) :
    NamedEquivalent
      (ownerRootName (quarter.finishOwnerAt endpoint endpoint_eq).parameterNonzero
        (quarter.finishOwnerAt endpoint endpoint_eq))
      (quarter.finishReadingAt endpoint endpoint_eq).lift.value.name := by
  cases endpoint_eq
  exact NamedEquivalent.transport (quarter.finishName_eq _ rfl).symm rfl quarter.finishEquivalent

/-- The new paid quarter's actual stored finishOwner is certified at the original unit-quarter endpoint. -/
@[expose] def unitFinishOwner (initial : current = UniformPrimitiveMesh.firstEndpoint) :
    OwnerAt site parameter unitQuarter positive UniformPrimitiveMesh.lastEndpoint :=
  quarter.finishOwnerAt UniformPrimitiveMesh.lastEndpoint (quarter.finalEndpoint_eq initial)

/-- The actual paid unit-quarter endpoint agrees with the identical retained original final Reading at that endpoint. -/
def unitFinishEquivalent (initial : current = UniformPrimitiveMesh.firstEndpoint) :
    NamedEquivalent (ownerRootName (quarter.unitFinishOwner initial).parameterNonzero (quarter.unitFinishOwner initial))
      (quarter.finishReadingAt UniformPrimitiveMesh.lastEndpoint (quarter.finalEndpoint_eq initial)).lift.value.name :=
  quarter.finishEquivalentAt UniformPrimitiveMesh.lastEndpoint (quarter.finalEndpoint_eq initial)

end Quarter

end Retained

variable {prepared : Division.Prepared reading.lift.value}
variable (attachment : Spatial.Source reading prepared)
variable (attachedQuarter : Steps.Quarter actual regular current reading attachment.attached.owner)

/-- Realize one complete paid quarter from the existing initial Source attachment without attaching another Owner.

The already completed attachment supplies its original source comparison.
The entire original Quarter remains the query/Geometry input cache. Every
later source Owner and comparison is derived from the preceding stored paid
Endpoint by the total finite construction above.
-/
def ofSource : Quarter attachedQuarter attachment.attached.owner attachment.agrees :=
  Quarter.build attachedQuarter attachment.attached.owner attachment.agrees

end Steps.Acquisition

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
