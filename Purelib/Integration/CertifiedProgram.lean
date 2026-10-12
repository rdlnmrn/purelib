module

import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Rational.Geometric.Basic
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
public import Mathlib.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

public section

namespace Purelib.Integration.CertifiedProgram

open Purelib.Data.Rat in
/-- The rational carrier for certified integration allowances and targets. -/
abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian carrier for cached samples. -/
abbrev Gaussian := Basic.Canonical
open Purelib.Approximation.Gaussian in
/-- The exact Gaussian approximation-data carrier exposed by a certified program. -/
abbrev Approximation := Sequence.ApproximationData

set_option genInjectivity false in
/-- The sample and rational allowance readbacks for one original model type.

Both functions read the same supplied model type. Their exact results
are the sample and allowance stored by the indexed cache. -/
structure ModelOperations (Model : Type u) where
  /-- The Gaussian sample operation on an original model. -/ sample : Model → Gaussian
  /-- The rational allowance operation on an original model. -/ allowance : Model → Coordinate

constructive_injectivity ModelOperations

variable {Model : Type u} {operations : ModelOperations Model}

set_option genInjectivity false in
/-- A retained original model with cached sample and allowance and their defining readback equalities.

The retained model and its two cached readings are linked by the supplied
readback equalities. Each downstream operation consumes those same caches. -/
structure CachedModel (operations : ModelOperations Model) where
  /-- The retained original model. -/ model : Model
  /-- The retained exact Gaussian sample reading. -/ sample : Gaussian
  /-- The cached sample equals the sample operation on the original model. -/ sample_eq : sample = operations.sample
    model
  /-- The retained exact rational allowance reading. -/ allowance : Coordinate
  /-- The cached allowance equals the allowance operation on the original model. -/ allowance_eq : allowance =
    operations.allowance model

constructive_injectivity CachedModel

namespace CachedModel

/-- Compute and retain both exact operation readbacks for the supplied original model. -/
@[expose] def canonical (model : Model) : CachedModel operations :=
  { model := model
    sample := operations.sample model
    sample_eq := rfl
    allowance := operations.allowance model
    allowance_eq := rfl }

/-- Equal original models identify their complete certified caches, including both retained readbacks. -/
theorem eq_of_model_eq (first second : CachedModel operations)
    (equal : first.model = second.model) : first = second := by
  cases first with
  | mk model sample sampleEq allowance allowanceEq =>
    cases second with
    | mk otherModel otherSample otherSampleEq otherAllowance otherAllowanceEq =>
      cases equal
      cases sampleEq
      cases allowanceEq
      cases otherSampleEq
      cases otherAllowanceEq
      rfl

end CachedModel

open Purelib.Approximation.Rational in
/-- Every retained stage allowance lies below quarter-radius decay of the supplied error scale. -/
@[expose, reducible] def Allowances (stage : Nat → CachedModel operations) (errorScale : Coordinate) : Prop :=
  ∀ index, (stage index).allowance ≤ Geometric.Basic.quarterRadius errorScale index

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
/-- Every later retained sample is within the earlier stage's quarter-radius squared-distance allowance. -/
@[expose, reducible] def LaterClose (stage : Nat → CachedModel operations) (errorScale : Coordinate) : Prop :=
  ∀ {earlier later : Nat}, earlier ≤ later →
    Data.Gaussian.Norm.Basic.normSq ((stage later).sample - (stage earlier).sample) ≤ Geometric.Basic.quarterRadius
      errorScale earlier

open Purelib.Data.Gaussian in
/-- Every retained stage sample has squared norm at most the common center bound. -/
@[expose, reducible] def SampleBounds (stage : Nat → CachedModel operations) (centerBound : Coordinate) : Prop :=
  ∀ index, Data.Gaussian.Norm.Basic.normSq (stage index).sample ≤ centerBound

set_option genInjectivity false in
/-- A retained model-cache sequence with geometric allowances, later-sample comparison and uniform sample bounds.

The original stage models and both cached readbacks remain linked by their exact cache equalities; error and center
scales retain separate nonnegativity certificates. -/
structure Program (operations : ModelOperations Model) where
  /-- The original sequence of retained model caches. -/ stage : Nat → CachedModel operations
  /-- The retained scale for geometric error decay. -/ errorScale : Coordinate
  /-- The geometric error scale is nonnegative. -/ errorScale_nonneg : 0 ≤ errorScale
  /-- Each original stage allowance obeys its geometric decay bound. -/ modelAllowance_le : Allowances stage errorScale
  /-- Later original samples obey the earlier stage's geometric squared-distance bound. -/ later_close : LaterClose
    stage errorScale
  /-- The common squared-norm bound for all retained samples. -/ centerBound : Coordinate
  /-- The retained common sample bound is nonnegative. -/ centerBound_nonneg : 0 ≤ centerBound
  /-- Every original stage sample obeys the retained common bound. -/ sample_bounded : SampleBounds stage centerBound

constructive_injectivity Program

set_option genInjectivity false in
/-- A producer paired with a certified program whose original stage models equal that producer's model readbacks.

The retained producer and program remain separate owners. At every stage,
the supplied equality identifies the program model with that producer reading. -/
structure View (Producer : Type v) (operations : ModelOperations Model)
    (modelAt : Producer → Nat → Model) where
  /-- The exact retained producer. -/ producer : Producer
  /-- The certified program associated with the retained producer. -/ program : Program operations
  /-- The original program models equal the retained producer's model readbacks at each index. -/ model_eq : ∀ index,
    (program.stage index).model = modelAt producer index

constructive_injectivity View

@[expose] public section

set_option genInjectivity false in
/-- A current stage and strictly positive rational target for a certified refinement request.

The starting stage and rational target are retained together. Positivity
certifies that the same displayed target is a valid accuracy request. -/
structure Request where
  /-- The original requested starting stage. -/ current : Nat
  /-- The original rational target tolerance. -/ target : Coordinate
  /-- The requested target is strictly positive. -/ positive : 0 < target
deriving DecidableEq

constructive_injectivity Request

end

@[expose] public section

set_option genInjectivity false in
/-- The original current stage and target together with a certificate that the target is not positive.

The original stage and target are retained with a proof that positivity
fails. This record certifies that exact violated request condition. -/
structure InvalidRequest where
  /-- The original requested starting stage. -/ current : Nat
  /-- The original rational target tolerance. -/ target : Coordinate
  /-- The original requested target is not strictly positive. -/ nonpositive : ¬ 0 < target
deriving DecidableEq

constructive_injectivity InvalidRequest

end

namespace Request

/-- Return the exact positive-target request or a typed invalid request retaining the original inputs and failed
condition.

A positive target returns the same stage and target with its proof.
Otherwise the error retains both inputs and the failed positivity condition. -/
@[expose] def checked (current : Nat) (target : Coordinate) : Except InvalidRequest Request :=
  if positive : 0 < target then .ok ⟨current, target, positive⟩
  else .error ⟨current, target, positive⟩

/-- A positive target makes the checked request succeed with the exact original inputs. -/
theorem checked_of_positive (current : Nat) (target : Coordinate) (positive : 0 < target) :
    checked current target = .ok ⟨current, target, positive⟩ := by
  rw [checked, dif_pos positive]

/-- A failed request retains the original current stage and target and certifies target nonpositivity. -/
theorem checked_error {current : Nat} {target : Coordinate} {error : InvalidRequest}
    (failure : checked current target = .error error) :
    error.current = current ∧ error.target = target ∧ ¬ 0 < target := by
  unfold checked at failure
  split at failure
  · cases failure
  · rename_i nonpositive
    cases failure
    exact ⟨rfl, rfl, nonpositive⟩

end Request

namespace Program

section
open Purelib.Approximation.Rational
/-- Expose the certified cached sample sequence as Gaussian approximation data with geometric refinement search.

The original cached samples, later-close witness and center bound are reused; search starts from the supplied current
stage. -/
@[expose] def approximation (program : Program operations) : Approximation where
  sample index := (program.stage index).sample
  radiusSq := Geometric.Basic.quarterRadius program.errorScale
  radiusSq_nonneg := Geometric.Basic.quarterRadius_nonneg program.errorScale_nonneg
  later_close := program.later_close
  refineIndex current target _ := Geometric.Search.firstQuarterBelow program.errorScale current target
  refineIndex_ge current target _ := Geometric.Search.firstQuarterBelow_ge program.errorScale current target
  refineIndex_accurate := Geometric.Search.firstQuarterBelow_accurate program.errorScale program.errorScale_nonneg
  centerBound := program.centerBound
  centerBound_nonneg := program.centerBound_nonneg
  sample_bounded := program.sample_bounded

/-- Find the first sufficient quarter-radius refinement at or above the request's current stage.

The original error scale, current stage and rational target are supplied
to the same finite geometric search. Its selected stage is retained unchanged. -/
@[expose] def selectedIndex (program : Program operations) (request : Request) : Nat :=
  Geometric.Search.firstQuarterBelow program.errorScale request.current request.target

end

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
set_option genInjectivity false in
/-- The exact selected stage cache with its retained index, radius, accuracy and center-bound certificates.

The cache remains equal to the original program stage, and both radius and model allowance are below the original
requested target. -/
structure Prepared (program : Program operations) (request : Request) where
  /-- The retained stage index selected for this request. -/ index : Nat
  /-- The retained index equals this exact program's selected request index. -/ index_eq : index = program.selectedIndex
    request
  /-- The selected index is at least the original requested current stage. -/ index_ge : request.current ≤ index
  /-- The retained original model cache at the selected stage. -/ cache : CachedModel operations
  /-- The retained cache equals the exact original program stage at the selected index. -/ cache_eq : cache =
    program.stage index
  /-- The retained squared-radius allowance at the selected stage. -/ radiusSq : Coordinate
  /-- The retained radius equals quarter-radius decay at the original error scale and selected index. -/ radiusSq_eq :
    radiusSq = Geometric.Basic.quarterRadius program.errorScale index
  /-- The retained squared-radius allowance is nonnegative. -/ radiusSq_nonnegative : 0 ≤ radiusSq
  /-- The retained squared-radius allowance is below the original target. -/ radiusSq_accurate : radiusSq <
    request.target
  /-- The retained model allowance is below the original target. -/ allowance_accurate : cache.allowance <
    request.target
  /-- The retained cached sample obeys the original program's center bound. -/ center_bounded :
    Data.Gaussian.Norm.Basic.normSq cache.sample ≤ program.centerBound

constructive_injectivity Prepared

open Purelib.Approximation.Rational in
/-- Select a sufficient stage, retain that exact stage cache once and certify its radius and allowance against the
request.

The computed stage index selects one exact original cache. Its retained
radius and allowance certificates both pay the supplied positive target. -/
@[expose] def prepare (program : Program operations) (request : Request) : Prepared program request :=
  let index := program.selectedIndex request
  let cache := program.stage index
  let radius := Geometric.Basic.quarterRadius program.errorScale index
  have accurate : radius < request.target :=
    Geometric.Search.firstQuarterBelow_accurate program.errorScale program.errorScale_nonneg
      request.current request.target request.positive
  { index := index
    index_eq := rfl
    index_ge := Geometric.Search.firstQuarterBelow_ge program.errorScale request.current request.target
    cache := cache
    cache_eq := rfl
    radiusSq := radius
    radiusSq_eq := rfl
    radiusSq_nonnegative := Geometric.Basic.quarterRadius_nonneg program.errorScale_nonneg index
    radiusSq_accurate := accurate
    allowance_accurate := (program.modelAllowance_le index).trans_lt accurate
    center_bounded := program.sample_bounded index }

/-- The approximation interface's requested refinement has model allowance below the original positive target. -/
theorem requested_allowance (program : Program operations) (current : Nat)
    (target : Coordinate) (positive : 0 < target) :
    (program.stage (program.approximation.refineIndex current target positive)).allowance < target :=
  (program.modelAllowance_le _).trans_lt
    (program.approximation.refineIndex_accurate current target positive)

namespace Prepared

variable {program : Program operations} {request : Request}

/-- The prepared cache's sample is the sample readback of its exact original model. -/
theorem sample_model (prepared : Prepared program request) :
    prepared.cache.sample = operations.sample prepared.cache.model := prepared.cache.sample_eq

/-- The prepared cache's allowance is the allowance readback of its exact original model. -/
theorem allowance_model (prepared : Prepared program request) :
    prepared.cache.allowance = operations.allowance prepared.cache.model := prepared.cache.allowance_eq

open Purelib.Data.Gaussian in
/-- Every later program sample lies within the prepared cache's retained squared radius. -/
theorem contains_later (prepared : Prepared program request) {later : Nat}
    (order : prepared.index ≤ later) :
    Data.Gaussian.Norm.Basic.normSq ((program.stage later).sample - prepared.cache.sample) ≤ prepared.radiusSq := by
  rw [prepared.cache_eq, prepared.radiusSq_eq]
  exact program.later_close order

end Prepared
end Program
end Purelib.Integration.CertifiedProgram
