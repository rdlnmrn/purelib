module

public import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Joins
public import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Payment
public import Purelib.Riemann.Paths.OwnerTracePath.Join
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Append
import Purelib.Data.List.Membership
import Purelib.Tactic.Ring
import Purelib.Algebra.Quadratic.Pair.Polynomial
import Purelib.Approximation.AccuracyRequest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings

/-! # Paid sewing of unchanged primitive observation spines

A constructed owner path retains its whole original endpoint observations.
Only actual new stationary handoffs enter the separate ordered junction
list. Its increment identity and local comparison payments are derived
while appending; no old request is retagged or observed again.
-/

public section

namespace Purelib.Riemann.Paths.OwnerTracePath.OwnerPath.Primitive.Spine

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients Expression)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational.Budget
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner OwnerJoin ownerName)

variable {polynomial : Coefficients} {expression : Expression polynomial} {accuracy : AccuracyRequest}
variable {start middle finish : Canonical}
variable {left : Owner (polynomial.eval start)} {center : Owner (polynomial.eval middle)}
variable {right : Owner (polynomial.eval finish)}
variable (first : Vertex expression start left accuracy) (last : Vertex expression finish right accuracy)

/-- An actual owner path and complete primitive Spine retaining two specified whole original endpoint Vertices. -/
@[expose] def Between :=
  Σ path : OwnerPath polynomial start left finish right,
    {sampled : Spine expression accuracy path // sampled.first = first ∧ sampled.last = last}

/-- An actual sewn Spine with the ordered new handoff values and their internally paid increment identity.

The supplied sample is the sum of the original piece increments. Every
new junction value is bounded by the SAME preselected local request. The
whole actual path/Spine retains its real links, old observations and all
stationary comparison caches, including those already inside the pieces.
-/
@[expose] def Sewing (sample : Canonical) :=
  Σ _actual : Between first last,
  {junctions : List Canonical //
    (∀ value ∈ junctions, Norm.Basic.normSq value ≤ accuracy.tolerance) ∧
      last.value - first.value = sample + Norm.Sum.Basic.gaussianSum junctions}

namespace Sewing

variable {first last} {sample : Canonical} (sewn : Sewing first last sample)

/-- Read the actual owner path, including all supplied old pieces and newly acquired handoff links. -/
@[expose] def path : OwnerPath polynomial start left finish right := sewn.1.1

/-- Read the complete actual primitive-observation Spine on that identical retained path. -/
@[expose] def observed : Spine expression accuracy sewn.path := sewn.1.2.val

/-- Read only the new handoff values in their actual execution order. -/
@[expose] def junctions : List Canonical := sewn.2.1

/-- The constructed path retains the entire specified original source Vertex. -/
theorem first_eq : sewn.observed.first = first := sewn.1.2.property.1

/-- The constructed path retains the entire specified original target Vertex. -/
theorem last_eq : sewn.observed.last = last := sewn.1.2.property.2

/-- Each retained new handoff has its internally derived finite local comparison payment. -/
theorem junctions_bounded : ∀ value ∈ sewn.junctions, Norm.Basic.normSq value ≤ accuracy.tolerance :=
  sewn.2.2.1

/-- The actual full endpoint increment equals the original piece sample plus exactly the retained new handoffs. -/
theorem increment_eq : last.value - first.value = sample + Norm.Sum.Basic.gaussianSum sewn.junctions :=
  sewn.2.2.2

/-- Retain a complete original piece with no new handoff, query or observation. -/
def ofSpine {path : OwnerPath polynomial start left finish right}
    (sampled : Spine expression accuracy path) :
    Sewing sampled.first sampled.last (sampled.last.value - sampled.first.value) :=
  ⟨⟨path, ⟨sampled, ⟨rfl, rfl⟩⟩⟩, [], ⟨(by
    intro value member
    cases member), by
    change sampled.last.value - sampled.first.value =
      (sampled.last.value - sampled.first.value) + 0
    ring1⟩⟩

/-- Reindex only an exactly equal scalar piece sample, retaining the complete actual path and observation cache. -/
def castSample {next : Canonical} (equal : sample = next) (before : Sewing first last sample) :
    Sewing first last next :=
  Eq.mp (congrArg (Sewing first last) equal) before

/-- Exact scalar sample transport retains the complete actual observed Spine heterogeneously. -/
theorem castSample_observed_heq {next : Canonical} (equal : sample = next) (before : Sewing first last sample) :
    HEq (castSample equal before).observed before.observed := by
  cases equal
  unfold castSample
  rfl

/-- Acquire a genuine stationary handoff and compare the unchanged supplied endpoint observations once. -/
def stationary (first : Vertex expression start left accuracy) (last : Vertex expression finish right accuracy)
    (same : start = finish) (roots : NamedEquivalent (ownerName left) (ownerName right)) :
    Sewing first last 0 :=
  let joined := OwnerJoin.acquireAt (polynomial := polynomial) same roots
  let link := OwnerLink.ofJoinAt (polynomial := polynomial) same joined
  let comparison := Stationary.compare (polynomial := polynomial)
    (expression := expression) (accuracy := accuracy) link same first last
  let compared : Stationary.Compared (polynomial := polynomial)
    (expression := expression) (accuracy := accuracy) link first last (.isTrue same) := ⟨comparison, rfl⟩
  let sampled := Stationary.spine (polynomial := polynomial)
    (expression := expression) (accuracy := accuracy) link same first last compared
  ⟨⟨.cons link (.nil finish right),
      ⟨sampled, ⟨Stationary.spine_first (polynomial := polynomial)
        (expression := expression) (accuracy := accuracy) link same first last compared,
        Stationary.spine_last (polynomial := polynomial)
          (expression := expression) (accuracy := accuracy) link same first last compared⟩⟩⟩,
    [last.value - first.value], ⟨by
      intro value member
      have equal := Membership.mem_singleton.mp member
      exact equal.symm ▸ (Stationary.jump_lt (polynomial := polynomial)
        (expression := expression) (accuracy := accuracy) first last comparison).le,
    by
      change last.value - first.value = 0 + ((last.value - first.value) + 0)
      ring1⟩⟩

variable {middleVertex : Vertex expression middle center accuracy} {beforeSample afterSample : Canonical}

/-- Append actual sewn caches at the SAME entire shared Vertex, preserving every ordered junction occurrence. -/
def append (before : Sewing first middleVertex beforeSample) (after : Sewing middleVertex last afterSample) :
    Sewing first last (beforeSample + afterSample) :=
  let same := after.first_eq.trans before.last_eq.symm
  let sampled := Spine.append (polynomial := polynomial)
    (expression := expression) (accuracy := accuracy) before.observed after.observed same
  ⟨⟨before.path.append after.path,
      ⟨sampled, ⟨(Spine.append_first (polynomial := polynomial)
        (expression := expression) (accuracy := accuracy) before.observed after.observed same).trans before.first_eq,
        (Spine.append_last (polynomial := polynomial)
          (expression := expression) (accuracy := accuracy) before.observed after.observed same).trans after.last_eq⟩⟩⟩,
    before.junctions ++ after.junctions, ⟨by
      intro value member
      cases Membership.mem_append.mp member with
      | inl member => exact before.junctions_bounded value member
      | inr member => exact after.junctions_bounded value member,
    by
      have firstPayment := before.increment_eq
      have lastPayment := after.increment_eq
      calc
        last.value - first.value =
            (middleVertex.value - first.value) + (last.value - middleVertex.value) := by ring1
        _ = (beforeSample + Norm.Sum.Basic.gaussianSum before.junctions) +
            (afterSample + Norm.Sum.Basic.gaussianSum after.junctions) :=
          congrArg₂ (· + ·) firstPayment lastPayment
        _ = (beforeSample + afterSample) +
            Norm.Sum.Basic.gaussianSum (before.junctions ++ after.junctions) := by
          rewrite [Norm.Sum.Basic.gaussianSum_append]
          ring1⟩⟩

/-- Exact finish-point and whole-Owner transport retains the actual full old Spine and all original requests.

Only original owned endpoint-index transport executes. The returned final
Vertex is the actual transported old final cache; its accuracy is unchanged.
-/
def castFinish {nextFinish : Canonical} {nextRight : Owner (polynomial.eval nextFinish)}
    (same : finish = nextFinish) (owners : HEq right nextRight) (before : Sewing first last sample) :
    Σ final : Vertex expression nextFinish nextRight accuracy, Sewing first final sample :=
  let sampled := Spine.castEndpoints (polynomial := polynomial)
    (expression := expression) (accuracy := accuracy) rfl same (HEq.refl left) owners before.observed
  have firstEq : sampled.first = first := by
    cases same
    cases eq_of_heq owners
    exact before.first_eq
  have valueEq : sampled.last.value = last.value := by
    cases same
    cases eq_of_heq owners
    exact congrArg (fun value : Vertex expression finish right accuracy => value.value) before.last_eq
  ⟨sampled.last,
    ⟨⟨before.path.castEndpoints rfl same (HEq.refl left) owners,
        ⟨sampled, ⟨firstEq, rfl⟩⟩⟩,
      before.junctions, ⟨before.junctions_bounded,
        (congrArg (fun value : Canonical => value - first.value) valueEq).trans before.increment_eq⟩⟩⟩

/-- Exact finish transport preserves the entire old observed Spine heterogeneously, including every request. -/
theorem castFinish_observed_heq {nextFinish : Canonical} {nextRight : Owner (polynomial.eval nextFinish)}
    (same : finish = nextFinish) (owners : HEq right nextRight) (before : Sewing first last sample) :
    HEq (castFinish same owners before).2.observed before.observed := by
  unfold castFinish
  exact Spine.castEndpoints_heq (polynomial := polynomial)
    (expression := expression) (accuracy := accuracy) rfl same (HEq.refl left) owners before.observed

/-- The exact finite Cauchy budget pays the sum of the actual newly retained handoffs. -/
theorem error_le : Norm.Basic.normSq (last.value - first.value - sample) ≤
    (sewn.junctions.length : Rational) * ((sewn.junctions.length : Rational) * accuracy.tolerance) := by
  have identity : last.value - first.value - sample = Norm.Sum.Basic.gaussianSum sewn.junctions := by
    rewrite [sewn.increment_eq]
    ring1
  exact Eq.mpr (congrArg (fun value : Canonical => Norm.Basic.normSq value ≤
      (sewn.junctions.length : Rational) * ((sewn.junctions.length : Rational) * accuracy.tolerance)) identity)
    (Norm.Sum.Bounds.normSq_sum_le sewn.junctions accuracy.tolerance sewn.junctions_bounded)

/-- An unchanged original piece contributes no new stationary handoff. -/
theorem ofSpine_count {path : OwnerPath polynomial start left finish right}
    (sampled : Spine expression accuracy path) :
    (ofSpine (polynomial := polynomial) (expression := expression) (accuracy := accuracy) sampled).junctions.length =
      0 := by
  unfold ofSpine
  rfl

/-- A newly constructed real stationary handoff contributes exactly one new paid occurrence. -/
theorem stationary_count (first : Vertex expression start left accuracy)
    (last : Vertex expression finish right accuracy) (same : start = finish)
    (roots : NamedEquivalent (ownerName left) (ownerName right)) :
    (stationary (polynomial := polynomial) (expression := expression) (accuracy := accuracy)
      first last same roots).junctions.length = 1 := by
  unfold stationary
  rfl

/-- Appending actual sewn caches adds their retained new-handoff counts without deduplication. -/
theorem append_count (before : Sewing first middleVertex beforeSample)
    (after : Sewing middleVertex last afterSample) :
    (append (polynomial := polynomial) (expression := expression)
      (accuracy := accuracy) before after).junctions.length =
      before.junctions.length + after.junctions.length := by
  unfold append
  exact Append.length_append before.junctions after.junctions

/-- Exact scalar sample transport preserves the literal number of actual new handoffs. -/
theorem castSample_count {next : Canonical} (equal : sample = next) (before : Sewing first last sample) :
    (castSample (polynomial := polynomial) (expression := expression) (accuracy := accuracy)
      equal before).junctions.length = before.junctions.length := by
  cases equal
  unfold castSample
  rfl

/-- Exact whole-Owner endpoint transport preserves every actual new handoff and its count. -/
theorem castFinish_count {nextFinish : Canonical} {nextRight : Owner (polynomial.eval nextFinish)}
    (same : finish = nextFinish) (owners : HEq right nextRight) (before : Sewing first last sample) :
    (castFinish (polynomial := polynomial) (expression := expression) (accuracy := accuracy)
      same owners before).2.junctions.length = before.junctions.length := by
  unfold castFinish
  rfl

/-- A request allocated before the actual observations pays the count of these SAME new handoffs.

Only the sewing residual is covered. Neither existing endpoint requests,
model remainders nor any unrelated integral or primitive normalization is
weakened or paid by this local allocation.
-/
theorem error_lt {target : AccuracyRequest} {budgetCount : Nat}
    (countBound : sewn.junctions.length ≤ budgetCount)
    (localBound : accuracy.tolerance ≤
      Aggregate.perTerm target.tolerance budgetCount) :
    Norm.Basic.normSq (last.value - first.value - sample) < target.tolerance := by
  have paid := Aggregate.count_mul_allowance_lt countBound target.positive localBound
  simp only [Aggregate.countCoordinate_eq] at paid
  exact (error_le (polynomial := polynomial) (expression := expression) (accuracy := accuracy) sewn).trans_lt paid

end Sewing

end Purelib.Riemann.Paths.OwnerTracePath.OwnerPath.Primitive.Spine

end
