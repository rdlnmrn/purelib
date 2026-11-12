module

public import Purelib.Riemann.Paths.OwnerTracePath.Primitive
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Data.Gaussian.Norm.Basic

/-! # Ordered primitive observations on the same original owner path

The original OwnerPath drives every dependent index. Each target primitive
request is constructed once and passed unchanged as the tail's source.
A stationary step retains its actual original observation Comparison and
its actual link; moving steps contribute zero only to the separate
stationary-jump list. No trace or continuation factory is run by this fold.
The common expression's actual denominator domain is explicit at every
original vertex, not inferred from geometric coincidence.
-/

public section

namespace Purelib.Riemann.Paths.OwnerTracePath.OwnerPath.Primitive

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients Expression)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner)

variable {polynomial : Coefficients}

namespace Stationary

variable {expression : Expression polynomial} {start finish : Canonical}
variable {left : Owner (polynomial.eval start)} {right : Owner (polynomial.eval finish)}
variable {accuracy : AccuracyRequest}

/-- The old-reading comparison is retained only for an actual coincident-endpoint decision on the original link. -/
@[expose] def Compared (link : OwnerLink polynomial start finish left right)
    (first : Vertex expression start left accuracy) (last : Vertex expression finish right accuracy) :
    Decidable (start = finish) → Type 1
  | .isTrue same =>
      { retained : Observation.Comparison first.observation last.observation (tailRequest accuracy).tolerance //
        retained = Stationary.compare link same first last }
  | .isFalse _ => PUnit

/-- The cached original endpoint decision and actual stationary comparison on the same retained link and observations.

The existing Decidable parent retains its actual equality or inequality
certificate. A true branch stores the original generic Comparison; a false
branch has no stationary comparison. No new geometry or Owner is introduced.
-/
@[expose] def Step (link : OwnerLink polynomial start finish left right)
    (first : Vertex expression start left accuracy) (last : Vertex expression finish right accuracy) :=
  Σ decision : Decidable (start = finish), Compared link first last decision

namespace Step

/-- Decide stationarity once and compare unchanged observations through this link's actual signed evidence. -/
def build (link : OwnerLink polynomial start finish left right)
    (first : Vertex expression start left accuracy) (last : Vertex expression finish right accuracy) :
    Step link first last :=
  match (inferInstance : Decidable (start = finish)) with
  | .isTrue same => ⟨.isTrue same, ⟨Stationary.compare link same first last, rfl⟩⟩
  | .isFalse different => ⟨.isFalse different, PUnit.unit⟩

/-- Read the actual signed primitive jump of a stationary step, or zero in the separate moving-step branch. -/
@[expose] def jump {link : OwnerLink polynomial start finish left right}
    {first : Vertex expression start left accuracy} {last : Vertex expression finish right accuracy} :
    Step link first last → Canonical
  | ⟨.isTrue _, _⟩ => last.value - first.value
  | ⟨.isFalse _, _⟩ => 0

/-- The actual old observations and stored stationary comparison pay this step's finite jump allowance. -/
theorem jump_lt {link : OwnerLink polynomial start finish left right}
    {first : Vertex expression start left accuracy} {last : Vertex expression finish right accuracy}
    (step : Step link first last) : Norm.Basic.normSq step.jump < accuracy.tolerance := by
  cases step with
  | mk decision compared =>
      cases decision with
      | isTrue _same => exact Stationary.jump_lt first last compared.val
      | isFalse _different =>
          change Norm.Basic.normSq 0 < accuracy.tolerance
          rewrite [Norm.Basic.normSq_zero]
          exact accuracy.positive

/-- A retained true endpoint decision gives the literal signed difference of the same two old values.

The existing decision is inspected directly. A false branch contradicts
the supplied original endpoint equality; no link or comparison is rebuilt.
-/
theorem jump_eq_of_same {link : OwnerLink polynomial start finish left right}
    {first : Vertex expression start left accuracy} {last : Vertex expression finish right accuracy}
    (step : Step link first last) (same : start = finish) : step.jump = last.value - first.value := by
  cases step with
  | mk decision compared =>
      cases decision with
      | isTrue _ => rfl
      | isFalse different => exact False.elim (different same)

end Step

end Stationary

/-- The common coefficient expression is defined at every exact original owner-path vertex. -/
@[expose] def Defined (expression : Expression polynomial) :
    {start finish : Canonical} → {left : Owner (polynomial.eval start)} →
    {right : Owner (polynomial.eval finish)} → OwnerPath polynomial start left finish right → Prop
  | _, _, _, _, .nil point _ => expression.Defined point
  | start, _, _, _, .cons _ tail => expression.Defined start ∧ Defined expression tail

namespace Defined

/-- Read the common expression's genuine denominator-domain evidence at this same original source vertex. -/
theorem first {expression : Expression polynomial} {start finish : Canonical}
    {left : Owner (polynomial.eval start)} {right : Owner (polynomial.eval finish)}
    {path : OwnerPath polynomial start left finish right} (defined : Defined expression path) :
    expression.Defined start := by
  cases path with
  | nil => exact defined
  | cons => exact defined.1

end Defined

/-- The ordered target observations and comparisons follow the same original owner-path constructors.

The source cache is an exact index. Each head stores its original target
cache, the completed original stationary-comparison outcome, and the tail
whose source is that identical target cache. Only the original path is
matched; no replacement Subdivision, trace or Owner datatype is constructed.
-/
@[expose] def Tail (expression : Expression polynomial) (accuracy : AccuracyRequest) :
    {start finish : Canonical} → {left : Owner (polynomial.eval start)} →
    {right : Owner (polynomial.eval finish)} →
    (path : OwnerPath polynomial start left finish right) → Vertex expression start left accuracy → Type 1
  | _, _, _, _, .nil _ _, _ => PUnit
  | _, _, _, _, .cons (middle := middle) (center := center) link tail, first =>
      Σ next : Vertex expression middle center accuracy,
        Stationary.Step link first next × Tail expression accuracy tail next

namespace Tail

/-- Construct one target primitive observation per actual link and pass each literal target into the next source.

The supplied original source is reused unchanged. The original path, its
links, every endpoint Owner and the admitted coefficient-domain evidence
are inputs. New primitive channel requests and stationary tail comparisons
are constructed exactly once at their respective retained nodes.
-/
def build (expression : Expression polynomial) (accuracy : AccuracyRequest) :
    {start finish : Canonical} → {left : Owner (polynomial.eval start)} →
    {right : Owner (polynomial.eval finish)} →
    (path : OwnerPath polynomial start left finish right) → (first : Vertex expression start left accuracy) →
    Defined expression path → Tail expression accuracy path first
  | _, _, _, _, .nil _ _, _, _ => PUnit.unit
  | _, _, _, _, .cons (middle := middle) (center := center) link tail, first, defined =>
      let next := Vertex.build expression middle center accuracy (Defined.first (path := tail) defined.2)
      let compared := Stationary.Step.build link first next
      let following := build expression accuracy tail next defined.2
      ⟨next, compared, following⟩
termination_by structural _ _ _ _ path _ _ => path

/-- Read the retained target primitive values in the exact original link order. -/
@[expose] def values {expression : Expression polynomial} {accuracy : AccuracyRequest} :
    {start finish : Canonical} → {left : Owner (polynomial.eval start)} →
    {right : Owner (polynomial.eval finish)} →
    (path : OwnerPath polynomial start left finish right) → (first : Vertex expression start left accuracy) →
    Tail expression accuracy path first → List Canonical
  | _, _, _, _, .nil _ _, _, _ => []
  | _, _, _, _, .cons _ tail, _, observed => observed.1.value :: values tail observed.1 observed.2.2
termination_by structural _ _ _ _ path _ _ => path

/-- Read one signed stationary jump per actual original link, with zero only for a moving-step comparison branch. -/
@[expose] def jumps {expression : Expression polynomial} {accuracy : AccuracyRequest} :
    {start finish : Canonical} → {left : Owner (polynomial.eval start)} →
    {right : Owner (polynomial.eval finish)} →
    (path : OwnerPath polynomial start left finish right) → (first : Vertex expression start left accuracy) →
    Tail expression accuracy path first → List Canonical
  | _, _, _, _, .nil _ _, _, _ => []
  | _, _, _, _, .cons _ tail, _, observed => observed.2.1.jump :: jumps tail observed.1 observed.2.2
termination_by structural _ _ _ _ path _ _ => path

/-- Read the exact cached final primitive vertex without selecting a new request at the terminal Owner. -/
@[expose] def last {expression : Expression polynomial} {accuracy : AccuracyRequest} :
    {start finish : Canonical} → {left : Owner (polynomial.eval start)} →
    {right : Owner (polynomial.eval finish)} →
    (path : OwnerPath polynomial start left finish right) → (first : Vertex expression start left accuracy) →
    Tail expression accuracy path first → Vertex expression finish right accuracy
  | _, _, _, _, .nil _ _, first, _ => first
  | _, _, _, _, .cons _ tail, _, observed => last tail observed.1 observed.2.2
termination_by structural _ _ _ _ path _ _ => path

/-- The retained target-value list contains exactly the original path's number of links. -/
theorem values_length {expression : Expression polynomial} {accuracy : AccuracyRequest} :
    ∀ {start finish : Canonical} {left : Owner (polynomial.eval start)}
      {right : Owner (polynomial.eval finish)} (path : OwnerPath polynomial start left finish right)
      (first : Vertex expression start left accuracy) (observed : Tail expression accuracy path first),
      (values path first observed).length = path.vertices.length
  | _, _, _, _, .nil _ _, _, _ => rfl
  | _, _, _, _, .cons _ tail, _, observed =>
      congrArg Nat.succ (values_length tail observed.1 observed.2.2)

/-- The stationary-jump list retains one ordered occurrence for each actual original owner-path link. -/
theorem jumps_length {expression : Expression polynomial} {accuracy : AccuracyRequest} :
    ∀ {start finish : Canonical} {left : Owner (polynomial.eval start)}
      {right : Owner (polynomial.eval finish)} (path : OwnerPath polynomial start left finish right)
      (first : Vertex expression start left accuracy) (observed : Tail expression accuracy path first),
      (jumps path first observed).length = path.vertices.length
  | _, _, _, _, .nil _ _, _, _ => rfl
  | _, _, _, _, .cons _ tail, _, observed =>
      congrArg Nat.succ (jumps_length tail observed.1 observed.2.2)

/-- Every ordered jump is paid by its original vertex requests and the actual stored link comparison. -/
theorem jumps_bounded {expression : Expression polynomial} {accuracy : AccuracyRequest} :
    ∀ {start finish : Canonical} {left : Owner (polynomial.eval start)}
      {right : Owner (polynomial.eval finish)} (path : OwnerPath polynomial start left finish right)
      (first : Vertex expression start left accuracy) (observed : Tail expression accuracy path first),
      ∀ jump ∈ jumps path first observed, Norm.Basic.normSq jump ≤ accuracy.tolerance
  | _, _, _, _, .nil _ _, _, _, _, member => by cases member
  | _, _, _, _, .cons _ tail, _, observed, _, member => by
      cases member with
      | head => exact observed.2.1.jump_lt.le
      | tail _ member => exact jumps_bounded tail observed.1 observed.2.2 _ member

end Tail

/-- A source observation and complete ordered primitive-observation tail on this identical original OwnerPath. -/
@[expose] def Spine (expression : Expression polynomial) (accuracy : AccuracyRequest)
    {start finish : Canonical} {left : Owner (polynomial.eval start)} {right : Owner (polynomial.eval finish)}
    (path : OwnerPath polynomial start left finish right) :=
  Σ first : Vertex expression start left accuracy, Tail expression accuracy path first

namespace Spine

variable {expression : Expression polynomial} {accuracy : AccuracyRequest}
variable {start finish : Canonical} {left : Owner (polynomial.eval start)} {right : Owner (polynomial.eval finish)}
variable {path : OwnerPath polynomial start left finish right}

/-- Retain an old original source cache and a completed observation tail without running any producer again. -/
@[expose] def ofCompleted (first : Vertex expression start left accuracy)
    (following : Tail expression accuracy path first) :
    Spine expression accuracy path := ⟨first, following⟩

/-- Reuse the actual old source, then construct each original target primitive observation once on this SAME path. -/
@[expose] def ofSource (first : Vertex expression start left accuracy) (defined : Defined expression path) :
    Spine expression accuracy path := ⟨first, Tail.build expression accuracy path first defined⟩

/-- Construct the source observation once and retain the whole actual ordered primitive-observation execution. -/
def build (path : OwnerPath polynomial start left finish right) (defined : Defined expression path) :
    Spine expression accuracy path :=
  let first := Vertex.build expression start left accuracy (Defined.first (path := path) defined)
  ofSource first defined

variable (observed : Spine expression accuracy path)

/-- Read the identical original source vertex cache retained by this complete spine. -/
@[expose] def first : Vertex expression start left accuracy := observed.1

/-- Read all actual old primitive values, including the unchanged source and every ordered original target. -/
@[expose] def values : List Canonical := observed.first.value :: Tail.values path observed.first observed.2

/-- Read the actual ordered stationary jumps without treating moving integral increments as zero. -/
@[expose] def jumps : List Canonical := Tail.jumps path observed.first observed.2

/-- Read the literal original final vertex observation already retained at the end of this same spine. -/
@[expose] def last : Vertex expression finish right accuracy := Tail.last path observed.first observed.2

/-- The retained observation execution has exactly one primitive observation at each original owner-path vertex. -/
theorem values_length : observed.values.length = path.vertices.length + 1 :=
  congrArg Nat.succ (Tail.values_length path observed.first observed.2)

/-- The old supplied source is preserved literally by the automatic tail constructor. -/
theorem ofSource_first (first : Vertex expression start left accuracy) (defined : Defined expression path) :
    (ofSource first defined).first = first := rfl

/-- A single retained stationary link contributes the literal difference of its two original observations.

The same source, target and comparison caches are inspected. The original
stationary decision supplies its signed jump equation; neither observation
nor link is rebuilt and no equality of the two values is asserted.
-/
theorem stationary_increment_eq {point : Canonical}
    {source target : Owner (polynomial.eval point)}
    {link : OwnerLink polynomial point point source target}
    (sampled : Spine expression accuracy (.cons link (.nil point target))) :
    Norm.Sum.Basic.gaussianSum sampled.jumps = sampled.last.value - sampled.first.value := by
  rcases sampled with ⟨first, next, compared, following⟩
  change compared.jump + 0 = next.value - first.value
  exact (Basic.add_zero compared.jump).trans (compared.jump_eq_of_same rfl)

/-- Transport the complete old primitive spine through exact endpoint and original Owner identities.

All original requests, readings and stationary comparisons cross together.
The original path is changed only by its existing endpoint-index transport.
-/
@[expose] def castEndpoints {nextStart nextFinish : Canonical}
    {nextLeft : Owner (polynomial.eval nextStart)} {nextRight : Owner (polynomial.eval nextFinish)}
    (startEq : start = nextStart) (finishEq : finish = nextFinish)
    (leftEq : HEq left nextLeft) (rightEq : HEq right nextRight)
    (observed : Spine expression accuracy path) :
    Spine expression accuracy (path.castEndpoints startEq finishEq leftEq rightEq) := by
  cases startEq
  cases finishEq
  cases eq_of_heq leftEq
  cases eq_of_heq rightEq
  exact observed

/-- Recover the whole original primitive spine from that same path's exact endpoint-index transport.

The supplied complete observation cache is retained. No path, source, target
or observation producer is run by reversing these exact indices.
-/
@[expose] def uncastEndpoints {nextStart nextFinish : Canonical}
    {nextLeft : Owner (polynomial.eval nextStart)} {nextRight : Owner (polynomial.eval nextFinish)}
    (startEq : start = nextStart) (finishEq : finish = nextFinish)
    (leftEq : HEq left nextLeft) (rightEq : HEq right nextRight)
    (observed : Spine expression accuracy (path.castEndpoints startEq finishEq leftEq rightEq)) :
    Spine expression accuracy path := by
  cases startEq
  cases finishEq
  cases eq_of_heq leftEq
  cases eq_of_heq rightEq
  exact observed

/-- Exact endpoint transport preserves the entire original observation spine heterogeneously. -/
theorem castEndpoints_heq {nextStart nextFinish : Canonical}
    {nextLeft : Owner (polynomial.eval nextStart)} {nextRight : Owner (polynomial.eval nextFinish)}
    (startEq : start = nextStart) (finishEq : finish = nextFinish)
    (leftEq : HEq left nextLeft) (rightEq : HEq right nextRight)
    (observed : Spine expression accuracy path) :
    HEq (castEndpoints startEq finishEq leftEq rightEq observed) observed := by
  cases startEq
  cases finishEq
  cases eq_of_heq leftEq
  cases eq_of_heq rightEq
  rfl

/-- Reversing exact endpoint transport preserves the entire supplied observation spine heterogeneously. -/
theorem uncastEndpoints_heq {nextStart nextFinish : Canonical}
    {nextLeft : Owner (polynomial.eval nextStart)} {nextRight : Owner (polynomial.eval nextFinish)}
    (startEq : start = nextStart) (finishEq : finish = nextFinish)
    (leftEq : HEq left nextLeft) (rightEq : HEq right nextRight)
    (observed : Spine expression accuracy (path.castEndpoints startEq finishEq leftEq rightEq)) :
    HEq (uncastEndpoints startEq finishEq leftEq rightEq observed) observed := by
  cases startEq
  cases finishEq
  cases eq_of_heq leftEq
  cases eq_of_heq rightEq
  rfl

/-- Reversing the exact endpoint indices preserves every old value in its original order. -/
theorem uncastEndpoints_values {nextStart nextFinish : Canonical}
    {nextLeft : Owner (polynomial.eval nextStart)} {nextRight : Owner (polynomial.eval nextFinish)}
    (startEq : start = nextStart) (finishEq : finish = nextFinish)
    (leftEq : HEq left nextLeft) (rightEq : HEq right nextRight)
    (observed : Spine expression accuracy (path.castEndpoints startEq finishEq leftEq rightEq)) :
    (uncastEndpoints startEq finishEq leftEq rightEq observed).values = observed.values := by
  cases startEq
  cases finishEq
  cases eq_of_heq leftEq
  cases eq_of_heq rightEq
  rfl

/-- Transport the complete old observation spine through an equality of its SAME original indexed path. -/
@[expose] def castPath {nextPath : OwnerPath polynomial start left finish right} (equal : path = nextPath)
    (observed : Spine expression accuracy path) : Spine expression accuracy nextPath := by
  cases equal
  exact observed

/-- Exact path-index transport preserves the entire supplied original observation execution heterogeneously. -/
theorem castPath_heq {nextPath : OwnerPath polynomial start left finish right} (equal : path = nextPath)
    (observed : Spine expression accuracy path) : HEq (castPath equal observed) observed := by
  cases equal
  rfl

/-- Exact path-index transport preserves all actual old values in their original order. -/
theorem castPath_values {nextPath : OwnerPath polynomial start left finish right} (equal : path = nextPath)
    (observed : Spine expression accuracy path) : (castPath equal observed).values = observed.values := by
  cases equal
  rfl

/-- Exact path-index transport preserves the literal old source vertex and its complete request cache. -/
theorem castPath_first {nextPath : OwnerPath polynomial start left finish right} (equal : path = nextPath)
    (observed : Spine expression accuracy path) : (castPath equal observed).first = observed.first := by
  cases equal
  rfl

/-- Exact path-index transport preserves the literal old final vertex and its complete request cache. -/
theorem castPath_last {nextPath : OwnerPath polynomial start left finish right} (equal : path = nextPath)
    (observed : Spine expression accuracy path) : (castPath equal observed).last = observed.last := by
  cases equal
  rfl

/-- Reversing exact endpoint transport retains the complete old source vertex with its original Owner index. -/
theorem uncastEndpoints_first_heq {nextStart nextFinish : Canonical}
    {nextLeft : Owner (polynomial.eval nextStart)} {nextRight : Owner (polynomial.eval nextFinish)}
    (startEq : start = nextStart) (finishEq : finish = nextFinish)
    (leftEq : HEq left nextLeft) (rightEq : HEq right nextRight)
    (observed : Spine expression accuracy (path.castEndpoints startEq finishEq leftEq rightEq)) :
    HEq (uncastEndpoints startEq finishEq leftEq rightEq observed).first observed.first := by
  cases startEq
  cases finishEq
  cases eq_of_heq leftEq
  cases eq_of_heq rightEq
  rfl

/-- Reversing exact endpoint transport retains the complete old final vertex with its original Owner index. -/
theorem uncastEndpoints_last_heq {nextStart nextFinish : Canonical}
    {nextLeft : Owner (polynomial.eval nextStart)} {nextRight : Owner (polynomial.eval nextFinish)}
    (startEq : start = nextStart) (finishEq : finish = nextFinish)
    (leftEq : HEq left nextLeft) (rightEq : HEq right nextRight)
    (observed : Spine expression accuracy (path.castEndpoints startEq finishEq leftEq rightEq)) :
    HEq (uncastEndpoints startEq finishEq leftEq rightEq observed).last observed.last := by
  cases startEq
  cases finishEq
  cases eq_of_heq leftEq
  cases eq_of_heq rightEq
  rfl

/-- Reversing exact endpoint transport preserves the SAME actual old initial scalar value. -/
theorem uncastEndpoints_first_value {nextStart nextFinish : Canonical}
    {nextLeft : Owner (polynomial.eval nextStart)} {nextRight : Owner (polynomial.eval nextFinish)}
    (startEq : start = nextStart) (finishEq : finish = nextFinish)
    (leftEq : HEq left nextLeft) (rightEq : HEq right nextRight)
    (observed : Spine expression accuracy (path.castEndpoints startEq finishEq leftEq rightEq)) :
    (uncastEndpoints startEq finishEq leftEq rightEq observed).first.value = observed.first.value := by
  cases startEq
  cases finishEq
  cases eq_of_heq leftEq
  cases eq_of_heq rightEq
  rfl

/-- Reversing exact endpoint transport preserves the SAME actual old final scalar value. -/
theorem uncastEndpoints_last_value {nextStart nextFinish : Canonical}
    {nextLeft : Owner (polynomial.eval nextStart)} {nextRight : Owner (polynomial.eval nextFinish)}
    (startEq : start = nextStart) (finishEq : finish = nextFinish)
    (leftEq : HEq left nextLeft) (rightEq : HEq right nextRight)
    (observed : Spine expression accuracy (path.castEndpoints startEq finishEq leftEq rightEq)) :
    (uncastEndpoints startEq finishEq leftEq rightEq observed).last.value = observed.last.value := by
  cases startEq
  cases finishEq
  cases eq_of_heq leftEq
  cases eq_of_heq rightEq
  rfl

/-- Exact path-index transport preserves the SAME actual original initial scalar value. -/
theorem castPath_first_value {nextPath : OwnerPath polynomial start left finish right} (equal : path = nextPath)
    (observed : Spine expression accuracy path) : (castPath equal observed).first.value = observed.first.value := by
  cases equal
  rfl

/-- Exact path-index transport preserves the SAME actual original final scalar value. -/
theorem castPath_last_value {nextPath : OwnerPath polynomial start left finish right} (equal : path = nextPath)
    (observed : Spine expression accuracy path) : (castPath equal observed).last.value = observed.last.value := by
  cases equal
  rfl

end Spine

end Purelib.Riemann.Paths.OwnerTracePath.OwnerPath.Primitive

end
