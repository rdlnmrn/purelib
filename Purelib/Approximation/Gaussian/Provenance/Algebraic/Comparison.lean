module

public import Purelib.Approximation.Gaussian.Provenance.Algebraic
public import Purelib.Approximation.Gaussian.Name.Coherent.Difference
import Purelib.Approximation.Gaussian.Division.Obstruction.Zero
import Purelib.Polynomial.Approximation.CoherentEvaluation
import Purelib.Approximation.Gaussian.Geometric.Coherent.Comparison
import Purelib.Approximation.Gaussian.Arithmetic.Mul
import Purelib.Approximation.Gaussian.Division.Prepared.Decision.Laws
import Purelib.Approximation.Gaussian.Division.Prepared.Equivalence
import Purelib.Riemann.RootContinuation.CoherentRoot.CommonSource
import Purelib.Riemann.RootContinuation.CoherentRoot.PairSeparation
import Purelib.Riemann.RootContinuation.CoherentRoot.Polynomial
import Purelib.Approximation.Gaussian.Provenance.PolynomialRoot
import Init.Core
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Independent algebraic comparison on the original channels

The original two constructions supply a quantitative residual for their actual
difference. Its finite exact decision supplies an operational equality or an
apart presentation, retaining both input owners and the computed difference.
-/

public section

namespace Purelib.Approximation.Gaussian.Provenance.Algebraic

open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Polynomial.Approximation
open Purelib.Riemann.RootContinuation
open CoherentRoot (CertifiedName CommonSource WindingOneState)

set_option genInjectivity false in
/-- Equality of two original channels or their retained quantitative apart difference presentation. -/
inductive Comparison (first second : CoherentNamed) : Type 1 where
  /-- Both original channels have a computed operational agreement certificate. -/
  | equal (equivalent : NamedEquivalent first.name second.name)
  /-- The actual original difference has a computed whole-ball-apart presentation. -/
  | distinct (prepared : Division.Prepared (Difference.difference first second))
      (different : ¬ Nonempty (NamedEquivalent first.name second.name))

constructive_injectivity Comparison

namespace Comparison

/-- Read the checked original-channel comparison from one retained exact difference decision. -/
@[expose] def ofDecision (first second : CoherentNamed)
    (decision : Division.Prepared.Decision (Difference.difference first second)) : Comparison first second :=
  match decision with
  | .excluded zero => .equal (Difference.equivalent_of_difference_zero first second zero).symm
  | .prepared prepared => .distinct prepared (fun ⟨equivalent⟩ =>
      Division.Obstruction.Zero.ZeroIdentity.incompatible_prepared
        (Difference.difference_zero_of_equivalent first second equivalent.symm) prepared)

/-- Read the stored comparison agreement using independently proved operational agreement.

The equality branch returns its literal retained certificate. The distinct
branch contradicts the supplied agreement using its own rejection proof;
no selected site or numerical decision is assumed.
-/
def equivalent {first second : CoherentNamed} (comparison : Comparison first second)
    (known : NamedEquivalent first.name second.name) : NamedEquivalent first.name second.name :=
  match comparison with
  | .equal actual => actual
  | .distinct _ different => False.elim (different ⟨known⟩)

end Comparison

namespace Sidecar

namespace Compared

/-- The exact original five-field complete difference comparison as a dependent view.

Both complete computations and their defining equalities are retained. This
is a tuple view of the original Sidecar and Decision owners, not an alternate
comparison certificate family.
-/
@[expose] def Materialized {first second : CoherentNamed} (left : Sidecar first) (right : Sidecar second) : Type 2 :=
  Σ difference : { value : Sidecar (Difference.difference first second) // value = right.sub left },
    Σ resolved : { value : Resolved difference.val // value = difference.val.resolve },
      { value : Division.Prepared.Decision (Difference.difference first second) // value = resolved.val.decision } ×
        Comparison first second

namespace Materialized

/-- The actual complete algebraic difference at both original input channels. -/
@[expose] def difference {first second : CoherentNamed} {left : Sidecar first} {right : Sidecar second}
    (materialized : Materialized left right) : Sidecar (Difference.difference first second) := materialized.1.val

/-- The stored complete difference is computed from the same original inputs. -/
theorem difference_eq {first second : CoherentNamed} {left : Sidecar first} {right : Sidecar second}
    (materialized : Materialized left right) : materialized.difference = right.sub left := materialized.1.property

/-- The complete classification actually computed by this same retained difference. -/
@[expose] def resolved {first second : CoherentNamed} {left : Sidecar first} {right : Sidecar second}
    (materialized : Materialized left right) : Resolved materialized.difference := materialized.2.1.val

/-- The stored classification is the original resolver on the same stored difference. -/
theorem resolved_eq {first second : CoherentNamed} {left : Sidecar first} {right : Sidecar second}
    (materialized : Materialized left right) : materialized.resolved = materialized.difference.resolve :=
  materialized.2.1.property

/-- The exact decision made by the same retained complete difference construction. -/
@[expose] def decision {first second : CoherentNamed} {left : Sidecar first} {right : Sidecar second}
    (materialized : Materialized left right) : Division.Prepared.Decision (Difference.difference first second) :=
  materialized.2.2.1.val

/-- The complete difference decision is projected from its same actual retained classification. -/
theorem decision_resolved {first second : CoherentNamed} {left : Sidecar first} {right : Sidecar second}
    (materialized : Materialized left right) : materialized.decision = materialized.resolved.decision :=
  materialized.2.2.1.property

/-- The same stored complete difference computes this exact stored decision. -/
theorem decision_eq {first second : CoherentNamed} {left : Sidecar first} {right : Sidecar second}
    (materialized : Materialized left right) : materialized.decision = materialized.difference.decide :=
  materialized.2.2.1.property.trans (congrArg Resolved.decision materialized.2.1.property)

/-- The original checked equality or distinctness read from the complete difference decision. -/
@[expose] def comparison {first second : CoherentNamed} {left : Sidecar first} {right : Sidecar second}
    (materialized : Materialized left right) : Comparison first second := materialized.2.2.2

end Materialized

/-- The complete original root sidecar and its actual retained root/input view at one indexed algebraic input.

The exact getter equalities retain the original nominal parent and actual
certificate. An equivalently valued replacement owner cannot satisfy these
requirements merely from matching samples or polynomial coefficients.
-/
@[expose] def RootInput {channel : CoherentNamed} (original : Sidecar channel) : Type 1 :=
  Σ root : { value : PolynomialRoot.Sidecar channel // original.cached.root? = some value },
    { value : CertifiedName.View channel // root.val.view? = some value }

namespace RootInput

/-- The entire original stored root sidecar, including its nominal owner and numerical cache. -/
@[expose] def root {channel : CoherentNamed} {original : Sidecar channel} (input : RootInput original) :
    PolynomialRoot.Sidecar channel := input.1.val

/-- The retained complete root sidecar is the same original algebraic input's computed root projection. -/
theorem root_eq {channel : CoherentNamed} {original : Sidecar channel} (input : RootInput original) :
    original.cached.root? = some input.root := input.1.property

/-- The exact actual root/input/channel view projected from this original retained root sidecar. -/
@[expose] def view {channel : CoherentNamed} {original : Sidecar channel} (input : RootInput original) :
    CertifiedName.View channel := input.2.val

/-- The retained root/input view is computed from that same complete original root sidecar. -/
theorem view_eq {channel : CoherentNamed} {original : Sidecar channel} (input : RootInput original) :
    input.root.view? = some input.view := input.2.property

/-- Read the original input view through an accessor authenticated at the same complete stored root.

Both root getter identities identify one original nominal parent. Transport
changes only its getter proof; the supplied accessor receives the actual
complete cached root, retained view and unchanged numerical state index.
-/
def stateFromRoot {m : Type → Type} {channel : CoherentNamed} {original : Sidecar channel}
    (input : RootInput original) (root : PolynomialRoot.Sidecar channel) (found : original.cached.root? = some root)
    (read : (actual : PolynomialRoot.Sidecar channel) → actual = root →
      (view : CertifiedName.View channel) → actual.view? = some view → (index : Nat) →
      m {current : WindingOneState view.polynomial view.ambient // current = view.root.stateAt index})
    (index : Nat) : m {current : WindingOneState input.view.polynomial input.view.ambient //
      current = input.view.root.stateAt index} :=
  let same : input.root = root := Option.some.inj (input.root_eq.symm.trans found)
  read input.root same input.view input.view_eq index

end RootInput

/-- Inspect both original root projections and then both original views in input order.

A successful pair retains each complete root owner and its exact getter
equalities. An unavailable projection leaves the original full-difference
fallback to the caller; this inspection performs no root preparation.
-/
@[expose] def rootInputs? {first second : CoherentNamed} (left : Sidecar first) (right : Sidecar second) :
    Option (RootInput left × RootInput right) :=
  match leftFound : left.cached.root? with
  | none => none
  | some leftRoot => match rightFound : right.cached.root? with
      | none => none
      | some rightRoot => match leftViewFound : leftRoot.view? with
          | none => none
          | some leftView => match rightViewFound : rightRoot.view? with
              | none => none
              | some rightView => some
                  (⟨⟨leftRoot, leftFound⟩, ⟨leftView, leftViewFound⟩⟩,
                    ⟨⟨rightRoot, rightFound⟩, ⟨rightView, rightViewFound⟩⟩)

/-- Both authenticated original inputs are exactly the pair returned by the same ordered inspection. -/
theorem rootInputs_eq_some {first second : CoherentNamed} {left : Sidecar first} {right : Sidecar second}
    (firstInput : RootInput left) (secondInput : RootInput right) :
    rootInputs? left right = some (firstInput, secondInput) := by
  unfold rootInputs?
  split
  · rename_i missing
    exact nomatch firstInput.root_eq.symm.trans missing
  · rename_i leftRoot leftFound
    have sameLeft : leftRoot = firstInput.root := Option.some.inj (leftFound.symm.trans firstInput.root_eq)
    subst leftRoot
    split
    · rename_i missing
      exact nomatch secondInput.root_eq.symm.trans missing
    · rename_i rightRoot rightFound
      have sameRight : rightRoot = secondInput.root := Option.some.inj (rightFound.symm.trans secondInput.root_eq)
      subst rightRoot
      split
      · rename_i missing
        exact nomatch firstInput.view_eq.symm.trans missing
      · rename_i leftView leftViewFound
        have sameLeftView : leftView = firstInput.view :=
          Option.some.inj (leftViewFound.symm.trans firstInput.view_eq)
        subst leftView
        split
        · rename_i missing
          exact nomatch secondInput.view_eq.symm.trans missing
        · rename_i rightView rightViewFound
          have sameRightView : rightView = secondInput.view :=
            Option.some.inj (rightViewFound.symm.trans secondInput.view_eq)
          subst rightView
          rfl

/-- An absent original left root leaves the ordered input inspection unavailable. -/
theorem rootInputs_left_absent {first second : CoherentNamed} (left : Sidecar first) (right : Sidecar second)
    (absent : left.cached.root? = none) : rootInputs? left right = none := by
  unfold rootInputs?
  split
  · rfl
  · rename_i root found
    exact nomatch absent.symm.trans found

/-- An absent original right root leaves the ordered input inspection unavailable. -/
theorem rootInputs_right_absent {first second : CoherentNamed} (left : Sidecar first) (right : Sidecar second)
    (absent : right.cached.root? = none) : rootInputs? left right = none := by
  unfold rootInputs?
  split
  · rfl
  · split
    · rfl
    · rename_i leftRoot leftFound rightRoot rightFound
      exact nomatch absent.symm.trans rightFound

/-- An unavailable view of the same actual left root preserves the original fallback route. -/
theorem rootInputs_left_view_absent {first second : CoherentNamed} (left : Sidecar first) (right : Sidecar second)
    (root : PolynomialRoot.Sidecar first) (found : left.cached.root? = some root) (absent : root.view? = none) :
    rootInputs? left right = none := by
  unfold rootInputs?
  split
  · rfl
  · rename_i actual actualFound
    have same : actual = root := Option.some.inj (actualFound.symm.trans found)
    subst actual
    split
    · rfl
    · split
      · rfl
      · rename_i view viewFound
        exact nomatch absent.symm.trans viewFound

/-- An unavailable view of the same actual right root preserves the original fallback route. -/
theorem rootInputs_right_view_absent {first second : CoherentNamed} (left : Sidecar first) (right : Sidecar second)
    (root : PolynomialRoot.Sidecar second) (found : right.cached.root? = some root) (absent : root.view? = none) :
    rootInputs? left right = none := by
  unfold rootInputs?
  split
  · rfl
  · split
    · rfl
    · rename_i leftRoot leftFound actual actualFound
      have same : actual = root := Option.some.inj (actualFound.symm.trans found)
      subst actual
      split
      · rfl
      · split
        · rfl
        · rename_i view viewFound
          exact nomatch absent.symm.trans viewFound

/-- One original-root result with both same complete parents and its actual checked-initial procedure request. -/
@[expose] def Intrinsic {first second : CoherentNamed} (left : Sidecar first) (right : Sidecar second)
    (firstStart secondStart : Nat) : Type 1 :=
  Σ first : RootInput left, Σ second : RootInput right,
    { value : CommonSource.PreparedComparison first.view.input second.view.input
        first.view.root second.view.root firstStart secondStart //
      value = CommonSource.prepareComparison first.view.input second.view.input
        first.view.root second.view.root firstStart secondStart value.inspectInitial value.inspectLocal }

namespace Intrinsic

/-- The same retained actual left numerical root, original input and original-channel link. -/
@[expose] def left {first second : CoherentNamed} {originalLeft : Sidecar first} {originalRight : Sidecar second}
    {firstStart secondStart : Nat} (intrinsic : Intrinsic originalLeft originalRight firstStart secondStart) :
    RootInput originalLeft := intrinsic.1

/-- The same retained actual right numerical root, original input and original-channel link. -/
@[expose] def right {first second : CoherentNamed} {originalLeft : Sidecar first} {originalRight : Sidecar second}
    {firstStart secondStart : Nat} (intrinsic : Intrinsic originalLeft originalRight firstStart secondStart) :
    RootInput originalRight := intrinsic.2.1

/-- The complete once-computed common source, assignments and actual outcome on those same original root caches. -/
@[expose] def prepared {first second : CoherentNamed} {originalLeft : Sidecar first} {originalRight : Sidecar second}
    {firstStart secondStart : Nat} (intrinsic : Intrinsic originalLeft originalRight firstStart secondStart) :
    CommonSource.PreparedComparison intrinsic.left.view.input intrinsic.right.view.input
      intrinsic.left.view.root intrinsic.right.view.root firstStart secondStart := intrinsic.2.2.val

/-- The retained preparation is the actual procedure on both original views, starts and stored request. -/
theorem prepared_eq {first second : CoherentNamed} {originalLeft : Sidecar first} {originalRight : Sidecar second}
    {firstStart secondStart : Nat} (intrinsic : Intrinsic originalLeft originalRight firstStart secondStart) :
    intrinsic.prepared = CommonSource.prepareComparison
      intrinsic.left.view.input intrinsic.right.view.input intrinsic.left.view.root intrinsic.right.view.root
      firstStart secondStart intrinsic.prepared.inspectInitial intrinsic.prepared.inspectLocal := intrinsic.2.2.property

/-- Read exact zero or the actual paid pair separation and comparison together without difference elimination.

Every root request, assignment, gap and sample bound belongs to the same
stored common-source result. Only the original channel links are composed;
no root producer, refiner or difference annihilator is invoked here.
-/
@[expose] def result {first second : CoherentNamed} {originalLeft : Sidecar first} {originalRight : Sidecar second}
    {firstStart secondStart : Nat} (intrinsic : Intrinsic originalLeft originalRight firstStart secondStart)
    (bound : Option (Difference.Request first second) := none) :
    Division.Prepared.Decision (Difference.difference first second) × Comparison first second :=
  let left := intrinsic.left.view
  let right := intrinsic.right.view
  match intrinsic.prepared.comparison with
  | .equal equivalent =>
      let original := left.transportComparison right equivalent
      ⟨.excluded (Difference.difference_zero_of_equivalent first second original.symm bound), .equal original⟩
  | .distinct separation =>
      let link := Difference.respects first left.root.value second right.root.value
        left.equivalent right.equivalent
      let prepared := separation.prepareDifference.transport link.symm
      ⟨.prepared prepared, .distinct prepared (fun ⟨equivalent⟩ =>
        separation.rejects (left.equivalent.symm.trans (equivalent.trans right.equivalent)))⟩

/-- The absent bound preserves the complete original branch/result procedure on both retained root views. -/
theorem result_none {first second : CoherentNamed} {originalLeft : Sidecar first} {originalRight : Sidecar second}
    {firstStart secondStart : Nat} (intrinsic : Intrinsic originalLeft originalRight firstStart secondStart) :
    intrinsic.result none =
      (let left := intrinsic.left.view
       let right := intrinsic.right.view
       match intrinsic.prepared.comparison with
       | .equal equivalent =>
           let original := left.transportComparison right equivalent
           ⟨.excluded (Difference.difference_zero_of_equivalent first second original.symm), .equal original⟩
       | .distinct separation =>
           let link := Difference.respects first left.root.value second right.root.value
             left.equivalent right.equivalent
           let prepared := separation.prepareDifference.transport link.symm
           ⟨.prepared prepared, .distinct prepared (fun ⟨equivalent⟩ =>
             separation.rejects (left.equivalent.symm.trans (equivalent.trans right.equivalent)))⟩) := by
  unfold result
  rfl

/-- A bound changes discrepancy payment while retaining the original named comparison and both input links. -/
theorem result_comparison {first second : CoherentNamed} {originalLeft : Sidecar first}
    {originalRight : Sidecar second} {firstStart secondStart : Nat}
    (intrinsic : Intrinsic originalLeft originalRight firstStart secondStart)
    (bound : Option (Difference.Request first second)) :
    (intrinsic.result bound).2 = (intrinsic.result none).2 := by
  unfold result
  cases intrinsic.prepared.comparison <;> rfl

end Intrinsic

end Compared

/-- Compute the original full difference, exact decision and checked comparison once at an explicit boundary. -/
@[expose] def compareMaterialized {first second : CoherentNamed} (left : Sidecar first) (right : Sidecar second) :
    Compared.Materialized left right :=
  let difference := right.sub left
  let resolved := difference.resolve
  let decision := resolved.decision
  let comparison := Comparison.ofDecision first second decision
  ⟨⟨difference, rfl⟩, ⟨resolved, rfl⟩, ⟨decision, rfl⟩, comparison⟩

set_option genInjectivity false in
/-- Both original algebraic inputs and their intrinsic root comparison or complete fallback cache.

The stored input records retain actual runtime owner caches at the original
indices. Intrinsic requests use one stored common-source result. The memoized
full difference is forced only by explicit materialization; its complete
result is linked to those exact same retained inputs.
-/
structure Compared {first second : CoherentNamed} (originalLeft : Sidecar first) (originalRight : Sidecar second)
    (firstStart secondStart : Nat := 0) where
  /-- The complete actual left input retained for cache reads and explicit later materialization. -/
  left : Sidecar first
  /-- The stored complete left record is the original indexed input. -/
  left_eq : left = originalLeft
  /-- The complete actual right input retained for cache reads and explicit later materialization. -/
  right : Sidecar second
  /-- The stored complete right record is the original indexed input. -/
  right_eq : right = originalRight
  /-- The actual intrinsic original-root result or the already complete original difference fallback. -/
  cache : Compared.Intrinsic originalLeft originalRight firstStart secondStart ⊕
    Compared.Materialized originalLeft originalRight
  /-- The actual finite bound-inspection request used to build this retained original difference decision. -/
  inspectBound : Bool
  /-- The retained original difference bound and finite coverage check for both requested raw-source floors. -/
  bound : Option (Difference.Request first second)
  /-- The stored request result is computed from the same actual retained root views or the unchanged full fallback. -/
  bound_computed : bound = if inspectBound then
    cache.elim (fun intrinsic =>
      intrinsic.left.view.differenceRequest? intrinsic.right.view firstStart secondStart) (fun _ => none)
    else none
  /-- The exact zero-or-preparation decision consumed by requests at the unchanged original difference. -/
  decision : Division.Prepared.Decision (Difference.difference first second)
  /-- The same retained branch cache computes this exact stored decision. -/
  decision_computed : decision = cache.elim (fun intrinsic => (intrinsic.result bound).1) Compared.Materialized.decision
  /-- The checked outcome between both unchanged original input channels. -/
  comparison : Comparison first second
  /-- The chosen checked outcome is read from the same retained branch and decision. -/
  comparison_eq : comparison = cache.elim
    (fun intrinsic => (intrinsic.result bound).2) Compared.Materialized.comparison
  /-- The single memoized explicit full-difference computation on these same original inputs. -/
  materialization : Thunk (Compared.Materialized originalLeft originalRight)
  /-- Forcing the retained thunk gives the complete original result on those same exact indexed inputs. -/
  materialization_eq : materialization.get = compareMaterialized originalLeft originalRight

constructive_injectivity Compared

namespace Compared

/-- Force the stored full-difference thunk, reusing its complete result on every later explicit materialization. -/
@[expose] def materialize {first second : CoherentNamed} {left : Sidecar first} {right : Sidecar second}
    {firstStart secondStart : Nat} (compared : Compared left right firstStart secondStart) : Materialized left right :=
  compared.materialization.get

/-- Explicit materialization retains the complete original fallback result and both stored defining equalities. -/
theorem materialize_eq {first second : CoherentNamed} {left : Sidecar first} {right : Sidecar second}
    {firstStart secondStart : Nat} (compared : Compared left right firstStart secondStart) :
    compared.materialize = compareMaterialized left right :=
  compared.materialization_eq

/-- Explicit materialization computes its difference from the same two stored complete runtime inputs. -/
theorem materialize_difference {first second : CoherentNamed} {originalLeft : Sidecar first}
    {originalRight : Sidecar second} {firstStart secondStart : Nat}
    (compared : Compared originalLeft originalRight firstStart secondStart) :
    compared.materialize.difference = compared.right.sub compared.left :=
  compared.materialize.difference_eq.trans
    ((congrArg (fun (right : Sidecar second) => right.sub originalLeft) compared.right_eq.symm).trans
      (congrArg (fun (left : Sidecar first) => compared.right.sub left) compared.left_eq.symm))

/-- Retain one exact original root result and defer the full difference at both same original input caches. -/
@[expose] def ofIntrinsic {first second : CoherentNamed} (left : Sidecar first) (right : Sidecar second)
    (firstStart secondStart : Nat) (intrinsic : Intrinsic left right firstStart secondStart)
    (inspectBound : Bool := false) : Compared left right firstStart secondStart :=
  let bound := if inspectBound then
    intrinsic.left.view.differenceRequest? intrinsic.right.view firstStart secondStart else none
  let result := intrinsic.result bound
  let materialization := Thunk.mk fun _ => compareMaterialized left right
  ⟨left, rfl, right, rfl, .inl intrinsic, inspectBound, bound, rfl,
    result.1, rfl, result.2, rfl, materialization, rfl⟩

/-- Disabling bound inspection retains every original result field and deferred full-difference procedure. -/
theorem ofIntrinsic_false {first second : CoherentNamed} (left : Sidecar first) (right : Sidecar second)
    (firstStart secondStart : Nat) (intrinsic : Intrinsic left right firstStart secondStart) :
    ofIntrinsic left right firstStart secondStart intrinsic false =
      (let result := intrinsic.result none
       let materialization := Thunk.mk fun _ => compareMaterialized left right
       ⟨left, rfl, right, rfl, .inl intrinsic, false, none, rfl,
         result.1, rfl, result.2, rfl, materialization, rfl⟩) := by
  unfold ofIntrinsic
  rfl

/-- The covered request stores the literal bound computed from these same two original root views. -/
theorem ofIntrinsic_bound {first second : CoherentNamed} (left : Sidecar first) (right : Sidecar second)
    (firstStart secondStart : Nat) (intrinsic : Intrinsic left right firstStart secondStart) :
    (ofIntrinsic left right firstStart secondStart intrinsic true).bound =
      intrinsic.left.view.differenceRequest? intrinsic.right.view firstStart secondStart := by
  unfold ofIntrinsic
  rfl

/-- The retained decision consumes that same stored bound request once and is reused by direct projection. -/
theorem ofIntrinsic_decision {first second : CoherentNamed} (left : Sidecar first) (right : Sidecar second)
    (firstStart secondStart : Nat) (intrinsic : Intrinsic left right firstStart secondStart) (inspectBound : Bool) :
    (ofIntrinsic left right firstStart secondStart intrinsic inspectBound).decision =
      (intrinsic.result (ofIntrinsic left right firstStart secondStart intrinsic inspectBound).bound).1 := by
  unfold ofIntrinsic
  rfl

/-- Compute the existing complete fallback once and retain that same result inside its materialization thunk. -/
@[expose] def fallback {first second : CoherentNamed} (left : Sidecar first) (right : Sidecar second)
    (firstStart secondStart : Nat) (inspectBound : Bool := false) : Compared left right firstStart secondStart :=
  let materialized := compareMaterialized left right
  ⟨left, rfl, right, rfl, .inr materialized, inspectBound, none, by cases inspectBound <;> rfl,
    materialized.decision, rfl,
    materialized.comparison, rfl, Thunk.pure materialized, rfl⟩

end Compared

/-- The numerical difference reads both same original source caches and the exact negative unit.

It presents the original stateful difference channel without computing a
new polynomial annihilator. This is the same certified finite geometric
arithmetic used by the complete algebraic construction.
-/
@[expose] def differenceSource {first second : CoherentNamed} (left : Sidecar first) (right : Sidecar second) :=
  right.residual.source.add ((Geometric.GeometricApproximation.exact (-1)).mul left.residual.source)

set_option genInjectivity false in
/-- The actual signed difference prefixes, final program and original-channel comparison.

The negative-unit prefix and final ordered sum are computed once from both
original residual programs. The comparison consumes those same stored targets.
-/
structure DifferenceProgram {first second : CoherentNamed} (left : Sidecar first) (right : Sidecar second) where
  /-- The same exact negative-unit geometric program used by the original difference. -/
  unit : Geometric.GeometricApproximation
  /-- The retained unit program is the complete original exact negative unit. -/
  unit_eq : unit = Geometric.GeometricApproximation.exact (-1)
  /-- The actual product of that same unit and the original first input program. -/
  negative : Geometric.GeometricApproximation
  /-- The retained negative prefix is computed from the same actual stored unit and input. -/
  negative_eq : negative = unit.mul left.residual.source
  /-- The actual second-plus-negative-first geometric program. -/
  source : Geometric.GeometricApproximation
  /-- The retained output is the complete original difference program in its same subtraction order. -/
  source_eq : source = left.differenceSource right
  /-- The original difference channel realizes this same retained numerical output. -/
  equivalent : NamedEquivalent (Difference.difference first second).name source.toApproximation.toNamed

constructive_injectivity DifferenceProgram

/-- Compute the original signed difference programs and compare those same retained targets. -/
@[expose] def differenceProgram {first second : CoherentNamed} (left : Sidecar first) (right : Sidecar second) :
    DifferenceProgram left right :=
  let unit := Geometric.GeometricApproximation.exact (-1)
  let negative := unit.mul left.residual.source
  let source := right.residual.source.add negative
  let negativeEquivalent := (Arithmetic.Mul.coherentMul_minus_one_left first).symm.trans
    (Geometric.Coherent.Comparison.mul_agreesWith (CoherentNamed.Coherence.exact (-1)) first unit
      left.residual.source negative
      (Geometric.Coherent.Comparison.exact_agreesWith (-1) unit (fun _ => rfl))
      left.residual.equivalent
      (fun _ => rfl))
  let equivalent := Geometric.Coherent.Comparison.add_agreesWith second (CoherentNamed.neg first)
    right.residual.source negative source right.residual.equivalent negativeEquivalent (fun _ => rfl)
  ⟨unit, rfl, negative, rfl, source, rfl, equivalent⟩

/-- The computed numerical difference agrees with the unchanged original stateful difference channel. -/
def differenceSource_equivalent {first second : CoherentNamed} (left : Sidecar first) (right : Sidecar second) :
    NamedEquivalent (Difference.difference first second).name
      (left.differenceSource right).toApproximation.toNamed := by
  let program := left.differenceProgram right
  have equivalent := program.equivalent
  rewrite [program.source_eq] at equivalent
  exact equivalent

set_option genInjectivity false in
/-- Typed separation or current inconclusivity on the same retained original difference observation. -/
inductive InitialOutcome {first second : CoherentNamed}
    (source : Geometric.GeometricApproximation)
    (equivalent : NamedEquivalent (Difference.difference first second).name source.toApproximation.toNamed)
    (initial : Geometric.Preparation.Observation source (Difference.difference first second) equivalent) where
  /-- The stored original difference ball is separated and supplies this exact quantitative distinctness result. -/
  | distinct (separated : Geometric.Preparation.Separated initial.ball)
      (prepared : Division.Prepared (Difference.difference first second))
      (prepared_eq : prepared = Geometric.Preparation.fromBall source
        (Difference.difference first second) equivalent initial.state initial.ball initial.readback separated)
      (computed : initial.outcome = .prepared separated prepared prepared_eq)
      (different : ¬ Nonempty (NamedEquivalent first.name second.name))
  /-- The same finite sufficient test fails; both original caches and this actual unresolved ball remain retained. -/
  | inconclusive (failed : ¬ Geometric.Preparation.Separated initial.ball)
      (computed : initial.outcome = .inconclusive failed)

constructive_injectivity InitialOutcome

set_option genInjectivity false in
/-- Both original algebraic inputs and one computed geometric difference observation with its typed finite outcome. -/
structure InitialComparison {first second : CoherentNamed}
    (originalLeft : Sidecar first) (originalRight : Sidecar second) where
  /-- The same actual original left owner and all its retained construction caches. -/
  left : Sidecar first
  /-- The stored left data is the original supplied sidecar. -/
  left_eq : left = originalLeft
  /-- The same actual original right owner and all its retained construction caches. -/
  right : Sidecar second
  /-- The stored right data is the original supplied sidecar. -/
  right_eq : right = originalRight
  /-- The actual computed geometric difference program consumes those same stored original inputs. -/
  source : Geometric.GeometricApproximation
  /-- The stored difference program is computed from those same actual sidecars. -/
  source_eq : source = left.differenceSource right
  /-- The actual original difference channel agrees with this same stored numerical program. -/
  equivalent : NamedEquivalent (Difference.difference first second).name source.toApproximation.toNamed
  /-- The stored original-channel comparison is the computed comparison of those same input programs. -/
  equivalent_eq : equivalent = source_eq.symm ▸ left.differenceSource_equivalent right
  /-- The once read original difference state and ball consume that same stored program and comparison. -/
  initial : Geometric.Preparation.Observation source (Difference.difference first second) equivalent
  /-- This same stored observation supplies a quantitative distinctness certificate or current inconclusivity. -/
  outcome : InitialOutcome source equivalent initial

constructive_injectivity InitialComparison

/-- Inspect the actual original numerical difference once for sufficient finite separation.

Success certifies distinctness at both original channels. Inconclusivity
retains the actual state, readback, ball and failed sufficient test, and
asserts no equality or zero. The complete algebraic classifier is separate.
-/
def compareInitial {first second : CoherentNamed} (left : Sidecar first) (right : Sidecar second) :
    InitialComparison left right :=
  let program := left.differenceProgram right
  let source := program.source
  let equivalent := program.equivalent
  let initial := Geometric.Preparation.inspectInitial source (Difference.difference first second) equivalent
  let outcome := match computed : initial.outcome with
    | .prepared separated prepared preparedEq =>
        InitialOutcome.distinct separated prepared preparedEq computed (fun ⟨equivalent⟩ =>
          Division.Obstruction.Zero.ZeroIdentity.incompatible_prepared
            (Difference.difference_zero_of_equivalent first second equivalent.symm) prepared)
    | .inconclusive failed => InitialOutcome.inconclusive failed computed
  ⟨left, rfl, right, rfl, source, program.source_eq, equivalent, rfl, initial, outcome⟩

/-- Compare actual intrinsic root owners before constructing the complete algebraic difference.

Both original sidecars remain indexed and stored inputs. When their original
retained roots are available, the same checked initial-nesting request may
reuse their cached paid refinements. The same optional local request can
consume actual floor separation or a checked constant/affine cofactor region;
otherwise the original common-source partition pays the requested floors. The stored result supplies every later
original-channel request. Disabling initial inspection keeps the original
whole partition procedure when local inspection is also disabled. The local
request defaults to the same supplied initial-inspection bit. The separately retained bound-inspection request defaults
to that bit as well and can pay a discrepancy request from both actual initial boxes. Disabling it preserves the
original discrepancy comparison; unavailable whole-channel identities and tighter tolerances use the same original
fallback. When no intrinsic root view is available,
the existing full-difference classifier is computed and retained once. Calling
`materialize` explicitly obtains the complete original difference in either case.
-/
@[expose] def compare {first second : CoherentNamed} (left : Sidecar first) (right : Sidecar second)
    (firstStart secondStart : Nat := 0) (inspectInitial : Bool := true) (inspectLocal : Bool := inspectInitial)
    (inspectBound : Bool := inspectInitial) :
    Compared left right firstStart secondStart :=
  match Compared.rootInputs? left right with
  | none => Compared.fallback left right firstStart secondStart inspectBound
  | some inputs =>
      let first := inputs.1
      let second := inputs.2
      let prepared := CommonSource.prepareComparison
        first.view.input second.view.input first.view.root second.view.root firstStart secondStart
        inspectInitial inspectLocal
      Compared.ofIntrinsic left right firstStart secondStart ⟨first, second, ⟨prepared, rfl⟩⟩ inspectBound

/-- A retained original intrinsic preparation gives the complete ordinary comparison at its same request bits.

Both input getter identities determine the same ordered inspection. The
complete retained preparation replaces only its equal default computation;
decision, comparison, bound inspection and deferred full materialization
remain the original constructors at those exact input owners and floors.
-/
theorem compare_of_intrinsic {first second : CoherentNamed} (left : Sidecar first) (right : Sidecar second)
    (firstStart secondStart : Nat) (intrinsic : Compared.Intrinsic left right firstStart secondStart)
    (inspectBound : Bool) :
    left.compare right firstStart secondStart
      intrinsic.prepared.inspectInitial intrinsic.prepared.inspectLocal inspectBound =
      Compared.ofIntrinsic left right firstStart secondStart intrinsic inspectBound := by
  rcases intrinsic with ⟨firstInput, secondInput, ⟨prepared, same⟩⟩
  unfold compare
  rewrite [Compared.rootInputs_eq_some firstInput secondInput]
  dsimp only [Compared.Intrinsic.prepared, Compared.Intrinsic.left, Compared.Intrinsic.right]
  exact congrArg (fun retained : {value : CommonSource.PreparedComparison firstInput.view.input secondInput.view.input
      firstInput.view.root secondInput.view.root firstStart secondStart //
      value = CommonSource.prepareComparison firstInput.view.input secondInput.view.input
        firstInput.view.root secondInput.view.root firstStart secondStart value.inspectInitial value.inspectLocal} =>
    Compared.ofIntrinsic left right firstStart secondStart ⟨firstInput, secondInput, retained⟩ inspectBound)
    (Subtype.ext same.symm)

/-- Disabling initial inspection retains the entire original root-view discrimination and common-source computation. -/
theorem compare_default {first second : CoherentNamed} (left : Sidecar first) (right : Sidecar second)
    (firstStart secondStart : Nat) :
    left.compare right firstStart secondStart false =
    (match leftFound : left.cached.root? with
      | none => Compared.fallback left right firstStart secondStart
      | some leftRoot => match rightFound : right.cached.root? with
          | none => Compared.fallback left right firstStart secondStart
          | some rightRoot => match leftViewFound : leftRoot.view? with
              | none => Compared.fallback left right firstStart secondStart
              | some leftView => match rightViewFound : rightRoot.view? with
                  | none => Compared.fallback left right firstStart secondStart
                  | some rightView =>
                      let first : Compared.RootInput left := ⟨⟨leftRoot, leftFound⟩, ⟨leftView, leftViewFound⟩⟩
                      let second : Compared.RootInput right := ⟨⟨rightRoot, rightFound⟩, ⟨rightView, rightViewFound⟩⟩
                      let prepared := CommonSource.prepareComparison
                        first.view.input second.view.input first.view.root second.view.root firstStart secondStart
                      Compared.ofIntrinsic left right firstStart secondStart ⟨first, second, ⟨prepared, rfl⟩⟩) := by
  symm
  unfold compare
  split
  · rename_i missing
    rewrite [Compared.rootInputs_left_absent left right missing]
    rfl
  · rename_i leftRoot leftFound
    split
    · rename_i missing
      rewrite [Compared.rootInputs_right_absent left right missing]
      rfl
    · rename_i rightRoot rightFound
      split
      · rename_i missing
        rewrite [Compared.rootInputs_left_view_absent left right leftRoot leftFound missing]
        rfl
      · rename_i leftView leftViewFound
        split
        · rename_i missing
          rewrite [Compared.rootInputs_right_view_absent left right rightRoot rightFound missing]
          rfl
        · rename_i rightView rightViewFound
          rewrite [Compared.rootInputs_eq_some
            (⟨⟨leftRoot, leftFound⟩, ⟨leftView, leftViewFound⟩⟩ : Compared.RootInput left)
            (⟨⟨rightRoot, rightFound⟩, ⟨rightView, rightViewFound⟩⟩ : Compared.RootInput right)]
          rfl

/-- An unavailable original left root projection retains the complete original fallback result as its branch cache. -/
theorem compare_cache_of_left_absent {first second : CoherentNamed} (left : Sidecar first) (right : Sidecar second)
    (firstStart secondStart : Nat) (absent : left.cached.root? = none) :
    (left.compare right firstStart secondStart).cache = .inr (compareMaterialized left right) := by
  unfold compare
  rewrite [Compared.rootInputs_left_absent left right absent]
  rfl

/-- An unavailable original right root projection retains the complete original fallback result as its branch cache. -/
theorem compare_cache_of_right_absent {first second : CoherentNamed} (left : Sidecar first) (right : Sidecar second)
    (firstStart secondStart : Nat) (absent : right.cached.root? = none) :
    (left.compare right firstStart secondStart).cache = .inr (compareMaterialized left right) := by
  unfold compare
  rewrite [Compared.rootInputs_right_absent left right absent]
  rfl

end Sidecar

end Purelib.Approximation.Gaussian.Provenance.Algebraic

end
