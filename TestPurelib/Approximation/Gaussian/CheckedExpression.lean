module

import Purelib.System.IO
import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Construction
import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Acquisition
import Purelib.Approximation.Gaussian.Division.Search.State
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Data.Gaussian.Norm.Basic
public meta import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Acquisition
public meta import Purelib.System.IO
meta import Purelib.Approximation.Gaussian.Division.Search.State
meta import Purelib.Approximation.Gaussian.Name.Coherent
meta import Purelib.Data.Gaussian.Field

/-! # Complete admitted checked expressions, first zero occurrences and retained admission retries -/

namespace TestPurelib.Approximation.Gaussian.CheckedExpression

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Acquisition.Expression
open Purelib.Approximation.Gaussian.Acquisition.Expression.Checked
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Norm.Basic (normSq)

example {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (admitted : Admitted environment expression) : admitted.run.Resolved := admitted.complete

example {arity : Nat} {environment : Fin arity → Annotated} {expression : Basic.Expr arity}
    (cached : Base.Cached environment expression) (admissions : Base.Admissions cached.compiled.bindings) :
    (Admitted.inverse (Admitted.base cached admissions)).run.Resolved :=
  (Admitted.inverse (Admitted.base cached admissions)).complete

example {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (completed : Completed environment expression)
    (state : Name.Coherent.Refinement.State completed.channel)
    (numerator : CoherentNamed) (threshold : Purelib.Data.Rat.Fraction.Rational) (positive : 0 < threshold) :
    (completed.finish.acquire state numerator threshold positive).1.route = .cached ∧
      (completed.finish.acquire state numerator threshold positive).1.next.state = state :=
  completed.finish.acquire_cached state numerator threshold positive

example {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (finished : Finished environment expression) :
    (⟨⟨finished.completed, finished.decision⟩, finished.resolved⟩ :
      Σ result : (retained : Construction.Result environment expression) ×
          Division.Prepared.Decision retained.channel,
        Option (Construction.Result.Resolution result.1 result.2)) = finished.source.resolve :=
  finished.resolution_eq

example {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (finished : Finished environment expression)
    (receipt : Construction.Result.Resolution finished.completed finished.decision) :
    receipt.resolved = receipt.completed.sidecar.resolve := receipt.resolved_eq

example {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (finished : Finished environment expression)
    (receipt : Construction.Result.Resolution finished.completed finished.decision) :
    finished.decision = (receipt.channel_eq ▸ receipt.resolved.decision) := receipt.decision_eq

example {channel : CoherentNamed} (root : PolynomialRoot.Sidecar channel) :
    let environment : Fin 1 → Annotated := fun _ => Annotated.polynomialRoot root
    (Admitted.inverse (Admitted.atom environment ⟨0, by decide⟩ (Algebraic.Sidecar.ofRoot root))).run.Resolved :=
  (Admitted.inverse (Admitted.atom _ _ _)).complete

/-- Optional admissions retain the original pair shape and both same-channel entry types. -/
private theorem slots_shape {arity : Nat} {environment : Fin arity → Annotated}
    (first : Basic.Binding environment) (remaining : List (Basic.Binding environment)) :
    Base.Slots (first :: remaining) =
      (Option (Algebraic.Sidecar first.annotation.channel) × Base.Slots remaining) := rfl

/-- Complete admissions retain the original pair shape without raising their entry universe. -/
private theorem admissions_shape {arity : Nat} {environment : Fin arity → Annotated}
    (first : Basic.Binding environment) (remaining : List (Basic.Binding environment)) :
    Base.Admissions (first :: remaining) =
      (Algebraic.Sidecar first.annotation.channel × Base.Admissions remaining) := rfl

/-- Partial power inspections retain the exact original dependent pair and its original stored tail. -/
private theorem powers_shape {arity : Nat} {environment : Fin arity → Annotated}
    (first : Basic.Binding environment) (remaining : List (Basic.Binding environment)) :
    Base.Powers (first :: remaining) =
      (Option (Sigma fun sidecar : Algebraic.Sidecar first.annotation.channel => Base.PowerInspection sidecar) ×
        Base.Powers remaining) := rfl

/-- A successor slot lookup reduces to the same retained tail at the original bounded index. -/
private theorem slots_get_succ {arity : Nat} {environment : Fin arity → Annotated}
    (first : Basic.Binding environment) (remaining : List (Basic.Binding environment))
    (slots : Base.Slots (first :: remaining)) (index : Fin remaining.length) :
    Base.Slots.get (first :: remaining) slots index.succ = Base.Slots.get remaining slots.2 index := rfl

/-- A successor lookup returns the same optional original sidecar and its literal retained inspection. -/
private theorem powers_get_succ {arity : Nat} {environment : Fin arity → Annotated}
    (first : Basic.Binding environment) (remaining : List (Basic.Binding environment))
    (powers : Base.Powers (first :: remaining)) (index : Fin remaining.length) :
    Base.Powers.get (first :: remaining) powers index.succ = Base.Powers.get remaining powers.2 index := rfl

/-- Supplying the head admission retains the literal original optional-entry tail through ordinary imports. -/
private theorem slots_supply_head_tail {arity : Nat} {environment : Fin arity → Annotated}
    (first : Basic.Binding environment) (remaining : List (Basic.Binding environment))
    (slots : Base.Slots (first :: remaining)) (sidecar : Algebraic.Sidecar first.annotation.channel) :
    (Base.Slots.supply (first :: remaining) slots 0 sidecar).2 = slots.2 := rfl

/-- Supplying the head inspection retains the same complete original inspection tail without recomputing it. -/
private theorem powers_supply_head_tail {arity : Nat} {environment : Fin arity → Annotated}
    (first : Basic.Binding environment) (remaining : List (Basic.Binding environment))
    (powers : Base.Powers (first :: remaining)) (sidecar : Algebraic.Sidecar first.annotation.channel)
    (inspection : Base.PowerInspection sidecar) :
    (Base.Powers.supply (first :: remaining) powers 0 sidecar inspection).2 = powers.2 := rfl

/-- Ordinary clients recover every supplied certificate from the same materialized admission bank. -/
private theorem admissions_ofFunction_get {arity : Nat} {environment : Fin arity → Annotated}
    (bindings : List (Basic.Binding environment))
    (evidence : (index : Fin bindings.length) →
      Algebraic.Sidecar (Basic.Binding.read bindings index).annotation.channel) (index : Fin bindings.length) :
    Base.Admissions.get bindings (Base.Admissions.ofFunction bindings evidence) index = evidence index :=
  Base.Admissions.get_ofFunction bindings evidence index

/-- The original two scalar channels deliberately omit their annotation evidence. -/
private meta def opaqueInputs (index : Fin 2) : Annotated :=
  Annotated.opaque (CoherentNamed.Coherence.exact (if index.val = 0 then 2 else 3))

/-- New intrinsic evidence is linked to those same original numerical atom channels. -/
private meta def intrinsicInputs (index : Fin 2) : Algebraic.Sidecar (opaqueInputs index).channel :=
  Algebraic.Sidecar.ofRational (RationalSidecar.exact (if index.val = 0 then 2 else 3))

/-- Execute the fragment and verify the first invalid reciprocal is retained through original ordered contexts. -/
public meta def checkOccurrences : IO Unit := do
  System.IO.println "occurrences: begin"
  (← IO.getStdout).flush
  let empty : Fin 0 → Annotated := Fin.elim0
  let two : Expr 0 := Expr.rational 2
  let firstZero : Expr 0 := .inverse (Expr.rational 0)
  let laterZero : Expr 0 := .inverse (.sub two two)
  match Expr.attempt empty (.add firstZero laterZero) with
  | .invalid first =>
      match first.denominator.1 with
      | .base (.rational value) =>
          unless value = 0 do
            throw (IO.userError "the first invalid reciprocal was replaced by a later zero occurrence")
      | _ => throw (IO.userError "the original first invalid reciprocal source syntax was discarded")
      let denominator := first.denominator.2.1.materialize
      unless first.prefix.isEmpty ∧ denominator.sidecar.residual.source.sample 3 = 0 do
        throw (IO.userError "the first invalid reciprocal lost its original zero denominator or evaluation position")
  | _ => throw (IO.userError "checked evaluation did not report the original first invalid left reciprocal")
  System.IO.println "occurrences: first zero retained"
  (← IO.getStdout).flush
  match Expr.attempt empty (.add (.pow two 3) firstZero) with
  | .invalid first =>
      match first.prefix with
      | [retained] =>
          let materialized := retained.2.materialize
          unless materialized.sidecar.residual.source.sample 4 = 8 do
            throw (IO.userError "first invalid right reciprocal lost its completed original left sibling")
      | _ => throw (IO.userError "first invalid right reciprocal lost its exact completed prefix")
  | _ => throw (IO.userError "checked evaluation did not retain the productive prefix of its first invalid reciprocal")
  System.IO.println "occurrences: powered prefix retained"
  (← IO.getStdout).flush
  let arithmetic : Expr 0 := .inverse (.conj (.sub (.mul (.neg two) (Expr.rational 3)) (Expr.rational 1)))
  System.IO.println "occurrences: checking arithmetic"
  (← IO.getStdout).flush
  match arithmetic.check empty with
  | .finished result =>
      match result.resolved with
      | some receipt =>
          match receipt.resolved with
          | .scalar reading _ =>
              unless reading.value = (-7 : Canonical)⁻¹ do
                throw (IO.userError "finished scalar resolution lost the original arithmetic coefficient")
          | _ => throw (IO.userError "finished scalar result discarded its actual exact reading construction")
      | none => pure ()
      unless result.decision.isPrepared do
        throw (IO.userError "the finite checked fragment failed its computed final nonzero decision")
      let materialized := result.materialize
      match materialized.sidecar.scalar? with
      | some reading =>
          unless reading.value = (-7 : Canonical)⁻¹ do
            throw (IO.userError "the actual materialized scalar result changed its original exact coefficient")
      | none => throw (IO.userError "the actual materialized scalar result lost its retained exact reading")
      unless materialized.sidecar.residual.source.sample 5 = (-7 : Canonical)⁻¹ do
        throw (IO.userError "checked closure did not preserve original arithmetic and reciprocal sample programs")
      System.IO.println "occurrences: arithmetic finished"
      (← IO.getStdout).flush
      let state := (Division.Search.State.initial result.source.channel).advance.advance
      System.IO.println "occurrences: state advanced"
      (← IO.getStdout).flush
      let first := result.acquire state (CoherentNamed.Coherence.exact 1) (1 / 16) (by decide)
      have positiveSecond : (0 : Purelib.Data.Rat.Fraction.Rational) < 1 / 32 :=
        Purelib.Data.Rat.Fraction.Order.Field.div_pos_direct (by decide)
          (Purelib.Data.Rat.Fraction.Cast.Order.natCast_pos_direct (n := 32) (by decide))
      let retainedInput : Division.Acquisition.State.Input result.source.channel := first.1.next
      let second := Division.Acquisition.Dispatch.acquire (channel := result.source.channel)
        (CoherentNamed.Coherence.exact 3) retainedInput (1 / 32) positiveSecond
      unless first.1.route = .cached ∧ second.1.route = .cached ∧
          first.1.next.state.nextIndex = 2 ∧ second.1.next.state.nextIndex = 2 do
        throw (IO.userError "production retries recomputed a completed checked-expression decision")
  | _ => throw (IO.userError "the admitted scalar checked fragment did not finish")

/-- Supply two original atom admissions and retain the reciprocal prefix across the second suspension. -/
public meta def checkRetries : IO Unit := do
  System.IO.println "retries: begin"
  (← IO.getStdout).flush
  let expression : Expr 2 := .add (.inverse (Expr.atom (0 : Fin 2))) (.inverse (Expr.atom (1 : Fin 2)))
  match expression.attempt opaqueInputs with
  | .pending first =>
      unless first.depth = 2 ∧ first.unresolved.length = 1 ∧ first.unvisited.length = 1 do
        throw (IO.userError "the first admission request lost original unresolved positions or unvisited syntax")
      System.IO.println "retries: first request"
      (← IO.getStdout).flush
      match first.fromAtoms intrinsicInputs with
      | none => throw (IO.userError "new original atom evidence could not be supplied at its exact original occurrence")
      | some firstEvidence => match first.resume firstEvidence with
        | .pending second =>
            System.IO.println "retries: second request"
            (← IO.getStdout).flush
            match second.prefix with
            | [retained] =>
                let materialized := retained.2.materialize
                unless materialized.sidecar.residual.source.sample 6 = (2 : Canonical)⁻¹ do
                  throw (IO.userError "resumption replaced the original completed reciprocal prefix")
            | _ => throw (IO.userError "the second admission did not retain its actual completed original left sibling")
            match second.fromAtoms intrinsicInputs with
            | none => throw (IO.userError "the second original atom evidence was not accepted at its source channel")
            | some secondEvidence => match second.resume secondEvidence with
              | .completed output =>
                  System.IO.println "retries: completed"
                  (← IO.getStdout).flush
                  let output := output.materialize
                  unless output.sidecar.residual.source.sample 7 =
                      (2 : Canonical)⁻¹ + (3 : Canonical)⁻¹ do
                    throw (IO.userError "cached resumption lost the original completed reciprocal result")
              | _ => throw (IO.userError "both original intrinsic admissions failed to complete the checked expression")
        | _ =>
            throw (IO.userError "the original unresolved right atom was silently completed or invalidated")
  | _ => throw (IO.userError "unsupported original opaque atoms did not return a typed admission request")
  let cancelled : Expr 2 := .base (.sub (.atom ⟨0, by decide⟩) (.atom ⟨0, by decide⟩))
  match cancelled.attempt opaqueInputs with
  | .completed retained =>
      let retained := retained.materialize
      unless retained.sidecar.residual.source.sample 4 = 0 do
        throw (IO.userError "the original total compiler's cancellation fast path changed its numerical channel")
  | _ => throw (IO.userError "original cancellation requested irrelevant opaque leaf admissions")

/-- The original one-argument type spelling still selects the total grammar. -/
private theorem default_total (arity : Nat) : Basic.Expr arity = Basic.Expr arity .total := rfl

/-- The checked type is exactly the checked index of the original owner. -/
private theorem checked_view (arity : Nat) : Expr arity = Basic.Expr arity .checked := rfl

/-- An arbitrary total base remains one checked node without visiting its internal syntax. -/
private theorem checked_base_size {arity : Nat} (expression : Basic.Expr arity) :
    Expr.size (.base expression) = 1 := rfl

/-- Total negation retains the original all-input defining equation through ordinary imports. -/
private theorem total_neg_reduction {arity : Nat} (environment : Fin arity → Annotated)
    (input : Basic.Expr arity) :
    (Basic.Expr.neg input).denote environment = CoherentNamed.neg (input.denote environment) := rfl

/-- Checked addition preserves its all-input left-first equation and original delayed right child. -/
private theorem checked_add_reduction {arity : Nat} (environment : Fin arity → Annotated)
    (left right : Expr arity) :
    Expr.attempt environment (.add left right) =
      (left.attempt environment).binary .add (fun _ => right.attempt environment) := rfl

/-- The original generated equality procedure remains reducible in the total view. -/
private theorem total_eq_decision :
    decide ((.neg (.rational 0) : Basic.Expr 0) = .neg (.rational 0)) = true := rfl

/-- The same generated equality procedure reduces across a retained checked base boundary. -/
private theorem checked_eq_decision :
    decide ((.inverse (.base (.rational 0)) : Expr 0) = .inverse (.base (.rational 0))) = true := rfl

/-- Materialization preserves the complete former result in both retained-cache branches. -/
private theorem materialize_complete_branch {arity : Nat} {environment : Fin arity → Annotated}
    {expression : Expr arity} (result : Construction.Result environment expression) :
    result.materialize =
      (match selected : result.cached with
      | some sidecar =>
          ⟨result.channel, result.construction, sidecar, result.coherent, result.cacheMatches sidecar selected⟩
      | none =>
          ⟨result.channel, result.construction, result.construction.buildSidecar, result.coherent, rfl⟩) := by
  rcases result with ⟨channel, construction, ⟨cached, coherent, cache_matches⟩⟩
  cases cached <;> rfl

/-- Packing an actual completed cache and materializing it preserves the entire original completion. -/
private theorem materialize_completed {arity : Nat} {environment : Fin arity → Annotated}
    {expression : Expr arity} (completed : Completed environment expression) :
    completed.toResult.materialize = completed := by
  cases completed
  rfl

/-- Exercise complete checked comparisons, independent named starts and an unused original atom.

Both computations retain their own annotations and reciprocal guards. The
positive expression covers every checked operation; zero power skips numerical
atom comparison only after its original denominator guard has completed.
-/
public def checkComparisons : IO Unit := do
  let index : Fin 1 := ⟨0, by decide⟩
  let firstEnvironment : Fin 1 → Annotated := fun _ => Annotated.rational 3
  let secondEnvironment : Fin 1 → Annotated := fun _ => Annotated.opaque (CoherentNamed.Coherence.exact 3)
  let sidecar := Algebraic.Sidecar.ofRational (RationalSidecar.exact 3)
  let firstAtom := Admitted.atom firstEnvironment index sidecar
  let secondAtom := Admitted.atom secondEnvironment index sidecar
  let input := Expr.atom index
  let expression : Expr 1 := .add (.inverse (.add input (Expr.rational 1)))
    (.conj (.pow (.mul (.neg input) (.sub input (Expr.rational 1))) 2))
  let build (environment : Fin 1 → Annotated) (atom : Admitted environment input) :
      Admitted environment expression :=
    (Admitted.inverse (atom.add (Admitted.rational environment 1))).add
      ((atom.neg.mul (atom.sub (Admitted.rational environment 1))).pow 2).conj
  match (build firstEnvironment firstAtom).run, (build secondEnvironment secondAtom).run with
  | .completed first, .completed second =>
      let compared := first.namedEquivalent second (fun _ => NamedEquivalent.refl _)
      let paid := compared.compare 2 5 1 (by decide)
      let left := (Name.Sampling.approximation first.channel.name).sample paid.leftIndex
      let right := (Name.Sampling.approximation second.channel.name).sample paid.rightIndex
      unless paid.leftIndex ≥ 2 ∧ paid.rightIndex ≥ 5 ∧ normSq (left - right) ≤ 1 do
        throw (IO.userError "Checked expression comparison lost its actual named payment or independent starts")
  | _, _ => throw (IO.userError "Nonzero complete checked arithmetic failed to construct both original results")
  let unused (index : Fin 1) :
      NamedEquivalent (firstEnvironment index).channel.name (secondEnvironment index).channel.name :=
    letI : Inhabited
        (NamedEquivalent (firstEnvironment index).channel.name (secondEnvironment index).channel.name) :=
      ⟨NamedEquivalent.refl _⟩
    panic! "A constant checked result demanded an unused atom comparison"
  match ((Admitted.inverse firstAtom).pow 0).run, ((Admitted.inverse secondAtom).pow 0).run with
  | .completed first, .completed second =>
      let compared := first.namedEquivalent second unused
      let paid := compared.compare 1 3 1 (by decide)
      let left := (Name.Sampling.approximation first.channel.name).sample paid.leftIndex
      let right := (Name.Sampling.approximation second.channel.name).sample paid.rightIndex
      unless paid.leftIndex ≥ 1 ∧ paid.rightIndex ≥ 3 ∧ normSq (left - right) ≤ 1 do
        throw (IO.userError "Zero-power comparison lost its original completed guards or named payment")
  | _, _ => throw (IO.userError "The nonzero original atom lost its checked inverse under zero power")
  match ((Admitted.inverse (Admitted.rational firstEnvironment 0)).pow 0).run with
  | .invalid _ => pure ()
  | _ => throw (IO.userError "Zero power erased an original undefined denominator")
  System.IO.println
    "Checked expression comparisons: all operations, named starts and original zero-power domains retained"

end TestPurelib.Approximation.Gaussian.CheckedExpression
