module

import Purelib.Polynomial.Multivariate.Sparse
public import Purelib.Polynomial.Multivariate.Gaussian.Operational
public import Purelib.Polynomial.Multivariate.PowerReduction
public import Purelib.Data.Vector.Dependent
public import Purelib.Polynomial.Approximation.CoherentEvaluation
import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.Nat.Order
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Cached finite polynomial interpretations

Every original exponent retains its actual power and remaining product.
Terms retain the coefficient channel and monomial cache; finite sums retain
their original head and tail interpretations. Construction uses each cached
child channel once, with exact equations to the original polynomial evaluator.
-/

public section

namespace Purelib.Polynomial.Multivariate

open Purelib.Data.List.Membership (mem_cons)
open Purelib.Data.List.Map (mem_map)
open Purelib.Data.Vector (DependentVector)
open Purelib.Data.Nat
open Purelib.Data.Gaussian.Basic renaming Canonical -> Coefficient
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Polynomial.Approximation

namespace Monomial

set_option genInjectivity false in
/-- The actual power and suffix-product channels of an original monomial interpretation. -/
inductive Products : {arity : Nat} → Monomial arity → (Fin arity → CoherentNamed) → CoherentNamed → Type 1
  /-- The empty original exponent vector retains its exact unit channel. -/
  | nil (environment : Fin 0 → CoherentNamed) (channel : CoherentNamed)
      (channel_eq : channel = CoherentNamed.Coherence.exact 1) : Products .nil environment channel
  /-- Retain the original first power, exact remaining interpretation and product of those same cached channels. -/
  | cons {arity : Nat} (exponent : Nat) (remaining : Monomial arity)
      (environment : Fin (arity + 1) → CoherentNamed)
      (power : CoherentNamed) (power_eq : power = Power.namedPower (environment 0) exponent)
      (tailChannel : CoherentNamed) (tail : Products remaining (fun index => environment index.succ) tailChannel)
      (channel : CoherentNamed) (channel_eq : channel = CoherentNamed.mul power tailChannel) :
      Products (.cons exponent remaining) environment channel

constructive_injectivity Products

/-- Every cached original monomial product has the exact original finite evaluator as its readback. -/
theorem Products.channel_eq {arity : Nat} {monomial : Monomial arity}
    {environment : Fin arity → CoherentNamed} {channel : CoherentNamed}
    (products : Products monomial environment channel) : channel = monomial.denote environment := by
  induction products with
  | nil environment channel same => exact same
  | cons exponent remaining environment power power_eq tailChannel tail channel same ih =>
      exact same.trans (congrArg₂ CoherentNamed.mul power_eq ih)

set_option genInjectivity false in
/-- One cached original monomial channel and its complete original power/product construction. -/
structure Denotation {arity : Nat} (monomial : Monomial arity) (environment : Fin arity → CoherentNamed) where
  /-- The actual computed monomial product channel. -/
  channel : CoherentNamed
  /-- The retained powers and suffix products construct this exact channel. -/
  products : Products monomial environment channel

constructive_injectivity Denotation

/-- Cache every power and suffix product once, consuming the actual original variable channels. -/
@[expose] def retain : {arity : Nat} → (monomial : Monomial arity) →
    (environment : Fin arity → CoherentNamed) → Denotation monomial environment
  | 0, .nil, environment =>
      ⟨CoherentNamed.Coherence.exact 1, .nil environment _ rfl⟩
  | _ + 1, .cons exponent remaining, environment =>
      let tail := remaining.retain (fun index => environment index.succ)
      let power := Power.namedPower (environment 0) exponent
      let channel := CoherentNamed.mul power tail.channel
      ⟨channel, .cons exponent remaining environment power rfl tail.channel tail.products channel rfl⟩

/-- The stored monomial channel reads back to its original exponent vector and variable owners. -/
theorem Denotation.channel_eq {arity : Nat} {monomial : Monomial arity}
    {environment : Fin arity → CoherentNamed} (retained : Denotation monomial environment) :
    retained.channel = monomial.denote environment := retained.products.channel_eq

/-- Compare original cached powers and suffix products across explicitly related variable owners. -/
def Products.compareAcross : {arity : Nat} → {monomial : Monomial arity} →
    (left right : Fin arity → CoherentNamed) →
    (∀ index, NamedEquivalent (left index).name (right index).name) →
    {first second : CoherentNamed} → Products monomial left first → Products monomial right second →
    NamedEquivalent first.name second.name
  | _, _, _, _, _, _, _, .nil _ _ first_eq, .nil _ _ second_eq => by
      rewrite [first_eq, second_eq]
      exact NamedEquivalent.refl _
  | _, _, left, right, equivalent, _, _,
      .cons exponent remaining _ firstPower firstPower_eq firstTail firstProducts _ first_eq,
      .cons _ _ _ secondPower secondPower_eq secondTail secondProducts _ second_eq => by
      have powers := Power.namedPower_respects (left 0) (right 0) (equivalent 0) exponent
      rewrite [← firstPower_eq, ← secondPower_eq] at powers
      have tails := compareAcross (fun index => left index.succ) (fun index => right index.succ)
        (fun index => equivalent index.succ) firstProducts secondProducts
      have compared := Product.Congruence.coherentMul_respects firstPower secondPower firstTail secondTail powers tails
      change NamedEquivalent (CoherentNamed.mul firstPower firstTail).name
        (CoherentNamed.mul secondPower secondTail).name at compared
      rewrite [← first_eq, ← second_eq] at compared
      exact compared

/-- Compare the same retained original monomial channels using explicit comparisons of their original variables. -/
def Denotation.compareAcross {arity : Nat} {monomial : Monomial arity}
    {left right : Fin arity → CoherentNamed} (first : Denotation monomial left) (second : Denotation monomial right)
    (equivalent : ∀ index, NamedEquivalent (left index).name (right index).name) :
    NamedEquivalent first.channel.name second.channel.name :=
  first.products.compareAcross left right equivalent second.products

end Monomial

namespace Term

set_option genInjectivity false in
/-- One original term's cached coefficient channel, monomial products and actual numerical product. -/
structure Denotation {arity : Nat} (environment : Fin arity → CoherentNamed)
    (term : Term Coefficient arity) where
  /-- The exact original coefficient channel retained as executable data. -/
  coefficient : CoherentNamed
  /-- The coefficient channel contains this same original term coefficient. -/
  coefficient_eq : coefficient = CoherentNamed.Coherence.exact term.coefficient
  /-- The retained original monomial interpretation. -/
  monomial : Monomial.Denotation term.monomial environment
  /-- The actual product of the retained coefficient and monomial. -/
  channel : CoherentNamed
  /-- This product consumes those exact two cached channels. -/
  product_eq : channel = CoherentNamed.mul coefficient monomial.channel

constructive_injectivity Denotation

/-- Cache an original coefficient and its product with the same supplied monomial interpretation. -/
@[expose] def withMonomial {arity : Nat} (environment : Fin arity → CoherentNamed) (term : Term Coefficient arity)
    (monomial : Monomial.Denotation term.monomial environment) :
    Denotation environment term :=
  let coefficient := CoherentNamed.Coherence.exact term.coefficient
  let channel := CoherentNamed.mul coefficient monomial.channel
  ⟨coefficient, rfl, monomial, channel, rfl⟩

/-- Cache an original term's coefficient and monomial interpretation, then their actual product once. -/
@[expose] def retain {arity : Nat} (environment : Fin arity → CoherentNamed) (term : Term Coefficient arity) :
    Denotation environment term := withMonomial environment term (term.monomial.retain environment)

/-- Term construction consumes the literal supplied original monomial cache. -/
theorem withMonomial_monomial {arity : Nat} (environment : Fin arity → CoherentNamed)
    (term : Term Coefficient arity) (monomial : Monomial.Denotation term.monomial environment) :
    (withMonomial environment term monomial).monomial = monomial := rfl

/-- The cached original term reads back to the original coefficient and monomial evaluator. -/
theorem Denotation.channel_eq {arity : Nat} {environment : Fin arity → CoherentNamed}
    {term : Term Coefficient arity} (retained : Denotation environment term) :
    retained.channel = term.denote environment :=
  retained.product_eq.trans (congrArg₂ CoherentNamed.mul retained.coefficient_eq retained.monomial.channel_eq)

/-- Compare the same original term at both cached coefficient and monomial products. -/
def Denotation.compareAcross {arity : Nat} {term : Term Coefficient arity}
    {left right : Fin arity → CoherentNamed} (first : Denotation left term) (second : Denotation right term)
    (equivalent : ∀ index, NamedEquivalent (left index).name (right index).name) :
    NamedEquivalent first.channel.name second.channel.name := by
  have coefficient_eq : first.coefficient = second.coefficient :=
    first.coefficient_eq.trans second.coefficient_eq.symm
  have coefficients : NamedEquivalent first.coefficient.name second.coefficient.name := by
    rewrite [coefficient_eq]
    exact NamedEquivalent.refl _
  have compared := Product.Congruence.coherentMul_respects first.coefficient second.coefficient
    first.monomial.channel second.monomial.channel coefficients
    (first.monomial.compareAcross second.monomial equivalent)
  change NamedEquivalent (CoherentNamed.mul first.coefficient first.monomial.channel).name
    (CoherentNamed.mul second.coefficient second.monomial.channel).name at compared
  rewrite [← first.product_eq, ← second.product_eq] at compared
  exact compared

end Term

namespace Terms

/-- Every original term has the variable evidence needed by its nonzero exponents. -/
@[expose] def Supported {arity : Nat} (available : Fin arity → Prop) : List (Term Coefficient arity) → Prop
  | [] => True
  | first :: remaining => first.monomial.Supported available ∧ Supported available remaining

/-- Decide support from the same original finite term list and availability conditions. -/
instance supportedDecidable {arity : Nat} (available : Fin arity → Prop)
    [∀ index, Decidable (available index)] :
    (terms : List (Term Coefficient arity)) → Decidable (Supported available terms)
  | [] => isTrue True.intro
  | first :: remaining =>
      letI := supportedDecidable available remaining
      inferInstanceAs (Decidable (first.monomial.Supported available ∧ Supported available remaining))

/-- Availability at every original index supplies the support of every retained term. -/
theorem supported_all {arity : Nat} (available : Fin arity → Prop) (ready : ∀ index, available index) :
    (terms : List (Term Coefficient arity)) → Supported available terms
  | [] => True.intro
  | first :: remaining => ⟨first.monomial.supported_all available ready, supported_all available ready remaining⟩

set_option genInjectivity false in
/-- The cached original head, remaining sum and output at every finite term-list occurrence. -/
inductive Sums {arity : Nat} (environment : Fin arity → CoherentNamed) :
    List (Term Coefficient arity) → CoherentNamed → Type 1
  /-- An empty term list retains its exact zero channel. -/
  | nil (channel : CoherentNamed) (channel_eq : channel = CoherentNamed.Coherence.exact 0) : Sums environment [] channel
  /-- A nonempty term list consumes its exact cached head and original remaining sum. -/
  | cons (first : Term Coefficient arity) (remaining : List (Term Coefficient arity))
      (head : Term.Denotation environment first) (tailChannel : CoherentNamed)
      (tail : Sums environment remaining tailChannel) (channel : CoherentNamed)
      (channel_eq : channel = CoherentNamed.add head.channel tailChannel) :
      Sums environment (first :: remaining) channel

constructive_injectivity Sums

/-- Every retained original finite sum has the exact original term-list evaluator as its readback. -/
theorem Sums.channel_eq {arity : Nat} {environment : Fin arity → CoherentNamed}
    {terms : List (Term Coefficient arity)} {channel : CoherentNamed} (sums : Sums environment terms channel) :
    channel = Terms.denote environment terms := by
  induction sums with
  | nil channel same => exact same
  | cons first remaining head tailChannel tail channel same ih =>
      exact same.trans (congrArg₂ CoherentNamed.add head.channel_eq ih)

set_option genInjectivity false in
/-- One original finite term list's cached numerical sum and complete interpretation construction. -/
structure Denotation {arity : Nat} (environment : Fin arity → CoherentNamed)
    (terms : List (Term Coefficient arity)) where
  /-- The actual cached finite polynomial channel. -/
  channel : CoherentNamed
  /-- The exact original cached head and tail sums construct this same channel. -/
  sums : Sums environment terms channel

constructive_injectivity Denotation

/-- Find an existing original monomial cache, comparing only its finite exponent vector. -/
@[expose] def Sums.findMonomial {arity : Nat} {environment : Fin arity → CoherentNamed}
    (monomial : Monomial arity) :
    {terms : List (Term Coefficient arity)} → {channel : CoherentNamed} → Sums environment terms channel →
      Option (Monomial.Denotation monomial environment)
  | _, _, .nil _ _ => none
  | _, _, .cons first _ head _ tail _ _ =>
      if same : first.monomial = monomial then some (same ▸ head.monomial)
      else tail.findMonomial monomial

/-- A matching original first monomial returns its literal existing cache. -/
theorem Sums.findMonomial_head {arity : Nat} {environment : Fin arity → CoherentNamed}
    (first : Term Coefficient arity) (remaining : List (Term Coefficient arity))
    (head : Term.Denotation environment first) (tailChannel : CoherentNamed)
    (tail : Sums environment remaining tailChannel) (channel : CoherentNamed)
    (same : channel = CoherentNamed.add head.channel tailChannel) :
    (Sums.cons first remaining head tailChannel tail channel same).findMonomial first.monomial =
      some head.monomial := by
  unfold findMonomial
  rewrite [dif_pos rfl]
  rfl

/-- Read a monomial from the same original cached term-list construction. -/
@[expose] def Denotation.findMonomial {arity : Nat} {environment : Fin arity → CoherentNamed}
    {terms : List (Term Coefficient arity)} (retained : Denotation environment terms) (monomial : Monomial arity) :
    Option (Monomial.Denotation monomial environment) := retained.sums.findMonomial monomial

/-- Every actual term monomial is found in the supplied original product-cache lookup. -/
@[expose] def CacheComplete {arity : Nat} (environment : Fin arity → CoherentNamed)
    (cached : (monomial : Monomial arity) → Option (Monomial.Denotation monomial environment))
    (terms : List (Term Coefficient arity)) : Prop :=
  MonomialsSatisfy (fun monomial => ∃ retained, cached monomial = some retained) terms

/-- Construct an original finite term interpretation entirely from its complete retained monomial lookup.

Every selected `some` value is consumed literally. The impossible `none`
branch is discharged by the same finite completeness certificate; this
builder contains no call to the fresh monomial-product constructor.
-/
@[expose] def retainFrom {arity : Nat} (environment : Fin arity → CoherentNamed)
    (cached : (monomial : Monomial arity) → Option (Monomial.Denotation monomial environment)) :
    (terms : List (Term Coefficient arity)) → CacheComplete environment cached terms → Denotation environment terms
  | [], _ => ⟨CoherentNamed.Coherence.exact 0, .nil _ rfl⟩
  | first :: remaining, complete =>
      match selected : cached first.monomial with
      | some monomial =>
          let head := first.withMonomial environment monomial
          let tail := retainFrom environment cached remaining complete.2
          let channel := CoherentNamed.add head.channel tail.channel
          ⟨channel, .cons first remaining head tail.channel tail.sums channel rfl⟩
      | none => by
          have impossible : False := by
            rcases complete.1 with ⟨monomial, known⟩
            have incompatible : (none : Option (Monomial.Denotation first.monomial environment)) =
                some monomial := selected.symm.trans known
            cases incompatible
          exact False.elim impossible

/-- The complete-cache builder's first product is the literal original monomial returned by its lookup. -/
theorem retainFrom_head {arity : Nat} (environment : Fin arity → CoherentNamed)
    (cached : (monomial : Monomial arity) → Option (Monomial.Denotation monomial environment))
    (first : Term Coefficient arity) (remaining : List (Term Coefficient arity))
    (complete : CacheComplete environment cached (first :: remaining))
    (monomial : Monomial.Denotation first.monomial environment) (known : cached first.monomial = some monomial) :
    (retainFrom environment cached (first :: remaining) complete).findMonomial first.monomial = some monomial := by
  unfold retainFrom
  split
  next actual selected =>
    have same : actual = monomial := Option.some.inj (selected.symm.trans known)
    cases same
    exact Sums.findMonomial_head first remaining (first.withMonomial environment monomial)
      (retainFrom environment cached remaining complete.2).channel
      (retainFrom environment cached remaining complete.2).sums _ rfl
  next selected =>
    have incompatible : (none : Option (Monomial.Denotation first.monomial environment)) =
        some monomial := selected.symm.trans known
    cases incompatible

/-- Retain a finite interpretation, reusing supplied monomial products and computing only missing ones. -/
@[expose] def retainWith {arity : Nat} (environment : Fin arity → CoherentNamed)
    (cached : (monomial : Monomial arity) → Option (Monomial.Denotation monomial environment)) :
    (terms : List (Term Coefficient arity)) → Denotation environment terms
  | [] => ⟨CoherentNamed.Coherence.exact 0, .nil _ rfl⟩
  | first :: remaining =>
      let monomial := match cached first.monomial with
        | some retained => retained
        | none => first.monomial.retain environment
      let head := first.withMonomial environment monomial
      let tail := retainWith environment cached remaining
      let channel := CoherentNamed.add head.channel tail.channel
      ⟨channel, .cons first remaining head tail.channel tail.sums channel rfl⟩

/-- Retain every original term and suffix sum once, consuming their same actual cached channels. -/
@[expose] def retain {arity : Nat} (environment : Fin arity → CoherentNamed) :
    (terms : List (Term Coefficient arity)) → Denotation environment terms :=
  retainWith environment (fun _ => none)

/-- A supplied first monomial is the literal cache returned by the resulting original interpretation. -/
theorem retainWith_head {arity : Nat} (environment : Fin arity → CoherentNamed)
    (cached : (monomial : Monomial arity) → Option (Monomial.Denotation monomial environment))
    (first : Term Coefficient arity) (remaining : List (Term Coefficient arity))
    (monomial : Monomial.Denotation first.monomial environment) (known : cached first.monomial = some monomial) :
    (retainWith environment cached (first :: remaining)).findMonomial first.monomial = some monomial := by
  unfold retainWith
  rewrite [known]
  exact Sums.findMonomial_head first remaining (first.withMonomial environment monomial)
    (retainWith environment cached remaining).channel (retainWith environment cached remaining).sums _ rfl

/-- The stored polynomial channel reads back to the original finite coefficient list and variable owners. -/
theorem Denotation.channel_eq {arity : Nat} {environment : Fin arity → CoherentNamed}
    {terms : List (Term Coefficient arity)} (retained : Denotation environment terms) :
    retained.channel = Terms.denote environment terms := retained.sums.channel_eq

/-- Compare the original cached heads and suffix sums using explicit comparisons of both variable environments. -/
def Sums.compareAcross {arity : Nat} (left right : Fin arity → CoherentNamed)
    (equivalent : ∀ index, NamedEquivalent (left index).name (right index).name) :
    {terms : List (Term Coefficient arity)} → {first second : CoherentNamed} →
    Sums left terms first → Sums right terms second → NamedEquivalent first.name second.name
  | _, _, _, .nil _ first_eq, .nil _ second_eq => by
      rewrite [first_eq, second_eq]
      exact NamedEquivalent.refl _
  | _, _, _, .cons _ _ firstHead firstTail firstSums _ first_eq,
      .cons _ _ secondHead secondTail secondSums _ second_eq => by
      have heads := firstHead.compareAcross secondHead equivalent
      have tails := compareAcross left right equivalent firstSums secondSums
      have compared := Sum.Congruence.coherentAdd_respects
        firstHead.channel secondHead.channel firstTail secondTail heads tails
      change NamedEquivalent (CoherentNamed.add firstHead.channel firstTail).name
        (CoherentNamed.add secondHead.channel secondTail).name at compared
      rewrite [← first_eq, ← second_eq] at compared
      exact compared

/-- Compare both complete cached finite interpretations without rebuilding their polynomial channels. -/
def Denotation.compareAcross {arity : Nat} {terms : List (Term Coefficient arity)}
    {left right : Fin arity → CoherentNamed} (first : Denotation left terms) (second : Denotation right terms)
    (equivalent : ∀ index, NamedEquivalent (left index).name (right index).name) :
    NamedEquivalent first.channel.name second.channel.name :=
  first.sums.compareAcross left right equivalent second.sums

/-- Transport a cached finite interpretation to an equal original coefficient list, retaining its numerical channel. -/
@[expose] def Denotation.cast {arity : Nat} {environment : Fin arity → CoherentNamed}
    {first second : List (Term Coefficient arity)} (retained : Denotation environment first) (same : first = second) :
    Denotation environment second := ⟨retained.channel, same ▸ retained.sums⟩

/-- Coefficient-list transport retains the literal original numerical interpretation channel. -/
theorem Denotation.cast_channel {arity : Nat} {environment : Fin arity → CoherentNamed}
    {first second : List (Term Coefficient arity)} (retained : Denotation environment first) (same : first = second) :
    (retained.cast same).channel = retained.channel := rfl

end Terms

namespace Monomial

/-- Replace only one power in an original retained product, reusing all other powers and suffixes.

The supplied new power is linked to the same original bounded variable.
At the selected coordinate the original tail is retained literally; earlier
coordinates reuse their exact original stored powers.
-/
@[expose] def Products.replaceAt : {arity : Nat} → {monomial : Monomial arity} →
    {bindings : Fin arity → CoherentNamed} → {channel : CoherentNamed} →
    Products monomial bindings channel → (index : Fin arity) → (replacement : Nat) →
    (power : CoherentNamed) → power = Power.namedPower (bindings index) replacement →
    Denotation (monomial.withExponentAt index replacement) bindings
  | _, _, _, _, .nil _ _ _, index, _, _, _ => Fin.elim0 index
  | _, _, _, _, .cons exponent remaining bindings originalPower originalPower_eq tailChannel tail _ _,
      index, replacement, power, power_eq => by
      revert power_eq
      refine Fin.cases ?_ ?_ index
      · intro power_eq
        let next := CoherentNamed.mul power tailChannel
        exact ⟨next, .cons replacement remaining bindings power power_eq tailChannel tail next rfl⟩
      · intro tailIndex power_eq
        let changed := tail.replaceAt tailIndex replacement power power_eq
        let next := CoherentNamed.mul originalPower changed.channel
        exact ⟨next, .cons exponent (remaining.withExponentAt tailIndex replacement) bindings
          originalPower originalPower_eq changed.channel changed.products next rfl⟩

/-- Read the exact original stored power at one bounded coordinate of a retained product. -/
@[expose] def Products.powerAt : {arity : Nat} → {monomial : Monomial arity} →
    {bindings : Fin arity → CoherentNamed} → {channel : CoherentNamed} →
    Products monomial bindings channel → (index : Fin arity) →
      {power : CoherentNamed // power = Power.namedPower (bindings index) (monomial.exponentAt index)}
  | _, _, _, _, .nil _ _ _, index => Fin.elim0 index
  | _, _, _, _, .cons _ _ _ power same _ remaining _ _, index =>
      Fin.cases ⟨power, same⟩ (fun tail => remaining.powerAt tail) index

/-- One original generator power and its exact stored coherent-channel readback. -/
abbrev PowerEntry (generator : CoherentNamed) :=
  Sigma fun exponent : Nat => {channel : CoherentNamed // channel = Power.namedPower generator exponent}

/-- Read an already computed original generator power by its exact natural exponent. -/
@[expose] def findPower (generator : CoherentNamed) (exponent : Nat) :
    List (PowerEntry generator) → Option {channel : CoherentNamed // channel = Power.namedPower generator exponent}
  | [] => none
  | first :: remaining =>
      if same : first.1 = exponent then some (same ▸ first.2)
      else findPower generator exponent remaining

/-- Materialize each requested original generator power once, sharing repeated natural exponents. -/
@[expose] def retainPowersWith (generator : CoherentNamed) :
    List (PowerEntry generator) → List Nat → List (PowerEntry generator)
  | retained, [] => retained
  | retained, exponent :: remaining =>
      let next := match findPower generator exponent retained with
        | some _ => retained
        | none => ⟨exponent, ⟨Power.namedPower generator exponent, rfl⟩⟩ :: retained
      retainPowersWith generator next remaining

/-- Retain a finite original-generator power table from an initially empty cache. -/
@[expose] def retainPowers (generator : CoherentNamed) (exponents : List Nat) : List (PowerEntry generator) :=
  retainPowersWith generator [] exponents

/-- Extending a power bank retains the exact complete stored value returned at every existing exponent.

A missing requested exponent can prepend only a different power. A request
for an existing exponent keeps the original bank, so neither its channel nor
its specification proof is replaced by a recomputed reading.
-/
theorem findPower_retainPowersWith_preserves (generator : CoherentNamed) (exponent : Nat)
    (power : {channel : CoherentNamed // channel = Power.namedPower generator exponent}) :
    (retained : List (PowerEntry generator)) → (requested : List Nat) →
    findPower generator exponent retained = some power →
    findPower generator exponent (retainPowersWith generator retained requested) = some power
  | _, [], known => known
  | retained, next :: remaining, known => by
      cases selected : findPower generator next retained with
      | some _ =>
          unfold retainPowersWith
          rewrite [selected]
          exact findPower_retainPowersWith_preserves generator exponent power retained remaining known
      | none =>
          have different : next ≠ exponent := by
            intro same
            cases same
            have incompatible := selected.symm.trans known
            cases incompatible
          have kept : findPower generator exponent
              (⟨next, ⟨Power.namedPower generator next, rfl⟩⟩ :: retained) = some power := by
            unfold findPower
            rewrite [dif_neg different]
            exact known
          unfold retainPowersWith
          rewrite [selected]
          exact findPower_retainPowersWith_preserves generator exponent power _ remaining kept

/-- Extending a power bank preserves successful lookup of an actual previously stored generator power. -/
theorem findPower_retainPowersWith_existing (generator : CoherentNamed) (exponent : Nat) :
    (retained : List (PowerEntry generator)) → (requested : List Nat) →
    (∃ power, findPower generator exponent retained = some power) →
    ∃ power, findPower generator exponent (retainPowersWith generator retained requested) = some power := by
  intro retained requested known
  rcases known with ⟨power, stored⟩
  exact ⟨power, findPower_retainPowersWith_preserves generator exponent power retained requested stored⟩

/-- Every requested exponent is found in the same actual extended generator-power bank.

The successful branch retains the old bank. The missing branch computes one
original generator power, then later requests share that same stored value.
-/
theorem findPower_retainPowersWith_requested (generator : CoherentNamed) (exponent : Nat) :
    (retained : List (PowerEntry generator)) → (requested : List Nat) → exponent ∈ requested →
    ∃ power, findPower generator exponent (retainPowersWith generator retained requested) = some power
  | _, [], present => by cases present
  | retained, next :: remaining, present => by
      let extended := match findPower generator next retained with
        | some _ => retained
        | none => ⟨next, ⟨Power.namedPower generator next, rfl⟩⟩ :: retained
      have ready : ∃ power, findPower generator next extended = some power := by
        unfold extended
        cases selected : findPower generator next retained with
        | some power => exact ⟨power, selected⟩
        | none =>
            refine ⟨⟨Power.namedPower generator next, rfl⟩, ?_⟩
            unfold findPower
            rewrite [dif_pos rfl]
            rfl
      cases mem_cons.mp present with
      | inl same =>
          subst exponent
          exact findPower_retainPowersWith_existing generator next extended remaining ready
      | inr later => exact findPower_retainPowersWith_requested generator exponent extended remaining later

/-- Every exponent below a finite ceiling has an actual stored original generator power. -/
@[expose] def PrefixComplete (generator : CoherentNamed) (degree : Nat) (powers : List (PowerEntry generator)) : Prop :=
  ∀ exponent, exponent < degree → ∃ power, findPower generator exponent powers = some power

/-- One complete prefix of the original generator-power bank, with its actual entries retained. -/
abbrev PowerPrefix (generator : CoherentNamed) (degree : Nat) :=
  {powers : List (PowerEntry generator) // PrefixComplete generator degree powers}

/-- Read a certified existing generator power directly from the retained bank.

The success branch returns its whole original channel and specification proof.
The impossible missing branch consumes the supplied lookup certificate.
-/
@[expose] def powerFrom (generator : CoherentNamed) (powers : List (PowerEntry generator)) (exponent : Nat)
    (known : ∃ power, findPower generator exponent powers = some power) :
    {channel : CoherentNamed // channel = Power.namedPower generator exponent} :=
  match found : findPower generator exponent powers with
  | some power => power
  | none => False.elim (by
      rcases known with ⟨power, stored⟩
      have incompatible := found.symm.trans stored
      cases incompatible)

/-- Read the complete stored power at a bounded position of the same certified prefix. -/
@[expose] def PowerPrefix.power {generator : CoherentNamed} {degree : Nat}
    (powers : PowerPrefix generator degree) (exponent : Fin degree) :
    {channel : CoherentNamed // channel = Power.namedPower generator exponent.val} :=
  powerFrom generator powers.val exponent.val (powers.property exponent.val exponent.isLt)

/-- A newly prepended original exponent returns the same whole supplied power cache. -/
theorem findPower_cons_same (generator : CoherentNamed) (exponent : Nat)
    (power : {channel : CoherentNamed // channel = Power.namedPower generator exponent})
    (powers : List (PowerEntry generator)) :
    findPower generator exponent (⟨exponent, power⟩ :: powers) = some power := by
  unfold findPower
  rewrite [dif_pos rfl]
  rfl

/-- Prepending a missing exponent preserves every successful original lookup literally. -/
theorem findPower_cons_preserves (generator : CoherentNamed) (exponent other : Nat)
    (power : {channel : CoherentNamed // channel = Power.namedPower generator exponent})
    (retained : {channel : CoherentNamed // channel = Power.namedPower generator other})
    (powers : List (PowerEntry generator))
    (missing : findPower generator exponent powers = none)
    (known : findPower generator other powers = some retained) :
    findPower generator other (⟨exponent, power⟩ :: powers) = some retained := by
  have different : exponent ≠ other := by
    intro same
    cases same
    have incompatible := missing.symm.trans known
    cases incompatible
  unfold findPower
  rewrite [dif_neg different]
  exact known

/-- Build one missing successor power from its actual stored predecessor.

Exponent zero uses the exact unit. A positive exponent multiplies the already
retained predecessor and the same original generator; no finite power program
is evaluated again.
-/
@[expose] def prefixPower (generator : CoherentNamed) :
    (degree : Nat) → PowerPrefix generator degree →
      {channel : CoherentNamed // channel = Power.namedPower generator degree}
  | 0, _ => ⟨CoherentNamed.Coherence.exact 1, rfl⟩
  | previous + 1, powers =>
      let prior := powerFrom generator powers.val previous (powers.property previous (Nat.lt_succ_self previous))
      ⟨CoherentNamed.mul prior.val generator, congrArg (fun value => CoherentNamed.mul value generator) prior.property⟩

/-- Complete a finite power prefix while retaining every already computed original entry.

Only a missing exponent is added. Each missing positive power consumes the
literal cached predecessor produced by the preceding step, so repeated powers
and pre-existing high powers are shared rather than recomputed.
-/
@[expose] def retainPowerPrefix (generator : CoherentNamed) (retained : List (PowerEntry generator)) :
    (degree : Nat) → PowerPrefix generator degree
  | 0 => ⟨retained, fun _ below => False.elim (Nat.not_lt_zero _ below)⟩
  | degree + 1 => by
      let previous := retainPowerPrefix generator retained degree
      match found : findPower generator degree previous.val with
      | some power =>
          refine ⟨previous.val, ?_⟩
          intro exponent below
          cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ below) with
          | inl earlier => exact previous.property exponent earlier
          | inr same => cases same; exact ⟨power, found⟩
      | none =>
          let power := prefixPower generator degree previous
          refine ⟨⟨degree, power⟩ :: previous.val, ?_⟩
          intro exponent below
          cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ below) with
          | inl earlier =>
              rcases previous.property exponent earlier with ⟨original, stored⟩
              exact ⟨original,
                findPower_cons_preserves generator degree exponent power original previous.val found stored⟩
          | inr same => cases same; exact ⟨power, findPower_cons_same generator degree power previous.val⟩

/-- Prefix completion preserves the entire original successful lookup, including its exact channel and equation. -/
theorem findPower_retainPowerPrefix_preserves (generator : CoherentNamed) (exponent : Nat)
    (power : {channel : CoherentNamed // channel = Power.namedPower generator exponent})
    (retained : List (PowerEntry generator)) (known : findPower generator exponent retained = some power) :
    (degree : Nat) → findPower generator exponent (retainPowerPrefix generator retained degree).val = some power
  | 0 => known
  | degree + 1 => by
      have previous := findPower_retainPowerPrefix_preserves generator exponent power retained known degree
      unfold retainPowerPrefix
      dsimp only
      split
      next selected found => exact previous
      next found => exact findPower_cons_preserves generator degree exponent _ power _ found previous

end Monomial

namespace Terms

/-- Find a source monomial differing only at the selected exponent, and reuse its other actual product caches. -/
@[expose] def Sums.findReplacement {arity : Nat} {bindings : Fin arity → CoherentNamed}
    (index : Fin arity) (powers : List (Monomial.PowerEntry (bindings index))) (target : Monomial arity) :
    {terms : List (Term Coefficient arity)} → {channel : CoherentNamed} → Sums bindings terms channel →
      Option (Monomial.Denotation target bindings)
  | _, _, .nil _ _ => none
  | _, _, .cons first _ head _ remaining _ _ =>
      if same : first.monomial.withExponentAt index (target.exponentAt index) = target then
        match Monomial.findPower (bindings index) (target.exponentAt index) powers with
        | some power => some (same ▸ head.monomial.products.replaceAt index (target.exponentAt index)
            power.val power.property)
        | none => none
      else remaining.findReplacement index powers target

/-- Reuse an exact old monomial or replace only its selected power with a stored original-generator power. -/
@[expose] def Denotation.replacementLookup {arity : Nat} {bindings : Fin arity → CoherentNamed}
    {terms : List (Term Coefficient arity)} (retained : Denotation bindings terms)
    (index : Fin arity) (powers : List (Monomial.PowerEntry (bindings index)))
    (target : Monomial arity) : Option (Monomial.Denotation target bindings) :=
  match retained.findMonomial target with
  | some exact => some exact
  | none => retained.sums.findReplacement index powers target

/-- Retain references to the actual selected-coordinate powers already stored in the original term cache. -/
@[expose] def Sums.powersAt {arity : Nat} {bindings : Fin arity → CoherentNamed}
    (index : Fin arity) :
    {terms : List (Term Coefficient arity)} → {channel : CoherentNamed} → Sums bindings terms channel →
      List (Monomial.PowerEntry (bindings index))
  | _, _, .nil _ _ => []
  | _, _, .cons first _ head _ remaining _ _ =>
      ⟨first.monomial.exponentAt index, head.monomial.products.powerAt index⟩ :: remaining.powersAt index

/-- Extend original stored powers only for the new exponents needed by a coefficient reduction. -/
@[expose] def Denotation.retainPowersAt {arity : Nat} {bindings : Fin arity → CoherentNamed}
    {terms : List (Term Coefficient arity)} (retained : Denotation bindings terms)
    (index : Fin arity) (exponents : List Nat) : List (Monomial.PowerEntry (bindings index)) :=
  Monomial.retainPowersWith (bindings index) (retained.sums.powersAt index) exponents

/-- An actual source replacement and a retained selected power make the original replacement lookup succeed. -/
theorem Sums.findReplacement_exists {arity : Nat} {bindings : Fin arity → CoherentNamed}
    (index : Fin arity) (powers : List (Monomial.PowerEntry (bindings index))) (target : Monomial arity) :
    {terms : List (Term Coefficient arity)} → {channel : CoherentNamed} → (sums : Sums bindings terms channel) →
    ReplacementOrigin index terms target →
    (∃ power, Monomial.findPower (bindings index) (target.exponentAt index) powers = some power) →
    ∃ retained, sums.findReplacement index powers target = some retained
  | _, _, .nil _ _, origin, _ => by
      rcases origin with ⟨term, present, _⟩
      cases present
  | _, _, .cons first remaining head tailChannel tail channel same, origin, ready => by
      change ∃ retained,
        (if replacement : first.monomial.withExponentAt index (target.exponentAt index) = target then
          match Monomial.findPower (bindings index) (target.exponentAt index) powers with
          | some power => some (replacement ▸ head.monomial.products.replaceAt index (target.exponentAt index)
              power.val power.property)
          | none => none
        else tail.findReplacement index powers target) = some retained
      by_cases matched : first.monomial.withExponentAt index (target.exponentAt index) = target
      · rcases ready with ⟨power, stored⟩
        refine ⟨matched ▸ head.monomial.products.replaceAt index (target.exponentAt index)
          power.val power.property, ?_⟩
        rewrite [dif_pos matched, stored]
        rfl
      · rcases origin with ⟨term, present, changed⟩
        have later : ReplacementOrigin index remaining target := by
          cases mem_cons.mp present with
          | inl equal =>
              cases equal
              exact False.elim (matched changed)
          | inr present => exact ⟨term, present, changed⟩
        rewrite [dif_neg matched]
        exact Sums.findReplacement_exists index powers target tail later ready

/-- The original complete lookup returns an existing monomial or an actual retained selected-coordinate replacement. -/
theorem Denotation.replacementLookup_exists {arity : Nat} {bindings : Fin arity → CoherentNamed}
    {terms : List (Term Coefficient arity)} (retained : Denotation bindings terms)
    (index : Fin arity) (powers : List (Monomial.PowerEntry (bindings index))) (target : Monomial arity)
    (origin : ReplacementOrigin index terms target)
    (ready : ∃ power, Monomial.findPower (bindings index) (target.exponentAt index) powers = some power) :
    ∃ monomial, retained.replacementLookup index powers target = some monomial := by
  unfold Denotation.replacementLookup
  cases selected : retained.findMonomial target with
  | some exact => exact ⟨exact, rfl⟩
  | none => exact retained.sums.findReplacement_exists index powers target origin ready

/-- The actual map of selected exponents includes every monomial in its original finite source list. -/
theorem selectedExponents_complete {arity : Nat} (index : Fin arity) (terms : List (Term Coefficient arity)) :
    MonomialsSatisfy
      (fun monomial => monomial.exponentAt index ∈ terms.map (fun term => term.monomial.exponentAt index))
      terms :=
  monomialsSatisfy_of_forall_mem _ terms (fun term present => mem_map.mpr ⟨term, present, rfl⟩)

/-- Every original replacement-origin term is found by the same retained monomial lookup and extended power bank.

Success is established after canonical combination and cancellation. The
resulting finite cache-completeness certificate permits construction through
only the actual `some` branches, with no fresh monomial-product fallback.
-/
theorem Denotation.replacementLookup_complete {arity : Nat} {bindings : Fin arity → CoherentNamed}
    {original : List (Term Coefficient arity)} (retained : Denotation bindings original)
    (index : Fin arity) (exponents : List Nat) : (terms : List (Term Coefficient arity)) →
    MonomialsSatisfy (ReplacementOrigin index original) terms →
    MonomialsSatisfy (fun monomial => monomial.exponentAt index ∈ exponents) terms →
    CacheComplete bindings (retained.replacementLookup index (retained.retainPowersAt index exponents)) terms
  | [], _, _ => True.intro
  | first :: remaining, origins, requested =>
      ⟨retained.replacementLookup_exists index _ first.monomial origins.1
          (Monomial.findPower_retainPowersWith_requested (bindings index) (first.monomial.exponentAt index)
            (retained.sums.powersAt index) exponents requested.1),
        retained.replacementLookup_complete index exponents remaining origins.2 requested.2⟩

end Terms

namespace Monomial

/-- Compare each retained prefix power using its actual cached predecessor and original generator.

The comparison never reconstructs a coherent finite-power channel. Every
multiplication receives the actual stored predecessor and generator, and the
result is transported to the actual cached current power by its retained
whole-channel equation.
-/
private def prefixPower_agrees (generator : CoherentNamed) (source : GeometricApproximation)
    (sourceEq : NamedEquivalent generator.name source.toApproximation.toNamed)
    {degree : Nat} (powers : PowerPrefix generator degree) :
    (exponent : Nat) → (below : exponent < degree) →
    NamedEquivalent (powerFrom generator powers.val exponent (powers.property exponent below)).val.name
      (CoherentEvaluation.powerSource source exponent).toApproximation.toNamed
  | 0, below => by
      let actual := powerFrom generator powers.val 0 (powers.property 0 below)
      have same : actual.val = Coherence.exact 1 := actual.property
      have agreement := CoherentEvaluation.exact_agrees (1 : Coefficient)
      rewrite [← same] at agreement
      exact agreement
  | exponent + 1, below => by
      have earlier : exponent < degree := Nat.lt_trans (Nat.lt_succ_self exponent) below
      let prior := powerFrom generator powers.val exponent (powers.property exponent earlier)
      let actual := powerFrom generator powers.val (exponent + 1) (powers.property (exponent + 1) below)
      have same : actual.val = CoherentNamed.mul prior.val generator :=
        actual.property.trans (congrArg (fun value => CoherentNamed.mul value generator) prior.property.symm)
      have agreement := CoherentEvaluation.mul_agrees prior.val generator
        (CoherentEvaluation.powerSource source exponent) source
        (prefixPower_agrees generator source sourceEq powers exponent earlier) sourceEq
      rewrite [← same] at agreement
      exact agreement

/-- Compare an actual supplied original power through the same complete retained predecessor bank. -/
def powerFrom_agrees (generator : CoherentNamed) (source : GeometricApproximation)
    (sourceEq : NamedEquivalent generator.name source.toApproximation.toNamed)
    {degree : Nat} (powers : PowerPrefix generator degree) (exponent : Fin degree)
    (actual : {channel : CoherentNamed // channel = Power.namedPower generator exponent.val}) :
    NamedEquivalent actual.val.name (CoherentEvaluation.powerSource source exponent.val).toApproximation.toNamed := by
  let selected := powerFrom generator powers.val exponent.val (powers.property exponent.val exponent.isLt)
  have same : actual.val = selected.val := actual.property.trans selected.property.symm
  have agreement := prefixPower_agrees generator source sourceEq powers exponent.val exponent.isLt
  rewrite [← same] at agreement
  exact agreement

/-- Stored power prefixes at the original finite variable positions. -/
abbrev PowerBanks {arity : Nat} (environment : Fin arity → CoherentNamed) (bounds : Fin arity → Nat) :=
  DependentVector (fun index => PowerPrefix (environment index) (bounds index))

/-- Retained monomial interpretations in their original occurrence order. -/
abbrev Caches {arity : Nat} (environment : Fin arity → CoherentNamed) :=
  List ((monomial : Monomial arity) × Denotation monomial environment)

/-- Read the first literal matching monomial interpretation from the stored inventory. -/
@[expose] def findCache {arity : Nat} {environment : Fin arity → CoherentNamed}
    (monomial : Monomial arity) : Caches environment → Option (Denotation monomial environment)
  | [] => none
  | first :: remaining =>
      if same : first.1 = monomial then some (same ▸ first.2)
      else findCache monomial remaining

/-- The first matching occurrence supplies its complete original monomial cache. -/
theorem findCache_head {arity : Nat} {environment : Fin arity → CoherentNamed}
    (monomial : Monomial arity) (retained : Denotation monomial environment) (remaining : Caches environment) :
    findCache monomial (⟨monomial, retained⟩ :: remaining) = some retained := by
  unfold findCache
  rewrite [dif_pos rfl]
  rfl

/-- Read an actual retained product's suffix without rebuilding its powers or numerical channel. -/
@[expose] def Products.tail {arity : Nat} {exponent : Nat} {remaining : Monomial arity}
    {environment : Fin (arity + 1) → CoherentNamed} {channel : CoherentNamed}
    (products : Products (.cons exponent remaining) environment channel) :
    Denotation remaining (fun index => environment index.succ) :=
  match products with
  | .cons _ _ _ _ _ tailChannel tail _ _ => ⟨tailChannel, tail⟩

/-- Project the actual suffix interpretations in the same stored occurrence order. -/
@[expose] def tails {arity : Nat} {environment : Fin (arity + 1) → CoherentNamed} :
    Caches environment → Caches (fun index => environment index.succ)
  | [] => []
  | ⟨.cons _ remaining, retained⟩ :: rest => ⟨remaining, retained.products.tail⟩ :: tails rest

/-- Construct a target monomial from its existing cache or actual stored variable powers and suffixes.

A complete old match is returned literally. Otherwise the recursion searches
only projected original suffix caches and multiplies a certified stored power
by that actual suffix output. There is no finite-power evaluator fallback.
-/
@[expose] def retainWithBanks : {arity : Nat} → (monomial : Monomial arity) →
    (environment : Fin arity → CoherentNamed) → (bounds : Fin arity → Nat) →
    PowerBanks environment bounds → Caches environment →
    (∀ index, monomial.exponentAt index < bounds index) → Denotation monomial environment
  | 0, .nil, environment, _bounds, banks, cached, _below =>
      match findCache .nil cached with
      | some retained => retained
      | none => match banks with
        | .nil => ⟨CoherentNamed.Coherence.exact 1, .nil environment _ rfl⟩
  | _ + 1, .cons exponent remaining, environment, bounds, banks, cached, below =>
      match findCache (.cons exponent remaining) cached with
      | some retained => retained
      | none => match banks with
        | .cons first rest =>
            let tail := retainWithBanks remaining (fun index => environment index.succ)
              (fun index => bounds index.succ) rest (tails cached)
              (exponentAt_tail_lt exponent remaining bounds below)
            let power := first.power ⟨exponent, exponentAt_head_lt exponent remaining bounds below⟩
            let channel := CoherentNamed.mul power.val tail.channel
            ⟨channel, .cons exponent remaining environment power.val power.property
              tail.channel tail.products channel rfl⟩
termination_by structural _ monomial _ _ _ _ _ => monomial

/-- Nonempty retained construction uses the original lookup or the same actual prefix and suffix caches. -/
theorem retainWithBanks_cons {arity : Nat} (exponent : Nat) (remaining : Monomial arity)
    (environment : Fin (arity + 1) → CoherentNamed) (bounds : Fin (arity + 1) → Nat)
    (first : PowerPrefix (environment 0) (bounds 0))
    (rest : PowerBanks (fun index => environment index.succ) (fun index => bounds index.succ))
    (cached : Caches environment)
    (below : ∀ index, (.cons exponent remaining : Monomial (arity + 1)).exponentAt index < bounds index) :
    retainWithBanks (.cons exponent remaining) environment bounds (.cons first rest) cached below =
      (match findCache (.cons exponent remaining) cached with
      | some original => original
      | none =>
          let tail := retainWithBanks remaining (fun index => environment index.succ)
            (fun index => bounds index.succ) rest (tails cached)
            (exponentAt_tail_lt exponent remaining bounds below)
          let power := first.power ⟨exponent, exponentAt_head_lt exponent remaining bounds below⟩
          let channel := CoherentNamed.mul power.val tail.channel
          ⟨channel, .cons exponent remaining environment power.val power.property
            tail.channel tail.products channel rfl⟩) := rfl

/-- A successful original lookup supplies the literal complete output of retained monomial construction. -/
theorem retainWithBanks_existing {arity : Nat} (monomial : Monomial arity)
    (environment : Fin arity → CoherentNamed) (bounds : Fin arity → Nat)
    (banks : PowerBanks environment bounds) (cached : Caches environment)
    (below : ∀ index, monomial.exponentAt index < bounds index)
    (retained : Denotation monomial environment) (found : findCache monomial cached = some retained) :
    retainWithBanks monomial environment bounds banks cached below = retained := by
  cases monomial with
  | nil =>
      cases banks
      unfold retainWithBanks
      rewrite [found]
      rfl
  | cons exponent remaining =>
      cases banks with
      | cons first rest =>
          rewrite [retainWithBanks_cons, found]
          rfl

/-- Rebuilding a changed first exponent retains an unchanged actual old suffix interpretation literally. -/
theorem retainWithBanks_suffix {arity : Nat} (exponent : Nat) (remaining : Monomial arity)
    (environment : Fin (arity + 1) → CoherentNamed) (bounds : Fin (arity + 1) → Nat)
    (banks : PowerBanks environment bounds) (cached : Caches environment)
    (below : ∀ index, (.cons exponent remaining : Monomial (arity + 1)).exponentAt index < bounds index)
    (missing : findCache (.cons exponent remaining) cached = none)
    (suffix : Denotation remaining (fun index => environment index.succ))
    (known : findCache remaining (tails cached) = some suffix) :
    (retainWithBanks (.cons exponent remaining) environment bounds banks cached below).products.tail = suffix := by
  cases banks with
  | cons first rest =>
      have built := retainWithBanks_cons exponent remaining environment bounds first rest cached below
      rewrite [missing] at built
      have projected := congrArg
        (fun result : Denotation (.cons exponent remaining) environment => result.products.tail) built
      exact projected.trans (retainWithBanks_existing remaining _ _ rest (tails cached) _ suffix known)

/-- Rebuilding a missing monomial consumes the literal stored first power from its certified prefix. -/
theorem retainWithBanks_power {arity : Nat} (exponent : Nat) (remaining : Monomial arity)
    (environment : Fin (arity + 1) → CoherentNamed) (bounds : Fin (arity + 1) → Nat)
    (first : PowerPrefix (environment 0) (bounds 0))
    (rest : PowerBanks (fun index => environment index.succ) (fun index => bounds index.succ))
    (cached : Caches environment)
    (below : ∀ index, (.cons exponent remaining : Monomial (arity + 1)).exponentAt index < bounds index)
    (missing : findCache (.cons exponent remaining) cached = none) :
    (retainWithBanks (.cons exponent remaining) environment bounds (.cons first rest) cached below).products.powerAt 0 =
      (⟨(first.power ⟨exponent, exponentAt_head_lt exponent remaining bounds below⟩).val,
        (first.power ⟨exponent, exponentAt_head_lt exponent remaining bounds below⟩).property.trans
          (congrArg (Power.namedPower (environment 0)) (exponentAt_cons_zero exponent remaining).symm)⟩ :
        {channel : CoherentNamed // channel = Power.namedPower (environment 0)
          ((.cons exponent remaining : Monomial (arity + 1)).exponentAt 0)}) := by
  have built := retainWithBanks_cons exponent remaining environment bounds first rest cached below
  rewrite [missing] at built
  exact congrArg
    (fun result : Denotation (.cons exponent remaining) environment => result.products.powerAt 0) built

/-- The synchronized scalar sample program of an original exponent vector. -/
@[expose] def source : {arity : Nat} → Monomial arity →
    (Fin arity → GeometricApproximation) → GeometricApproximation
  | 0, .nil, _ => GeometricApproximation.exact 1
  | _ + 1, .cons exponent remaining, inputs =>
      (CoherentEvaluation.powerSource (inputs 0) exponent).mul (source remaining (fun index => inputs index.succ))

/-- Every monomial source sample is its scalar evaluation at the same original input indices. -/
theorem source_sample : {arity : Nat} → (monomial : Monomial arity) →
    (inputs : Fin arity → GeometricApproximation) → (index : Nat) →
    (source monomial inputs).sample index = monomial.eval (fun inputIndex => (inputs inputIndex).sample index)
  | 0, .nil, _, _ => rfl
  | _ + 1, .cons exponent remaining, inputs, index => by
      change ((CoherentEvaluation.powerSource (inputs 0) exponent).mul
        (source remaining (fun inputIndex => inputs inputIndex.succ))).sample index = _
      rewrite [GeometricApproximation.mul_sample, CoherentEvaluation.powerSource_sample, source_sample]
      rfl

/-- Compare actual retained powers and suffix channels to the synchronized finite scalar program.

Every product comparison receives the stored power and suffix channel. Prefix
comparison consumes the same actual predecessor bank, and the final endpoint
is transported using this original product's retained construction equation.
-/
def Products.source_agrees : {arity : Nat} → {monomial : Monomial arity} →
    {environment : Fin arity → CoherentNamed} → {channel : CoherentNamed} →
    Products monomial environment channel → (bounds : Fin arity → Nat) →
    PowerBanks environment bounds → (∀ index, monomial.exponentAt index < bounds index) →
    (inputs : Fin arity → GeometricApproximation) →
    (∀ index, NamedEquivalent (environment index).name (inputs index).toApproximation.toNamed) →
    NamedEquivalent channel.name (source monomial inputs).toApproximation.toNamed
  | _, _, _, _, .nil _ _ same, _, .nil, _, _, _ => by
      have agreement := CoherentEvaluation.exact_agrees (1 : Coefficient)
      rewrite [← same] at agreement
      exact agreement
  | _, _, environment, _, .cons exponent remaining _ power power_eq tailChannel tail _ same,
      bounds, .cons first rest, below, inputs, inputEq => by
      have powers := powerFrom_agrees (environment 0) (inputs 0) (inputEq 0) first
        ⟨exponent, below 0⟩ ⟨power, power_eq⟩
      have suffix := tail.source_agrees (fun index => bounds index.succ) rest
        (fun index => below index.succ) (fun index => inputs index.succ) (fun index => inputEq index.succ)
      have agreement := CoherentEvaluation.mul_agrees power tailChannel
        (CoherentEvaluation.powerSource (inputs 0) exponent)
        (source remaining (fun index => inputs index.succ)) powers suffix
      rewrite [← same] at agreement
      exact agreement

end Monomial

namespace Term

/-- The synchronized scalar program of the original coefficient and exponent vector. -/
@[expose] def source {arity : Nat} (inputs : Fin arity → GeometricApproximation) (term : Term Coefficient arity) :
    GeometricApproximation :=
  (GeometricApproximation.exact term.coefficient).mul (Monomial.source term.monomial inputs)

/-- The same retained coefficient multiplies the monomial reading at every source sample. -/
theorem source_sample {arity : Nat} (inputs : Fin arity → GeometricApproximation)
    (term : Term Coefficient arity) (index : Nat) :
    (source inputs term).sample index = term.eval (fun inputIndex => (inputs inputIndex).sample index) := by
  unfold source
  rewrite [GeometricApproximation.mul_sample, GeometricApproximation.exact_sample, Monomial.source_sample]
  rfl

/-- Compare the literal original coefficient and monomial caches to their finite scalar program. -/
def Denotation.source_agrees {arity : Nat} {environment : Fin arity → CoherentNamed}
    {term : Term Coefficient arity} (retained : Denotation environment term)
    (bounds : Fin arity → Nat) (banks : Monomial.PowerBanks environment bounds)
    (below : ∀ index, term.monomial.exponentAt index < bounds index)
    (inputs : Fin arity → GeometricApproximation)
    (inputEq : ∀ index, NamedEquivalent (environment index).name (inputs index).toApproximation.toNamed) :
    NamedEquivalent retained.channel.name (source inputs term).toApproximation.toNamed := by
  have coefficient := CoherentEvaluation.exact_agrees term.coefficient
  rewrite [← retained.coefficient_eq] at coefficient
  have agreement := CoherentEvaluation.mul_agrees retained.coefficient retained.monomial.channel
    (GeometricApproximation.exact term.coefficient) (Monomial.source term.monomial inputs) coefficient
    (retained.monomial.products.source_agrees bounds banks below inputs inputEq)
  rewrite [← retained.product_eq] at agreement
  exact agreement

end Term

namespace Terms

/-- The original retained term interpretations indexed by their complete ordered coefficient lists. -/
abbrev Caches {arity : Nat} (environment : Fin arity → CoherentNamed) :=
  List ((terms : List (Term Coefficient arity)) × Denotation environment terms)

/-- One scalar ceiling at each original variable bounds the complete displayed term list. -/
@[expose] def Bounded {arity : Nat} (bounds : Fin arity → Nat) (terms : List (Term Coefficient arity)) : Prop :=
  ∀ index, ExponentBelow index (bounds index) terms

/-- Retain the original term monomial caches without changing their occurrence order or stored fields. -/
@[expose] def Sums.monomials {arity : Nat} {environment : Fin arity → CoherentNamed} :
    {terms : List (Term Coefficient arity)} → {channel : CoherentNamed} → Sums environment terms channel →
    Monomial.Caches environment
  | _, _, .nil _ _ => []
  | _, _, .cons first _ head _ remaining _ _ => ⟨first.monomial, head.monomial⟩ :: remaining.monomials

/-- Collect actual original monomial caches, retaining source order and duplicate occurrences. -/
@[expose] def monomials {arity : Nat} {environment : Fin arity → CoherentNamed} :
    Caches environment → Monomial.Caches environment
  | [] => []
  | first :: remaining => first.2.sums.monomials ++ monomials remaining

/-- Collect actual original powers at one bounded variable, retaining each source's occurrence order. -/
@[expose] def powersAt {arity : Nat} {environment : Fin arity → CoherentNamed} (index : Fin arity) :
    Caches environment → List (Monomial.PowerEntry (environment index))
  | [] => []
  | first :: remaining => first.2.sums.powersAt index ++ powersAt index remaining

/-- Compute a common finite exponent ceiling over actual original coefficient lists. -/
@[expose] def cacheBound {arity : Nat} {environment : Fin arity → CoherentNamed} (index : Fin arity) :
    Caches environment → Nat
  | [] => 1
  | first :: remaining => max (exponentBound index first.1) (cacheBound index remaining)

/-- Every actual source list is bounded by the computed common exponent ceiling. -/
theorem cacheBound_below {arity : Nat} {environment : Fin arity → CoherentNamed} (index : Fin arity) :
    (sources : Caches environment) → (terms : List (Term Coefficient arity)) →
    (retained : Denotation environment terms) → (⟨terms, retained⟩ : (items : List (Term Coefficient arity)) ×
      Denotation environment items) ∈ sources → ExponentBelow index (cacheBound index sources) terms
  | [], _, _, present => by cases present
  | first :: remaining, terms, retained, present => by
      cases mem_cons.mp present with
      | inl same =>
          cases same
          exact exponentBelow_mono index (Order.le_max_left _ _) _ (exponentBound_below index _)
      | inr later =>
          exact exponentBelow_mono index (Order.le_max_right _ _) _
            (cacheBound_below index remaining terms retained later)

/-- Materialize complete power banks from the actual original term caches, adding only missing predecessors. -/
@[expose] def retainBanks {arity : Nat} (environment : Fin arity → CoherentNamed) (sources : Caches environment) :
    Monomial.PowerBanks environment (fun index => cacheBound index sources) :=
  DependentVector.ofFn (fun index =>
    Monomial.retainPowerPrefix (environment index) (powersAt index sources) (cacheBound index sources))

/-- Lookup returns the literal complete prefix built from the actual original selected powers. -/
theorem retainBanks_get {arity : Nat} (environment : Fin arity → CoherentNamed) (sources : Caches environment)
    (index : Fin arity) :
    (retainBanks environment sources).get index =
      Monomial.retainPowerPrefix (environment index) (powersAt index sources) (cacheBound index sources) :=
  DependentVector.ofFn_get _ index

/-- Construct an ordered finite interpretation using only retained powers and actual old suffix caches. -/
@[expose] def retainWithBanks {arity : Nat} (environment : Fin arity → CoherentNamed)
    (bounds : Fin arity → Nat) (banks : Monomial.PowerBanks environment bounds)
    (cached : Monomial.Caches environment) :
    (terms : List (Term Coefficient arity)) → Bounded bounds terms → Denotation environment terms
  | [], _ => ⟨CoherentNamed.Coherence.exact 0, .nil _ rfl⟩
  | first :: remaining, below =>
      let monomial := Monomial.retainWithBanks first.monomial environment bounds banks cached
        (fun index => (below index).1)
      let head := Term.withMonomial environment first monomial
      let tail := retainWithBanks environment bounds banks cached remaining (fun index => (below index).2)
      let channel := CoherentNamed.add head.channel tail.channel
      ⟨channel, .cons first remaining head tail.channel tail.sums channel rfl⟩

/-- The synchronized scalar program of the complete original ordered coefficient list. -/
@[expose] def source {arity : Nat} (inputs : Fin arity → GeometricApproximation) :
    List (Term Coefficient arity) → GeometricApproximation
  | [] => GeometricApproximation.exact 0
  | first :: remaining => (Term.source inputs first).add (source inputs remaining)

/-- Every ordered source sum evaluates the original coefficient list at the same finite input samples. -/
theorem source_sample {arity : Nat} (inputs : Fin arity → GeometricApproximation) :
    (terms : List (Term Coefficient arity)) → (index : Nat) →
    (source inputs terms).sample index = eval (fun inputIndex => (inputs inputIndex).sample index) terms
  | [], _ => rfl
  | first :: remaining, index => by
      change ((Term.source inputs first).add (source inputs remaining)).sample index = _
      rewrite [GeometricApproximation.add_sample, Term.source_sample, source_sample]
      rfl

/-- Compare the actual retained coefficient products and suffix sums with their finite scalar program. -/
def Sums.source_agrees {arity : Nat} {environment : Fin arity → CoherentNamed}
    (bounds : Fin arity → Nat) (banks : Monomial.PowerBanks environment bounds)
    (inputs : Fin arity → GeometricApproximation)
    (inputEq : ∀ index, NamedEquivalent (environment index).name (inputs index).toApproximation.toNamed) :
    {terms : List (Term Coefficient arity)} → {channel : CoherentNamed} →
    Sums environment terms channel → Bounded bounds terms →
    NamedEquivalent channel.name (source inputs terms).toApproximation.toNamed
  | _, _, .nil _ same, _ => by
      have agreement := CoherentEvaluation.exact_agrees (0 : Coefficient)
      rewrite [← same] at agreement
      exact agreement
  | _, _, .cons first remaining head tailChannel tail _ same, below => by
      have agreement := CoherentEvaluation.add_agrees head.channel tailChannel
        (Term.source inputs first) (source inputs remaining)
        (head.source_agrees bounds banks (fun index => (below index).1) inputs inputEq)
        (tail.source_agrees bounds banks inputs inputEq (fun index => (below index).2))
      rewrite [← same] at agreement
      exact agreement

/-- Read the operational bridge from the actual original sum cache. -/
def Denotation.source_agrees {arity : Nat} {environment : Fin arity → CoherentNamed}
    {terms : List (Term Coefficient arity)} (retained : Denotation environment terms)
    (bounds : Fin arity → Nat) (banks : Monomial.PowerBanks environment bounds) (below : Bounded bounds terms)
    (inputs : Fin arity → GeometricApproximation)
    (inputEq : ∀ index, NamedEquivalent (environment index).name (inputs index).toApproximation.toNamed) :
    NamedEquivalent retained.channel.name (source inputs terms).toApproximation.toNamed :=
  retained.sums.source_agrees bounds banks inputs inputEq below

end Terms

namespace Terms.Denotation

/-- Original input and computed-output interpretation caches for one exact coefficient construction.

This is an indexed view of existing coefficient forms, dependent power banks
and complete denotations. Its proof binds the stored form to the original
coefficient operation and bounds every original input and output exponent.
It stores no alternative polynomial syntax or operational equivalence.
-/
abbrev Prepared {arity : Nat} (environment : Fin arity → CoherentNamed)
    (sources : Terms.Caches environment) (target : Sparse Coefficient arity) :=
  (bounds : Fin arity → Nat) × Monomial.PowerBanks environment bounds ×
    (form : Sparse Coefficient arity) × Terms.Denotation environment form.terms ×
      PLift (form = target ∧ Terms.Bounded bounds form.terms ∧
        ∀ terms retained, (⟨terms, retained⟩ : (items : List (Term Coefficient arity)) ×
          Terms.Denotation environment items) ∈ sources → Terms.Bounded bounds terms)

namespace Prepared

variable {arity : Nat} {environment : Fin arity → CoherentNamed}
  {sources : Terms.Caches environment} {target : Sparse Coefficient arity}

/-- Read the stored original finite exponent ceilings. -/
abbrev bounds (prepared : Prepared environment sources target) := prepared.1

/-- Read the actual stored original-variable power banks. -/
abbrev banks (prepared : Prepared environment sources target) := prepared.2.1

/-- Read the actual computed coefficient form. -/
abbrev form (prepared : Prepared environment sources target) := prepared.2.2.1

/-- Read the actual output interpretation built from the original retained powers and suffix products. -/
abbrev denotation (prepared : Prepared environment sources target) := prepared.2.2.2.1

/-- The stored coefficient form is the original specified coefficient operation. -/
theorem form_eq (prepared : Prepared environment sources target) : prepared.form = target :=
  prepared.2.2.2.2.down.1

/-- Every stored output exponent is covered by the same actual retained power banks. -/
theorem bounded (prepared : Prepared environment sources target) : Terms.Bounded prepared.bounds prepared.form.terms :=
  prepared.2.2.2.2.down.2.1

/-- Every actual original source occurrence is covered by those same retained power banks. -/
theorem source_bounded (prepared : Prepared environment sources target)
    {terms : List (Term Coefficient arity)} (retained : Terms.Denotation environment terms)
    (present : (⟨terms, retained⟩ : (items : List (Term Coefficient arity)) ×
      Terms.Denotation environment items) ∈ sources) : Terms.Bounded prepared.bounds terms :=
  prepared.2.2.2.2.down.2.2 terms retained present

end Prepared

/-- Prepare one actual coefficient form using the original retained powers and monomial suffix caches.

Coefficient selection is supplied by the original finite polynomial operation.
The form is stored once. Power completion preserves existing entries and builds
only missing predecessors; output products consume that complete bank and
literal old monomial or suffix caches. The source inventory stays indexed by
its actual ordered original denotations.
-/
@[expose] def prepare {arity : Nat} (environment : Fin arity → CoherentNamed)
    (sources : Terms.Caches environment) (target : Sparse Coefficient arity)
    (retained : Option (Terms.Denotation environment target.terms) := none)
    (powerEntries : Option (DependentVector
      (fun index => List (Monomial.PowerEntry (environment index)))) := none) :
    Prepared environment sources target := by
  let bounds := fun index => max (Terms.exponentBound index target.terms) (Terms.cacheBound index sources)
  let banks : Monomial.PowerBanks environment bounds :=
    DependentVector.ofFn (fun index =>
      Monomial.retainPowerPrefix (environment index)
        (match powerEntries with
        | none => Terms.powersAt index sources
        | some entries => entries.get index) (bounds index))
  have below : Terms.Bounded bounds target.terms := fun index =>
    Terms.exponentBelow_mono index (Order.le_max_left _ _) target.terms
      (Terms.exponentBound_below index target.terms)
  let denotation := match retained with
    | some denotation => denotation
    | none => Terms.retainWithBanks environment bounds banks (Terms.monomials sources) target.terms below
  exact ⟨bounds, banks, target, denotation, ⟨⟨rfl, below, fun terms retained present index =>
    Terms.exponentBelow_mono index (Order.le_max_right _ _) terms
      (Terms.cacheBound_below index sources terms retained present)⟩⟩⟩

/-- Preparation stores the complete original computed coefficient form literally. -/
theorem prepare_form {arity : Nat} (environment : Fin arity → CoherentNamed)
    (sources : Terms.Caches environment) (target : Sparse Coefficient arity) :
    (prepare environment sources target).form = target := rfl

/-- Preparation stores the actual output interpretation produced from the same stored banks and source inventory. -/
theorem prepare_denotation {arity : Nat} (environment : Fin arity → CoherentNamed)
    (sources : Terms.Caches environment) (target : Sparse Coefficient arity) :
    (prepare environment sources target).denotation =
      Terms.retainWithBanks environment (prepare environment sources target).bounds
        (prepare environment sources target).banks (Terms.monomials sources) target.terms
        (prepare environment sources target).bounded := rfl

/-- Every original stored power is preserved literally in the same prepared variable bank. -/
theorem prepare_power_existing {arity : Nat} (environment : Fin arity → CoherentNamed)
    (sources : Terms.Caches environment) (target : Sparse Coefficient arity) (index : Fin arity)
    (exponent : Nat) (power : {channel : CoherentNamed // channel = Power.namedPower (environment index) exponent})
    (known : Monomial.findPower (environment index) exponent (Terms.powersAt index sources) = some power) :
    Monomial.findPower (environment index) exponent ((prepare environment sources target).banks.get index).val =
      some power := by
  change Monomial.findPower (environment index) exponent
    ((DependentVector.ofFn (fun inputIndex =>
      Monomial.retainPowerPrefix (environment inputIndex) (Terms.powersAt inputIndex sources)
        ((prepare environment sources target).bounds inputIndex))).get index).val = some power
  rewrite [DependentVector.ofFn_get]
  exact Monomial.findPower_retainPowerPrefix_preserves (environment index) exponent power
    (Terms.powersAt index sources) known _

/-- A supplied original output interpretation is retained completely, without rebuilding its ordered sums. -/
theorem prepare_retained_denotation {arity : Nat} (environment : Fin arity → CoherentNamed)
    (sources : Terms.Caches environment) (target : Sparse Coefficient arity)
    (retained : Terms.Denotation environment target.terms)
    (powerEntries : Option (DependentVector
      (fun index => List (Monomial.PowerEntry (environment index)))) := none) :
    (prepare environment sources target (some retained) powerEntries).denotation = retained := rfl

/-- Stored named-source approximations and their original operational relation witnesses. -/
abbrev Inputs {arity : Nat} (environment : Fin arity → CoherentNamed) :=
  DependentVector (fun index => (source : GeometricApproximation) ×
    NamedEquivalent (environment index).name source.toApproximation.toNamed)

/-- Store each original variable's geometric sampler and comparison once at its actual finite position. -/
@[expose] def inputs {arity : Nat} (environment : Fin arity → CoherentNamed) : Inputs environment :=
  DependentVector.ofFn (fun index =>
    let source := GeometricApproximation.ofNamed (environment index).name
    ⟨source, CoherentEvaluation.named_agrees (environment index) ⟨source, rfl⟩⟩)

/-- Read the literal stored source approximation for one original finite variable. -/
abbrev Inputs.source {arity : Nat} {environment : Fin arity → CoherentNamed}
    (inputs : Inputs environment) (index : Fin arity) := (inputs.get index).1

/-- Read the actual original source's retained operational relation witness. -/
abbrev Inputs.equivalent {arity : Nat} {environment : Fin arity → CoherentNamed}
    (inputs : Inputs environment) (index : Fin arity) := (inputs.get index).2

/-- Compare an actual prepared output through its retained original power and term caches. -/
def Prepared.equivalent {arity : Nat} {environment : Fin arity → CoherentNamed}
    {sources : Terms.Caches environment} {target : Sparse Coefficient arity}
    (prepared : Prepared environment sources target) (inputs : Inputs environment) :
    NamedEquivalent prepared.denotation.channel.name
      (Terms.source inputs.source prepared.form.terms).toApproximation.toNamed :=
  prepared.denotation.source_agrees prepared.bounds prepared.banks prepared.bounded inputs.source inputs.equivalent

/-- Compare an actual source occurrence using the same prepared original variable-power bank. -/
def Prepared.source_equivalent {arity : Nat} {environment : Fin arity → CoherentNamed}
    {sources : Terms.Caches environment} {target : Sparse Coefficient arity}
    (prepared : Prepared environment sources target) (inputs : Inputs environment)
    {terms : List (Term Coefficient arity)} (retained : Terms.Denotation environment terms)
    (present : (⟨terms, retained⟩ : (items : List (Term Coefficient arity)) ×
      Terms.Denotation environment items) ∈ sources) :
    NamedEquivalent retained.channel.name (Terms.source inputs.source terms).toApproximation.toNamed :=
  retained.source_agrees prepared.bounds prepared.banks (prepared.source_bounded retained present)
    inputs.source inputs.equivalent

end Terms.Denotation

namespace Monomial

/-- Retain actual source powers at a renamed variable whose original numerical channel is literally the target channel.

Original source products and their variable positions remain indexed throughout.
The supplied equalities transport only the power specifications; the actual
stored numerical channels are returned unchanged, in original variable order.
-/
@[expose] def Products.renamePowers {target : Nat} : {arity : Nat} → {monomial : Monomial arity} →
    {environment : Fin arity → CoherentNamed} → {channel : CoherentNamed} →
    Products monomial environment channel → (destination : Fin target → CoherentNamed) →
    (mapping : Fin arity → Fin target) → (∀ index, environment index = destination (mapping index)) →
    (index : Fin target) → List (PowerEntry (destination index))
  | _, _, _, _, .nil _ _ _, _, _, _, _ => []
  | _, _, _, _, .cons exponent _ _ power power_eq _ tail _ _, destination, mapping, same, index =>
      let remaining := tail.renamePowers destination (fun next => mapping next.succ) (fun next => same next.succ) index
      if selected : mapping 0 = index then
        let generator_eq := (same 0).trans (congrArg destination selected)
        ⟨exponent, ⟨power,
          power_eq.trans (congrArg (fun generator => Power.namedPower generator exponent) generator_eq)⟩⟩ :: remaining
      else remaining

end Monomial

namespace Terms

/-- Retain renamed actual generator powers in original term and variable occurrence order. -/
@[expose] def Sums.renamePowers {arity target : Nat} {environment : Fin arity → CoherentNamed}
    (destination : Fin target → CoherentNamed) (mapping : Fin arity → Fin target)
    (same : ∀ index, environment index = destination (mapping index)) (index : Fin target) :
    {terms : List (Term Coefficient arity)} → {channel : CoherentNamed} → Sums environment terms channel →
    List (Monomial.PowerEntry (destination index))
  | _, _, .nil _ _ => []
  | _, _, .cons _ _ head _ remaining _ _ =>
      head.monomial.products.renamePowers destination mapping same index ++
        remaining.renamePowers destination mapping same index

end Terms

end Purelib.Polynomial.Multivariate

end
