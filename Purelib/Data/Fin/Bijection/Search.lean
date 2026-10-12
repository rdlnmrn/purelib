module

import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Fin
import Purelib.Data.Nat.Order

public import Purelib.Data.Fin.Bijection.Basic
-- The exposed selected-preimage builder retains the original search acceptance certificate.
public import Purelib.Data.List.Search
import Purelib.Data.Fin.Cardinality
import Mathlib.Tactic.Linter.Lint
import Mathlib.Tactic.Simproc.ExistsAndEq
meta import Purelib.Elab.ConstructiveInjectivity

section
open Purelib.Data.Fin
open Purelib.Data.Fin.Bijection.Basic
open Purelib.Data.Fin.Bijection
open Purelib.Data.List
public section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

namespace Purelib.Data.Fin.Bijection
section Bijection

open scoped Purelib.Data.Nat

/-- Search all displayed finite indices for a preimage of the supplied target.

Enumerate Fin count in its core ofFn list order and return the first source whose
mapped value equals the target, or none if no source passes the equality test. -/
@[expose] def findPreimage? {count : Nat} (map : Fin count → Fin count)
    (target : Fin count) : Option (Fin count) :=
  (List.ofFn fun index : Fin count => index).find? fun source =>
    decide (map source = target)

/-- An injective endomap of Fin count reaches each displayed target.

Bounded preimage search supplies the witness on success. On failure, adjoining the
missing target would give an injection from count + 1 indices into count,
contradicting the finite cardinality bound. -/
theorem fin_surjective_of_injective {count : Nat} (map : Fin count → Fin count)
    (injective : Function.Injective map) (target : Fin count) :
    ∃ source : Fin count, map source = target := by
  match found : Bijection.findPreimage? map target with
  | some source =>
      have checked := Search.find?_eq_some_accepts_certificate found
      change decide (map source = target) = true at checked
      exact ⟨source, of_decide_eq_true checked⟩
  | none =>
    have rejected : ∀ source ∈ List.ofFn (fun index : Fin count => index),
        decide (map source = target) = false := by
      apply Search.find?_eq_none.mp
      simpa only [Bijection.findPreimage?] using found
    have targetDifferent (source : Fin count) : target ≠ map source := by
      intro equal
      have sourceMember : source ∈
          List.ofFn (fun index : Fin count => index) :=
        OfFn.Basic.mem_ofFn.mpr ⟨source, rfl⟩
      have rejectedSource := rejected source sourceMember
      have accepted : decide (map source = target) = true :=
        decide_eq_true equal.symm
      rw [accepted] at rejectedSource
      exact Bool.noConfusion rejectedSource
    let extended : Fin (count + 1) → Fin count :=
      fun index => Purelib.Data.Fin.cases target (fun source => map source) index
    have extendedInjective : Function.Injective extended := by
      intro left right equal
      cases left using Purelib.Data.Fin.cases_induction with
      | first =>
          cases right using Purelib.Data.Fin.cases_induction with
          | first => rfl
          | following rightTail =>
              have impossible : target = map rightTail := by
                simpa only [extended, Purelib.Data.Fin.cases_zero, Purelib.Data.Fin.cases_succ]
                  using equal
              exact (targetDifferent rightTail impossible).elim
      | following leftTail =>
          cases right using Purelib.Data.Fin.cases_induction with
          | first =>
              have impossible : map leftTail = target := by
                simpa only [extended, Purelib.Data.Fin.cases_zero, Purelib.Data.Fin.cases_succ]
                  using equal
              exact (targetDifferent leftTail impossible.symm).elim
          | following rightTail =>
              apply congrArg Fin.succ
              apply injective
              simpa only [extended, Purelib.Data.Fin.cases_succ] using equal
    have impossible :=
      Cardinality.fin_card_le_of_injective_direct
        extended extendedInjective
    exact (Nat.not_succ_le_self count (by
        simpa only [Nat.add_comm]
          using impossible)).elim

/-- A displayed surjectivity witness guarantees success of bounded finite preimage
search. -/
theorem findPreimage?_isSome_of_surjective
    {count : Nat} (map : Fin count → Fin count)
    (surjective : ∀ target, ∃ source, map source = target)
    (target : Fin count) : (Bijection.findPreimage? map target).isSome := by
  change ((List.ofFn fun index : Fin count => index).find?
    (fun source => decide (map source = target))).isSome = true
  apply Search.find?_isSome.mpr
  obtain ⟨source, equal⟩ := surjective target
  exact ⟨source, OfFn.Basic.mem_ofFn.mpr ⟨source, rfl⟩, decide_eq_true equal⟩

set_option genInjectivity false in
/-- Retain a selected finite source together with its equation to the target.

The map and target are parameters of the record. The retained equality certifies that
this exact source is a preimage under that map. -/
structure SelectedPreimage {count : Nat} (map : Fin count → Fin count)
    (target : Fin count) where
  /-- The source index selected by bounded preimage search. -/ source : Fin count
  /-- The supplied map sends this retained source to the target. -/ equal : map source = target

constructive_injectivity SelectedPreimage

namespace SelectedPreimage

end SelectedPreimage
/-- Return the preimage found by bounded search together with its checked equation.

The supplied surjectivity witness rules out the empty search result. The successful
branch retains the actual source selected by findPreimage?. -/
@[expose] def selectPreimage {count : Nat} (map : Fin count → Fin count)
    (surjective : ∀ target, ∃ source, map source = target)
    (target : Fin count) : SelectedPreimage map target := by
  match found : Bijection.findPreimage? map target with
  | none =>
      have present := Bijection.findPreimage?_isSome_of_surjective map surjective target
      rw [found] at present
      exact Bool.noConfusion present
  | some source =>
      have checked := Search.find?_eq_some_accepts_certificate found
      change decide (map source = target) = true at checked
      exact ⟨source, of_decide_eq_true checked⟩

/-- Construct an executable finite bijection from an injective finite endomap.

Keep the supplied map as the forward direction. The backward direction performs
bounded preimage search, and the retained search equation and injectivity prove both
inverse laws. -/
@[expose] def ofInjectiveEndomap {count : Nat} (map : Fin count → Fin count)
    (injective : Function.Injective map) : Bijection count count := by
  let surjective : ∀ target, ∃ source, map source = target :=
    Bijection.fin_surjective_of_injective map injective
  let selected (target : Fin count) : SelectedPreimage map target :=
    Bijection.selectPreimage map surjective target
  exact
    { forward := map
      backward := fun target => (selected target).source
      backward_forward := by
        intro source
        apply injective
        exact (selected (map source)).equal
      forward_backward := fun target => (selected target).equal }

/-- The bijection constructed from an injective endomap retains that exact forward map. -/
@[simp] theorem ofInjectiveEndomap_forward
    {count : Nat} (map : Fin count → Fin count)
    (injective : Function.Injective map) (index : Fin count) :
    (Bijection.ofInjectiveEndomap map injective).forward index = map index := rfl
end Bijection

end Purelib.Data.Fin.Bijection

end
