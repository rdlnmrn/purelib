module
import Purelib.Data.Nat.Addition
import Purelib.Data.List.Membership
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction

section
@[expose] public section

/-!
# Explicit finite repeated sampling

An `iidSamples` table contains lists of exactly a supplied natural number of
draws from one displayed rational distribution.  The construction uses only
finite products and pushforwards.  Sample sums and means then have exact
rational expectation and variance formulas, giving a one-shot finite
Chebyshev estimate with the familiar reciprocal sample-count factor.

No infinite product, sequence of random variables, or asymptotic law is
constructed.
-/

namespace Purelib.Measure
namespace Distribution

/-- Construct the exact finite law of ordered independent draws from the original distribution.

Zero draws give the point mass at the empty list; each successor retains the product of one original draw with the
recursively constructed tail law. -/
def iidSamples {α : Type} (source : Distribution α) :
    Nat → Distribution (List α)
  | 0 => Distribution.pure []
  | count + 1 =>
      (source.product (iidSamples source count)).map fun pair =>
        pair.1 :: pair.2

/-- Zero independent draws give exactly the point mass at the empty sample list. -/
theorem iidSamples_zero {α : Type} (source : Distribution α) :
    iidSamples source 0 = Distribution.pure [] := rfl

/-- A successor sample law is the exact pushforward of the original source times the retained tail law by list
construction. -/
theorem iidSamples_succ {α : Type} (source : Distribution α)
    (count : Nat) :
    iidSamples source (count + 1) =
      (source.product (iidSamples source count)).map fun pair =>
        pair.1 :: pair.2 := rfl

/-- The exact sample law has the original atom count raised to the number of draws. -/
theorem iidSamples_atoms_length {α : Type} (source : Distribution α) :
    ∀ count : Nat,
      (iidSamples source count).atoms.length = source.atoms.length ^ count
  | 0 => rfl
  | count + 1 => by
      rw [iidSamples_succ, Distribution.map_atoms_length,
        Distribution.product_atoms_length,
        iidSamples_atoms_length source count, pow_succ]
      exact Nat.mul_comm _ _

/-- Require every sample-list occurrence to equal the payload of some retained original source atom. -/
def SampleSupportedBy {α : Type} (source : Distribution α) : List α → Prop
  | [] => True
  | item :: remaining =>
      (∃ atom, atom ∈ source.atoms ∧ atom.item = item) ∧
        SampleSupportedBy source remaining

open Purelib.Data
/-- Every member of a supported sample list has a matching retained original source atom. -/
theorem sampleSupportedBy_source_of_mem {α : Type}
    (source : Distribution α) (item : α) :
    ∀ {samples : List α}, SampleSupportedBy source samples →
      item ∈ samples →
        ∃ atom, atom ∈ source.atoms ∧ atom.item = item
  | [], supported, member => (List.not_mem_nil member).elim
  | head :: remaining, supported, member => by
      rcases supported with ⟨headSupported, tailSupported⟩
      rcases List.Membership.mem_cons.mp member with equal | tailMember
      · rcases headSupported with ⟨atom, member, atomEqual⟩
        exact ⟨atom, member, atomEqual.trans equal.symm⟩
      · exact source.sampleSupportedBy_source_of_mem item
          tailSupported tailMember

/-- Every atom of the exact independent-sample law has a sample list supported by the original source atoms. -/
theorem iidSamples_atom_sampleSupportedBy {α : Type}
    (source : Distribution α) : ∀ (count : Nat)
    (candidate : Weighted (List α)),
      candidate ∈ (source.iidSamples count).atoms →
        SampleSupportedBy source candidate.item
  | 0, candidate, member => by
      rw [iidSamples_zero] at member
      change candidate ∈ [⟨[], 1, by decide⟩] at member
      have member := List.Membership.mem_singleton.mp member
      have payloadEqual :=
        congrArg (fun atom : Weighted (List α) => atom.item) member
      rw [payloadEqual]
      trivial
  | count + 1, candidate, member => by
      rw [iidSamples_succ] at member
      rcases (source.product (source.iidSamples count)).mem_map_atoms_source
          (fun pair => pair.1 :: pair.2) candidate member with
        ⟨pairAtom, pairMember, mappedEqual⟩
      rcases source.mem_product_atoms_sources (source.iidSamples count)
          pairAtom pairMember with
        ⟨headAtom, headMember, tailAtom, tailMember, pairEqual⟩
      rw [← mappedEqual, ← pairEqual]
      exact ⟨⟨headAtom, headMember, rfl⟩,
        source.iidSamples_atom_sampleSupportedBy count tailAtom tailMember⟩

/-- The exact independent-sample law gives probability one to lists of the requested length. -/
theorem iidSamples_probability_sampleLength_eq {α : Type}
    (source : Distribution α) : ∀ count : Nat,
    (iidSamples source count).probability
      (fun sample => decide (sample.length = count)) = 1
  | 0 => by
      rw [iidSamples_zero, Distribution.pure_probability]
      rfl
  | count + 1 => by
      rw [iidSamples_succ, Distribution.map_probability]
      calc
        (source.product (iidSamples source count)).probability
              (fun pair : α × List α =>
                decide ((pair.1 :: pair.2).length = count + 1)) =
            (source.product (iidSamples source count)).probability
              (fun pair => (fun _ : α => true) pair.1 &&
                decide (pair.2.length = count)) :=
          (source.product (iidSamples source count)).probability_congr _ _
            (fun pair => by
              change decide (pair.2.length + 1 = count + 1) =
                (true && decide (pair.2.length = count))
              cases equal : decide (pair.2.length = count)
              · have unequal : pair.2.length ≠ count := of_decide_eq_false equal
                have successorUnequal : pair.2.length + 1 ≠ count + 1 :=
                  fun same => unequal (Nat.Addition.add_right_cancel same)
                rewrite [decide_eq_false successorUnequal]
                rfl
              · have same : pair.2.length = count := of_decide_eq_true equal
                rewrite [same, decide_eq_true (rfl : count + 1 = count + 1)]
                rfl)
        (source.product (iidSamples source count)).probability
              (fun pair => (fun _ : α => true) pair.1 &&
                decide (pair.2.length = count)) =
            source.probability (fun _ : α => true) *
              (iidSamples source count).probability
                (fun sample => decide (sample.length = count)) :=
          source.product_probability_rectangle (iidSamples source count)
            (fun _ => true) (fun sample => decide (sample.length = count))
        _ = 1 := by
          rewrite [source.probability_true,
            iidSamples_probability_sampleLength_eq source count, one_mul]
          rfl
end Distribution

end Purelib.Measure

end
