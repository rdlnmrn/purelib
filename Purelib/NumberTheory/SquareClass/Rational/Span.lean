module
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.List.Filter

import Purelib.Data.Bool.Xor
import Purelib.Data.List.Bool.Xor
import Purelib.Data.List.Nodup
import Purelib.Data.Vector.Boolean.Basic
import Purelib.LinearAlgebra.Span.Boolean.Basic
public import Purelib.LinearAlgebra.Span.Boolean.Compute
import Purelib.NumberTheory.SquareClass.Rational.Basic

public import Purelib.NumberTheory.SquareClass.Rational.Signature
import Purelib.NumberTheory.Prime.Basic
meta import Purelib.Elab.ConstructiveInjectivity

public section

/-!
# Finite chi-visible generator profiles

For one supplied finite list of positive rational square-class targets, this
module forms their finite union of prime supports, encodes every signature as
a fixed-length Boolean vector, and computes the exact XOR span.  Every listed
image retains a Boolean generator word, while arbitrary Boolean words are
classified by the span completeness certificate.  No generated subgroup is
formed as a completed set.
-/

namespace Purelib.NumberTheory.SquareClass.Rational.Span

open Purelib

open Purelib.LinearAlgebra.Span

open Purelib.NumberTheory.SquareClass

namespace GeneratorProfiles

open Purelib.NumberTheory.SquareClass.Rational.Signature.PositiveSquareClassSignatures
open _root_.Purelib.NumberTheory.SquareClass.Rational.Signature renaming Positive -> Signature

/-- A retained strictly positive rational square-class representative. -/
abbrev Target := Rational.Basic.TheoremSixtyTwo.PositiveSquareClassRepresentative

/-- Merge duplicate-free prime supports in their retained order.

The left support is followed by right entries absent from that support.
The original filter preserves the right list order and selected occurrences. -/
@[expose] def unionSupport (left right : List Nat) : List Nat :=
  left ++ difference right left

/-- Membership in the retained support union is membership in either original list. -/
theorem mem_unionSupport_iff (value : Nat) (left right : List Nat) :
    value ∈ unionSupport left right ↔ value ∈ left ∨ value ∈ right := by
  change value ∈ left ++ difference right left ↔ _
  constructor
  · intro member
    rcases Data.List.Membership.mem_append.mp member with leftMember | rightOnly
    · exact Or.inl leftMember
    · exact Or.inr ((mem_difference_iff value right left).mp rightOnly).1
  · intro member
    apply Data.List.Membership.mem_append.mpr
    rcases member with leftMember | rightMember
    · exact Or.inl leftMember
    · cases containsEq : natContains value left with
      | true => exact Or.inl ((natContains_eq_true_iff value left).mp containsEq)
      | false => exact Or.inr ((mem_difference_iff value right left).mpr
          ⟨rightMember, (natContains_eq_false_iff value left).mp containsEq⟩)

/-- The ordered union of duplicate-free supports remains duplicate-free. -/
theorem unionSupport_nodup {left right : List Nat}
    (leftNodup : left.Nodup) (rightNodup : right.Nodup) :
    (unionSupport left right).Nodup := by
  unfold unionSupport
  apply Data.List.Nodup.nodup_append leftNodup (Data.List.Filter.pairwise_filter _ rightNodup)
  intro leftValue leftMember rightValue rightMember equal
  have rightOnly := (mem_difference_iff rightValue right left).1 rightMember
  apply rightOnly.2
  exact equal ▸ leftMember

open Purelib.NumberTheory.SquareClass.Rational.Span.GeneratorProfiles in
/-- The support union preserves primality of all entries.

Each retained occurrence comes from one of the original support lists.
The supplied prime certificate for that same natural value is transported directly. -/
theorem unionSupport_prime {left right : List Nat}
    (leftPrime : ∀ prime ∈ left, NumberTheory.Prime prime)
    (rightPrime : ∀ prime ∈ right, NumberTheory.Prime prime) :
    ∀ prime ∈ unionSupport left right, NumberTheory.Prime prime := by
  intro prime member
  rcases (mem_unionSupport_iff prime left right).1 member with
    leftMember | rightMember
  · exact leftPrime prime leftMember
  · exact rightPrime prime rightMember

/-- The finite union of all odd-prime supports in a supplied target list. -/
@[expose] def support : List Target → List Nat
  | [] => []
  | target :: targets =>
      unionSupport (compute target).primes
        (support targets)

/-- The combined prime support of a finite target list has no repeated entries. -/
theorem support_nodup : ∀ targets : List Target,
    (support targets).Nodup
  | [] => List.Pairwise.nil
  | target :: targets =>
      unionSupport_nodup (compute target).primes_nodup
        (support_nodup targets)

/-- Every entry of the combined target support is prime.

Each original target signature carries prime certificates for its support.
The ordered recursive union retains those same values and certificates. -/
theorem support_prime : ∀ (targets : List Target),
    ∀ prime ∈ support targets, NumberTheory.Prime prime
  | [], prime, impossible => by nomatch impossible
  | target :: targets, prime, member =>
      unionSupport_prime (compute target).primes_prime
        (support_prime targets) prime member

open Purelib.NumberTheory.SquareClass.Rational.Span.GeneratorProfiles in
/-- Every prime in a retained target signature belongs to the combined support of its original target list. -/
theorem target_primes_subset_support : ∀ {targets : List Target}
    {target : Target}, target ∈ targets →
      ∀ prime ∈ (compute target).primes, prime ∈ support targets
  | [], _target, impossible => by nomatch impossible
  | head :: tail, target, member => by
      rcases Data.List.Membership.mem_cons.mp member with equal | tailMember
      · subst target
        intro prime primeMember
        apply (mem_unionSupport_iff prime _ _).2
        exact Or.inl primeMember
      · intro prime primeMember
        apply (mem_unionSupport_iff prime _ _).2
        exact Or.inr (target_primes_subset_support
          tailMember prime primeMember)

/-- Boolean coordinates of one signature on one displayed finite support. -/
@[expose] def signatureBits (finiteSupport primes : List Nat) : List Bool :=
  finiteSupport.map fun prime => natContains prime primes

/-- The Boolean signature has exactly the displayed support length. -/
theorem signatureBits_length (finiteSupport primes : List Nat) :
    (signatureBits finiteSupport primes).length = finiteSupport.length := by
  rw [signatureBits, Data.List.Map.length_map]

/-- Fixed-length Boolean vector of one positive rational square class.

The supplied support determines the original coordinate count and order.
Each Boolean entry reads membership in the retained target signature. -/
@[expose] def signatureVector (finiteSupport : List Nat) (target : Target) :
    Data.Vector.Boolean finiteSupport.length where
  bits := signatureBits finiteSupport (compute target).primes
  length_eq := signatureBits_length _ _

/-- Prime membership in a product signature is the Boolean XOR of its factor memberships.

The four literal Boolean cases use the original symmetric-difference support
certificate and retain both positive target signatures. -/
private theorem contains_mul_eq_bitXor (prime : Nat)
    (left right : Target) :
    natContains prime (compute (mulTarget left right)).primes =
      Purelib.Data.Bool.Xor.bitXor
        (natContains prime (compute left).primes)
        (natContains prime (compute right).primes) := by
  have productSupport := compute_mulTarget_support left right prime
  cases leftContains : natContains prime (compute left).primes with
  | false =>
      have leftAbsent := (natContains_eq_false_iff prime _).1 leftContains
      cases rightContains : natContains prime (compute right).primes with
      | false =>
          have rightAbsent :=
            (natContains_eq_false_iff prime _).1 rightContains
          have productAbsent :
              prime ∉ (compute (mulTarget left right)).primes := by
            intro member
            rcases (mem_xorSupport_iff prime _ _).1
              (productSupport.1 member) with leftOnly | rightOnly
            · exact leftAbsent leftOnly.1
            · exact rightAbsent rightOnly.1
          rw [(natContains_eq_false_iff prime _).2 productAbsent]
          rfl
      | true =>
          have rightMember :=
            (natContains_eq_true_iff prime _).1 rightContains
          have productMember :
              prime ∈ (compute (mulTarget left right)).primes :=
            productSupport.2 ((mem_xorSupport_iff prime _ _).2
              (Or.inr ⟨rightMember, leftAbsent⟩))
          rw [(natContains_eq_true_iff prime _).2 productMember]
          rfl
  | true =>
      have leftMember := (natContains_eq_true_iff prime _).1 leftContains
      cases rightContains : natContains prime (compute right).primes with
      | false =>
          have rightAbsent :=
            (natContains_eq_false_iff prime _).1 rightContains
          have productMember :
              prime ∈ (compute (mulTarget left right)).primes :=
            productSupport.2 ((mem_xorSupport_iff prime _ _).2
              (Or.inl ⟨leftMember, rightAbsent⟩))
          rw [(natContains_eq_true_iff prime _).2 productMember]
          rfl
      | true =>
          have rightMember :=
            (natContains_eq_true_iff prime _).1 rightContains
          have productAbsent :
              prime ∉ (compute (mulTarget left right)).primes := by
            intro member
            rcases (mem_xorSupport_iff prime _ _).1
              (productSupport.1 member) with leftOnly | rightOnly
            · exact leftOnly.2 rightMember
            · exact rightOnly.2 leftMember
          rw [(natContains_eq_false_iff prime _).2 productAbsent]
          rfl

/-- The Boolean encoding turns square-class multiplication into vector XOR.

Every coordinate uses the original displayed finite support and the retained
product-signature membership equation; the vector order is unchanged. -/
theorem signatureVector_mul (finiteSupport : List Nat)
    (left right : Target) :
    signatureVector finiteSupport (mulTarget left right) =
      Data.Vector.Boolean.Basic.xor
        (signatureVector finiteSupport left)
        (signatureVector finiteSupport right) := by
  apply Data.Vector.Boolean.ext
  change signatureBits finiteSupport (compute (mulTarget left right)).primes =
    Data.List.Bool.Xor.bitsXor
      (signatureBits finiteSupport (compute left).primes)
      (signatureBits finiteSupport (compute right).primes)
  induction finiteSupport with
  | nil => rfl
  | cons prime tail inductionHypothesis =>
      change natContains prime (compute (mulTarget left right)).primes ::
          signatureBits tail (compute (mulTarget left right)).primes =
        Data.Bool.Xor.bitXor (natContains prime (compute left).primes)
          (natContains prime (compute right).primes) :: _
      exact congrArg₂ List.cons (contains_mul_eq_bitXor prime left right) inductionHypothesis

/-- Generator signature vectors on their shared finite support.

Every original target contributes its signature on the same retained support.
The map keeps the target list order and its exact coordinate count. -/
@[expose] def generatorVectors (targets : List Target) :
    List (Data.Vector.Boolean (support targets).length) :=
  targets.map (signatureVector (support targets))

set_option genInjectivity false in
/-- Finite profile of the positive square-class image of supplied generators.

The cached prime support and Boolean vectors retain the supplied target order.
Their exact equations and distinct XOR-span certificate refer to those same caches. -/
structure VisibleGeneratorProfile (targets : List Target) where
  /-- The cached finite prime support shared by all original targets. -/ finiteSupport : List Nat
  /-- The retained support is the exact ordered support computed from the original targets. -/ finiteSupport_eq :
    finiteSupport = support targets
  /-- The retained shared support contains no repeated prime. -/ finiteSupport_nodup : finiteSupport.Nodup
  /-- Every retained shared-support entry is prime. -/ finiteSupport_prime : ∀ prime ∈ finiteSupport, NumberTheory.Prime
    prime
  /-- The cached Boolean signature vectors on the retained support. -/ vectors : List (Data.Vector.Boolean
    finiteSupport.length)
  /-- The retained vectors are exactly the original target signatures in list order. -/ vectors_eq : vectors =
    targets.map (signatureVector finiteSupport)
  /-- The complete distinct finite XOR span of the retained signature vectors. -/ span : Boolean.Basic.Result vectors

constructive_injectivity VisibleGeneratorProfile

/-- Compute the exact distinct XOR image of one supplied finite target list.

The builder caches the original ordered support and signature vectors once.
The executable Boolean span keeps its generator words and completeness certificate. -/
@[expose] def visibleGeneratorProfile (targets : List Target) :
    VisibleGeneratorProfile targets := by
  let finiteSupport := support targets
  let vectors := targets.map (signatureVector finiteSupport)
  exact
    { finiteSupport := finiteSupport
      finiteSupport_eq := rfl
      finiteSupport_nodup := support_nodup targets
      finiteSupport_prime := support_prime targets
      vectors := vectors
      vectors_eq := rfl
      span := Boolean.Compute.compute vectors }

/-- The computed distinct signature image has size two to the retained rank. -/
theorem visibleGeneratorProfile_image_length (targets : List Target) :
    (visibleGeneratorProfile targets).span.entries.length =
      2 ^ (visibleGeneratorProfile targets).span.rank :=
  (visibleGeneratorProfile targets).span.length_eq

/-- The computed profile contains no repeated Boolean image vectors. -/
theorem visibleGeneratorProfile_image_nodup (targets : List Target) :
    ((visibleGeneratorProfile targets).span.entries.map
      Boolean.Basic.Entry.vector).Nodup :=
  (visibleGeneratorProfile targets).span.vectors_nodup

/-- Every supplied fixed-length Boolean generator word is classified by one
retained distinct image entry. -/
theorem classifyWord (targets : List Target) (choices : List Bool)
    (lengthEq : choices.length = targets.length) :
    ∃ entry ∈ (visibleGeneratorProfile targets).span.entries,
      Boolean.Basic.evaluate choices
          (visibleGeneratorProfile targets).vectors = entry.vector := by
  apply (visibleGeneratorProfile targets).span.complete choices
  rw [(visibleGeneratorProfile targets).vectors_eq, Data.List.Map.length_map]
  exact lengthEq

end GeneratorProfiles

end Purelib.NumberTheory.SquareClass.Rational.Span

section
open Purelib
open Purelib.Data.Vector
open Purelib.LinearAlgebra.Span
open Purelib.LinearAlgebra.Span.Boolean.Basic
open Purelib.NumberTheory.SquareClass
open Purelib.NumberTheory.SquareClass.Rational.Span
open Purelib.NumberTheory.SquareClass.Rational.Signature.PositiveSquareClassSignatures
open _root_.Purelib.NumberTheory.SquareClass.Rational.Signature renaming Positive -> Signature
namespace Purelib.NumberTheory.SquareClass.Rational.Span.GeneratorProfiles

/-- Equal signature bits on a support containing the queried prime give equal membership decisions for that prime. -/
public theorem
  natContains_eq_of_signatureBits_eq
    (prime : Nat) : ∀ (finiteSupport leftPrimes rightPrimes : List Nat),
    prime ∈ finiteSupport →
      signatureBits finiteSupport leftPrimes =
        signatureBits finiteSupport rightPrimes →
      natContains prime leftPrimes = natContains prime rightPrimes
  | [], _leftPrimes, _rightPrimes, impossible, _equal => by
      nomatch impossible
  | head :: tail, leftPrimes, rightPrimes, member, equal => by
      change natContains head leftPrimes ::
          signatureBits tail leftPrimes =
        natContains head rightPrimes ::
          signatureBits tail rightPrimes at equal
      have equal := List.cons.inj equal
      cases member with
      | head => exact equal.1
      | tail _ tailMember =>
          exact
            natContains_eq_of_signatureBits_eq
            prime tail leftPrimes
            rightPrimes tailMember equal.2

/-- Prime lists with the same members have the same signature bits on every supplied support. -/
public theorem
  signatureBits_eq_of_same_members
    (finiteSupport leftPrimes rightPrimes : List Nat)
    (sameMembers : ∀ prime, prime ∈ leftPrimes ↔ prime ∈ rightPrimes) :
    signatureBits finiteSupport leftPrimes =
      signatureBits finiteSupport rightPrimes := by
  induction finiteSupport with
  | nil => rfl
  | cons prime tail inductionHypothesis =>
      change natContains prime leftPrimes ::
          signatureBits tail leftPrimes =
        natContains prime rightPrimes ::
          signatureBits tail rightPrimes
      apply congrArg₂ List.cons
      · cases leftContains : natContains prime leftPrimes <;>
          cases rightContains : natContains prime rightPrimes
        · rfl
        · have leftAbsent :=
            (natContains_eq_false_iff prime leftPrimes).mp leftContains
          have rightMember :=
            (natContains_eq_true_iff prime rightPrimes).mp rightContains
          exact False.elim (leftAbsent ((sameMembers prime).mpr rightMember))
        · have leftMember :=
            (natContains_eq_true_iff prime leftPrimes).mp leftContains
          have rightAbsent :=
            (natContains_eq_false_iff prime rightPrimes).mp rightContains
          exact False.elim (rightAbsent ((sameMembers prime).mp leftMember))
        · rfl
      · exact inductionHypothesis

/-- The empty prime support produces an all-false signature. -/
public theorem
  signatureBits_empty
  (finiteSupport : List Nat) :
    signatureBits finiteSupport [] =
      List.replicate finiteSupport.length false := by
  induction finiteSupport with
  | nil => rfl
  | cons _prime tail inductionHypothesis =>
      change false :: signatureBits tail [] =
        false :: List.replicate tail.length false
      exact congrArg (List.cons false) inductionHypothesis

/-- A complete signature supported in the displayed finite list is zero exactly when its prime list is empty. -/
public theorem
  signatureVector_eq_zero_iff_primes_empty_of_subset
    (finiteSupport : List Nat)
    (target : Target)
    (subset : ∀ prime, prime ∈ (compute target).primes →
      prime ∈ finiteSupport) :
    signatureVector finiteSupport target =
        Boolean.Basic.zero finiteSupport.length ↔
      (compute target).primes = [] := by
  constructor
  · intro vectorZero
    have bitsZero := congrArg Data.Vector.Boolean.bits vectorZero
    change signatureBits finiteSupport
        (compute target).primes = List.replicate finiteSupport.length false
      at bitsZero
    cases primesEq : (compute target).primes with
    | nil => rfl
    | cons prime tail =>
        have member : prime ∈ (compute target).primes := by
          rw [primesEq]
          exact List.mem_cons_self
        have supportMember := subset prime member
        have zeroBits :
            signatureBits finiteSupport
                (compute target).primes =
              signatureBits finiteSupport [] :=
          bitsZero.trans
            (signatureBits_empty
            finiteSupport).symm
        have containsFalse :
            natContains prime (compute target).primes = false := by
          have containsEqual :=
            natContains_eq_of_signatureBits_eq
            prime
            finiteSupport (compute target).primes [] supportMember zeroBits
          simpa only [natContains, -eq_self, -iff_self] using containsEqual
        have notMember :=
          (natContains_eq_false_iff prime (compute target).primes).mp
            containsFalse
        exact False.elim (notMember member)
  · intro primesEmpty
    apply Data.Vector.Boolean.ext
    change signatureBits finiteSupport
        (compute target).primes = List.replicate finiteSupport.length false
    rw [primesEmpty]
    exact
      signatureBits_empty
      finiteSupport

/-- The positive square-class target represented by rational one. -/
@[expose] public def
  oneTarget
  : Target :=
  positiveNaturalTarget 1 (by decide)

/-- The canonical natural kernel of the unit target is one. -/
public theorem
  oneTarget_kernel_eq_one
  :
    (compute
      oneTarget).kernel = 1
      := by decide +kernel

end Purelib.NumberTheory.SquareClass.Rational.Span.GeneratorProfiles
end
