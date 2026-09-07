import RationalRotations.PositiveSquareClassSignatures
import mathlib.RFAP.FiniteBooleanSpan

/-!
# Finite chi-visible generator profiles

For one supplied finite list of positive rational square-class targets, this
module forms their finite union of prime supports, encodes every signature as
a fixed-length Boolean vector, and computes the exact XOR span.  Every listed
image retains a Boolean generator word, while arbitrary Boolean words are
classified by the span completeness certificate.  No generated subgroup is
formed as a completed set.
-/

namespace RationalRotations

namespace FiniteGeneratorProfiles

open PositiveSquareClassSignatures

abbrev Target := TheoremSixtyTwo.PositiveSquareClassRepresentative

/-- Duplicate-free union, retaining the order of the left support followed
by genuinely new entries from the right support. -/
def unionSupport (left right : List Nat) : List Nat :=
  left ++ difference right left

theorem mem_unionSupport_iff (value : Nat) (left right : List Nat) :
    value ∈ unionSupport left right ↔ value ∈ left ∨ value ∈ right := by
  rw [unionSupport, List.mem_append, mem_difference_iff]
  constructor
  · intro member
    rcases member with leftMember | rightOnly
    · exact Or.inl leftMember
    · exact Or.inr rightOnly.1
  · intro member
    rcases member with leftMember | rightMember
    · exact Or.inl leftMember
    · cases containsEq : natContains value left with
      | true =>
          exact Or.inl ((natContains_eq_true_iff value left).1 containsEq)
      | false =>
          exact Or.inr ⟨rightMember,
            (natContains_eq_false_iff value left).1 containsEq⟩

theorem unionSupport_nodup {left right : List Nat}
    (leftNodup : left.Nodup) (rightNodup : right.Nodup) :
    (unionSupport left right).Nodup := by
  unfold unionSupport
  apply QuotientFreeList.nodup_append leftNodup (rightNodup.filter _)
  intro leftValue leftMember rightValue rightMember equal
  have rightOnly := (mem_difference_iff rightValue right left).1 rightMember
  apply rightOnly.2
  exact equal ▸ leftMember

theorem unionSupport_prime {left right : List Nat}
    (leftPrime : ∀ prime ∈ left, Nat.Prime prime)
    (rightPrime : ∀ prime ∈ right, Nat.Prime prime) :
    ∀ prime ∈ unionSupport left right, Nat.Prime prime := by
  intro prime member
  rcases (mem_unionSupport_iff prime left right).1 member with
    leftMember | rightMember
  · exact leftPrime prime leftMember
  · exact rightPrime prime rightMember

/-- The finite union of all odd-prime supports in a supplied target list. -/
def support : List Target → List Nat
  | [] => []
  | target :: targets =>
      unionSupport (compute target).primes (support targets)

theorem support_nodup : ∀ targets : List Target,
    (support targets).Nodup
  | [] => List.Pairwise.nil
  | target :: targets =>
      unionSupport_nodup (compute target).primes_nodup
        (support_nodup targets)

theorem support_prime : ∀ (targets : List Target),
    ∀ prime ∈ support targets, Nat.Prime prime
  | [], prime, impossible => by nomatch impossible
  | target :: targets, prime, member =>
      unionSupport_prime (compute target).primes_prime
        (support_prime targets) prime member

theorem target_primes_subset_support : ∀ {targets : List Target}
    {target : Target}, target ∈ targets →
      ∀ prime ∈ (compute target).primes, prime ∈ support targets
  | [], _target, impossible => by nomatch impossible
  | head :: tail, target, member => by
      rw [List.mem_cons] at member
      rcases member with equal | tailMember
      · subst target
        intro prime primeMember
        apply (mem_unionSupport_iff prime _ _).2
        exact Or.inl primeMember
      · intro prime primeMember
        apply (mem_unionSupport_iff prime _ _).2
        exact Or.inr (target_primes_subset_support tailMember prime primeMember)

/-- Boolean coordinates of one signature on one displayed finite support. -/
def signatureBits (finiteSupport primes : List Nat) : List Bool :=
  finiteSupport.map fun prime => natContains prime primes

theorem signatureBits_length (finiteSupport primes : List Nat) :
    (signatureBits finiteSupport primes).length = finiteSupport.length := by
  rw [signatureBits, List.length_map]

/-- Fixed-length Boolean vector of one positive rational square class. -/
def signatureVector (finiteSupport : List Nat) (target : Target) :
    RFAP.FiniteBooleanSpan.Vector finiteSupport.length where
  bits := signatureBits finiteSupport (compute target).primes
  length_eq := signatureBits_length _ _

private theorem contains_mul_eq_bitXor (prime : Nat)
    (left right : Target) :
    natContains prime (compute (mulTarget left right)).primes =
      RFAP.FiniteBooleanSpan.bitXor
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

/-- The Boolean encoding turns square-class multiplication into vector XOR. -/
theorem signatureVector_mul (finiteSupport : List Nat)
    (left right : Target) :
    signatureVector finiteSupport (mulTarget left right) =
      RFAP.FiniteBooleanSpan.xor
        (signatureVector finiteSupport left)
        (signatureVector finiteSupport right) := by
  apply RFAP.FiniteBooleanSpan.Vector.ext
  change signatureBits finiteSupport (compute (mulTarget left right)).primes =
    RFAP.FiniteBooleanSpan.bitsXor
      (signatureBits finiteSupport (compute left).primes)
      (signatureBits finiteSupport (compute right).primes)
  induction finiteSupport with
  | nil => rfl
  | cons prime tail inductionHypothesis =>
      simp only [signatureBits, List.map_cons,
        RFAP.FiniteBooleanSpan.bitsXor, List.cons.injEq]
      exact ⟨contains_mul_eq_bitXor prime left right,
        inductionHypothesis⟩

/-- Generator signature vectors on their shared finite support. -/
def generatorVectors (targets : List Target) :
    List (RFAP.FiniteBooleanSpan.Vector (support targets).length) :=
  targets.map (signatureVector (support targets))

/-- Complete finite profile of the part of a supplied generator system seen
by the positive rational square-class map. -/
structure VisibleGeneratorProfile (targets : List Target) where
  finiteSupport : List Nat
  finiteSupport_eq : finiteSupport = support targets
  finiteSupport_nodup : finiteSupport.Nodup
  finiteSupport_prime : ∀ prime ∈ finiteSupport, Nat.Prime prime
  vectors : List (RFAP.FiniteBooleanSpan.Vector finiteSupport.length)
  vectors_eq : vectors = targets.map (signatureVector finiteSupport)
  span : RFAP.FiniteBooleanSpan.Result vectors

/-- Compute the exact distinct XOR image of one supplied finite target list. -/
def visibleGeneratorProfile (targets : List Target) :
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
      span := RFAP.FiniteBooleanSpan.compute vectors }

theorem visibleGeneratorProfile_image_length (targets : List Target) :
    (visibleGeneratorProfile targets).span.entries.length =
      2 ^ (visibleGeneratorProfile targets).span.rank :=
  (visibleGeneratorProfile targets).span.length_eq

theorem visibleGeneratorProfile_image_nodup (targets : List Target) :
    ((visibleGeneratorProfile targets).span.entries.map
      RFAP.FiniteBooleanSpan.Entry.vector).Nodup :=
  (visibleGeneratorProfile targets).span.vectors_nodup

/-- Every supplied fixed-length Boolean generator word is classified by one
retained distinct image entry. -/
theorem classifyWord (targets : List Target) (choices : List Bool)
    (lengthEq : choices.length = targets.length) :
    ∃ entry ∈ (visibleGeneratorProfile targets).span.entries,
      RFAP.FiniteBooleanSpan.evaluate choices
          (visibleGeneratorProfile targets).vectors = entry.vector := by
  apply (visibleGeneratorProfile targets).span.complete choices
  rw [(visibleGeneratorProfile targets).vectors_eq, List.length_map]
  exact lengthEq

end FiniteGeneratorProfiles

end RationalRotations
