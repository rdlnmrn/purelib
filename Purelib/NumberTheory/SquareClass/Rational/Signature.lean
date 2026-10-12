module

import Purelib.Data.List.Membership
import Purelib.Data.List.Filter
import Purelib.Data.List.Fold
import Purelib.Data.List.Permutation
import Purelib.Data.Int.Arithmetic
import Purelib.Data.Nat.Multiplication
-- The exposed signature computation retains the original natural cast certificates.
public import Purelib.Algebra.NatCast
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.SquareClass.Basic
import Purelib.Data.List.Nodup
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.Fraction.Cast
public import Purelib.Data.Rat.Fraction.Cast.Order
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.NumberTheory.Prime.Factor
public import Purelib.NumberTheory.SquareClass.Rational.Basic

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.NumberTheory.Prime.Parity
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

public section

/-!
# Finite signatures for positive rational square classes

A positive rational `a / b` has the same square class as the positive natural
`a * b`.  The finite prime-parity decomposition of that one displayed natural
therefore supplies a canonical natural kernel.  This module caches the
decomposition and proves that equality of the computed kernels is exactly
square-class equivalence.  No carrier of all square classes, global prime
enumeration, or quotient is formed.
-/

namespace Purelib.NumberTheory.SquareClass.Rational.Signature

-- Preserve the existing nominal Signature record contract until its dirty
-- span/profile clients can migrate together; this was already disabled here.

section PositiveSquareClassSignatures

open Purelib.Algebra.Field

open Purelib

open Purelib.Data.Rat

open Purelib.NumberTheory

open Purelib.NumberTheory.SquareClass
open Purelib.Data.List
open Purelib.Algebra
open Purelib.Data.Nat

namespace PositiveSquareClassSignatures

/-- The canonical rational coefficient type of positive square-class signatures. -/
abbrev Scalar := Fraction.Rational

end PositiveSquareClassSignatures

namespace PositiveSquareClassSignatures

/-- Executable structural membership in one displayed natural list.

The original equality decision checks each head before its retained tail. The first equal head returns true; exhausting
the list returns false. -/
@[expose] def natContains (value : Nat) : List Nat → Bool
  | [] => false
  | head :: tail =>
      match Nat.decEq value head with
      | isTrue _ => true
      | isFalse _ => natContains value
        tail

end PositiveSquareClassSignatures

namespace PositiveSquareClassSignatures

/-- The structural membership test returns true exactly for members of the original list.

Both directions follow the same head comparisons and retained tails. The certificate concerns membership in that exact
supplied list. -/
theorem natContains_eq_true_iff (value : Nat) : ∀ values : List Nat,
    natContains value values = true ↔ value ∈ values
  | [] => by
      constructor
      · intro impossible; cases impossible
      · intro impossible; nomatch impossible
  | head :: tail => by
      unfold natContains
      match equality : Nat.decEq value head with
      | isTrue equal =>
          constructor
          · intro _; exact Membership.mem_cons.mpr (Or.inl equal)
          · intro _; rfl
      | isFalse different =>
          constructor
          · intro accepted
            exact List.Mem.tail head (natContains_eq_true_iff value tail |>.mp accepted)
          · intro member
            cases member with
            | head => exact (different rfl).elim
            | tail _ member => exact (natContains_eq_true_iff value tail).mpr member

end PositiveSquareClassSignatures

namespace PositiveSquareClassSignatures

/-- The structural membership test returns false exactly for elements absent from the original list.

The two Boolean outcomes are distinguished by their constructors. Failure excludes every occurrence certified by the
same scan. -/
theorem natContains_eq_false_iff (value : Nat) (values : List Nat) :
    natContains value values = false ↔ value ∉ values := by
  cases contains : natContains value values with
  | false =>
      constructor
      · intro _ member
        have trueEquation := (natContains_eq_true_iff value values).2 member
        rw [contains] at trueEquation
        exact Bool.noConfusion trueEquation
      · intro _
        rfl
  | true =>
      constructor
      · intro impossible
        exact Bool.noConfusion impossible
      · intro notMember
        exact (notMember ((natContains_eq_true_iff value values).1 contains)).elim

end PositiveSquareClassSignatures

namespace PositiveSquareClassSignatures

/-- Entries of `source` absent from `against`, retaining source order.

The Boolean test filters the supplied source in its original order and retains every occurrence whose value is absent
from against. -/
@[expose] def difference (source against : List Nat) : List Nat :=
  source.filter fun value => !(natContains value against)

end PositiveSquareClassSignatures

namespace PositiveSquareClassSignatures

/-- Entries of `source` also present in `against`, retaining source order.

The Boolean test filters the supplied source in its original order and retains every occurrence shared with against. -/
@[expose] def intersection (source against : List Nat) : List Nat :=
  source.filter fun value => natContains value against

end PositiveSquareClassSignatures

namespace PositiveSquareClassSignatures

/-- Symmetric difference of two displayed finite prime supports.

The left-only entries precede the right-only entries. Each block preserves the corresponding source order and
multiplicity. -/
@[expose] def xorSupport (left right : List Nat) : List Nat :=
  difference left right ++ difference right left

end PositiveSquareClassSignatures

namespace PositiveSquareClassSignatures

/-- A difference entry is in the source list and absent from the list being subtracted.

The original filter retains a source occurrence and a false result for the membership scan of the other list. -/
theorem mem_difference_iff (value : Nat) (source against : List Nat) :
    value ∈ difference source against ↔
      value ∈ source ∧ value ∉ against := by
  unfold difference
  constructor
  · intro member
    have filtered := Filter.mem_filter.mp member
    exact ⟨filtered.1, (natContains_eq_false_iff value against).mp (by
      cases selected : natContains value against with
      | false => rfl
      | true => rw [selected] at filtered; cases filtered.2)⟩
  · rintro ⟨member, absent⟩
    apply Filter.mem_filter.mpr
    refine ⟨member, ?_⟩
    rw [(natContains_eq_false_iff value against).mpr absent]
    rfl

end PositiveSquareClassSignatures

namespace PositiveSquareClassSignatures

/-- An intersection entry belongs to both original lists.

The original filter retains a source occurrence and a true result for the membership scan of the other list. -/
theorem mem_intersection_iff (value : Nat) (source against : List Nat) :
    value ∈ intersection source against ↔
      value ∈ source ∧ value ∈ against := by
  unfold intersection
  constructor
  · intro member
    have retained := Filter.mem_filter.mp member
    exact ⟨retained.1, (natContains_eq_true_iff value against).mp retained.2⟩
  · rintro ⟨member, shared⟩
    exact Filter.mem_filter.mpr ⟨member, (natContains_eq_true_iff value against).mpr shared⟩

end PositiveSquareClassSignatures

namespace PositiveSquareClassSignatures

/-- A symmetric-difference entry belongs to exactly one of the original supports.

The concatenated difference blocks identify which supplied support contains the retained occurrence and which excludes
it. -/
theorem mem_xorSupport_iff (value : Nat) (left right : List Nat) :
    value ∈ xorSupport left right ↔
      (value ∈ left ∧ value ∉ right) ∨
        (value ∈ right ∧ value ∉ left) := by
  unfold xorSupport
  constructor
  · intro member
    cases Membership.mem_append.mp member with
    | inl left => exact Or.inl (mem_difference_iff value _ _ |>.mp left)
    | inr right => exact Or.inr (mem_difference_iff value _ _ |>.mp right)
  · intro member
    cases member with
    | inl left => exact Membership.mem_append.mpr (Or.inl (mem_difference_iff value _ _ |>.mpr left))
    | inr right => exact Membership.mem_append.mpr (Or.inr (mem_difference_iff value _ _ |>.mpr right))

end PositiveSquareClassSignatures

namespace PositiveSquareClassSignatures

/-- A list product splits into the product of its difference and intersection with another list.

Filtering each retained head selects exactly one of the two products. Natural associativity and commutativity
reconstruct the same complete source product. -/
private theorem product_partition (source against : List Nat) :
    source.prod =
      (difference source against).prod *
        (intersection source against).prod := by
  induction source with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      unfold difference intersection at inductionHypothesis ⊢
      cases contains : natContains head against with
      | false =>
          rw [List.prod_cons, Filter.filter_cons, Filter.filter_cons, contains]
          change head * tail.prod =
            (head * (List.filter
              (fun value => !natContains value against) tail).prod) *
              (List.filter (fun value => natContains value against) tail).prod
          rw [inductionHypothesis]
          ring1
      | true =>
          rw [List.prod_cons, Filter.filter_cons, Filter.filter_cons, contains]
          change head * tail.prod =
            (List.filter
              (fun value => !natContains value against) tail).prod *
              (head *
                (List.filter (fun value => natContains value against) tail).prod)
          rw [inductionHypothesis]
          ring1

end PositiveSquareClassSignatures

namespace PositiveSquareClassSignatures

/-- The positive square-class representative of a displayed positive natural.

The supplied positive natural is cast with the canonical rational operations. Cast injectivity certifies its nonzero
field. -/
@[expose] def positiveNaturalClass (value : Nat) (positive : 0 < value) :
    Algebra.Field.SquareClass.Basic.SquareClassRepresentative Scalar where
  value := (value : Scalar)
  nonzero := by
    intro zero
    exact (Nat.ne_of_gt positive) (Fraction.Cast.Compatibility.natCast_injective_direct zero)

end PositiveSquareClassSignatures

namespace PositiveSquareClassSignatures

/-- Regard one displayed positive natural as a positive rational square-class target.

The retained natural cast supplies both the square-class representative and its strict positivity certificate. -/
@[expose] def positiveNaturalTarget (value : Nat) (positive : 0 < value) :
    Rational.Basic.TheoremSixtyTwo.PositiveSquareClassRepresentative where
  representative := positiveNaturalClass value positive
  positive := Fraction.Cast.Order.natCast_pos_direct positive

end PositiveSquareClassSignatures

set_option genInjectivity false in
/-- Cached output of the finite square-class signature computation.

The record keeps the exact numerator-times-denominator source, factorization root and ordered odd-prime support. Its
kernel and rational scaling factor relate those same caches to the supplied positive target. -/
structure Positive
    (target : Rational.Basic.TheoremSixtyTwo.PositiveSquareClassRepresentative) where
  /-- The retained natural source obtained by multiplying the target numerator and denominator. -/ source : Nat
  /-- The retained source is exactly the canonical numerator times denominator. -/ source_eq : source = target.numerator
    * target.denominator
  /-- The retained natural source is positive. -/ source_positive : 0 < source
  /-- The retained natural root of the extracted square factor. -/ root : Nat
  /-- The retained square-factor root is positive. -/ root_positive : 0 < root
  /-- The finite support of primes occurring with odd exponent. -/ primes : List Nat
  /-- Every retained support entry is prime. -/ primes_prime : ∀ prime ∈ primes, NumberTheory.Prime prime
  /-- The retained support contains each prime at most once. -/ primes_nodup : primes.Nodup
  /-- The cached natural square-free kernel. -/ kernel : Nat
  /-- The cached kernel is the product of the exact retained prime list. -/ kernel_eq : kernel = primes.prod
  /-- The cached natural kernel is positive. -/ kernel_positive : 0 < kernel
  /-- The retained source equals the root squared times the cached kernel. -/ decomposition : source = root ^ 2 * kernel
  /-- The rational scaling factor relating the kernel to the original target. -/ squareFactor :
    PositiveSquareClassSignatures.Scalar
  /-- The retained rational scaling factor is nonzero. -/ squareFactor_nonzero : squareFactor ≠ 0
  /-- The original target value equals the retained rational factor squared times the cached kernel. -/
    value_eq_squareFactor_sq_mul_kernel :
    target.representative.value = squareFactor ^ 2 * (kernel :
      PositiveSquareClassSignatures.Scalar)
  /-- The positive natural kernel represents the same square class as the original target. -/ equivalent :
    (PositiveSquareClassSignatures.positiveNaturalClass
      kernel kernel_positive).Equivalent
      target.representative

constructive_injectivity Positive

namespace Positive.mk

end Positive.mk

namespace Positive.mk

end Positive.mk

namespace PositiveSquareClassSignatures

/-- Compute the finite odd-prime signature of one positive rational class.

The canonical numerator and denominator determine one retained natural source. Its prime-parity decomposition supplies
the ordered support, kernel and square root; the same denominator then determines the rational scaling factor. -/
@[expose] def compute
    (target : Rational.Basic.TheoremSixtyTwo.PositiveSquareClassRepresentative) :
    Positive target := by
  let source := target.numerator * target.denominator
  have sourcePositive : 0 < source :=
    Nat.mul_pos target.numerator_positive target.denominator_positive
  let output := Prime.Parity.decompose source sourcePositive
  have kernelPositive : 0 < output.primes.prod :=
    Prime.prod_pos output.primes_prime
  have rootPositive : 0 < output.root := by
    apply Nat.pos_of_ne_zero
    intro rootZero
    have sourceZero : source = 0 := by
      calc
        source = output.root ^ 2 * output.primes.prod := output.equation
        _ = 0 ^ 2 * output.primes.prod :=
          congrArg (fun root : Nat => root ^ 2 * output.primes.prod) rootZero
        _ = 0 := Nat.zero_mul output.primes.prod
    exact (Nat.ne_of_gt sourcePositive) sourceZero
  have rootCastNonzero : (output.root : Scalar) ≠ 0 := by
    intro castZero
    have naturalZero : output.root = 0 :=
      Fraction.Cast.Compatibility.natCast_injective_direct (by
        simpa only [Nat.cast_zero] using castZero)
    exact (Nat.ne_of_gt rootPositive) naturalZero
  have denominatorNonzero : (target.denominator : Scalar) ≠ 0 :=
    target.denominator_cast_ne_zero
  have inverseNonzero : (target.denominator : Scalar)⁻¹ ≠ 0 :=
    ExplicitField.inv_ne_zero denominatorNonzero
  let squareFactor :=
    (output.root : Scalar) * (target.denominator : Scalar)⁻¹
  have squareFactorNonzero : squareFactor ≠ 0 :=
    ExplicitField.mul_ne_zero rootCastNonzero inverseNonzero
  have valueEquation : target.representative.value =
      squareFactor ^ 2 * (output.primes.prod : Scalar) := by
    have castDecomposition := congrArg (fun value : Nat => (value : Scalar))
      output.equation
    have castDecomposition' :
        (target.numerator : Scalar) * (target.denominator : Scalar) =
          (output.root : Scalar) ^ 2 * (output.primes.prod : Scalar) := by
      simpa only [source, NatCast.mul, NatCast.pow] using castDecomposition
    have denominatorCancel := ExplicitField.mul_inv_cancel
      (target.denominator : Scalar) denominatorNonzero
    have targetFormula : target.representative.value =
        ((target.numerator : Scalar) *
          (target.denominator : Scalar)) *
          (target.denominator : Scalar)⁻¹ ^ 2 := by
      rw [target.value_eq_div]
      simp only [ExplicitField.div_eq_mul_inv]
      calc
        (target.numerator : Scalar) * (target.denominator : Scalar)⁻¹ =
          (target.numerator : Scalar) *
            (target.denominator : Scalar)⁻¹ *
              ((target.denominator : Scalar) *
                (target.denominator : Scalar)⁻¹) := by
                  rw [denominatorCancel, mul_one]
        _ = ((target.numerator : Scalar) *
              (target.denominator : Scalar)) *
                (target.denominator : Scalar)⁻¹ ^ 2 := by ring1
    have scaledDecomposition :
        ((target.numerator : Scalar) * (target.denominator : Scalar)) *
            (target.denominator : Scalar)⁻¹ ^ 2 =
          ((output.root : Scalar) ^ 2 *
            (output.primes.prod : Scalar)) *
              (target.denominator : Scalar)⁻¹ ^ 2 :=
      congrArg
        (fun value : Scalar =>
          value * (target.denominator : Scalar)⁻¹ ^ 2)
        castDecomposition'
    have rearranged :
        ((output.root : Scalar) ^ 2 *
            (output.primes.prod : Scalar)) *
              (target.denominator : Scalar)⁻¹ ^ 2 =
          squareFactor ^ 2 * (output.primes.prod : Scalar) := by
      unfold squareFactor
      ring1
    exact targetFormula.trans (scaledDecomposition.trans rearranged)
  exact
    { source := source
      source_eq := rfl
      source_positive := sourcePositive
      root := output.root
      root_positive := rootPositive
      primes := output.primes
      primes_prime := output.primes_prime
      primes_nodup := output.primes_nodup
      kernel := output.primes.prod
      kernel_eq := rfl
      kernel_positive := kernelPositive
      decomposition := output.equation
      squareFactor := squareFactor
      squareFactor_nonzero := squareFactorNonzero
      value_eq_squareFactor_sq_mul_kernel := valueEquation
      equivalent := ⟨squareFactor, squareFactorNonzero, valueEquation⟩ }

end PositiveSquareClassSignatures

namespace Positive

/-- The computed natural kernel is one exactly when its complete finite
odd-prime support is empty.

Every retained support entry is prime and thus greater than one. A nonempty support contributes a prime divisor of the
kernel, which excludes the unit value. -/
theorem kernel_eq_one_iff_primes_eq_nil
    {target : Rational.Basic.TheoremSixtyTwo.PositiveSquareClassRepresentative}
    (signature : Positive target) :
    signature.kernel = 1 ↔ signature.primes = [] := by
  constructor
  · intro kernelOne
    cases primesEq : signature.primes with
    | nil => rfl
    | cons prime tail =>
        have primeMember : prime ∈ signature.primes := by
          rw [primesEq]
          exact List.mem_cons_self
        have primeDividesKernel : prime ∣ signature.kernel := by
          rw [signature.kernel_eq, primesEq, List.prod_cons]
          exact ⟨tail.prod, rfl⟩
        have primeDividesOne : prime ∣ 1 := by
          rw [← kernelOne]
          exact primeDividesKernel
        exact False.elim
          ((signature.primes_prime prime primeMember).not_dvd_one
            primeDividesOne)
  · intro primesEmpty
    rw [signature.kernel_eq, primesEmpty]
    rfl

end Positive

namespace PositiveSquareClassSignatures

/-- A prime present in one square-free support and absent from the other prevents rational square-class equivalence.

Clearing the retained rational denominator identifies a natural product equation. The unmatched prime then divides both
numerator and denominator, contradicting the supplied reduced fraction certificate. -/
private theorem not_equivalent_of_prime_mismatch
    {leftPrimes rightPrimes : List Nat}
    (leftPrime : ∀ prime ∈ leftPrimes, NumberTheory.Prime prime)
    (rightPrime : ∀ prime ∈ rightPrimes, NumberTheory.Prime prime)
    (leftNodup : leftPrimes.Nodup)
    {prime : Nat} (memberLeft : prime ∈ leftPrimes)
    (notMemberRight : prime ∉ rightPrimes) :
    ¬ (positiveNaturalClass leftPrimes.prod
        (Prime.prod_pos leftPrime)).Equivalent
      (positiveNaturalClass rightPrimes.prod
        (Prime.prod_pos rightPrime)) := by
  intro equivalent
  have primeIsPrime := leftPrime prime memberLeft
  rcases equivalent with ⟨factor, _factorNonzero, classEquation⟩
  change (rightPrimes.prod : Scalar) =
    factor ^ 2 * (leftPrimes.prod : Scalar) at classEquation
  let reduced := Fraction.Basic.representative factor
  have cleared := Fraction.Cast.representative_mul_den factor
  change factor * (reduced.den : Scalar) = (reduced.num : Scalar) at cleared
  have rationalEquation :
      (rightPrimes.prod : Scalar) * (reduced.den : Scalar) ^ 2 =
        (reduced.num : Scalar) ^ 2 * (leftPrimes.prod : Scalar) := by
    calc
      (rightPrimes.prod : Scalar) * (reduced.den : Scalar) ^ 2 =
          (factor ^ 2 * (leftPrimes.prod : Scalar)) *
            (reduced.den : Scalar) ^ 2 := by rw [classEquation]
      _ = (factor * (reduced.den : Scalar)) ^ 2 *
            (leftPrimes.prod : Scalar) := by ring1
      _ = (reduced.num : Scalar) ^ 2 *
            (leftPrimes.prod : Scalar) := by rw [cleared]
  have integerEquation :
      (rightPrimes.prod : Int) *
          ((reduced.den : Int) * (reduced.den : Int)) =
        (reduced.num * reduced.num) * (leftPrimes.prod : Int) := by
    apply Fraction.Cast.Compatibility.intCast_injective_direct
    rw [Fraction.Cast.intCast_mul_direct,
      Fraction.Cast.intCast_mul_direct,
      Fraction.Cast.intCast_mul_direct,
      Fraction.Cast.intCast_mul_direct]
    simpa only [Int.cast_natCast, pow_two] using rationalEquation
  have absoluteEquation := congrArg Int.natAbs integerEquation
  have naturalEquation :
      rightPrimes.prod * (reduced.den * reduced.den) =
        (reduced.num.natAbs * reduced.num.natAbs) * leftPrimes.prod := by
    simpa only [Data.Int.Arithmetic.natAbs_mul, Int.natAbs_natCast] using absoluteEquation
  rcases Prime.Factor.cofactor_of_mem primeIsPrime leftNodup leftPrime memberLeft with
    ⟨leftCofactor, leftProduct, notDividesLeftCofactor⟩
  have notDividesRightProduct : ¬ prime ∣ rightPrimes.prod :=
    Prime.Factor.not_dvd_prod_of_not_mem primeIsPrime rightPrime notMemberRight
  have primeDividesLeftSide :
      prime ∣ rightPrimes.prod * (reduced.den * reduced.den) := by
    refine ⟨(reduced.num.natAbs * reduced.num.natAbs) * leftCofactor, ?_⟩
    calc
      rightPrimes.prod * (reduced.den * reduced.den) =
          (reduced.num.natAbs * reduced.num.natAbs) * leftPrimes.prod :=
        naturalEquation
      _ = prime *
          ((reduced.num.natAbs * reduced.num.natAbs) * leftCofactor) := by
        rw [leftProduct]
        ring1
  have primeDividesDenominatorSquare :
      prime ∣ reduced.den * reduced.den :=
    Prime.Factor.prime_dvd_right_of_dvd_mul_of_not_dvd
      primeIsPrime notDividesRightProduct primeDividesLeftSide
  have primeDividesDenominator : prime ∣ reduced.den :=
    Prime.Factor.prime_dvd_of_dvd_square primeIsPrime
      primeDividesDenominatorSquare
  rcases primeDividesDenominator with ⟨denominatorCofactor,
    denominatorEquation⟩
  have canceledEquation :
      rightPrimes.prod * prime *
          (denominatorCofactor * denominatorCofactor) =
        (reduced.num.natAbs * reduced.num.natAbs) * leftCofactor := by
    apply Nat.eq_of_mul_eq_mul_left primeIsPrime.pos
    calc
      prime * (rightPrimes.prod * prime *
          (denominatorCofactor * denominatorCofactor)) =
        rightPrimes.prod *
          ((prime * denominatorCofactor) *
            (prime * denominatorCofactor)) := by ring1
      _ = rightPrimes.prod * (reduced.den * reduced.den) := by
        rw [← denominatorEquation]
      _ = (reduced.num.natAbs * reduced.num.natAbs) *
          leftPrimes.prod := naturalEquation
      _ = prime * ((reduced.num.natAbs * reduced.num.natAbs) *
          leftCofactor) := by
        rw [leftProduct]
        ring1
  have primeDividesNumeratorSquareTimesCofactor :
      prime ∣ (reduced.num.natAbs * reduced.num.natAbs) *
        leftCofactor := by
    refine ⟨rightPrimes.prod *
      (denominatorCofactor * denominatorCofactor), ?_⟩
    calc
      (reduced.num.natAbs * reduced.num.natAbs) * leftCofactor =
          rightPrimes.prod * prime *
            (denominatorCofactor * denominatorCofactor) :=
        canceledEquation.symm
      _ = prime * (rightPrimes.prod *
          (denominatorCofactor * denominatorCofactor)) := by ring1
  have primeDividesNumeratorSquare :
      prime ∣ reduced.num.natAbs * reduced.num.natAbs := by
    apply Prime.Factor.prime_dvd_right_of_dvd_mul_of_not_dvd
      primeIsPrime
        notDividesLeftCofactor
    simpa only [Nat.mul_comm leftCofactor] using
      primeDividesNumeratorSquareTimesCofactor
  have primeDividesNumerator : prime ∣ reduced.num.natAbs :=
    Prime.Factor.prime_dvd_of_dvd_square primeIsPrime
      primeDividesNumeratorSquare
  rcases reduced.reduced with ⟨coprime⟩
  have primeOne := coprime.eq_one_of_dvd
    primeDividesNumerator ⟨denominatorCofactor, denominatorEquation⟩
  exact primeIsPrime.ne_one primeOne

end PositiveSquareClassSignatures

namespace PositiveSquareClassSignatures

/-- Equivalent positive rational targets have the same prime-support membership in the indicated direction.

The two cached kernel representatives retain their target equivalences. An unmatched prime contradicts the exact
square-free support products. -/
private theorem equivalent_kernel_membership
    {leftTarget rightTarget :
      Rational.Basic.TheoremSixtyTwo.PositiveSquareClassRepresentative}
    (left : Positive leftTarget) (right : Positive rightTarget)
    (equivalent : leftTarget.representative.Equivalent
      rightTarget.representative) :
    ∀ prime, prime ∈ left.primes → prime ∈ right.primes := by
  intro prime memberLeft
  match @Membership.decideEq Nat Nat.decEq prime right.primes with
  | isTrue memberRight => exact memberRight
  | isFalse memberRight =>
      apply False.elim
      have kernelEquivalent :
          (positiveNaturalClass left.kernel left.kernel_positive).Equivalent
            (positiveNaturalClass right.kernel right.kernel_positive) :=
        Algebra.Field.SquareClass.Basic.SquareClassRepresentative.equivalent_trans left.equivalent
          (Algebra.Field.SquareClass.Basic.SquareClassRepresentative.equivalent_trans equivalent
            (Algebra.Field.SquareClass.Basic.SquareClassRepresentative.equivalent_symm right.equivalent))
      have displayedKernelEquivalent :
          (positiveNaturalClass left.primes.prod
            (Prime.prod_pos left.primes_prime)).Equivalent
          (positiveNaturalClass right.primes.prod
            (Prime.prod_pos right.primes_prime)) := by
        simpa only [left.kernel_eq, right.kernel_eq] using kernelEquivalent
      exact (not_equivalent_of_prime_mismatch left.primes_prime
        right.primes_prime left.primes_nodup memberLeft memberRight)
        displayedKernelEquivalent

end PositiveSquareClassSignatures

namespace PositiveSquareClassSignatures

/-- Natural classes represented by duplicate-free prime lists are equivalent
exactly when the finite supports have the same members.

Duplicate-free supports with the same members retain a permutation and thus the same natural product. A differing
membership excludes equivalence by the retained prime factorization witnesses. -/
theorem primeSupportEquivalent_iff
    {left right : List Nat}
    (leftPrime : ∀ prime ∈ left, NumberTheory.Prime prime)
    (rightPrime : ∀ prime ∈ right, NumberTheory.Prime prime)
    (leftNodup : left.Nodup) (rightNodup : right.Nodup) :
    (positiveNaturalClass left.prod
        (Prime.prod_pos leftPrime)).Equivalent
      (positiveNaturalClass right.prod
        (Prime.prod_pos rightPrime)) ↔
      ∀ prime, prime ∈ left ↔ prime ∈ right := by
  constructor
  · intro equivalent prime
    constructor
    · intro memberLeft
      match @Membership.decideEq Nat Nat.decEq prime right with
      | isTrue memberRight => exact memberRight
      | isFalse notMemberRight =>
          exact False.elim
            ((not_equivalent_of_prime_mismatch leftPrime rightPrime
              leftNodup memberLeft notMemberRight) equivalent)
    · intro memberRight
      match @Membership.decideEq Nat Nat.decEq prime left with
      | isTrue memberLeft => exact memberLeft
      | isFalse notMemberLeft =>
          exact False.elim
            ((not_equivalent_of_prime_mismatch rightPrime leftPrime
              rightNodup memberRight notMemberLeft)
              (Algebra.Field.SquareClass.Basic.SquareClassRepresentative.equivalent_symm equivalent))
  · intro sameMembers
    have permutation : left.Perm right :=
      Permutation.of_nodup_mem_iff leftNodup rightNodup sameMembers
    have productsEqual := Permutation.prod_eq Multiplication.mul_assoc Nat.mul_comm permutation
    have representativesEqual :
        positiveNaturalClass left.prod (Prime.prod_pos leftPrime) =
          positiveNaturalClass right.prod
            (Prime.prod_pos rightPrime) := by
      apply Algebra.Field.SquareClass.Basic.SquareClassRepresentative.ext
      exact congrArg (fun value : Nat => (value : Scalar)) productsEqual
    rw [representativesEqual]
    exact Algebra.Field.SquareClass.Basic.SquareClassRepresentative.equivalent_refl _

end PositiveSquareClassSignatures

namespace PositiveSquareClassSignatures

/-- Taking a list difference preserves primality of every retained entry.

Each filtered occurrence retains its original source membership, so its supplied prime certificate remains the same. -/
theorem difference_prime {source against : List Nat}
    (sourcePrime : ∀ prime ∈ source, NumberTheory.Prime prime) :
    ∀ prime ∈ difference source against, NumberTheory.Prime prime := by
  intro prime member
  exact sourcePrime prime
    ((mem_difference_iff prime source against).1 member).1

end PositiveSquareClassSignatures

namespace PositiveSquareClassSignatures

/-- Taking a list intersection preserves primality of every retained entry.

Each filtered occurrence retains its original source membership, so its supplied prime certificate remains the same. -/
theorem intersection_prime {source against : List Nat}
    (sourcePrime : ∀ prime ∈ source, NumberTheory.Prime prime) :
    ∀ prime ∈ intersection source against, NumberTheory.Prime prime := by
  intro prime member
  exact sourcePrime prime
    ((mem_intersection_iff prime source against).1 member).1

end PositiveSquareClassSignatures

namespace PositiveSquareClassSignatures

/-- The symmetric difference of two prime lists contains only primes.

Each occurrence belongs to one of the two retained difference blocks. That source supplies the same prime certificate.
-/
theorem xorSupport_prime {left right : List Nat}
    (leftPrime : ∀ prime ∈ left, NumberTheory.Prime prime)
    (rightPrime : ∀ prime ∈ right, NumberTheory.Prime prime) :
    ∀ prime ∈ xorSupport left right, NumberTheory.Prime prime := by
  intro prime member
  unfold xorSupport at member
  rcases Membership.mem_append.mp member with leftMember | rightMember
  · exact difference_prime leftPrime prime leftMember
  · exact difference_prime rightPrime prime rightMember

end PositiveSquareClassSignatures

namespace PositiveSquareClassSignatures

/-- The symmetric difference of two duplicate-free lists is duplicate-free.

Filtering preserves freshness within each block. An occurrence in both blocks would be both present and absent in the
same supplied source. -/
theorem xorSupport_nodup {left right : List Nat}
    (leftNodup : left.Nodup) (rightNodup : right.Nodup) :
    (xorSupport left right).Nodup := by
  unfold xorSupport
  apply Data.List.Nodup.nodup_append
    (Filter.pairwise_filter _ leftNodup) (Filter.pairwise_filter _ rightNodup)
  intro leftValue leftMember rightValue rightMember equal
  have leftProperties :=
    (mem_difference_iff leftValue left right).1 leftMember
  have rightProperties :=
    (mem_difference_iff rightValue right left).1 rightMember
  apply leftProperties.2
  exact equal ▸ rightProperties.1

end PositiveSquareClassSignatures

namespace PositiveSquareClassSignatures

/-- For duplicate-free lists, reversing the intersection operands preserves its product.

The two intersections retain the same members. Their freshness supplies a permutation certificate without a choice-based
enumeration. -/
private theorem intersection_product_comm
    {left right : List Nat} (leftNodup : left.Nodup)
    (rightNodup : right.Nodup) :
    (intersection left right).prod = (intersection right left).prod := by
  have permutation : (intersection left right).Perm
      (intersection right left) :=
    Permutation.of_nodup_mem_iff (Filter.pairwise_filter _ leftNodup)
      (Filter.pairwise_filter _ rightNodup) (fun value => by
        constructor
        · intro member
          have h := (mem_intersection_iff value left right).mp member
          exact (mem_intersection_iff value right left).mpr ⟨h.2, h.1⟩
        · intro member
          have h := (mem_intersection_iff value right left).mp member
          exact (mem_intersection_iff value left right).mpr ⟨h.2, h.1⟩)
  exact Permutation.prod_eq Multiplication.mul_assoc Nat.mul_comm permutation

end PositiveSquareClassSignatures

namespace PositiveSquareClassSignatures

/-- Multiplying two square-free prime products produces the square of their
common part times the product of their symmetric difference.

The two retained product partitions identify the common intersection on both sides. Explicit natural product laws then
collect its square and the ordered symmetric difference. -/
theorem product_eq_common_sq_mul_xor
    (left right : List Nat) (leftNodup : left.Nodup)
    (rightNodup : right.Nodup) :
    left.prod * right.prod =
      (intersection left right).prod ^ 2 * (xorSupport left right).prod := by
  rw [product_partition left right, product_partition right left,
    intersection_product_comm leftNodup rightNodup,
    xorSupport, Fold.prod_append Nat.one_mul Multiplication.mul_assoc]
  ring1

end PositiveSquareClassSignatures

namespace PositiveSquareClassSignatures

/-- Multiplication of two positive square classes as a positive target.

The supplied canonical rational values are multiplied with their original field operations. Direct positivity supplies
the retained positive target certificate. -/
@[expose] def mulTarget
    (left right : Rational.Basic.TheoremSixtyTwo.PositiveSquareClassRepresentative) :
    Rational.Basic.TheoremSixtyTwo.PositiveSquareClassRepresentative where
  representative := Algebra.Field.SquareClass.Basic.SquareClassRepresentative.mul
    left.representative right.representative
  positive := Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_pos_direct left.positive
    right.positive

end PositiveSquareClassSignatures

namespace PositiveSquareClassSignatures

/-- The natural class of a symmetric-difference support equals the product
of the two displayed natural classes.

The retained common-prime product is the nonzero rational square factor. Its natural product identity relates the
ordered symmetric difference to the two supplied classes. -/
theorem xorSupport_equivalent_mul
    {left right : List Nat}
    (leftPrime : ∀ prime ∈ left, NumberTheory.Prime prime)
    (rightPrime : ∀ prime ∈ right, NumberTheory.Prime prime)
    (leftNodup : left.Nodup) (rightNodup : right.Nodup) :
    (positiveNaturalClass (xorSupport left right).prod
        (Prime.prod_pos
          (xorSupport_prime leftPrime rightPrime))).Equivalent
      (Algebra.Field.SquareClass.Basic.SquareClassRepresentative.mul
        (positiveNaturalClass left.prod (Prime.prod_pos leftPrime))
        (positiveNaturalClass right.prod (Prime.prod_pos rightPrime))) := by
  have commonPrime : ∀ prime ∈ intersection left right,
      NumberTheory.Prime prime :=
    intersection_prime (source := left) (against := right) leftPrime
  have commonPositive : 0 < (intersection left right).prod :=
    Prime.prod_pos commonPrime
  have commonCastNonzero :
      ((intersection left right).prod : Scalar) ≠ 0 :=
    (Fraction.Cast.Order.natCast_pos_direct commonPositive).ne'
  refine ⟨((intersection left right).prod : Scalar), commonCastNonzero, ?_⟩
  change (left.prod : Scalar) * (right.prod : Scalar) =
    ((intersection left right).prod : Scalar) ^ 2 *
      ((xorSupport left right).prod : Scalar)
  have naturalEquation := product_eq_common_sq_mul_xor left right
    leftNodup rightNodup
  have castEquation := congrArg (fun value : Nat => (value : Scalar))
    naturalEquation
  simpa only [NatCast.mul, NatCast.pow] using castEquation

end PositiveSquareClassSignatures

namespace PositiveSquareClassSignatures

/-- The computed prime support of a product is the symmetric difference of
the computed supports of its factors.

The three cached decompositions represent the supplied classes and their product. Their equivalences and prime support
membership characterize the exact resulting support. -/
theorem compute_mulTarget_support
    (left right : Rational.Basic.TheoremSixtyTwo.PositiveSquareClassRepresentative) :
    let leftSignature := compute left
    let rightSignature := compute right
    let productSignature := compute (mulTarget left right)
    ∀ prime, prime ∈ productSignature.primes ↔
      prime ∈ xorSupport leftSignature.primes rightSignature.primes := by
  dsimp only
  let leftSignature := compute left
  let rightSignature := compute right
  let productSignature := compute (mulTarget left right)
  have leftDisplayed :
      (positiveNaturalClass leftSignature.primes.prod
        (Prime.prod_pos leftSignature.primes_prime)).Equivalent
        left.representative := by
    simpa only [leftSignature.kernel_eq] using leftSignature.equivalent
  have rightDisplayed :
      (positiveNaturalClass rightSignature.primes.prod
        (Prime.prod_pos rightSignature.primes_prime)).Equivalent
        right.representative := by
    simpa only [rightSignature.kernel_eq] using rightSignature.equivalent
  have productDisplayed :
      (positiveNaturalClass productSignature.primes.prod
        (Prime.prod_pos productSignature.primes_prime)).Equivalent
        (mulTarget left right).representative := by
    simpa only [productSignature.kernel_eq] using productSignature.equivalent
  have xorToDisplayedProduct := xorSupport_equivalent_mul
    leftSignature.primes_prime rightSignature.primes_prime
    leftSignature.primes_nodup rightSignature.primes_nodup
  have displayedProductToTarget :=
    Algebra.Field.SquareClass.Basic.SquareClassRepresentative.mul_respects_equivalent leftDisplayed
      rightDisplayed
  have xorToProductSignature :=
    Algebra.Field.SquareClass.Basic.SquareClassRepresentative.equivalent_trans xorToDisplayedProduct
      (Algebra.Field.SquareClass.Basic.SquareClassRepresentative.equivalent_trans displayedProductToTarget
        (Algebra.Field.SquareClass.Basic.SquareClassRepresentative.equivalent_symm productDisplayed))
  have sameMembers := (primeSupportEquivalent_iff
    (xorSupport_prime leftSignature.primes_prime rightSignature.primes_prime)
    productSignature.primes_prime
    (xorSupport_nodup leftSignature.primes_nodup
      rightSignature.primes_nodup)
    productSignature.primes_nodup).1 xorToProductSignature
  intro prime
  exact (sameMembers prime).symm

end PositiveSquareClassSignatures

namespace PositiveSquareClassSignatures

/-- Two positive rational classes are equivalent exactly when their finite
natural prime-parity kernels agree.

Each cached signature represents its original target. Equal kernels therefore give equivalent targets, while equivalence
identifies their duplicate-free prime products. -/
theorem equivalent_iff_kernel_eq
    {leftTarget rightTarget :
      Rational.Basic.TheoremSixtyTwo.PositiveSquareClassRepresentative}
    (left : Positive leftTarget) (right : Positive rightTarget) :
    leftTarget.representative.Equivalent rightTarget.representative ↔
      left.kernel = right.kernel := by
  constructor
  · intro equivalent
    have forward := equivalent_kernel_membership left right equivalent
    have reverse := equivalent_kernel_membership right left
      (Algebra.Field.SquareClass.Basic.SquareClassRepresentative.equivalent_symm equivalent)
    have permutation : left.primes.Perm right.primes :=
      Permutation.of_nodup_mem_iff left.primes_nodup
        right.primes_nodup (fun prime =>
          ⟨forward prime, reverse prime⟩)
    rw [left.kernel_eq, right.kernel_eq]
    exact Permutation.prod_eq Multiplication.mul_assoc Nat.mul_comm permutation
  · intro kernelsEqual
    have representativesEqual :
        positiveNaturalClass left.kernel left.kernel_positive =
          positiveNaturalClass right.kernel right.kernel_positive := by
      apply Algebra.Field.SquareClass.Basic.SquareClassRepresentative.ext
      exact congrArg (fun value : Nat => (value : Scalar)) kernelsEqual
    apply Algebra.Field.SquareClass.Basic.SquareClassRepresentative.equivalent_trans
      (Algebra.Field.SquareClass.Basic.SquareClassRepresentative.equivalent_symm left.equivalent)
    rw [representativesEqual]
    exact right.equivalent

end PositiveSquareClassSignatures

end PositiveSquareClassSignatures

end Purelib.NumberTheory.SquareClass.Rational.Signature
