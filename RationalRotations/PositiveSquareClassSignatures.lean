import RationalRotations.RationalSurjectivity
import mathlib.RFAP.ConstructivePrimeParity
import Mathlib.Data.List.Perm.Basic

/-!
# Finite signatures for positive rational square classes

A positive rational `a / b` has the same square class as the positive natural
`a * b`.  The finite prime-parity decomposition of that one displayed natural
therefore supplies a canonical natural kernel.  This module caches the
decomposition and proves that equality of the computed kernels is exactly
square-class equivalence.  No carrier of all square classes, global prime
enumeration, or quotient is formed.
-/

namespace RationalRotations

namespace PositiveSquareClassSignatures

abbrev Scalar := RFAP.ConstructiveFraction.Rational

private theorem primeProduct_positive {primes : List Nat}
    (primesPrime : ∀ prime ∈ primes, Nat.Prime prime) :
    0 < primes.prod := by
  induction primes with
  | nil => decide
  | cons head tail inductionHypothesis =>
      rw [List.prod_cons]
      exact Nat.mul_pos
        (primesPrime head List.mem_cons_self).pos
        (inductionHypothesis fun prime member =>
          primesPrime prime (List.mem_cons_of_mem head member))

/-- Structural natural-list membership, avoiding the upstream `BEq` law
bridge used by the optimized generic list-membership instance. -/
private def natMembership (value : Nat) :
    (values : List Nat) → Decidable (value ∈ values)
  | [] => isFalse fun impossible => by nomatch impossible
  | head :: tail =>
      match Nat.decEq value head with
      | isTrue equal => isTrue (List.mem_cons.mpr (Or.inl equal))
      | isFalse different =>
          match natMembership value tail with
          | isTrue member => isTrue (List.mem_cons_of_mem head member)
          | isFalse notMember => isFalse fun member => by
              rcases List.mem_cons.mp member with equal | tailMember
              · exact different equal
              · exact notMember tailMember

/-- Executable structural membership in one displayed natural list. -/
def natContains (value : Nat) : List Nat → Bool
  | [] => false
  | head :: tail =>
      match Nat.decEq value head with
      | isTrue _ => true
      | isFalse _ => natContains value tail

@[simp] theorem natContains_eq_true_iff (value : Nat) : ∀ values : List Nat,
    natContains value values = true ↔ value ∈ values
  | [] => by simp only [natContains, Bool.false_eq_true, List.not_mem_nil]
  | head :: tail => by
      unfold natContains
      match equality : Nat.decEq value head with
      | isTrue equal =>
          simp only [List.mem_cons]
          exact ⟨fun _ => Or.inl equal, fun _ => True.intro⟩
      | isFalse different =>
          rw [natContains_eq_true_iff]
          simp only [List.mem_cons]
          constructor
          · exact Or.inr
          · intro member
            rcases member with equal | tailMember
            · exact (different equal).elim
            · exact tailMember

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

/-- Entries of `source` absent from `against`, retaining source order. -/
def difference (source against : List Nat) : List Nat :=
  source.filter fun value => !(natContains value against)

/-- Entries of `source` also present in `against`, retaining source order. -/
def intersection (source against : List Nat) : List Nat :=
  source.filter fun value => natContains value against

/-- Symmetric difference of two displayed finite prime supports. -/
def xorSupport (left right : List Nat) : List Nat :=
  difference left right ++ difference right left

theorem mem_difference_iff (value : Nat) (source against : List Nat) :
    value ∈ difference source against ↔
      value ∈ source ∧ value ∉ against := by
  rw [difference, List.mem_filter]
  constructor
  · intro filtered
    have absentEquation : natContains value against = false := by
      cases contains : natContains value against with
      | false => rfl
      | true =>
          rw [contains] at filtered
          exact Bool.noConfusion filtered.2
    exact ⟨filtered.1,
      (natContains_eq_false_iff value against).1 absentEquation⟩
  · intro properties
    exact ⟨properties.1, by
      have absent := (natContains_eq_false_iff value against).2 properties.2
      rw [absent]
      rfl⟩

theorem mem_intersection_iff (value : Nat) (source against : List Nat) :
    value ∈ intersection source against ↔
      value ∈ source ∧ value ∈ against := by
  rw [intersection, List.mem_filter]
  constructor
  · intro filtered
    exact ⟨filtered.1,
      (natContains_eq_true_iff value against).1 filtered.2⟩
  · intro properties
    exact ⟨properties.1,
      (natContains_eq_true_iff value against).2 properties.2⟩

theorem mem_xorSupport_iff (value : Nat) (left right : List Nat) :
    value ∈ xorSupport left right ↔
      (value ∈ left ∧ value ∉ right) ∨
        (value ∈ right ∧ value ∉ left) := by
  rw [xorSupport, List.mem_append, mem_difference_iff, mem_difference_iff]

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
          rw [List.prod_cons, List.filter_cons, List.filter_cons, contains]
          change head * tail.prod =
            (head * (List.filter
              (fun value => !natContains value against) tail).prod) *
              (List.filter (fun value => natContains value against) tail).prod
          rw [inductionHypothesis]
          ring1
      | true =>
          rw [List.prod_cons, List.filter_cons, List.filter_cons, contains]
          change head * tail.prod =
            (List.filter
              (fun value => !natContains value against) tail).prod *
              (head *
                (List.filter (fun value => natContains value against) tail).prod)
          rw [inductionHypothesis]
          ring1

/-- The positive square-class representative of a displayed positive natural. -/
def positiveNaturalClass (value : Nat) (positive : 0 < value) :
    SquareClassRepresentative Scalar where
  value := (value : Scalar)
  nonzero := (RFAP.ConstructiveFraction.natCast_pos_direct positive).ne'

/-- Regard one displayed positive natural as a positive rational square-class
target.  This is useful for finite computations and examples. -/
def positiveNaturalTarget (value : Nat) (positive : 0 < value) :
    TheoremSixtyTwo.PositiveSquareClassRepresentative where
  representative := positiveNaturalClass value positive
  positive := RFAP.ConstructiveFraction.natCast_pos_direct positive

/-- Cached output of the finite square-class signature computation. -/
structure Signature
    (target : TheoremSixtyTwo.PositiveSquareClassRepresentative) where
  source : Nat
  source_eq : source = target.numerator * target.denominator
  source_positive : 0 < source
  root : Nat
  root_positive : 0 < root
  primes : List Nat
  primes_prime : ∀ prime ∈ primes, Nat.Prime prime
  primes_nodup : primes.Nodup
  kernel : Nat
  kernel_eq : kernel = primes.prod
  kernel_positive : 0 < kernel
  decomposition : source = root ^ 2 * kernel
  squareFactor : Scalar
  squareFactor_nonzero : squareFactor ≠ 0
  value_eq_squareFactor_sq_mul_kernel :
    target.representative.value = squareFactor ^ 2 * (kernel : Scalar)
  equivalent :
    (positiveNaturalClass kernel kernel_positive).Equivalent
      target.representative

/-- Compute the finite odd-prime signature of one positive rational class. -/
def compute
    (target : TheoremSixtyTwo.PositiveSquareClassRepresentative) :
    Signature target := by
  let source := target.numerator * target.denominator
  have sourcePositive : 0 < source :=
    Nat.mul_pos target.numerator_positive target.denominator_positive
  let output := RFAP.ConstructivePrimeParity.decompose source sourcePositive
  have kernelPositive : 0 < output.primes.prod :=
    primeProduct_positive output.primes_prime
  have rootPositive : 0 < output.root := by
    apply Nat.pos_of_ne_zero
    intro rootZero
    have sourceZero : source = 0 := by
      calc
        source = output.root ^ 2 * output.primes.prod := output.equation
        _ = 0 ^ 2 * output.primes.prod :=
          congrArg (fun root : Nat => root ^ 2 * output.primes.prod) rootZero
        _ = 0 := by
          simp only [Nat.zero_pow (by decide : 0 < 2), Nat.zero_mul]
    exact (Nat.ne_of_gt sourcePositive) sourceZero
  have rootCastNonzero : (output.root : Scalar) ≠ 0 := by
    intro castZero
    have naturalZero : output.root = 0 :=
      RFAP.ConstructiveFraction.natCast_injective_direct (by
        simpa only [Nat.cast_zero] using castZero)
    exact (Nat.ne_of_gt rootPositive) naturalZero
  have denominatorNonzero : (target.denominator : Scalar) ≠ 0 :=
    target.denominator_cast_ne_zero
  have inverseNonzero : (target.denominator : Scalar)⁻¹ ≠ 0 :=
    RFAP.ExplicitField.inv_ne_zero denominatorNonzero
  let squareFactor :=
    (output.root : Scalar) * (target.denominator : Scalar)⁻¹
  have squareFactorNonzero : squareFactor ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero rootCastNonzero inverseNonzero
  have valueEquation : target.representative.value =
      squareFactor ^ 2 * (output.primes.prod : Scalar) := by
    have castDecomposition := congrArg (fun value : Nat => (value : Scalar))
      output.equation
    have castDecomposition' :
        (target.numerator : Scalar) * (target.denominator : Scalar) =
          (output.root : Scalar) ^ 2 * (output.primes.prod : Scalar) := by
      simpa only [source, Nat.cast_mul, Nat.cast_pow] using castDecomposition
    have denominatorCancel := RFAP.ExplicitField.mul_inv_cancel
      (target.denominator : Scalar) denominatorNonzero
    have targetFormula : target.representative.value =
        ((target.numerator : Scalar) *
          (target.denominator : Scalar)) *
          (target.denominator : Scalar)⁻¹ ^ 2 := by
      rw [target.value_eq_div]
      simp only [RFAP.ExplicitField.div_eq_mul_inv]
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

/-- The computed natural kernel is one exactly when its complete finite
odd-prime support is empty. -/
theorem Signature.kernel_eq_one_iff_primes_eq_nil
    {target : TheoremSixtyTwo.PositiveSquareClassRepresentative}
    (signature : Signature target) :
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

private theorem prime_not_dvd_prime {left right : Nat}
    (leftPrime : Nat.Prime left) (rightPrime : Nat.Prime right)
    (different : left ≠ right) : ¬ left ∣ right := by
  intro divides
  exact different ((Nat.prime_dvd_prime_iff_eq leftPrime rightPrime).mp divides)

private theorem prime_not_dvd_product {prime : Nat}
    (primeIsPrime : Nat.Prime prime) : ∀ {values : List Nat},
    (∀ value ∈ values, Nat.Prime value) → prime ∉ values →
      ¬ prime ∣ values.prod
  | [], _allPrime, _notMember => primeIsPrime.not_dvd_one
  | head :: tail, allPrime, notMember => by
      intro divides
      have primeDifferentHead : prime ≠ head := by
        intro equal
        apply notMember
        exact equal ▸ List.mem_cons_self
      have notDividesHead : ¬ prime ∣ head :=
        prime_not_dvd_prime primeIsPrime
          (allPrime head List.mem_cons_self) primeDifferentHead
      have dividesTail : prime ∣ tail.prod :=
        RFAP.ConstructivePrimeFactor.prime_dvd_right_of_dvd_mul_of_not_dvd
          primeIsPrime notDividesHead (by
            simpa only [List.prod_cons] using divides)
      exact prime_not_dvd_product primeIsPrime
        (fun value member =>
          allPrime value (List.mem_cons_of_mem head member))
        (fun member => notMember (List.mem_cons_of_mem head member))
        dividesTail

private theorem primeCofactor {prime : Nat}
    (primeIsPrime : Nat.Prime prime) : ∀ {values : List Nat},
    values.Nodup → (∀ value ∈ values, Nat.Prime value) →
      prime ∈ values →
      ∃ cofactor : Nat,
        values.prod = prime * cofactor ∧ ¬ prime ∣ cofactor
  | [], _nodup, _allPrime, impossible => by nomatch impossible
  | head :: tail, nodup, allPrime, member => by
      have nodupParts := List.pairwise_cons.mp nodup
      rw [List.mem_cons] at member
      rcases member with equal | tailMember
      · subst head
        refine ⟨tail.prod, by simp only [List.prod_cons], ?_⟩
        apply prime_not_dvd_product primeIsPrime
        · intro value valueMember
          exact allPrime value (List.mem_cons_of_mem prime valueMember)
        · intro primeMember
          exact nodupParts.1 prime primeMember rfl
      · rcases primeCofactor primeIsPrime nodupParts.2
          (fun value valueMember =>
            allPrime value (List.mem_cons_of_mem head valueMember))
          tailMember with ⟨cofactor, productEquation, notDividesCofactor⟩
        have primeDifferentHead : prime ≠ head := by
          intro equal
          exact nodupParts.1 prime tailMember equal.symm
        have notDividesHead : ¬ prime ∣ head :=
          prime_not_dvd_prime primeIsPrime
            (allPrime head List.mem_cons_self) primeDifferentHead
        refine ⟨head * cofactor, ?_, ?_⟩
        · simp only [List.prod_cons]
          rw [productEquation]
          ring1
        · intro divides
          have dividesCofactor :=
            RFAP.ConstructivePrimeFactor.prime_dvd_right_of_dvd_mul_of_not_dvd
                primeIsPrime notDividesHead divides
          exact notDividesCofactor dividesCofactor

private theorem not_equivalent_of_prime_mismatch
    {leftPrimes rightPrimes : List Nat}
    (leftPrime : ∀ prime ∈ leftPrimes, Nat.Prime prime)
    (rightPrime : ∀ prime ∈ rightPrimes, Nat.Prime prime)
    (leftNodup : leftPrimes.Nodup)
    {prime : Nat} (memberLeft : prime ∈ leftPrimes)
    (notMemberRight : prime ∉ rightPrimes) :
    ¬ (positiveNaturalClass leftPrimes.prod
        (primeProduct_positive leftPrime)).Equivalent
      (positiveNaturalClass rightPrimes.prod
        (primeProduct_positive rightPrime)) := by
  intro equivalent
  have primeIsPrime := leftPrime prime memberLeft
  rcases equivalent with ⟨factor, _factorNonzero, classEquation⟩
  change (rightPrimes.prod : Scalar) =
    factor ^ 2 * (leftPrimes.prod : Scalar) at classEquation
  let reduced := RFAP.ConstructiveFraction.representative factor
  have cleared := RFAP.ConstructiveFraction.representative_mul_den factor
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
    apply RFAP.ConstructiveFraction.intCast_injective_direct
    rw [RFAP.ConstructiveFraction.intCast_mul_direct,
      RFAP.ConstructiveFraction.intCast_mul_direct,
      RFAP.ConstructiveFraction.intCast_mul_direct,
      RFAP.ConstructiveFraction.intCast_mul_direct]
    simpa only [Int.cast_natCast, pow_two] using rationalEquation
  have absoluteEquation := congrArg Int.natAbs integerEquation
  have naturalEquation :
      rightPrimes.prod * (reduced.den * reduced.den) =
        (reduced.num.natAbs * reduced.num.natAbs) * leftPrimes.prod := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using absoluteEquation
  rcases primeCofactor primeIsPrime leftNodup leftPrime memberLeft with
    ⟨leftCofactor, leftProduct, notDividesLeftCofactor⟩
  have notDividesRightProduct : ¬ prime ∣ rightPrimes.prod :=
    prime_not_dvd_product primeIsPrime rightPrime notMemberRight
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
    RFAP.ConstructivePrimeFactor.prime_dvd_right_of_dvd_mul_of_not_dvd
      primeIsPrime notDividesRightProduct primeDividesLeftSide
  have primeDividesDenominator : prime ∣ reduced.den :=
    RFAP.ConstructivePrimeFactor.prime_dvd_of_dvd_square primeIsPrime
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
    apply RFAP.ConstructivePrimeFactor.prime_dvd_right_of_dvd_mul_of_not_dvd
      primeIsPrime
        notDividesLeftCofactor
    simpa only [Nat.mul_comm leftCofactor] using
      primeDividesNumeratorSquareTimesCofactor
  have primeDividesNumerator : prime ∣ reduced.num.natAbs :=
    RFAP.ConstructivePrimeFactor.prime_dvd_of_dvd_square primeIsPrime
      primeDividesNumeratorSquare
  rcases reduced.reduced with ⟨coprime⟩
  have primeOne := coprime.eq_one_of_dvd
    primeDividesNumerator ⟨denominatorCofactor, denominatorEquation⟩
  exact primeIsPrime.ne_one primeOne

private theorem equivalent_kernel_membership
    {leftTarget rightTarget :
      TheoremSixtyTwo.PositiveSquareClassRepresentative}
    (left : Signature leftTarget) (right : Signature rightTarget)
    (equivalent : leftTarget.representative.Equivalent
      rightTarget.representative) :
    ∀ prime, prime ∈ left.primes → prime ∈ right.primes := by
  intro prime memberLeft
  match natMembership prime right.primes with
  | isTrue memberRight => exact memberRight
  | isFalse memberRight =>
      apply False.elim
      have kernelEquivalent :
          (positiveNaturalClass left.kernel left.kernel_positive).Equivalent
            (positiveNaturalClass right.kernel right.kernel_positive) :=
        SquareClassRepresentative.equivalent_trans left.equivalent
          (SquareClassRepresentative.equivalent_trans equivalent
            (SquareClassRepresentative.equivalent_symm right.equivalent))
      have displayedKernelEquivalent :
          (positiveNaturalClass left.primes.prod
            (primeProduct_positive left.primes_prime)).Equivalent
          (positiveNaturalClass right.primes.prod
            (primeProduct_positive right.primes_prime)) := by
        simpa only [left.kernel_eq, right.kernel_eq] using kernelEquivalent
      exact (not_equivalent_of_prime_mismatch left.primes_prime
        right.primes_prime left.primes_nodup memberLeft memberRight)
        displayedKernelEquivalent

private theorem perm_product_eq {left right : List Nat}
    (permutation : left.Perm right) : left.prod = right.prod := by
  induction permutation with
  | nil => rfl
  | cons head permutation inductionHypothesis =>
      simp only [List.prod_cons]
      rw [inductionHypothesis]
  | swap left right tail =>
      simp only [List.prod_cons]
      ring1
  | trans first second firstHypothesis secondHypothesis =>
      exact firstHypothesis.trans secondHypothesis

/-- Natural classes represented by duplicate-free prime lists are equivalent
exactly when the finite supports have the same members. -/
theorem primeSupportEquivalent_iff
    {left right : List Nat}
    (leftPrime : ∀ prime ∈ left, Nat.Prime prime)
    (rightPrime : ∀ prime ∈ right, Nat.Prime prime)
    (leftNodup : left.Nodup) (rightNodup : right.Nodup) :
    (positiveNaturalClass left.prod
        (primeProduct_positive leftPrime)).Equivalent
      (positiveNaturalClass right.prod
        (primeProduct_positive rightPrime)) ↔
      ∀ prime, prime ∈ left ↔ prime ∈ right := by
  constructor
  · intro equivalent prime
    constructor
    · intro memberLeft
      match natMembership prime right with
      | isTrue memberRight => exact memberRight
      | isFalse notMemberRight =>
          exact False.elim
            ((not_equivalent_of_prime_mismatch leftPrime rightPrime
              leftNodup memberLeft notMemberRight) equivalent)
    · intro memberRight
      match natMembership prime left with
      | isTrue memberLeft => exact memberLeft
      | isFalse notMemberLeft =>
          exact False.elim
            ((not_equivalent_of_prime_mismatch rightPrime leftPrime
              rightNodup memberRight notMemberLeft)
              (SquareClassRepresentative.equivalent_symm equivalent))
  · intro sameMembers
    have permutation : left.Perm right :=
      (List.perm_ext_iff_of_nodup leftNodup rightNodup).2 sameMembers
    have productsEqual := perm_product_eq permutation
    have representativesEqual :
        positiveNaturalClass left.prod (primeProduct_positive leftPrime) =
          positiveNaturalClass right.prod
            (primeProduct_positive rightPrime) := by
      apply SquareClassRepresentative.ext
      exact congrArg (fun value : Nat => (value : Scalar)) productsEqual
    rw [representativesEqual]
    exact SquareClassRepresentative.equivalent_refl _

theorem difference_prime {source against : List Nat}
    (sourcePrime : ∀ prime ∈ source, Nat.Prime prime) :
    ∀ prime ∈ difference source against, Nat.Prime prime := by
  intro prime member
  exact sourcePrime prime
    ((mem_difference_iff prime source against).1 member).1

theorem intersection_prime {source against : List Nat}
    (sourcePrime : ∀ prime ∈ source, Nat.Prime prime) :
    ∀ prime ∈ intersection source against, Nat.Prime prime := by
  intro prime member
  exact sourcePrime prime
    ((mem_intersection_iff prime source against).1 member).1

theorem xorSupport_prime {left right : List Nat}
    (leftPrime : ∀ prime ∈ left, Nat.Prime prime)
    (rightPrime : ∀ prime ∈ right, Nat.Prime prime) :
    ∀ prime ∈ xorSupport left right, Nat.Prime prime := by
  intro prime member
  rw [xorSupport, List.mem_append] at member
  rcases member with leftMember | rightMember
  · exact difference_prime leftPrime prime leftMember
  · exact difference_prime rightPrime prime rightMember

theorem xorSupport_nodup {left right : List Nat}
    (leftNodup : left.Nodup) (rightNodup : right.Nodup) :
    (xorSupport left right).Nodup := by
  unfold xorSupport
  apply QuotientFreeList.nodup_append
    (leftNodup.filter _) (rightNodup.filter _)
  intro leftValue leftMember rightValue rightMember equal
  have leftProperties :=
    (mem_difference_iff leftValue left right).1 leftMember
  have rightProperties :=
    (mem_difference_iff rightValue right left).1 rightMember
  apply leftProperties.2
  exact equal ▸ rightProperties.1

private theorem intersection_product_comm
    {left right : List Nat} (leftNodup : left.Nodup)
    (rightNodup : right.Nodup) :
    (intersection left right).prod = (intersection right left).prod := by
  have permutation : (intersection left right).Perm
      (intersection right left) :=
    (List.perm_ext_iff_of_nodup (leftNodup.filter _)
      (rightNodup.filter _)).2 fun value => by
        change value ∈ intersection left right ↔
          value ∈ intersection right left
        rw [mem_intersection_iff, mem_intersection_iff]
        exact and_comm
  exact perm_product_eq permutation

/-- Multiplying two square-free prime products produces the square of their
common part times the product of their symmetric difference. -/
theorem product_eq_common_sq_mul_xor
    (left right : List Nat) (leftNodup : left.Nodup)
    (rightNodup : right.Nodup) :
    left.prod * right.prod =
      (intersection left right).prod ^ 2 * (xorSupport left right).prod := by
  rw [product_partition left right, product_partition right left,
    intersection_product_comm leftNodup rightNodup,
    xorSupport, List.prod_append]
  ring1

/-- Multiplication of two positive square classes as a positive target. -/
def mulTarget
    (left right : TheoremSixtyTwo.PositiveSquareClassRepresentative) :
    TheoremSixtyTwo.PositiveSquareClassRepresentative where
  representative := SquareClassRepresentative.mul
    left.representative right.representative
  positive := RFAP.ConstructiveFraction.mul_pos_direct left.positive
    right.positive

/-- The natural class of a symmetric-difference support equals the product
of the two displayed natural classes. -/
theorem xorSupport_equivalent_mul
    {left right : List Nat}
    (leftPrime : ∀ prime ∈ left, Nat.Prime prime)
    (rightPrime : ∀ prime ∈ right, Nat.Prime prime)
    (leftNodup : left.Nodup) (rightNodup : right.Nodup) :
    (positiveNaturalClass (xorSupport left right).prod
        (primeProduct_positive
          (xorSupport_prime leftPrime rightPrime))).Equivalent
      (SquareClassRepresentative.mul
        (positiveNaturalClass left.prod (primeProduct_positive leftPrime))
        (positiveNaturalClass right.prod (primeProduct_positive rightPrime))) := by
  have commonPrime : ∀ prime ∈ intersection left right,
      Nat.Prime prime :=
    intersection_prime (source := left) (against := right) leftPrime
  have commonPositive : 0 < (intersection left right).prod :=
    primeProduct_positive commonPrime
  have commonCastNonzero :
      ((intersection left right).prod : Scalar) ≠ 0 :=
    (RFAP.ConstructiveFraction.natCast_pos_direct commonPositive).ne'
  refine ⟨((intersection left right).prod : Scalar), commonCastNonzero, ?_⟩
  change (left.prod : Scalar) * (right.prod : Scalar) =
    ((intersection left right).prod : Scalar) ^ 2 *
      ((xorSupport left right).prod : Scalar)
  have naturalEquation := product_eq_common_sq_mul_xor left right
    leftNodup rightNodup
  have castEquation := congrArg (fun value : Nat => (value : Scalar))
    naturalEquation
  simpa only [Nat.cast_mul, Nat.cast_pow] using castEquation

/-- The computed prime support of a product is the symmetric difference of
the computed supports of its factors. -/
theorem compute_mulTarget_support
    (left right : TheoremSixtyTwo.PositiveSquareClassRepresentative) :
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
        (primeProduct_positive leftSignature.primes_prime)).Equivalent
        left.representative := by
    simpa only [leftSignature.kernel_eq] using leftSignature.equivalent
  have rightDisplayed :
      (positiveNaturalClass rightSignature.primes.prod
        (primeProduct_positive rightSignature.primes_prime)).Equivalent
        right.representative := by
    simpa only [rightSignature.kernel_eq] using rightSignature.equivalent
  have productDisplayed :
      (positiveNaturalClass productSignature.primes.prod
        (primeProduct_positive productSignature.primes_prime)).Equivalent
        (mulTarget left right).representative := by
    simpa only [productSignature.kernel_eq] using productSignature.equivalent
  have xorToDisplayedProduct := xorSupport_equivalent_mul
    leftSignature.primes_prime rightSignature.primes_prime
    leftSignature.primes_nodup rightSignature.primes_nodup
  have displayedProductToTarget :=
    SquareClassRepresentative.mul_respects_equivalent leftDisplayed
      rightDisplayed
  have xorToProductSignature :=
    SquareClassRepresentative.equivalent_trans xorToDisplayedProduct
      (SquareClassRepresentative.equivalent_trans displayedProductToTarget
        (SquareClassRepresentative.equivalent_symm productDisplayed))
  have sameMembers := (primeSupportEquivalent_iff
    (xorSupport_prime leftSignature.primes_prime rightSignature.primes_prime)
    productSignature.primes_prime
    (xorSupport_nodup leftSignature.primes_nodup
      rightSignature.primes_nodup)
    productSignature.primes_nodup).1 xorToProductSignature
  intro prime
  exact (sameMembers prime).symm

/-- Two positive rational classes are equivalent exactly when their finite
natural prime-parity kernels agree. -/
theorem equivalent_iff_kernel_eq
    {leftTarget rightTarget :
      TheoremSixtyTwo.PositiveSquareClassRepresentative}
    (left : Signature leftTarget) (right : Signature rightTarget) :
    leftTarget.representative.Equivalent rightTarget.representative ↔
      left.kernel = right.kernel := by
  constructor
  · intro equivalent
    have forward := equivalent_kernel_membership left right equivalent
    have reverse := equivalent_kernel_membership right left
      (SquareClassRepresentative.equivalent_symm equivalent)
    have permutation : left.primes.Perm right.primes :=
      (List.perm_ext_iff_of_nodup left.primes_nodup
        right.primes_nodup).2 fun prime =>
          ⟨forward prime, reverse prime⟩
    rw [left.kernel_eq, right.kernel_eq]
    exact perm_product_eq permutation
  · intro kernelsEqual
    have representativesEqual :
        positiveNaturalClass left.kernel left.kernel_positive =
          positiveNaturalClass right.kernel right.kernel_positive := by
      apply SquareClassRepresentative.ext
      exact congrArg (fun value : Nat => (value : Scalar)) kernelsEqual
    apply SquareClassRepresentative.equivalent_trans
      (SquareClassRepresentative.equivalent_symm left.equivalent)
    rw [representativesEqual]
    exact right.equivalent

end PositiveSquareClassSignatures

end RationalRotations
