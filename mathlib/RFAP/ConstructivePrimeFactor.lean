import mathlib.Data.ConstructiveList
import mathlib.RFAP.CanonicalGCD
import mathlib.Tactic.QuotientFreeOmega
import Mathlib.Data.Nat.Prime.Basic

/-!
# Bounded constructive prime factors

This module returns one prime divisor of a displayed natural number at least
two.  Composite inputs are reduced by an explicit search through
`List.range value`; recursion is on the strictly smaller displayed factor.
It deliberately does not use `Nat.minFac`, whose upstream proof closure
contains choice through the implementation of minimal factors.
-/

namespace RFAP.ConstructivePrimeFactor

private theorem find?_eq_some_accepts {Alpha : Type*}
    {predicate : Alpha → Bool} {target : Alpha} :
    ∀ {values : List Alpha},
      values.find? predicate = some target → predicate target = true
  | [], impossible => by
      nomatch impossible
  | head :: tail, found => by
      cases accepted : predicate head with
      | false =>
          rw [List.find?_cons, accepted] at found
          exact find?_eq_some_accepts found
      | true =>
          rw [List.find?_cons, accepted] at found
          injection found with equal
          exact equal ▸ accepted

private theorem find?_eq_some_mem {Alpha : Type*}
    {predicate : Alpha → Bool} {target : Alpha} :
    ∀ {values : List Alpha}, values.find? predicate = some target →
      target ∈ values
  | [], impossible => by
      nomatch impossible
  | head :: tail, found => by
      cases accepted : predicate head with
      | false =>
          rw [List.find?_cons, accepted] at found
          exact List.mem_cons_of_mem head (find?_eq_some_mem found)
      | true =>
          rw [List.find?_cons, accepted] at found
          injection found with equal
          exact equal ▸ List.mem_cons_self

/-- A retained prime divisor of one displayed natural number. -/
structure Output (source : Nat) where
  factor : Nat
  factorPrime : Nat.Prime factor
  factorDivides : factor ∣ source

/-- Find one prime divisor using only a bounded proper-factor scan and
well-founded recursion on the returned factor. -/
def compute : (source : Nat) → 2 ≤ source → Output source :=
  Nat.strongRec (motive := fun source => 2 ≤ source → Output source)
    fun source recurse sourceAtLeastTwo => by
      let acceptedFactor : Nat → Bool := fun factor =>
        decide (2 ≤ factor) && decide (source % factor = 0)
      cases factorFound : (List.range source).find? acceptedFactor with
      | none =>
          have rejected := QuotientFreeList.find?_eq_none.mp factorFound
          have sourcePrime : Nat.Prime source := by
            apply Nat.prime_def.mpr
            refine ⟨sourceAtLeastTwo, ?_⟩
            intro divisor divisorDivides
            by_cases divisorOne : divisor = 1
            · exact Or.inl divisorOne
            · by_cases divisorSource : divisor = source
              · exact Or.inr divisorSource
              · have sourcePositive : 0 < source := by omega0
                have divisorPositive : 0 < divisor := by
                  by_contra divisorNotPositive
                  have divisorZero : divisor = 0 := by omega0
                  subst divisor
                  exact (by omega0 : source ≠ 0)
                    (Nat.eq_zero_of_zero_dvd divisorDivides)
                have divisorAtLeastTwo : 2 ≤ divisor := by omega0
                have divisorAtMostSource : divisor ≤ source :=
                  Nat.le_of_dvd sourcePositive divisorDivides
                have divisorBelow : divisor < source := by omega0
                have divisorMember : divisor ∈ List.range source :=
                  QuotientFreeList.mem_range.mpr divisorBelow
                have divisorRejected := rejected divisor divisorMember
                have divisorModulo : source % divisor = 0 :=
                  Nat.mod_eq_zero_of_dvd divisorDivides
                have divisorAccepted : acceptedFactor divisor = true := by
                  simp only [acceptedFactor, Bool.and_eq_true,
                    decide_eq_true_eq]
                  exact ⟨divisorAtLeastTwo, divisorModulo⟩
                rw [divisorAccepted] at divisorRejected
                exact False.elim (Bool.noConfusion divisorRejected)
          exact ⟨source, sourcePrime, dvd_refl source⟩
      | some factor =>
          have factorAccepted := find?_eq_some_accepts factorFound
          have factorMember := find?_eq_some_mem factorFound
          have factorConditions : 2 ≤ factor ∧ source % factor = 0 := by
            simpa only [acceptedFactor, Bool.and_eq_true,
              decide_eq_true_eq] using factorAccepted
          have factorBelow : factor < source :=
            QuotientFreeList.mem_range.mp factorMember
          have factorDividesSource : factor ∣ source :=
            Nat.dvd_of_mod_eq_zero factorConditions.2
          let smaller := recurse factor factorBelow factorConditions.1
          exact
            { factor := smaller.factor
              factorPrime := smaller.factorPrime
              factorDivides := dvd_trans smaller.factorDivides
                factorDividesSource }

theorem compute_factor_at_least_two (source : Nat)
    (sourceAtLeastTwo : 2 ≤ source) :
    2 ≤ (compute source sourceAtLeastTwo).factor :=
  (compute source sourceAtLeastTwo).factorPrime.two_le

/-! ## Choice-free prime cancellation -/

/-- Cancel a displayed factor not divisible by a prime.  The upstream
`Nat.Prime.dvd_mul` exposes a disjunction through classical propositional
decidability.  This directed version instead computes a Bézout certificate
for the displayed prime and left factor. -/
theorem prime_dvd_right_of_dvd_mul_of_not_dvd
    {prime left right : Nat} (primeIsPrime : Nat.Prime prime)
    (notDividesLeft : ¬ prime ∣ left)
    (dividesProduct : prime ∣ left * right) : prime ∣ right := by
  let result := RFAP.CanonicalGCD.compute prime left
  have specification := RFAP.CanonicalGCD.compute_spec prime left
  have gcdAlternative := primeIsPrime.eq_one_or_self_of_dvd result.gcd
    specification.2.1
  rcases gcdAlternative with gcdOne | gcdPrime
  · let coprime : RFAP.CanonicalGCD.CoprimeCertificate prime left :=
      { left := result.left
        right := result.right
        identity := by
          rw [← specification.1, gcdOne]
          rfl }
    apply coprime.dvd_of_dvd_mul_right
    simpa only [Nat.mul_comm] using dividesProduct
  · apply False.elim
    apply notDividesLeft
    rw [← gcdPrime]
    exact specification.2.2

/-- A prime detected in the square of one displayed natural already divides
that natural. -/
theorem prime_dvd_of_dvd_square {prime value : Nat}
    (primeIsPrime : Nat.Prime prime)
    (dividesSquare : prime ∣ value * value) : prime ∣ value := by
  by_cases dividesValue : prime ∣ value
  · exact dividesValue
  · exact prime_dvd_right_of_dvd_mul_of_not_dvd primeIsPrime
      dividesValue dividesSquare

end RFAP.ConstructivePrimeFactor
