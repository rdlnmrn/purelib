import CCL.Knot.TorusPermutation

/-!
# Coprime torus braids close to knots

This file proves the constructive coprime case of the torus-link component
theorem.  Each positive band decreases the finite strand label by one, with a
displayed wrap count.  Telescoping those finite equalities shows that a return
after `k` bands forces the strand count to divide `k`.  A stored Bézout
certificate then cancels the `q` factor for the braid
`(σ₁…σₚ₋₁)^q`, ruling out every early return when `p` and `q` are
coprime.
-/

namespace CCL.Knot.TorusKnot

open CCL.Knot.FiniteBraid
open CCL.Knot.TorusBraid
open CCL.Knot.TorusPermutation

abbrev CoprimeCertificate := RFAP.CanonicalGCD.CoprimeCertificate

/-! ## Finite wrap arithmetic -/

theorem cyclicPredecessor_balance {count : Nat} (positive : 0 < count)
    (index : Fin count) :
    ∃ wraps : Nat,
      (cyclicPredecessor positive index).val + 1 =
        index.val + wraps * count := by
  by_cases zero : index.val = 0
  · refine ⟨1, ?_⟩
    rw [cyclicPredecessor]
    simp only [zero, ↓reduceDIte, one_mul]
    omega
  · refine ⟨0, ?_⟩
    rw [cyclicPredecessor]
    simp only [zero, ↓reduceDIte, zero_mul, add_zero]
    omega

theorem positiveBand_balance {strands : Nat} (positive : 0 < strands)
    (index : Fin strands) :
    ∃ wraps : Nat,
      ((positiveBand strands).permutation.forward index).val + 1 =
        index.val + wraps * strands := by
  rw [positiveBand_permutation_forward positive index]
  exact cyclicPredecessor_balance positive index

/-- Telescoping balance for a displayed finite number of positive bands. -/
theorem positiveBand_iterate_balance {strands : Nat}
    (positive : 0 < strands) (steps : Nat) (index : Fin strands) :
    ∃ wraps : Nat,
      (CCL.FiniteMonodromy.FiniteBijection.iterateForward
          (positiveBand strands).permutation steps index).val + steps =
        index.val + wraps * strands := by
  induction steps with
  | zero =>
      exact ⟨0, by simp only [
        CCL.FiniteMonodromy.FiniteBijection.iterateForward_zero,
        add_zero, zero_mul]⟩
  | succ steps inductionHypothesis =>
      obtain ⟨earlierWraps, earlierBalance⟩ := inductionHypothesis
      let earlier := CCL.FiniteMonodromy.FiniteBijection.iterateForward
        (positiveBand strands).permutation steps index
      obtain ⟨nextWraps, nextBalance⟩ :=
        positiveBand_balance positive earlier
      refine ⟨earlierWraps + nextWraps, ?_⟩
      change
        ((positiveBand strands).permutation.forward earlier).val +
            (steps + 1) =
          index.val + (earlierWraps + nextWraps) * strands
      calc
        ((positiveBand strands).permutation.forward earlier).val +
              (steps + 1) =
            (((positiveBand strands).permutation.forward earlier).val + 1) +
              steps := by omega
        _ = (earlier.val + nextWraps * strands) + steps := by
          rw [nextBalance]
        _ = (earlier.val + steps) + nextWraps * strands := by ring1
        _ = (index.val + earlierWraps * strands) +
              nextWraps * strands := by rw [earlierBalance]
        _ = index.val + (earlierWraps + nextWraps) * strands := by ring1

/-- Returning after `steps` positive bands forces divisibility by the strand
count. -/
theorem positiveBand_return_dvd {strands : Nat} (positive : 0 < strands)
    (steps : Nat) (index : Fin strands)
    (returned : CCL.FiniteMonodromy.FiniteBijection.iterateForward
      (positiveBand strands).permutation steps index = index) :
    strands ∣ steps := by
  obtain ⟨wraps, balance⟩ :=
    positiveBand_iterate_balance positive steps index
  rw [returned] at balance
  have stepsEq : steps = wraps * strands := Nat.add_left_cancel balance
  exact ⟨wraps, stepsEq.trans (Nat.mul_comm wraps strands)⟩

/-- One positive band is itself a full cycle of all displayed strands. -/
theorem positiveBand_isSingleCycle {strands : Nat} (positive : 0 < strands) :
    CCL.FiniteMonodromy.FiniteBijection.IsSingleCycle
      (positiveBand strands).permutation := by
  apply CCL.FiniteMonodromy.FiniteBijection.isSingleCycle_of_noEarlyReturn
  intro index steps stepsPositive stepsSmall returned
  obtain ⟨factor, factorization⟩ :=
    positiveBand_return_dvd positive steps index returned
  have factorPositive : 0 < factor := by
    by_cases zero : factor = 0
    · subst factor
      simp only [Nat.mul_zero] at factorization
      exact (Nat.ne_of_gt stepsPositive factorization).elim
    · exact Nat.pos_of_ne_zero zero
  have strandsAtMostSteps : strands ≤ steps := by
    calc
      strands ≤ strands * factor :=
        Nat.le_mul_of_pos_right strands factorPositive
      _ = steps := factorization.symm
  exact (Nat.not_lt_of_ge strandsAtMostSteps stepsSmall).elim

theorem positiveBand_return_at_multiple {strands : Nat}
    (positive : 0 < strands) (factor : Nat) (index : Fin strands) :
    CCL.FiniteMonodromy.FiniteBijection.iterateForward
      (positiveBand strands).permutation (strands * factor) index = index := by
  induction factor with
  | zero => rfl
  | succ factor inductionHypothesis =>
      rw [Nat.mul_add, Nat.mul_one,
        CCL.FiniteMonodromy.FiniteBijection.iterateForward_add,
        inductionHypothesis]
      exact (positiveBand_isSingleCycle positive).return_at_count index

/-! ## Iterating a word power -/

theorem repeatWord_iterate {strands : Nat} (word : Word strands)
    (exponent circuits : Nat) (index : Fin strands) :
    CCL.FiniteMonodromy.FiniteBijection.iterateForward
        (repeatWord word exponent).permutation circuits index =
      CCL.FiniteMonodromy.FiniteBijection.iterateForward
        word.permutation (exponent * circuits) index := by
  induction circuits with
  | zero => rfl
  | succ circuits inductionHypothesis =>
      rw [CCL.FiniteMonodromy.FiniteBijection.iterateForward_succ,
        repeatWord_permutation, inductionHypothesis]
      calc
        CCL.FiniteMonodromy.FiniteBijection.iterateForward word.permutation
              exponent
              (CCL.FiniteMonodromy.FiniteBijection.iterateForward
                word.permutation (exponent * circuits) index) =
            CCL.FiniteMonodromy.FiniteBijection.iterateForward
              word.permutation (exponent * circuits + exponent) index :=
          (CCL.FiniteMonodromy.FiniteBijection.iterateForward_add
            word.permutation (exponent * circuits) exponent index).symm
        _ = CCL.FiniteMonodromy.FiniteBijection.iterateForward
            word.permutation (exponent * (circuits + 1)) index := by
          congr 2

theorem PowerSingularity.return_dvd_p (singularity : PowerSingularity)
    (steps : Nat) (index : Fin singularity.p)
    (returned : CCL.FiniteMonodromy.FiniteBijection.iterateForward
      singularity.closure.permutation steps index = index) :
    singularity.p ∣ singularity.q * steps := by
  change CCL.FiniteMonodromy.FiniteBijection.iterateForward
      (repeatWord (positiveBand singularity.p) singularity.q).permutation
      steps index = index at returned
  rw [repeatWord_iterate] at returned
  exact positiveBand_return_dvd singularity.pPositive
    (singularity.q * steps) index returned

/-! ## Coprime closure theorem -/

/-- Turn the computed finite Euclidean result `1` into its stored Bézout
certificate. -/
def coprimeCertificateOfGcdOne (leftInput rightInput : Nat)
    (gcdOne : (RFAP.CanonicalGCD.compute leftInput rightInput).gcd = 1) :
    CoprimeCertificate leftInput rightInput where
  left := (RFAP.CanonicalGCD.compute leftInput rightInput).left
  right := (RFAP.CanonicalGCD.compute leftInput rightInput).right
  identity := by
    rw [← (RFAP.CanonicalGCD.compute_spec leftInput rightInput).1, gcdOne]
    rfl

/-- A coprime torus braid has no positive return shorter than `p`, hence its
closure is a knot. -/
theorem PowerSingularity.closure_isKnot_of_coprime
    (singularity : PowerSingularity)
    (coprime : CoprimeCertificate singularity.p singularity.q) :
    singularity.closure.IsKnot := by
  apply CCL.FiniteMonodromy.FiniteBijection.isSingleCycle_of_noEarlyReturn
  intro index steps stepsPositive stepsSmall returned
  have dividesProduct : singularity.p ∣ steps * singularity.q := by
    simpa only [Nat.mul_comm] using
      PowerSingularity.return_dvd_p singularity steps index returned
  have dividesSteps : singularity.p ∣ steps :=
    coprime.dvd_of_dvd_mul_right dividesProduct
  obtain ⟨factor, factorization⟩ := dividesSteps
  have factorPositive : 0 < factor := by
    by_cases zero : factor = 0
    · subst factor
      simp only [Nat.mul_zero] at factorization
      exact (Nat.ne_of_gt stepsPositive factorization).elim
    · exact Nat.pos_of_ne_zero zero
  have strandsAtMostSteps : singularity.p ≤ steps := by
    calc
      singularity.p ≤ singularity.p * factor :=
        Nat.le_mul_of_pos_right singularity.p factorPositive
      _ = steps := factorization.symm
  exact (Nat.not_lt_of_ge strandsAtMostSteps stepsSmall).elim

theorem PowerSingularity.closure_isKnot_of_gcdOne
    (singularity : PowerSingularity)
    (gcdOne : (RFAP.CanonicalGCD.compute singularity.p singularity.q).gcd = 1) :
    singularity.closure.IsKnot :=
  PowerSingularity.closure_isKnot_of_coprime singularity
    (coprimeCertificateOfGcdOne singularity.p singularity.q gcdOne)

end CCL.Knot.TorusKnot
