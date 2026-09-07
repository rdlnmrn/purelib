import CCL.Knot.TorusKnot

/-!
# Finite closure-component certificates

A finite permutation decomposes into finite cycles.  For the torus family all
cycles have the same displayed length, so an exact component result is most
economically represented by a uniform-cycle certificate: component count
times orbit length is the strand count, every strand returns at that orbit
length, and no positive shorter return is possible.

For `(σ₁…σₚ₋₁)^q`, the component count is the output of the
project's structurally recursive certified Euclidean algorithm.  The proof
uses its divisibility data and quotient Bézout certificate; it does not use
upstream `Nat.gcd`.
-/

namespace CCL.Knot.ClosureComponents

open CCL.Knot.FiniteBraid
open CCL.Knot.TorusBraid
open CCL.Knot.TorusKnot

namespace Closure

/-- Exact finite evidence for a closure whose permutation cycles all have the
same displayed length. -/
structure UniformComponentCertificate (closure : Closure) where
  componentCount : Nat
  orbitLength : Nat
  count_mul_orbitLength : componentCount * orbitLength = closure.strands
  return_at_orbitLength : ∀ index : Fin closure.strands,
    CCL.FiniteMonodromy.FiniteBijection.iterateForward
      closure.permutation orbitLength index = index
  no_early_return : ∀ (index : Fin closure.strands) (steps : Nat),
    0 < steps → steps < orbitLength →
      CCL.FiniteMonodromy.FiniteBijection.iterateForward
        closure.permutation steps index ≠ index

end Closure

end CCL.Knot.ClosureComponents

namespace CCL.Knot.TorusBraid.PowerSingularity

open CCL.Knot.FiniteBraid
open CCL.Knot.TorusBraid
open CCL.Knot.TorusKnot

/-- Executable torus-link component count. -/
def componentCount (singularity : PowerSingularity) : Nat :=
  (RFAP.CanonicalGCD.compute singularity.p singularity.q).gcd

/-- Common length of every strand orbit in the torus closure. -/
def componentOrbitLength (singularity : PowerSingularity) : Nat :=
  singularity.p / singularity.componentCount

theorem componentCount_positive (singularity : PowerSingularity) :
    0 < singularity.componentCount :=
  RFAP.CanonicalGCD.compute_gcd_positive_right
    singularity.p singularity.qPositive

theorem componentCount_dvd_p (singularity : PowerSingularity) :
    singularity.componentCount ∣ singularity.p :=
  (RFAP.CanonicalGCD.compute_spec singularity.p singularity.q).2.1

theorem componentCount_dvd_q (singularity : PowerSingularity) :
    singularity.componentCount ∣ singularity.q :=
  (RFAP.CanonicalGCD.compute_spec singularity.p singularity.q).2.2

theorem componentCount_mul_orbitLength (singularity : PowerSingularity) :
    singularity.componentCount * singularity.componentOrbitLength =
      singularity.p := by
  rw [componentOrbitLength, Nat.mul_comm]
  exact Nat.div_mul_cancel singularity.componentCount_dvd_p

theorem totalBands_at_orbitLength (singularity : PowerSingularity) :
    singularity.q * singularity.componentOrbitLength =
      singularity.p * (singularity.q / singularity.componentCount) := by
  let divisor := singularity.componentCount
  have pFactor : singularity.p / divisor * divisor = singularity.p :=
    Nat.div_mul_cancel singularity.componentCount_dvd_p
  have qFactor : singularity.q / divisor * divisor = singularity.q :=
    Nat.div_mul_cancel singularity.componentCount_dvd_q
  change singularity.q * (singularity.p / divisor) =
    singularity.p * (singularity.q / divisor)
  calc
    singularity.q * (singularity.p / divisor) =
        (singularity.q / divisor * divisor) *
          (singularity.p / divisor) := by rw [qFactor]
    _ = (singularity.p / divisor * divisor) *
          (singularity.q / divisor) := by ring1
    _ = singularity.p * (singularity.q / divisor) := by rw [pFactor]

theorem closure_return_at_componentOrbitLength
    (singularity : PowerSingularity) (index : Fin singularity.p) :
    CCL.FiniteMonodromy.FiniteBijection.iterateForward
      singularity.closure.permutation singularity.componentOrbitLength index =
        index := by
  change CCL.FiniteMonodromy.FiniteBijection.iterateForward
    (repeatWord (positiveBand singularity.p) singularity.q).permutation
    singularity.componentOrbitLength index = index
  rw [repeatWord_iterate, singularity.totalBands_at_orbitLength]
  exact positiveBand_return_at_multiple singularity.pPositive
    (singularity.q / singularity.componentCount) index

theorem reducedDivides_of_fullDivides (singularity : PowerSingularity)
    {steps : Nat} (fullDivides : singularity.p ∣ singularity.q * steps) :
    singularity.componentOrbitLength ∣
      steps * (singularity.q / singularity.componentCount) := by
  let divisor := singularity.componentCount
  let reducedP := singularity.p / divisor
  let reducedQ := singularity.q / divisor
  have pFactor : reducedP * divisor = singularity.p :=
    Nat.div_mul_cancel singularity.componentCount_dvd_p
  have qFactor : reducedQ * divisor = singularity.q :=
    Nat.div_mul_cancel singularity.componentCount_dvd_q
  obtain ⟨factor, factorization⟩ := fullDivides
  refine ⟨factor, ?_⟩
  change steps * reducedQ = reducedP * factor
  apply Nat.mul_right_cancel singularity.componentCount_positive
  calc
    (steps * reducedQ) * divisor =
        (reducedQ * divisor) * steps := by ring1
    _ = singularity.q * steps := by rw [qFactor]
    _ = singularity.p * factor := factorization
    _ = (reducedP * divisor) * factor := by rw [pFactor]
    _ = (reducedP * factor) * divisor := by ring1

theorem closure_no_early_return_before_componentOrbitLength
    (singularity : PowerSingularity) (index : Fin singularity.p)
    (steps : Nat) (stepsPositive : 0 < steps)
    (stepsSmall : steps < singularity.componentOrbitLength) :
    CCL.FiniteMonodromy.FiniteBijection.iterateForward
      singularity.closure.permutation steps index ≠ index := by
  intro returned
  have fullDivides := PowerSingularity.return_dvd_p
    singularity steps index returned
  have reducedDivides := singularity.reducedDivides_of_fullDivides fullDivides
  let coprime := RFAP.CanonicalGCD.quotientCoprimeCertificate
    singularity.p singularity.qPositive
  have dividesSteps : singularity.componentOrbitLength ∣ steps :=
    coprime.dvd_of_dvd_mul_right reducedDivides
  obtain ⟨factor, factorization⟩ := dividesSteps
  have factorPositive : 0 < factor := by
    by_cases zero : factor = 0
    · subst factor
      simp only [Nat.mul_zero] at factorization
      exact (Nat.ne_of_gt stepsPositive factorization).elim
    · exact Nat.pos_of_ne_zero zero
  have orbitLengthAtMostSteps : singularity.componentOrbitLength ≤ steps := by
    calc
      singularity.componentOrbitLength ≤
          singularity.componentOrbitLength * factor :=
        Nat.le_mul_of_pos_right singularity.componentOrbitLength factorPositive
      _ = steps := factorization.symm
  exact Nat.not_lt_of_ge orbitLengthAtMostSteps stepsSmall

/-- Headline exact component theorem for the finite torus closure. -/
def componentCertificate (singularity : PowerSingularity) :
    CCL.Knot.ClosureComponents.Closure.UniformComponentCertificate
      singularity.closure where
  componentCount := singularity.componentCount
  orbitLength := singularity.componentOrbitLength
  count_mul_orbitLength := singularity.componentCount_mul_orbitLength
  return_at_orbitLength :=
    singularity.closure_return_at_componentOrbitLength
  no_early_return :=
    singularity.closure_no_early_return_before_componentOrbitLength

@[simp] theorem componentCertificate_count (singularity : PowerSingularity) :
    singularity.componentCertificate.componentCount =
      (RFAP.CanonicalGCD.compute singularity.p singularity.q).gcd := rfl

@[simp] theorem componentCertificate_orbitLength
    (singularity : PowerSingularity) :
    singularity.componentCertificate.orbitLength =
      singularity.p /
        (RFAP.CanonicalGCD.compute singularity.p singularity.q).gcd := rfl

end CCL.Knot.TorusBraid.PowerSingularity
