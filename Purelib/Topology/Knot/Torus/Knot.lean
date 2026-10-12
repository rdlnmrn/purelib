module
import Purelib.Data.Fin.Bijection.Cycle
import Purelib.Data.Fin.Bijection.Iteration
public import Purelib.Data.Nat.Coprime.Basic
import Purelib.Data.Nat.GCD.Coprime
public import Purelib.Data.Nat.GCD.Extended
import Purelib.Topology.Knot.Braid.PositiveBand.Basic
import Purelib.Topology.Knot.Braid.PositiveBand.Cycle
import Purelib.Topology.Knot.Braid.Word.Power
public import Purelib.Topology.Knot.Torus.Basic
import Purelib.Topology.Knot.Closure.Basic
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Data.Fin.Bijection.Basic

open Purelib.Data.Nat

open Purelib.Data.Nat.GCD

open Purelib.Topology.Knot

open Purelib.Topology.Knot.Braid

open Purelib.Topology.Knot.Braid.PositiveBand

section
@[expose] public section

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

namespace Purelib.Topology.Knot.Torus.PowerSingularity

/-- A strand return after steps torus circuits forces p to divide q times steps. -/
theorem return_dvd_p (singularity :
  Torus.Basic.PowerSingularity)
    (steps : Nat) (index : Fin singularity.p)
    (returned : Data.Fin.Bijection.iterateForward
      singularity.closure.permutation steps index = index) :
    singularity.p ∣ singularity.q * steps := by
  change Data.Fin.Bijection.iterateForward
      (Word.repeatWord (PositiveBand.Basic.positiveBand singularity.p) singularity.q).permutation
      steps index = index at returned
  rw [Word.repeatWord_iterate] at returned
  exact Cycle.positiveBand_return_dvd singularity.pPositive
    (singularity.q * steps) index returned

open Purelib.Topology.Knot.Torus
/-- A coprime torus braid has no positive return shorter than `p`, hence its closure is a knot. -/
theorem closure_isKnot_of_coprime
    (singularity : Torus.Basic.PowerSingularity)
    (coprime : Coprime.Basic.CoprimeCertificate singularity.p singularity.q) :
    singularity.closure.IsKnot := by
  apply Data.Fin.Bijection.isSingleCycle_of_noEarlyReturn
  intro index steps stepsPositive stepsSmall returned
  have dividesProduct : singularity.p ∣ steps * singularity.q := by
    simpa only [Nat.mul_comm] using
      return_dvd_p singularity steps index returned
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

/-- A computed gcd of one certifies that the torus closure has a single strand orbit. -/
theorem closure_isKnot_of_gcdOne
    (singularity : Torus.Basic.PowerSingularity)
    (gcdOne : (Extended.compute singularity.p singularity.q).gcd = 1) :
    singularity.closure.IsKnot :=
  closure_isKnot_of_coprime singularity
    (Coprime.coprimeCertificateOfGcdOne singularity.p singularity.q gcdOne)

end Purelib.Topology.Knot.Torus.PowerSingularity

end
