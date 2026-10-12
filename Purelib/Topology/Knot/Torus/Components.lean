module
import Purelib.Data.Nat.Division
import Purelib.Topology.Knot.Torus.Knot
import Purelib.Data.Fin.Bijection.Iteration
import Purelib.Data.Nat.GCD.Coprime
import Purelib.Data.Nat.GCD.Extended
import Purelib.Topology.Knot.Braid.PositiveBand.Cycle

public import Purelib.Data.Nat.GCD.Scalar
import Purelib.Topology.Knot.Braid.PositiveBand.Basic
import Purelib.Topology.Knot.Braid.Word.Power
public import Purelib.Topology.Knot.Closure.Components
public import Purelib.Topology.Knot.Torus.Basic
import Purelib.Topology.Knot.Closure.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Fin.Bijection.Basic

open Purelib.Data.Nat.GCD

open Purelib.Topology.Knot

open Purelib.Topology.Knot.Braid.PositiveBand

open Purelib.Topology.Knot.Closure.Components

open Purelib.Topology.Knot.Torus

open Purelib.Data

section
public section

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

namespace Purelib.Topology.Knot.Torus.Basic.PowerSingularity

open Purelib.Topology.Knot.Braid

/-- Executable torus-link component count. -/
@[expose] def componentCount (singularity : Torus.Basic.PowerSingularity) : Nat :=
  Scalar.gcd singularity.p singularity.q

/-- Common length of every strand orbit in the torus closure. -/
@[expose] def componentOrbitLength (singularity : Torus.Basic.PowerSingularity) : Nat :=
  singularity.p / singularity.componentCount

/-- The torus component count is positive for retained positive exponents. -/
theorem componentCount_positive (singularity : Torus.Basic.PowerSingularity) :
    0 < singularity.componentCount :=
  Scalar.gcd_positive_right
    singularity.p singularity.qPositive

/-- The computed component count divides the strand exponent. -/
theorem componentCount_dvd_p (singularity : Torus.Basic.PowerSingularity) :
    singularity.componentCount ∣ singularity.p :=
  (Scalar.gcd_dvd singularity.p singularity.q).1

/-- The computed component count divides the band exponent. -/
theorem componentCount_dvd_q (singularity : Torus.Basic.PowerSingularity) :
    singularity.componentCount ∣ singularity.q :=
  (Scalar.gcd_dvd singularity.p singularity.q).2

open Purelib.Topology.Knot.Torus.Basic in
/-- The component count times the common orbit length equals the strand exponent. -/
theorem componentCount_mul_orbitLength (singularity : Torus.Basic.PowerSingularity) :
    singularity.componentCount * singularity.componentOrbitLength =
      singularity.p := by
  rw [PowerSingularity.componentOrbitLength, Nat.mul_comm]
  exact Nat.Division.div_mul_cancel singularity.componentCount_dvd_p

/-- A full component orbit performs a strand-count multiple of positive bands.

The multiple is the band exponent divided by the computed common divisor. -/
theorem totalBands_at_orbitLength (singularity : Torus.Basic.PowerSingularity) :
    singularity.q * singularity.componentOrbitLength =
      singularity.p * (singularity.q / singularity.componentCount) := by
  let divisor := singularity.componentCount
  have pFactor : singularity.p / divisor * divisor = singularity.p :=
    Nat.Division.div_mul_cancel singularity.componentCount_dvd_p
  have qFactor : singularity.q / divisor * divisor = singularity.q :=
    Nat.Division.div_mul_cancel singularity.componentCount_dvd_q
  change singularity.q * (singularity.p / divisor) =
    singularity.p * (singularity.q / divisor)
  calc
    singularity.q * (singularity.p / divisor) =
        (singularity.q / divisor * divisor) *
          (singularity.p / divisor) := by rw [qFactor]
    _ = (singularity.p / divisor * divisor) *
          (singularity.q / divisor) := by ring1
    _ = singularity.p * (singularity.q / divisor) := by rw [pFactor]

/-- Every strand returns after the computed component orbit length. -/
theorem closure_return_at_componentOrbitLength
    (singularity : Torus.Basic.PowerSingularity) (index : Fin singularity.p) :
    Data.Fin.Bijection.iterateForward
      singularity.closure.permutation singularity.componentOrbitLength index =
        index := by
  change Data.Fin.Bijection.iterateForward
    (Word.repeatWord (PositiveBand.Basic.positiveBand singularity.p) singularity.q).permutation
    singularity.componentOrbitLength index = index
  rw [Word.repeatWord_iterate, singularity.totalBands_at_orbitLength]
  exact Cycle.positiveBand_return_at_multiple singularity.pPositive
    (singularity.q / singularity.componentCount) index

/-- Cancel the positive computed common divisor from a torus return divisibility equation.

Divisibility of q times steps by p implies divisibility of steps times reduced q by reduced p. -/
theorem reducedDivides_of_fullDivides (singularity : Torus.Basic.PowerSingularity)
    {steps : Nat} (fullDivides : singularity.p ∣ singularity.q * steps) :
    singularity.componentOrbitLength ∣
      steps * (singularity.q / singularity.componentCount) := by
  let divisor := singularity.componentCount
  let reducedP := singularity.p / divisor
  let reducedQ := singularity.q / divisor
  have pFactor : reducedP * divisor = singularity.p :=
    Nat.Division.div_mul_cancel singularity.componentCount_dvd_p
  have qFactor : reducedQ * divisor = singularity.q :=
    Nat.Division.div_mul_cancel singularity.componentCount_dvd_q
  obtain ⟨factor, factorization⟩ := fullDivides
  refine ⟨factor, ?_⟩
  change steps * reducedQ = reducedP * factor
  have scaled : (steps * reducedQ) * divisor = (reducedP * factor) * divisor := by
    calc
      (steps * reducedQ) * divisor =
          (reducedQ * divisor) * steps := by ring1
      _ = singularity.q * steps := by rw [qFactor]
      _ = singularity.p * factor := factorization
      _ = (reducedP * divisor) * factor := by rw [pFactor]
      _ = (reducedP * factor) * divisor := by ring1
  have divided := congrArg (fun value => value / divisor) scaled
  rw [Nat.mul_comm (steps * reducedQ) divisor, Nat.mul_comm (reducedP * factor) divisor,
    Nat.Division.mul_div_cancel_left _ singularity.componentCount_positive,
    Nat.Division.mul_div_cancel_left _ singularity.componentCount_positive] at divided
  exact divided

open Purelib.Topology.Knot.Torus.Basic in
/-- No strand returns before the positive computed component orbit length.

The step count is required to be positive and strictly below that length. -/
theorem closure_no_early_return_before_componentOrbitLength
    (singularity : Torus.Basic.PowerSingularity) (index : Fin singularity.p)
    (steps : Nat) (stepsPositive : 0 < steps)
    (stepsSmall : steps < singularity.componentOrbitLength) :
    Data.Fin.Bijection.iterateForward
      singularity.closure.permutation steps index ≠ index := by
  intro returned
  have fullDivides := PowerSingularity.return_dvd_p
    singularity steps index returned
  have reducedDivides := singularity.reducedDivides_of_fullDivides fullDivides
  let coprime := Coprime.quotientCoprimeCertificate
    singularity.p singularity.qPositive
  have dividesSteps : singularity.componentOrbitLength ∣ steps := by
    rw [PowerSingularity.componentOrbitLength, PowerSingularity.componentCount, Scalar.gcd_eq_compute]
    exact coprime.dvd_of_dvd_mul_right (by
      simpa only [-eq_self, -iff_self, PowerSingularity.componentOrbitLength, PowerSingularity.componentCount,
        Scalar.gcd_eq_compute]
        using reducedDivides)
  obtain ⟨factor, factorization⟩ := dividesSteps
  have factorPositive : 0 < factor := by
    by_cases zero : factor = 0
    · subst factor
      simp only [-eq_self, -iff_self, Nat.mul_zero] at factorization
      exact (Nat.ne_of_gt stepsPositive factorization).elim
    · exact Nat.pos_of_ne_zero zero
  have orbitLengthAtMostSteps : singularity.componentOrbitLength ≤ steps := by
    calc
      singularity.componentOrbitLength ≤
          singularity.componentOrbitLength * factor :=
        Nat.le_mul_of_pos_right singularity.componentOrbitLength factorPositive
      _ = steps := factorization.symm
  exact Nat.not_lt_of_ge orbitLengthAtMostSteps stepsSmall

/-- Construct exact uniform-component evidence for the finite torus closure.

The component count is the computed gcd, the common orbit length is p divided by that gcd, and the certificate retains
both return and no-early-return proofs. -/
@[expose] def componentCertificate (singularity : Torus.Basic.PowerSingularity) :
    Closure.Components.UniformComponentCertificate
      singularity.closure where
  componentCount := singularity.componentCount
  orbitLength := singularity.componentOrbitLength
  count_mul_orbitLength := singularity.componentCount_mul_orbitLength
  return_at_orbitLength :=
    singularity.closure_return_at_componentOrbitLength
  no_early_return :=
    singularity.closure_no_early_return_before_componentOrbitLength

/-- The certificate component count equals the gcd returned by the retained Euclidean computation. -/
@[simp] theorem componentCertificate_count (singularity : Torus.Basic.PowerSingularity) :
    singularity.componentCertificate.componentCount =
      (Extended.compute singularity.p singularity.q).gcd :=
  Scalar.gcd_eq_compute singularity.p singularity.q

/-- The certificate orbit length is p divided by the gcd returned by Euclidean computation. -/
@[simp] theorem componentCertificate_orbitLength
    (singularity : Torus.Basic.PowerSingularity) :
    singularity.componentCertificate.orbitLength =
      singularity.p /
        (Extended.compute singularity.p singularity.q).gcd := by
  change singularity.p / Scalar.gcd singularity.p singularity.q = _
  rw [Scalar.gcd_eq_compute]

end Purelib.Topology.Knot.Torus.Basic.PowerSingularity

end
