module
import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Arithmetic.Distributive
public import Purelib.Approximation.Gaussian.Arithmetic.Exact
public import Purelib.Approximation.Gaussian.Arithmetic.Mul
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Process.Multiplication
public import Purelib.Data.Gaussian.Natural
import Purelib.Data.Gaussian.Norm.Basic

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Enclosure.Ball.Mul
import Purelib.Approximation.Gaussian.Process.Coherence.Addition
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Multiplication
import Purelib.Approximation.Gaussian.Request.Basic
import Purelib.Approximation.Gaussian.Request.Multiplication
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

namespace Purelib.Approximation.Gaussian.Name.Coherent.Power

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Arithmetic
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian
open Purelib.Data.Gaussian

section
public section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

/-- Finite repeated CCL addition. -/
@[expose] def natSum (value : CoherentNamed) : Nat → CoherentNamed
  | 0 => Coherence.exact 0
  | count + 1 =>
      CoherentNamed.add value
        (Power.natSum value count)

/-- Finite repeated CCL multiplication. -/
@[expose] def natPower (value : CoherentNamed) : Nat → CoherentNamed
  | 0 => Coherence.exact 1
  | count + 1 =>
      CoherentNamed.mul value
        (Power.natPower value count)

/-- Multiply the original coherent name by the displayed exact Gaussian coefficient on the left. -/
@[expose] def scale (coefficient : Basic.Canonical) (value : CoherentNamed) :
  CoherentNamed :=
  CoherentNamed.mul
    (Coherence.exact coefficient)
    value

/-- Repeated addition of a scaled CCL name is operationally one multiplication by the displayed repeated coefficient. -/
@[expose] def natSum_scale (coefficient : Basic.Canonical) (value :
  CoherentNamed) :
    (count : Nat) →
      NamedEquivalent
        (natSum (scale coefficient
          value) count).name
        (scale (Natural.repeatedCoefficient coefficient count) value).name
  | 0 =>
      NamedEquivalent.symm
        (by
          simpa only [natSum,
            scale, Natural.repeatedCoefficient,
            Coherence.exact,
            CoherentNamed.mul] using
            Mul.coherentMul_zero_left value)
  | count + 1 => by
      let exactCoefficient :=
        Coherence.exact coefficient
      let previousCoefficient := Natural.repeatedCoefficient coefficient count
      let exactPrevious :=
        Coherence.exact
          previousCoefficient
      let combinedCoefficient := coefficient + previousCoefficient
      let exactCombined :=
        Coherence.exact
          combinedCoefficient
      let scaledCurrent := scale coefficient value
      let scaledPrevious := scale previousCoefficient value
      let repeatedPrevious := natSum scaledCurrent count
      have replacePrevious : NamedEquivalent
          (Named.add
            scaledCurrent.name repeatedPrevious.name)
          (Named.add
            scaledCurrent.name scaledPrevious.name) :=
        Congruence.coherentAdd_respects scaledCurrent scaledCurrent
          repeatedPrevious scaledPrevious
          (NamedEquivalent.refl
            scaledCurrent.name)
          (Power.natSum_scale coefficient value count)
      have collectProducts : NamedEquivalent
          (Named.add
            scaledCurrent.name scaledPrevious.name)
          (Named.mul
            (Named.add
              exactCoefficient.name exactPrevious.name)
            value.name) :=
        NamedEquivalent.symm
          (Distributive.coherentAdd_mul_right exactCoefficient exactPrevious value)
      have exactCoefficientSum : NamedEquivalent
          (Named.add
            exactCoefficient.name exactPrevious.name)
          exactCombined.name := by
        simpa only [exactCoefficient, exactPrevious, exactCombined,
          combinedCoefficient,
          Coherence.exact] using
          Exact.exactAdd_named_equivalent
            coefficient previousCoefficient
      have replaceCoefficient : NamedEquivalent
          (Named.mul
            (Named.add
              exactCoefficient.name exactPrevious.name)
            value.name)
          (Named.mul
            exactCombined.name value.name) :=
        Congruence.coherentMul_respects
          (CoherentNamed.add
            exactCoefficient exactPrevious)
          exactCombined value value exactCoefficientSum
          (NamedEquivalent.refl
            value.name)
      exact NamedEquivalent.trans
        (by simpa only [natSum, scaledCurrent, repeatedPrevious,
          CoherentNamed.add] using
          replacePrevious)
        (NamedEquivalent.trans
          collectProducts
          (by
            simpa only [scale, Natural.repeatedCoefficient,
              combinedCoefficient,
              exactCombined,
              CoherentNamed.mul,
              Coherence.exact] using
              replaceCoefficient))

end

public section

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

/-- Finite repeated power in the operational CCL arithmetic. -/
@[expose] def namedPower (value : CoherentNamed) : Nat -> CoherentNamed
  | 0 => Coherence.exact 1
  | exponent + 1 => CoherentNamed.mul
      (Power.namedPower value exponent) value

/-- A first finite power is operationally the original coherent channel. -/
@[expose] def namedPower_one (value : CoherentNamed) :
    NamedEquivalent (namedPower value 1).name value.name := Mul.coherentMul_one_left value

/-- Finite powers respect comparisons of their original coherent input channels. -/
@[expose] def namedPower_respects (left right : CoherentNamed)
    (equivalent : NamedEquivalent left.name right.name) :
    (exponent : Nat) → NamedEquivalent (namedPower left exponent).name (namedPower right exponent).name
  | 0 => NamedEquivalent.refl _
  | exponent + 1 => Congruence.coherentMul_respects
      (namedPower left exponent) (namedPower right exponent) left right
      (namedPower_respects left right equivalent exponent) equivalent

/-- Addition of finite exponents is multiplication of the retained finite power channels. -/
@[expose] def namedPower_add (value : CoherentNamed) (first : Nat) :
    (second : Nat) → NamedEquivalent (namedPower value (first + second)).name
      (CoherentNamed.mul (namedPower value first) (namedPower value second)).name
  | 0 => NamedEquivalent.symm (Mul.coherentMul_one_right (namedPower value first))
  | second + 1 => NamedEquivalent.trans
      (Congruence.coherentMul_respects (namedPower value (first + second))
        (CoherentNamed.mul (namedPower value first) (namedPower value second)) value value
        (namedPower_add value first second) (NamedEquivalent.refl value.name))
      (Laws.coherentMul_assoc (namedPower value first) (namedPower value second) value)

/-- An exact Gaussian name's finite power has the corresponding squared-norm power as center bound.

The original zero power retains the exact unit name. Each successor uses the
same operational multiplication and its original product of center bounds. -/
@[simp] theorem namedPower_exact_centerBound (point : Basic.Canonical)
    (exponent : Nat) :
    (namedPower (Coherence.exact point)
      exponent).name.process.centerBound =
        Norm.Basic.normSq point ^ exponent := by
  induction exponent with
  | zero =>
      change Norm.Basic.normSq (1 : Basic.Canonical) =
        Norm.Basic.normSq point ^ 0
      rw [pow_zero, Norm.Basic.normSq_one]
  | succ exponent inductionHypothesis =>
      simp only [namedPower,
        CoherentNamed.mul,
        Named.mul,
        Process.mul, pow_succ]
      rw [inductionHypothesis]
      rfl

/-- Every possible finite reading of an exact rational power is that exact power; multiplication introduces no semantic
branch. -/
theorem namedPower_exact_possible_eq (point : Basic.Canonical) (exponent : Nat)
    (state : (namedPower
      (Coherence.exact point)
        exponent).name.process.State)
    {candidate : Basic.Canonical}
    (possible : (namedPower
      (Coherence.exact point)
        exponent).name.process.Possible state candidate) :
    candidate = point ^ exponent := by
  induction exponent generalizing candidate with
  | zero =>
      change candidate = 1 at possible
      simpa only [pow_zero] using possible
  | succ exponent inductionHypothesis =>
      rcases possible with ⟨left, right, leftPossible, rightPossible, rfl⟩
      have leftEqual := inductionHypothesis state.1 leftPossible
      change right = point at rightPossible
      rw [leftEqual, rightPossible, pow_succ]

end

end

end Purelib.Approximation.Gaussian.Name.Coherent.Power
