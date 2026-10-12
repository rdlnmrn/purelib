module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Gaussian.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Ascending.Gaussian.Basic
import Purelib.Polynomial.Ascending.Gaussian.Integral
import Purelib.Polynomial.Ascending.Gaussian.Restriction.Basic
public import Purelib.Polynomial.Ascending.Gaussian.Restriction.Cached
import Purelib.Polynomial.Ascending.Gaussian.Restriction.Integral
public import Purelib.Integration.Program.Gaussian.Exact
public import Purelib.Integration.Program.Gaussian.Approximation
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field

@[expose] public section

/-!
# Finite integration transport regressions and a scope counterexample

The Gaussian quadratic exercises non-real coefficients and a non-dyadic
restriction.  The zero/one programs show why generic integration coherence
cannot imply agreement of unrelated sources.  Concrete arithmetic uses kernel
decision only; transport itself is obtained from the generic finite proof.
-/

namespace Purelib.Examples.Integration.Polynomial.Gaussian.Transport.WorkedExamples

open Purelib.Polynomial.Ascending.Gaussian (CoefficientPolynomial)
open Purelib.Polynomial.Ascending.Gaussian.Restriction (Cached)
open Purelib.Polynomial.Ascending.Gaussian

open Purelib.Approximation
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Integration
open Purelib.Polynomial
open Purelib.Examples

/-- The Gaussian quadratic with ascending coefficients 1+i, 2-i and 3i. -/
def quadratic :
  CoefficientPolynomial := ⟨[⟨1, 1⟩, ⟨2, -1⟩, ⟨0, 3⟩]⟩

/-- The displayed Gaussian quadratic has integral 2+3i/2 over [0,1]. -/
theorem quadratic_integral :
  Integral.definiteIntegral quadratic 0 1 =
  ⟨2, 3 / 2⟩ := by decide

/-- The retained affine restriction of the displayed quadratic to [1/3,2/3]. -/
def middle :
  Cached quadratic
  ⟨1 / 3, 0⟩ ⟨2 / 3, 0⟩ :=
  Cached.canonical
    quadratic ⟨1 / 3, 0⟩ ⟨2 / 3, 0⟩

/-- The cached normalized middle-interval integral is 2+23i/18. -/
theorem middle_sample :
  middle.sample = ⟨2, 23 / 18⟩ := by decide

/-- Multiplying the retained middle sample by its interval width gives the original definite integral. -/
theorem middle_integral :
    (⟨2 / 3, 0⟩ - ⟨1 / 3, 0⟩ : Gaussian.Basic.Canonical) *
      middle.sample =
      Integral.definiteIntegral quadratic ⟨1
        / 3, 0⟩ ⟨2 / 3, 0⟩ :=
  middle.transported_sample

/-- A cached degenerate interval needs no division by its zero width. -/
theorem degenerate_restriction
  (polynomial : CoefficientPolynomial) (point : Gaussian.Basic.Canonical) :
    (point - point) * (Cached.canonical polynomial point point).sample = 0 :=
      by
  rw [Gaussian.Basic.sub_self,
    Gaussian.Basic.zero_mul]

/-- Reversing the quadratic parameter preserves its definite integral over [0,1]. -/
theorem reverse_quadratic_integral :
    Integral.definiteIntegral (Ascending.Gaussian.Restriction.Basic.reverse
      quadratic) 0 1 = ⟨2, 3 / 2⟩ := by
  rw [Ascending.Gaussian.Restriction.Integral.definiteIntegral_reverse_parameter,
    quadratic_integral]

/-- Split at any displayed Gaussian parameter; no ordering or nonzero-width
premise is needed for this algebraic polynomial identity. -/
theorem cached_split (polynomial :
  CoefficientPolynomial) (start cut finish : Gaussian.Basic.Canonical)
    (left : Cached polynomial start cut) (right :
      Cached polynomial cut finish) :
    (cut - start) * left.sample + (finish - cut) * right.sample =
      Integral.definiteIntegral polynomial start finish :=
  left.split_samples right

/-- The exact zero-polynomial integration program on [0,1]. -/
def zeroProgram :
  Program.Gaussian.Basic.RefinementProgram :=
  .exactPolynomial 0 1 (Ascending.Gaussian.Basic.constant 0)

/-- The exact constant-one integration program on [0,1]. -/
def oneProgram :
  Program.Gaussian.Basic.RefinementProgram :=
  .exactPolynomial 0 1 (Ascending.Gaussian.Basic.constant 1)

/-- Every retained zero-program approximation sample is zero. -/
theorem zeroProgram_sample (index :
  Nat) : zeroProgram.approximation.sample index = 0 := by
  change zeroProgram.approximation.sample 0 = 0
  decide

/-- Every retained constant-one program approximation sample is one. -/
theorem oneProgram_sample (index : Nat)
  : oneProgram.approximation.sample index = 1 := by
  change oneProgram.approximation.sample 0 = 1
  decide

/-- Two fully coherent, zero-allowance integration programs need not agree.
The contradiction is the negative result itself, not a proof of positive data. -/
theorem exact_zero_one_not_equivalent
    (agreement : Gaussian.Equivalence.Equivalent
      zeroProgram.approximation
        oneProgram.approximation) : False := by
  let comparison := agreement.compare 0 0 1 (by decide)
  have close := comparison.close (Nat.le_refl comparison.leftIndex)
    (Nat.le_refl comparison.rightIndex)
  rw [zeroProgram_sample,
    oneProgram_sample] at close
  exact (show ¬Gaussian.Norm.Basic.normSq (0 - 1) < (1 : Fraction.Rational)
    from by decide) close

end Purelib.Examples.Integration.Polynomial.Gaussian.Transport.WorkedExamples

end
