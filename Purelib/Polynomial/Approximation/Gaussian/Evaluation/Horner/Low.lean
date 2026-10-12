module
import Purelib.Data.List.Reverse
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
public import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic

/-!
# Ascending coefficient evaluation by coherent Horner evaluation

Reversing an ascending coefficient list feeds its original entries to the
coherent Horner evaluator. The coefficient readbacks retain that same program
and the supplied input name.
-/

public section

namespace Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner.Low

open Purelib.Approximation.Gaussian
open Purelib.Data
open Purelib.Polynomial
open Purelib.Data.List
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence (exact)

/-- Evaluate ascending Gaussian coefficients through coherent Horner evaluation.

The original finite reversal orders the supplied coefficients for the Horner
scan, with the exact zero name as its initial accumulator. -/
@[expose] def low (coefficients : List Gaussian.Basic.Canonical) (input : Name.Coherent.CoherentNamed) :
  Name.Coherent.CoherentNamed :=
  Approximation.Gaussian.Evaluation.Horner.horner input (exact 0) coefficients.reverse

/-- The empty ascending coefficient list evaluates to the exact zero name. -/
theorem low_nil (input : Name.Coherent.CoherentNamed) : low [] input = exact 0 := rfl

/-- Prepending a coefficient adds its exact name to the remaining polynomial value.

The argument multiplies the retained tail evaluation; reversal and the Horner
concatenation law preserve the same coefficient order and initial accumulator. -/
theorem low_cons (coefficient : Gaussian.Basic.Canonical) (remaining : List Gaussian.Basic.Canonical) (input :
  Name.Coherent.CoherentNamed) :
    low (coefficient :: remaining) input = Name.Coherent.CoherentNamed.add (Name.Coherent.CoherentNamed.mul (low
      remaining input) input) (exact coefficient) := by
  unfold low
  rw [Reverse.reverse_cons,
    Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner.horner_append]
  rfl

/-- Reversed dense coefficients recover coherent polynomial evaluation.

The two finite reversal scans recover the supplied coefficient table, with
its original input name and exact-zero Horner accumulator. -/
theorem low_coeffs (polynomial : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
  (input : Name.Coherent.CoherentNamed) :
    low polynomial.coeffs.reverse input = Approximation.Gaussian.Evaluation.Horner.polynomialEval polynomial input := by
  unfold low Approximation.Gaussian.Evaluation.Horner.polynomialEval
  rw [Reverse.reverse_reverse]

end Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner.Low
