module

public import Purelib.Polynomial.Dense.Map.Ring
public import Purelib.Data.Gaussian.Conjugate.Arithmetic
public import Purelib.Polynomial.Dense.ZeroMultiplicity
import Purelib.Polynomial.Dense.Gaussian.Extensionality
import Purelib.Data.Gaussian.Power

/-!
# Coefficient conjugation of original Gaussian polynomials

The original coefficient map conjugates the same descending table. Its
Horner evaluation, exact normalized degree and original zero-root count
are retained without a second polynomial representation or evaluator.
-/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Conjugate

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Polynomial.Dense.Basic (DensePolynomial)

/-- Conjugate the same original descending coefficient table with the original coefficient mapper. -/
abbrev polynomial (source : DensePolynomial Canonical) := Map.map Canonical.conj source

/-- Coefficient conjugation evaluates as the conjugate original value at the conjugated point. -/
theorem eval (source : DensePolynomial Canonical) (point : Canonical) :
    (polynomial source).eval point = Canonical.conj (source.eval (Canonical.conj point)) := by
  have mapped := Map.map_eval Canonical.conj rfl Canonical.conj_add Canonical.conj_mul source (Canonical.conj point)
  rewrite [Canonical.conj_conj] at mapped
  exact mapped.symm

/-- Conjugating an original normalized table retains that same normalization. -/
theorem normalized (source : DensePolynomial Canonical) (retained : source.normalize = source) :
    (polynomial source).normalize = polynomial source :=
  (Map.map_normalize Canonical.conj rfl Canonical.conj_injective source).symm.trans
    (congrArg (Map.map Canonical.conj) retained)

/-- The original exact nonzero test is preserved by coefficient conjugation. -/
theorem nonzero (source : DensePolynomial Canonical) (retained : source.isZero = false) :
    (polynomial source).isZero = false :=
  (Map.map_isZero Canonical.conj rfl Canonical.conj_injective source).trans retained

/-- Coefficient conjugation retains the original normalized natural degree. -/
theorem natDegree (source : DensePolynomial Canonical) : (polynomial source).natDegree = source.natDegree :=
  Map.map_natDegree Canonical.conj rfl Canonical.conj_injective source

/-- The original zero-root multiplicity is preserved by coefficient conjugation. -/
theorem zeroMultiplicity (source : DensePolynomial Canonical) (retained : source.normalize = source)
    (notZero : source.isZero = false) : (polynomial source).zeroMultiplicity = source.zeroMultiplicity := by
  have identity : polynomial source = DensePolynomial.shift source.zeroMultiplicity (polynomial source.zeroCore) := by
    apply Extensionality.gaussian_normalized_eq_of_eval_eq (normalized source retained)
      (DensePolynomial.normalize_shift _ _)
    intro point
    rewrite [eval, DensePolynomial.eval_zeroCore_mul_power, Canonical.conj_mul]
    have power := Power.conj_pow (Canonical.conj point) source.zeroMultiplicity
    change Canonical.conj ((Canonical.conj point) ^ source.zeroMultiplicity) =
      (Canonical.conj (Canonical.conj point)) ^ source.zeroMultiplicity at power
    rewrite [Canonical.conj_conj] at power
    rewrite [power, DensePolynomial.eval_shift, eval]
    rfl
  have originalCore := DensePolynomial.zeroCore_eval_zero_nonzero notZero
  have coreAtZero : (polynomial source.zeroCore).eval 0 ≠ 0 := by
    rewrite [eval]
    exact Canonical.conj_ne_zero originalCore
  rewrite [identity, DensePolynomial.zeroMultiplicity_shift _
    (nonzero source.zeroCore (DensePolynomial.zeroCore_nonzero notZero)),
    DensePolynomial.zeroMultiplicity_eq_zero_of_eval_zero_nonzero _ coreAtZero]
  exact Nat.zero_add _

end Purelib.Polynomial.Dense.Gaussian.Conjugate

end
