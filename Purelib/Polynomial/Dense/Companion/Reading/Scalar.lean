module

public import Purelib.Polynomial.Dense.Companion.Reading
public import Purelib.Algebra.Ring.GaussianReading
public import Purelib.Data.Gaussian.Field
import Purelib.Algebra.FiniteSum.Fin
import Purelib.LinearAlgebra.Matrix.Rectangular

/-!
# Original Gaussian scalars and retained companion inverses

A polynomial's actual leading coefficient is the retained image of an
original Gaussian scalar. Its original companion's unit equation identifies
the cached inverse with the image of that scalar's Gaussian inverse, even
when the target coefficient algebra has zero divisors. An additive Gaussian
reading then supplies the exact scalar action needed by the original
companion-reading constructor.
-/

public section

namespace Purelib.Polynomial.Dense.Companion

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Algebra.Ring (Weight GaussianReading)
open Basic (DensePolynomial)
open Purelib.Algebra.FiniteSum.Fin
open Purelib.LinearAlgebra.Matrix

variable {K : Type*} [CommRing K] [DecidableEq K] {polynomial : DensePolynomial K}
variable {scalar : Canonical → K}

/-- The original cached companion inverse is the same embedded Gaussian leading inverse.

Only the original leading-unit equation and the original scalar map's zero,
unit and product laws are required. Uniqueness is proved by multiplying the
two explicit unit equations, without a field or cancellation premise on the
target coefficient algebra.
-/
theorem leadingInverse_scalar (original : Companion polynomial) (coefficient : Canonical)
    (scalarZero : scalar 0 = 0) (scalarOne : scalar 1 = 1)
    (scalarMul : ∀ left right, scalar (left * right) = scalar left * scalar right)
    (leading : polynomial.leadingCoeff = scalar coefficient) :
    original.leadingInverse = scalar coefficient⁻¹ := by
  have nonzero : coefficient ≠ 0 := by
    intro zero
    exact original.leading_nonzero (leading.trans ((congrArg scalar zero).trans scalarZero))
  have embeddedUnit : polynomial.leadingCoeff * scalar coefficient⁻¹ = 1 := by
    rewrite [leading, ← scalarMul, Canonical.mul_inv_cancel coefficient nonzero]
    exact scalarOne
  exact original.leadingInverse_of_unit _ embeddedUnit

namespace Reading

/-- The same Gaussian reading reads the actual original cached leading inverse as its Gaussian inverse. -/
theorem read_leadingInverse {weight : Weight K} (original : Companion polynomial)
    (reading : GaussianReading weight scalar) (coefficient : Canonical)
    (scalarZero : scalar 0 = 0) (scalarOne : scalar 1 = 1)
    (scalarMul : ∀ left right, scalar (left * right) = scalar left * scalar right)
    (leading : polynomial.leadingCoeff = scalar coefficient) :
    reading.read original.leadingInverse = coefficient⁻¹ :=
  (congrArg reading.read (leadingInverse_scalar original coefficient scalarZero scalarOne scalarMul leading)).trans
    (reading.read_scalar coefficient⁻¹)

/-- Exact original Gaussian scalar action preserves multiplication by the actual cached companion inverse. -/
theorem scale_leadingInverse {weight : Weight K} (original : Companion polynomial)
    (reading : GaussianReading weight scalar) (coefficient : Canonical)
    (scalarZero : scalar 0 = 0) (scalarOne : scalar 1 = 1)
    (scalarMul : ∀ left right, scalar (left * right) = scalar left * scalar right)
    (leading : polynomial.leadingCoeff = scalar coefficient) (value : K) :
    reading.read (value * original.leadingInverse) = reading.read value * coefficient⁻¹ := by
  rewrite [leadingInverse_scalar original coefficient scalarZero scalarOne scalarMul leading,
    mul_comm value (scalar coefficient⁻¹)]
  exact (reading.mapScalarMul coefficient⁻¹ value).trans (mul_comm _ _)

/-- Prepare the original companion reading from the same Gaussian reading and original scalar leading coefficient.

The Gaussian inverse is computed once. Exact original scalar action supplies
the required multiplication by the actual retained companion inverse; no
inverse image, multiplicative reading or final matrix identity is supplied
by the caller. The original `Reading.prepare` builds the observed table and
target companion once.
-/
@[expose] def ofGaussian {weight : Weight K} (original : Companion polynomial)
    (reading : GaussianReading weight scalar) (coefficient : Canonical)
    (scalarZero : scalar 0 = 0) (scalarOne : scalar 1 = 1)
    (scalarMul : ∀ left right, scalar (left * right) = scalar left * scalar right)
    (leading : polynomial.leadingCoeff = scalar coefficient) :
    Reading original reading.read coefficient⁻¹ :=
  let inverse := coefficient⁻¹
  prepare original reading.read inverse reading.mapZero reading.mapOne reading.mapNeg
    (scale_leadingInverse original reading coefficient scalarZero scalarOne scalarMul leading)

/-- Prepare the same original Gaussian companion from its already retained observed source table.

The original scalar-leading invariant derives the inverse and scalar action.
The shared original `Reading.ofObserved` consumes the exact supplied table,
without mapping the original formal coefficient payloads again.
-/
@[expose] def ofGaussianObserved {weight : Weight K} (original : Companion polynomial)
    (reading : GaussianReading weight scalar) (coefficient : Canonical)
    (observed : DensePolynomial Canonical) (observedEq : observed = Map.map reading.read polynomial)
    (scalarZero : scalar 0 = 0) (scalarOne : scalar 1 = 1)
    (scalarMul : ∀ left right, scalar (left * right) = scalar left * scalar right)
    (leading : polynomial.leadingCoeff = scalar coefficient) :
    Reading original reading.read coefficient⁻¹ :=
  let inverse := coefficient⁻¹
  ofObserved original reading.read inverse observed observedEq reading.mapZero reading.mapOne reading.mapNeg
    (scale_leadingInverse original reading coefficient scalarZero scalarOne scalarMul leading)

/-- Both Gaussian scalar-leading construction paths retain the same complete original companion reading. -/
theorem ofGaussianObserved_eq_ofGaussian {weight : Weight K} (original : Companion polynomial)
    (reading : GaussianReading weight scalar) (coefficient : Canonical)
    (observed : DensePolynomial Canonical) (observedEq : observed = Map.map reading.read polynomial)
    (scalarZero : scalar 0 = 0) (scalarOne : scalar 1 = 1)
    (scalarMul : ∀ left right, scalar (left * right) = scalar left * scalar right)
    (leading : polynomial.leadingCoeff = scalar coefficient) :
    ofGaussianObserved original reading coefficient observed observedEq scalarZero scalarOne scalarMul leading =
      ofGaussian original reading coefficient scalarZero scalarOne scalarMul leading := by
  cases observedEq
  rfl

/-- The same original transposed companion columns retain the source residual bound without unfolding matrix data.

Pointwise transpose readback transports the original finite row sum. The
same retained observed polynomial and inverse image supply the existing
source-action estimate; no transposed matrix or new entry readings are
computed by this proof.
-/
theorem transpose_action_error_normSq_le {function : K → Canonical} {inverseImage : Canonical}
    {original : Companion polynomial} (reading : Reading original function inverseImage)
    (point : Canonical) (column : Fin polynomial.natDegree) (epsilon : Purelib.Data.Rat.Fraction.Rational)
    (bound : Norm.Basic.normSq (reading.observed.eval point) ≤ epsilon) :
    Norm.Basic.normSq (sumFin (fun row : Fin polynomial.natDegree =>
      function ((Rectangular.transpose original.matrix) row column) * point ^ row.val) -
        point * point ^ column.val) ≤ epsilon * Norm.Basic.normSq inverseImage := by
  have entries : sumFin (fun row : Fin polynomial.natDegree =>
      function ((Rectangular.transpose original.matrix) row column) * point ^ row.val) =
      sumFin (fun row : Fin polynomial.natDegree => function (original.matrix column row) * point ^ row.val) := by
    apply sumFin_congr
    intro row
    exact congrArg (fun value => function value * point ^ row.val) (Rectangular.transpose_apply _ _ _)
  exact (congrArg (fun value => Norm.Basic.normSq (value - point * point ^ column.val)) entries).symm ▸
    (reading.source_action_error_normSq_le point column epsilon bound)

end Reading

end Purelib.Polynomial.Dense.Companion

end
