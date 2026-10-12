module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Reverse
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Basic
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.EvaluationLower

import Purelib.LinearAlgebra.Matrix.Inverse.PivotedScaledInverse
public import Purelib.Riemann.Readings.PreparedObservationPoints
public import Purelib.LinearAlgebra.Matrix.Inverse.ExactPivotInverse
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Finite interpolation on automatically clear observations

The fixed observation bank separates every standard differential numerator.
Its monomial evaluation matrix therefore has trivial left kernel, so the
selected-pivot finite inverse algorithm has nonzero scalar.  The
matrix and scaled inverse are cached together with their defining equations;
no interpolation or inverse-separation certificate is required from a curve's
caller.
-/

namespace Purelib.Riemann.Readings.PreparedObservationInterpolation

open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.LinearAlgebra
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.Readings.PreparedObservationPoints (Gaussian GaussianPolynomial)
open Purelib.Riemann.Readings.PreparedObservationPoints (ObservationBank)

/-- Appending one coefficient adds its final Horner step after the retained coefficient list. -/
private theorem horner_append_singleton (point last : Gaussian) :
    forall (coefficients : List Gaussian) (initial : Gaussian),
    (coefficients ++ [last]).foldl (fun value coefficient => value * point + coefficient) initial =
      coefficients.foldl (fun value coefficient => value * point + coefficient) initial * point + last
  | [], _ => rfl
  | coefficient :: coefficients, initial =>
      horner_append_singleton point last coefficients (initial * point + coefficient)

open Purelib.Polynomial in
/-- Appending a coefficient multiplies the previous polynomial evaluation by the point and adds that coefficient. -/
private theorem evalCoeffs_append_singleton (point : Gaussian)
    (coefficients : List Gaussian) (last : Gaussian) :
    Dense.Basic.DensePolynomial.evalCoeffs point (coefficients ++ [last]) =
      Dense.Basic.DensePolynomial.evalCoeffs point coefficients * point + last :=
  horner_append_singleton point last coefficients 0

open Purelib.Algebra in
open Purelib.Data in
open Purelib.Polynomial in
/-- The reversed finite coefficient list evaluates as the low-to-high monomial sum.

The reversal identifies the standard numerator basis ordering with the dense polynomial's Horner convention. -/
theorem eval_reverse_ofFn {count : Nat}
    (coefficients : Fin count -> Gaussian) (point : Gaussian) :
    Dense.Basic.DensePolynomial.evalCoeffs point (List.ofFn coefficients).reverse =
      FiniteSum.Fin.sumFin (fun row => coefficients row * point ^ row.val) := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [List.OfFn.Basic.ofFn_succ, List.Reverse.reverse_cons,
        evalCoeffs_append_singleton, inductionHypothesis, FiniteSum.Fin.sumFin_succ]
      change FiniteSum.Fin.sumFin (fun row : Fin count => coefficients row.succ * point ^ row.val) * point +
          coefficients 0 = coefficients 0 * point ^ 0 +
            FiniteSum.Fin.sumFin (fun row : Fin count => coefficients row.succ * point ^ (row.val + 1))
      rw [pow_zero, Gaussian.Basic.mul_one]
      have tailExpansion := FiniteSum.Fin.sumFin_congr
        (left := fun row : Fin count => coefficients row.succ * point ^ (row.val + 1))
        (right := fun row : Fin count => (coefficients row.succ * point ^ row.val) * point)
        (fun row => by rw [pow_succ]; ring1)
      rw [tailExpansion, FiniteSum.Fin.sumFin_mul_right]
      ring1

namespace ObservationBank

variable {polynomial : GaussianPolynomial} {count : Nat}

/-- The monomial evaluation matrix at the exact retained observation points. -/
def evaluationMatrix (bank : ObservationBank polynomial count) : Matrix Gaussian count :=
  Matrix.matrixOfFn fun row column => bank.pointAt column ^ row.val

open Purelib.Riemann in
/-- An evaluation-matrix entry is its retained observation raised to the row index. -/
@[simp] theorem evaluationMatrix_apply (bank : ObservationBank polynomial count)
    (row column : Fin count) :
    (Readings.PreparedObservationInterpolation.ObservationBank.evaluationMatrix bank) row column = bank.pointAt column ^
      row.val :=
  Matrix.matrixOfFn_apply _ _ _

open Purelib.Algebra in
open Purelib.Riemann in
open Purelib.Polynomial in
/-- Multiplying the coefficient vector by the retained matrix computes its actual dense polynomial evaluations. -/
theorem vectorMatrix_evaluationMatrix (bank : ObservationBank polynomial count)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector count)
    (column : Fin count) :
    Matrix.Multiplication.vectorMatrix coefficients
      (Readings.PreparedObservationInterpolation.ObservationBank.evaluationMatrix bank) column =
      (Geometry.EvaluationLower.coefficientPolynomial coefficients).eval
        (bank.pointAt column) := by
  rw [Matrix.Multiplication.vectorMatrix_apply]
  calc
    _ = FiniteSum.Fin.sumFin (fun row => coefficients row * bank.pointAt column ^ row.val) :=
      FiniteSum.Fin.sumFin_congr (fun row =>
        congrArg (fun value => coefficients row * value)
          ((Readings.PreparedObservationInterpolation.ObservationBank.evaluationMatrix_apply bank) row column))
    _ = _ := (eval_reverse_ofFn coefficients (bank.pointAt column)).symm

open Purelib.Riemann
/-- A certified distinct observation bank has an evaluation matrix with trivial left kernel.

Its retained finite root bound separates every coefficient vector through the exact observation readbacks. -/
theorem evaluationMatrix_leftKernelTrivial (bank : ObservationBank polynomial count) :
    Matrix.Inverse.PivotedScaledInverse.LeftKernelTrivial
      (Readings.PreparedObservationInterpolation.ObservationBank.evaluationMatrix bank) := by
  intro coefficients kernel
  apply bank.coefficients_zero_of_evaluations_zero coefficients
  intro point member
  rcases bank.exists_pointAt_of_mem member with ⟨column, rfl⟩
  rw [<- (Readings.PreparedObservationInterpolation.ObservationBank.vectorMatrix_evaluationMatrix bank) coefficients
    column]
  exact kernel column

/-- The complete finite scaled inverse of the retained observation matrix has nonzero scalar. -/
theorem evaluationMatrix_inverseScalar_nonzero (bank : ObservationBank polynomial count) :
    (Matrix.Inverse.PivotedScaledInverse.completeScaledInverse
      (Readings.PreparedObservationInterpolation.ObservationBank.evaluationMatrix bank)).scalar ≠ 0 :=
  Matrix.Inverse.PivotedScaledInverse.completeScaledInverse_scalar_nonzero_of_leftKernelTrivial
    (Readings.PreparedObservationInterpolation.ObservationBank.evaluationMatrix bank)
      (Readings.PreparedObservationInterpolation.ObservationBank.evaluationMatrix_leftKernelTrivial bank)

end ObservationBank

open Purelib.Riemann in
set_option genInjectivity false in
/-- A cached observation bank, its exact evaluation matrix and a certified scaled inverse.

The two scaled-inverse identities and nonzero scalar certify reconstruction. The retained inverse may be supplied by any
executable construction satisfying those checks. -/
structure ObservationInterpolation (polynomial : GaussianPolynomial) (count : Nat) where
  /-- The retained distinct observation bank away from the original polynomial zeros. -/ bank : ObservationBank
    polynomial count
  /-- The cached monomial evaluation matrix. -/ matrix : Matrix Gaussian count
  /-- The matrix cache equals evaluation at the exact retained observation bank. -/ matrix_eq : matrix =
    (Readings.PreparedObservationInterpolation.ObservationBank.evaluationMatrix bank)
  /-- The retained scaled inverse with both matrix identities. -/ inverse :
    Matrix.Inverse.Scaled.Basic.ScaledInverse matrix
  /-- The retained inverse scalar is nonzero. -/ scalar_nonzero : inverse.scalar ≠ 0

constructive_injectivity ObservationInterpolation

namespace ObservationInterpolation

variable {polynomial : GaussianPolynomial} {count : Nat}

open Purelib.Riemann in
/-- Compute and cache a certified finite interpolation inverse from the retained observation bank. -/
def ofBank (bank : ObservationBank polynomial count) :
    ObservationInterpolation polynomial count :=
  let computed := Matrix.Inverse.ExactPivotInverse.invert
    (Readings.PreparedObservationInterpolation.ObservationBank.evaluationMatrix bank)
    (Readings.PreparedObservationInterpolation.ObservationBank.evaluationMatrix_leftKernelTrivial bank)
  { bank := bank
    matrix := (Readings.PreparedObservationInterpolation.ObservationBank.evaluationMatrix bank)
    matrix_eq := rfl
    inverse := computed.inverse
    scalar_nonzero := computed.scalar_nonzero }

open Purelib.Algebra in
open Purelib.Riemann in
open Purelib.Data in
open Purelib.Polynomial in
/-- Recover each coefficient times the retained inverse scalar from the exact observed polynomial values.

The reconstruction uses the cached evaluation matrix and right scaled-inverse identity with the original coefficient
polynomial. -/
theorem reconstruct (interpolation : ObservationInterpolation polynomial count)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector count) (row : Fin count) :
    FiniteSum.Fin.sumFin (fun column =>
      (Geometry.EvaluationLower.coefficientPolynomial coefficients).eval
          (interpolation.bank.pointAt column) * interpolation.inverse.inverse column row) =
      coefficients row * interpolation.inverse.scalar := by
  have identity := congrArg (fun matrix => Matrix.Multiplication.vectorMatrix coefficients matrix)
    interpolation.inverse.right_identity
  rw [Matrix.Multiplication.vectorMatrix_mul,
    Matrix.Multiplication.vectorMatrix_scaleIdentity] at identity
  have coordinate := congrArg
    (fun vector : Data.Vector Gaussian count => vector row) identity
  rw [Vector.Basic.vectorOfFn_apply, Matrix.Multiplication.vectorMatrix_apply] at coordinate
  calc
    _ = FiniteSum.Fin.sumFin (fun column =>
        Matrix.Multiplication.vectorMatrix coefficients interpolation.matrix column *
          interpolation.inverse.inverse column row) := by
      apply FiniteSum.Fin.sumFin_congr
      intro column
      have evaluation :=
        (congrArg (fun matrix => Matrix.Multiplication.vectorMatrix coefficients matrix column)
          interpolation.matrix_eq).trans
            ((Readings.PreparedObservationInterpolation.ObservationBank.vectorMatrix_evaluationMatrix
              interpolation.bank) coefficients column)
      exact congrArg (fun value => value * interpolation.inverse.inverse column row)
        evaluation.symm
    _ = _ := coordinate

end ObservationInterpolation

open Purelib.Riemann in
open Purelib.Curves in
/-- Construct cached interpolation data on the admissible curve's fixed observation bank.

The data are independent of a later coefficient-vector request and retain the curve's exact polynomial and genus. -/
def curveObservationInterpolation {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) :
    ObservationInterpolation curve.polynomial genus :=
  ObservationInterpolation.ofBank (Readings.PreparedObservationPoints.curveObservations curve)

end Purelib.Riemann.Readings.PreparedObservationInterpolation
