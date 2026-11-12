module
public import Purelib.Polynomial.Dense.Map.Ring
public import Purelib.Algebra.Field.Embedding
import Purelib.Algebra.Field.ExplicitField
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Division.Basic
import Purelib.Polynomial.Dense.Division.CancelLead
public import Purelib.Polynomial.Dense.Multiplication

/-!
# Coefficient maps through retained field embeddings

The original scalar embedding visits every descending coefficient in order.
Its retained field-operation and injectivity certificates transport the same
finite long-division states, accumulators and completed outputs. Normalization
and ring arithmetic use the shared injective scalar-map laws.
-/

namespace Purelib.Polynomial.Dense.Map

open Purelib.Algebra.Field
open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense
open Purelib.Data

variable {K L : Type*}
  [ExplicitField K] [DecidableEq K]
  [ExplicitField L] [DecidableEq L]

/-- Coefficient mapping preserves the one-term quotient used in leading cancellation.

The original leading ratio maps by the retained division certificate. The exact same degree difference shifts that
retained single coefficient. -/
public theorem map_leadQuotient (embedding : Algebra.Field.Embedding K L)
    (left right : CoefficientPolynomial K) :
    map embedding.toFun (DensePolynomial.leadQuotient left right) =
      DensePolynomial.leadQuotient (map embedding.toFun left) (map embedding.toFun right) := by
  unfold DensePolynomial.leadQuotient
  rw [(map_shift embedding.toFun embedding.map_zero embedding.injective), (map_natDegree embedding.toFun
    embedding.map_zero embedding.injective), (map_natDegree embedding.toFun embedding.map_zero embedding.injective)]
  apply congrArg (DensePolynomial.shift (left.natDegree - right.natDegree))
  apply DensePolynomial.ext
  simp only [map_coeffs, List.map_cons, List.map_nil]
  rw [Embedding.map_div, (map_leadingCoeff embedding.toFun embedding.map_zero embedding.injective), (map_leadingCoeff
    embedding.toFun embedding.map_zero embedding.injective)]

/-- Coefficient mapping commutes with one exact leading-term cancellation.

Both original leading coefficients and their ratio map together. The same degree shift, scaled divisor and subtraction
state give the mapped cancellation output. -/
public theorem map_cancelLead (embedding : Algebra.Field.Embedding K L)
    (left right : CoefficientPolynomial K) :
    map embedding.toFun (DensePolynomial.cancelLead left right) =
      DensePolynomial.cancelLead (map embedding.toFun left) (map embedding.toFun right) := by
  unfold DensePolynomial.cancelLead
  rw [(map_sub embedding.toFun embedding.map_zero embedding.injective embedding.map_add embedding.map_neg), (map_shift
    embedding.toFun embedding.map_zero embedding.injective), (map_scale embedding.toFun embedding.map_zero
    embedding.injective embedding.map_mul), (map_natDegree embedding.toFun embedding.map_zero embedding.injective),
    (map_natDegree embedding.toFun embedding.map_zero embedding.injective),
    Embedding.map_div, (map_leadingCoeff embedding.toFun embedding.map_zero embedding.injective), (map_leadingCoeff
      embedding.toFun embedding.map_zero embedding.injective)]

/-- A coefficient embedding maps the quotient of a fixed-fuel division run to the quotient of the mapped run.

The initial quotient accumulator is mapped together with both inputs, preserving every stopping test. -/
public theorem map_divLoop_quotient (embedding : Algebra.Field.Embedding K L) :
    ∀ (fuel : Nat) (left right quotient : CoefficientPolynomial K),
      map embedding.toFun (DensePolynomial.divLoop fuel left right quotient).quotient =
        (DensePolynomial.divLoop fuel (map embedding.toFun left) (map embedding.toFun right)
          (map embedding.toFun quotient)).quotient
  | 0, _, _, _ => rfl
  | fuel + 1, left, right, quotient => by
      rw [DensePolynomial.divLoop_succ, DensePolynomial.divLoop_succ, (map_isZero embedding.toFun embedding.map_zero
        embedding.injective), (map_isZero embedding.toFun embedding.map_zero embedding.injective),
        (map_natDegree embedding.toFun embedding.map_zero embedding.injective), (map_natDegree embedding.toFun
          embedding.map_zero embedding.injective)]
      split
      · rfl
      · dsimp only
        rw [← map_cancelLead, ← map_leadQuotient, ← (map_add embedding.toFun embedding.map_zero embedding.injective
          embedding.map_add)]
        exact map_divLoop_quotient embedding fuel
          (DensePolynomial.cancelLead left right) right (quotient + DensePolynomial.leadQuotient left right)

/-- A coefficient embedding maps the remainder of a fixed-fuel division run to the mapped run remainder.

The original fuel, inputs and quotient accumulator determine the same stopping guard. Continuing branches map the same
cancelled dividend and completed recursive remainder. -/
public theorem map_divLoop_remainder (embedding : Algebra.Field.Embedding K L) :
    ∀ (fuel : Nat) (left right quotient : CoefficientPolynomial K),
      map embedding.toFun (DensePolynomial.divLoop fuel left right quotient).remainder =
        (DensePolynomial.divLoop fuel (map embedding.toFun left) (map embedding.toFun right)
          (map embedding.toFun quotient)).remainder
  | 0, _, _, _ => rfl
  | fuel + 1, left, right, quotient => by
      rw [DensePolynomial.divLoop_succ, DensePolynomial.divLoop_succ, (map_isZero embedding.toFun embedding.map_zero
        embedding.injective), (map_isZero embedding.toFun embedding.map_zero embedding.injective),
        (map_natDegree embedding.toFun embedding.map_zero embedding.injective), (map_natDegree embedding.toFun
          embedding.map_zero embedding.injective)]
      split
      · rfl
      · dsimp only
        rw [← map_cancelLead, ← map_leadQuotient, ← (map_add embedding.toFun embedding.map_zero embedding.injective
          embedding.map_add)]
        exact map_divLoop_remainder embedding fuel
          (DensePolynomial.cancelLead left right) right (quotient + DensePolynomial.leadQuotient left right)

/-- A coefficient embedding preserves the number of cancellations in a fixed-fuel division run.

The original stopping branch contributes zero steps. Every continuing branch adds one to the same completed
predecessor-fuel run after mapping its retained state. -/
public theorem map_divLoop_steps (embedding : Algebra.Field.Embedding K L) :
    ∀ (fuel : Nat) (left right quotient : CoefficientPolynomial K),
      (DensePolynomial.divLoop fuel left right quotient).steps =
        (DensePolynomial.divLoop fuel (map embedding.toFun left) (map embedding.toFun right)
          (map embedding.toFun quotient)).steps
  | 0, _, _, _ => rfl
  | fuel + 1, left, right, quotient => by
      rw [DensePolynomial.divLoop_succ, DensePolynomial.divLoop_succ, (map_isZero embedding.toFun embedding.map_zero
        embedding.injective), (map_isZero embedding.toFun embedding.map_zero embedding.injective),
        (map_natDegree embedding.toFun embedding.map_zero embedding.injective), (map_natDegree embedding.toFun
          embedding.map_zero embedding.injective)]
      split
      · rfl
      · dsimp only
        rw [← map_cancelLead, ← map_leadQuotient, ← (map_add embedding.toFun embedding.map_zero embedding.injective
          embedding.map_add)]
        exact congrArg (· + 1) (map_divLoop_steps embedding fuel
          (DensePolynomial.cancelLead left right) right (quotient + DensePolynomial.leadQuotient left right))

/-- Executable normalized division commutes with coefficient mapping on its quotient.

Normalized original inputs and the same coefficient-count fuel are retained. The completed mapped run returns the
embedding of the original quotient. -/
public theorem map_divMod_quotient (embedding : Algebra.Field.Embedding K L)
    (left right : CoefficientPolynomial K) :
    map embedding.toFun (DensePolynomial.divMod left right).quotient =
      (DensePolynomial.divMod (map embedding.toFun left) (map embedding.toFun right)).quotient := by
  unfold DensePolynomial.divMod
  rw [(map_degreeCount embedding.toFun embedding.map_zero embedding.injective), ← (map_normalize embedding.toFun
    embedding.map_zero embedding.injective), ← (map_normalize embedding.toFun embedding.map_zero embedding.injective),
    ← (map_zero_polynomial embedding.toFun)]
  exact map_divLoop_quotient embedding _ left.normalize right.normalize 0

/-- Executable normalized division commutes with coefficient mapping on its remainder.

Normalized original inputs and the same coefficient-count fuel are retained. The completed mapped run returns the
embedding of the original remainder. -/
public theorem map_divMod_remainder (embedding : Algebra.Field.Embedding K L)
    (left right : CoefficientPolynomial K) :
    map embedding.toFun (DensePolynomial.divMod left right).remainder =
      (DensePolynomial.divMod (map embedding.toFun left) (map embedding.toFun right)).remainder := by
  unfold DensePolynomial.divMod
  rw [(map_degreeCount embedding.toFun embedding.map_zero embedding.injective), ← (map_normalize embedding.toFun
    embedding.map_zero embedding.injective), ← (map_normalize embedding.toFun embedding.map_zero embedding.injective),
    ← (map_zero_polynomial embedding.toFun)]
  exact map_divLoop_remainder embedding _ left.normalize right.normalize 0

/-- Executable normalized division performs the same number of steps after a coefficient embedding.

Mapping preserves both original normalized states and their coefficient-count fuel. Each same cancellation decision
contributes to the retained step count. -/
public theorem map_divMod_steps (embedding : Algebra.Field.Embedding K L)
    (left right : CoefficientPolynomial K) :
    (DensePolynomial.divMod left right).steps =
      (DensePolynomial.divMod (map embedding.toFun left) (map embedding.toFun right)).steps := by
  unfold DensePolynomial.divMod
  rw [(map_degreeCount embedding.toFun embedding.map_zero embedding.injective), ← (map_normalize embedding.toFun
    embedding.map_zero embedding.injective), ← (map_normalize embedding.toFun embedding.map_zero embedding.injective),
    ← (map_zero_polynomial embedding.toFun)]
  exact map_divLoop_steps embedding _ left.normalize right.normalize 0

end Purelib.Polynomial.Dense.Map
