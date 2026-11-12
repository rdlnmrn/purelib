module

public import Purelib.Polynomial.Dense.Roots.Tower
public import Purelib.Polynomial.Dense.Companion.Reading.Scalar

/-!
# Original scalar leading coefficients throughout a retained root tower

Every source is the same original normalized polynomial or cached synthetic
quotient. Its leading coefficient and actual companion inverse remain the
successive original scalar images of one Gaussian coefficient and its
Gaussian inverse. The recursive invariant is proof data on the existing
tower, with no replacement carrier, adjunction, scalar map or quotient.
-/

public section

namespace Purelib.Polynomial.Dense.Roots.Tower

open Basic (DensePolynomial)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Algebra.Monogenic
open Purelib.Algebra.Ring (Weight GaussianReading)

universe u

/-- The same original source and cached companion retain their Gaussian scalar leading data at every tower stage.

Each stage keeps its original normalization and scalar-map laws. The next
stage uses exactly the same cyclic scalar embedding as the retained
adjunction and the same cached original synthetic quotient.
-/
@[expose] def Leading {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
    {polynomial : DensePolynomial K} (tower : Tower K ring equality polynomial)
    (scalar : Canonical → K) (coefficient : Canonical) : Prop :=
  polynomial.normalize = polynomial ∧ polynomial.leadingCoeff = scalar coefficient ∧
    scalar 0 = 0 ∧ scalar 1 = 1 ∧
    (∀ left right, scalar (left * right) = scalar left * scalar right) ∧
    match tower with
    | .constant _ _ => True
    | .step adjunction _ remaining =>
        adjunction.companion.leadingInverse = scalar coefficient⁻¹ ∧
          Leading remaining (fun value => Cyclic.Element.scalar adjunction.table (scalar value)) coefficient

namespace Leading

variable {K : Type u} [ring : CommRing K] [equality : DecidableEq K] {polynomial : DensePolynomial K}
variable {tower : Tower K ring equality polynomial} {scalar : Canonical → K} {coefficient : Canonical}

/-- The same original stage source retains its exact normalization. -/
theorem normalized (leading : Leading tower scalar coefficient) : polynomial.normalize = polynomial := by
  cases tower <;> exact leading.1

/-- The same original stage leading coefficient is the embedded original Gaussian coefficient. -/
theorem coefficient_eq (leading : Leading tower scalar coefficient) :
    polynomial.leadingCoeff = scalar coefficient := by
  cases tower <;> exact leading.2.1

/-- The original current scalar map preserves zero. -/
theorem scalar_zero (leading : Leading tower scalar coefficient) : scalar 0 = 0 := by
  cases tower <;> exact leading.2.2.1

/-- The original current scalar map preserves one. -/
theorem scalar_one (leading : Leading tower scalar coefficient) : scalar 1 = 1 := by
  cases tower <;> exact leading.2.2.2.1

/-- The original current scalar map preserves its same Gaussian products. -/
theorem scalar_mul (leading : Leading tower scalar coefficient) (left right : Canonical) :
    scalar (left * right) = scalar left * scalar right := by
  cases tower <;> exact leading.2.2.2.2.1 left right

/-- Reading the same original nonzero Gaussian leading coefficient preserves the observed source degree.

Only exact readback of the original scalar coefficient is needed. Other
formal coefficients may have equal readings, and the reading need not
preserve their products.
-/
theorem observed_degree {weight : Weight K} (leading : Leading tower scalar coefficient)
    (reading : GaussianReading weight scalar) (nonzero : coefficient ≠ 0)
    (observed : DensePolynomial Canonical) (observedEq : observed = Map.map reading.read polynomial) :
    observed.natDegree = polynomial.natDegree := by
  have leadingRead : reading.read polynomial.leadingCoeff = coefficient :=
    (congrArg reading.read leading.coefficient_eq).trans (reading.read_scalar coefficient)
  have leadingNonzero : reading.read polynomial.leadingCoeff ≠ 0 := fun zero =>
    nonzero (leadingRead.symm.trans zero)
  exact (congrArg DensePolynomial.natDegree observedEq).trans
    (Map.map_natDegree_of_leading_nonzero reading.read reading.mapZero polynomial leadingNonzero)

/-- Establish every stage's original scalar leading readbacks from the same initial normalized source.

The existing quotient-leading and quotient-normalization theorems transport
those original data through each retained adjunction. The actual companion
inverse follows from its original unit equation at that same stage.
-/
theorem ofSource (tower : Tower K ring equality polynomial) (scalar : Canonical → K) (coefficient : Canonical)
    (normalized : polynomial.normalize = polynomial) (leading : polynomial.leadingCoeff = scalar coefficient)
    (scalarZero : scalar 0 = 0) (scalarOne : scalar 1 = 1)
    (scalarMul : ∀ left right, scalar (left * right) = scalar left * scalar right) :
    Leading tower scalar coefficient := by
  induction tower with
  | constant => exact ⟨normalized, leading, scalarZero, scalarOne, scalarMul, True.intro⟩
  | step adjunction decreases remaining previous =>
      refine ⟨normalized, leading, scalarZero, scalarOne, scalarMul, ?_⟩
      refine ⟨Companion.leadingInverse_scalar adjunction.companion coefficient scalarZero scalarOne scalarMul leading,
        ?_⟩
      exact previous (fun value => Cyclic.Element.scalar adjunction.table (scalar value))
        (adjunction.quotient_normalized normalized)
        ((adjunction.quotient_leadingCoeff normalized).trans
          (congrArg (Cyclic.Element.scalar adjunction.table) leading))
        ((congrArg (Cyclic.Element.scalar adjunction.table) scalarZero).trans (Cyclic.Element.scalar_zero _))
        ((congrArg (Cyclic.Element.scalar adjunction.table) scalarOne).trans (Cyclic.Element.scalar_one _))
        (fun left right => (congrArg (Cyclic.Element.scalar adjunction.table) (scalarMul left right)).trans
          (Cyclic.Element.scalar_mul _ _ _))

variable {adjunction : Companion.Adjunction polynomial}
variable {decreases : adjunction.division.quotient.natDegree + 1 = polynomial.natDegree}
variable {remaining : Tower (StageScalar adjunction) inferInstance inferInstance adjunction.division.quotient}

/-- The actual retained current companion inverse is the same embedded Gaussian inverse. -/
theorem inverse_eq (leading : Leading (.step adjunction decreases remaining) scalar coefficient) :
    adjunction.companion.leadingInverse = scalar coefficient⁻¹ := leading.2.2.2.2.2.1

/-- The same retained original quotient has the next original scalar-leading invariant. -/
theorem next (leading : Leading (.step adjunction decreases remaining) scalar coefficient) :
    Leading remaining (fun value => Cyclic.Element.scalar adjunction.table (scalar value)) coefficient :=
  leading.2.2.2.2.2.2

/-- Prepare the same original current companion's Gaussian reading from its retained leading invariant. -/
@[expose] def reading {weight : Weight K}
    (leading : Leading (.step adjunction decreases remaining) scalar coefficient)
    (parent : GaussianReading weight scalar) : Companion.Reading adjunction.companion parent.read coefficient⁻¹ :=
  Companion.Reading.ofGaussian adjunction.companion parent coefficient leading.scalar_zero leading.scalar_one
    leading.scalar_mul leading.coefficient_eq

/-- Prepare the same original current companion reading from its retained observed source cache. -/
@[expose] def readingObserved {weight : Weight K}
    (leading : Leading (.step adjunction decreases remaining) scalar coefficient)
    (parent : GaussianReading weight scalar) (observed : DensePolynomial Canonical)
    (observedEq : observed = Map.map parent.read polynomial) :
    Companion.Reading adjunction.companion parent.read coefficient⁻¹ :=
  Companion.Reading.ofGaussianObserved adjunction.companion parent coefficient observed observedEq
    leading.scalar_zero leading.scalar_one leading.scalar_mul leading.coefficient_eq

/-- A retained observed cache gives the complete same original current-stage reading as its convenience constructor. -/
theorem readingObserved_eq_reading {weight : Weight K}
    (leading : Leading (.step adjunction decreases remaining) scalar coefficient)
    (parent : GaussianReading weight scalar) (observed : DensePolynomial Canonical)
    (observedEq : observed = Map.map parent.read polynomial) :
    leading.readingObserved parent observed observedEq = leading.reading parent :=
  Companion.Reading.ofGaussianObserved_eq_ofGaussian adjunction.companion parent coefficient observed observedEq
    leading.scalar_zero leading.scalar_one leading.scalar_mul leading.coefficient_eq

end Leading

end Purelib.Polynomial.Dense.Roots.Tower

end
