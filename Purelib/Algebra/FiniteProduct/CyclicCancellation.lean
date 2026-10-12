module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.FiniteProduct.List
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Algebra

section
public section

/-!
# Divine Proportions, Chapter 11 exercises

This module begins the reader problems following the Two-struts theorem.  All
normalizations are retained as finite polynomial equalities.  In particular,
Example 11.1 is checked by scaling the two quad triples by the displayed
factor `256`; no quadratic formula or selected root is used.
-/

namespace Purelib.Algebra.FiniteProduct.CyclicCancellation

variable {K : Type*} [ExplicitField K]

/-- Cancel a common nonzero product from cyclic entrywise product relations.

The two pointwise products have matching lengths, the next quadrances have the same product as the original quadrances,
and that retained product is nonzero. -/
theorem exercise_11_9_polygon
    (rSpreads pSpreads quadrances nextQuadrances : List K)
    (rLength : rSpreads.length = quadrances.length)
    (pLength : nextQuadrances.length = pSpreads.length)
    (spreadLaws :
      FiniteProduct.List.pointwiseScalarProduct rSpreads quadrances =
        FiniteProduct.List.pointwiseScalarProduct nextQuadrances pSpreads)
    (cyclicQuadrances :
      FiniteProduct.List.scalarProduct nextQuadrances =
        FiniteProduct.List.scalarProduct quadrances)
    (quadranceProductNonzero : FiniteProduct.List.scalarProduct quadrances ≠ 0) :
    FiniteProduct.List.scalarProduct rSpreads = FiniteProduct.List.scalarProduct pSpreads := by
  apply ExplicitField.eq_of_mul_eq_mul_right quadranceProductNonzero
  calc
    FiniteProduct.List.scalarProduct rSpreads * FiniteProduct.List.scalarProduct quadrances =
        FiniteProduct.List.scalarProduct
          (FiniteProduct.List.pointwiseScalarProduct rSpreads quadrances) :=
      (FiniteProduct.List.finiteScalarProduct_pointwise rSpreads quadrances rLength).symm
    _ = FiniteProduct.List.scalarProduct
        (FiniteProduct.List.pointwiseScalarProduct nextQuadrances pSpreads) := by
      rw [spreadLaws]
    _ = FiniteProduct.List.scalarProduct nextQuadrances *
        FiniteProduct.List.scalarProduct pSpreads :=
      FiniteProduct.List.finiteScalarProduct_pointwise nextQuadrances pSpreads pLength
    _ = FiniteProduct.List.scalarProduct pSpreads *
        FiniteProduct.List.scalarProduct quadrances := by
      rw [cyclicQuadrances]
      ring1

/-- Four cyclic cleared ratios imply equality of their numerator products.

Each of the four quadrances is nonzero, so their common product can be cancelled without division. -/
theorem exercise_11_9_quadrilateral
    (r₁ r₂ r₃ r₄ p₁ p₂ p₃ p₄ N₁ N₂ N₃ N₄ : K)
    (N₁Nonzero : N₁ ≠ 0) (N₂Nonzero : N₂ ≠ 0)
    (N₃Nonzero : N₃ ≠ 0) (N₄Nonzero : N₄ ≠ 0)
    (firstRatio : r₁ * N₁ = N₂ * p₂)
    (secondRatio : r₂ * N₂ = N₃ * p₃)
    (thirdRatio : r₃ * N₃ = N₄ * p₄)
    (fourthRatio : r₄ * N₄ = N₁ * p₁) :
    r₁ * r₂ * r₃ * r₄ = p₁ * p₂ * p₃ * p₄ := by
  have quadranceProductNonzero :
      FiniteProduct.List.scalarProduct [N₁, N₂, N₃, N₄] ≠ 0 := by
    simp only [FiniteProduct.List.scalarProduct]
    exact ExplicitField.mul_ne_zero N₁Nonzero
      (ExplicitField.mul_ne_zero N₂Nonzero
        (ExplicitField.mul_ne_zero N₃Nonzero
          (by simpa only [mul_one] using N₄Nonzero)))
  have finiteResult := FiniteProduct.CyclicCancellation.exercise_11_9_polygon
    [r₁, r₂, r₃, r₄] [p₂, p₃, p₄, p₁]
    [N₁, N₂, N₃, N₄] [N₂, N₃, N₄, N₁]
    rfl rfl (by
      simp only [FiniteProduct.List.pointwiseScalarProduct]
      rw [firstRatio, secondRatio, thirdRatio, fourthRatio])
    (by simp only [FiniteProduct.List.scalarProduct]; ring1)
    quadranceProductNonzero
  calc
    r₁ * r₂ * r₃ * r₄ =
        FiniteProduct.List.scalarProduct [r₁, r₂, r₃, r₄] := by
      simp only [FiniteProduct.List.scalarProduct]
      ring1
    _ = FiniteProduct.List.scalarProduct [p₂, p₃, p₄, p₁] := finiteResult
    _ = p₁ * p₂ * p₃ * p₄ := by
      simp only [FiniteProduct.List.scalarProduct]
      ring1
end Purelib.Algebra.FiniteProduct.CyclicCancellation

end
