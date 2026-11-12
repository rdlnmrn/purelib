module

public import Purelib.Polynomial.Dense.Roots.Tower.Algebra
public import Purelib.Polynomial.Dense.Roots.Product

/-!
# The original tower's complete ordered factorization

All retained stage roots are mapped through the same remaining scalar
embeddings into the final coefficient algebra. The original root-block
product then recovers the mapped original coefficient table literally.
The blocks here have multiplicity one and need not yet be separated.
-/

public section

namespace Purelib.Polynomial.Dense.Roots.Tower

open Basic (DensePolynomial)
open Purelib.Algebra.Monogenic

universe u

/-- Collect the same retained stage roots as ordered simple blocks in the final algebra. -/
@[expose] def blocks {K : Type u} {ring : CommRing K} {equality : DecidableEq K}
    {polynomial : DensePolynomial K} (tower : Tower K ring equality polynomial) : List (Block tower.Scalar) :=
  match tower with
  | .constant _ _ => []
  | .step adjunction _ remaining =>
      ⟨remaining.embed adjunction.root, 1, Nat.zero_lt_succ 0⟩ :: remaining.blocks

variable {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
variable {polynomial : DensePolynomial K}

/-- The same ordered blocks exhaust the original degree through their actual multiplicities. -/
theorem totalMultiplicity_blocks (tower : Tower K ring equality polynomial) :
    totalMultiplicity tower.blocks = polynomial.natDegree := by
  induction tower with
  | constant polynomial degree => exact degree.symm
  | @step K ring equality polynomial adjunction decreases remaining previous =>
      change 1 + totalMultiplicity remaining.blocks = polynomial.natDegree
      rewrite [previous, Nat.add_comm 1]
      exact decreases

/-- The collected original simple blocks have exactly the original polynomial degree. -/
theorem blocks_length (tower : Tower K ring equality polynomial) :
    tower.blocks.length = polynomial.natDegree := by
  induction tower with
  | constant polynomial degree => exact degree.symm
  | @step K ring equality polynomial _ decreases _ previous =>
      change _ + 1 = polynomial.natDegree
      exact (congrArg Nat.succ previous).trans decreases

/-- Every collected original stage root has its same displayed simple multiplicity. -/
theorem blocks_simple (tower : Tower K ring equality polynomial) (index : Fin tower.blocks.length) :
    (tower.blocks[index.val]'index.isLt).multiplicity = 1 := by
  induction tower with
  | constant => exact Fin.elim0 index
  | step _ _ remaining previous =>
      rcases index with ⟨position, bound⟩
      cases position with
      | zero => rfl
      | succ position => exact previous ⟨position, Nat.lt_of_succ_lt_succ bound⟩

/-- The collected original root blocks give a literal complete coefficient factorization.

The same original synthetic quotient is used at every step. The proof maps
each retained linear-factor identity through the remaining original scalar
embedding, then uses the same normalized dense product and scalar operation.
-/
theorem factorization (tower : Tower K ring equality polynomial) :
    polynomial.normalize = polynomial →
      (Map.map tower.embed polynomial).normalize =
        DensePolynomial.scale (tower.embed polynomial.leadingCoeff) (product tower.blocks) := by
  induction tower with
  | @constant K ring equality polynomial degree =>
      intro _
      change (Map.map id polynomial).normalize =
        DensePolynomial.scale polynomial.leadingCoeff (DensePolynomial.constant 1)
      rewrite [Map.map_id, DensePolynomial.scale_constant_one]
      cases zero : polynomial.isZero with
      | false =>
          exact (DensePolynomial.normalize_eq_constant_leadingCoeff_of_degree_zero zero degree).trans
            (DensePolynomial.normalize_constant_of_ne (DensePolynomial.leadingCoeff_ne_zero zero)).symm
      | true =>
          have normalizedZero := DensePolynomial.normalize_eq_zero_of_isZero zero
          have leadingZero : polynomial.leadingCoeff = 0 :=
            congrArg (fun value : DensePolynomial K => value.coeffs.headD 0) normalizedZero
          rewrite [normalizedZero, leadingZero, DensePolynomial.normalize_constant_zero]
          rfl
  | @step K ring equality polynomial adjunction _ remaining previous =>
      intro normalized
      have source : Map.map (fun value => remaining.embed (Cyclic.Element.scalar adjunction.table value)) polynomial =
          Map.map remaining.embed adjunction.source := by
        exact (Map.map_map remaining.embed (Cyclic.Element.scalar adjunction.table) polynomial).symm.trans
          (congrArg (Map.map remaining.embed) adjunction.source_eq.symm)
      have mapped := congrArg (Map.map remaining.embed) adjunction.factorization
      rewrite [Map.map_normalize remaining.embed remaining.embed_zero remaining.embed_injective,
        adjunction.product_eq,
        Map.map_mul remaining.embed remaining.embed_zero remaining.embed_injective
          remaining.embed_add remaining.embed_mul] at mapped
      have linear : Map.map remaining.embed (⟨[1, -adjunction.root]⟩ : DensePolynomial (StageScalar adjunction)) =
          (⟨[1, -remaining.embed adjunction.root]⟩ : DensePolynomial remaining.Scalar) := by
        apply DensePolynomial.ext
        change [remaining.embed 1, remaining.embed (-adjunction.root)] = [1, -remaining.embed adjunction.root]
        rewrite [remaining.embed_one, remaining.embed_neg]
        rfl
      have quotientNormalized : (Map.map remaining.embed adjunction.division.quotient).normalize =
          Map.map remaining.embed adjunction.division.quotient :=
        (Map.map_normalize remaining.embed remaining.embed_zero remaining.embed_injective _).symm.trans
          (congrArg (Map.map remaining.embed) (adjunction.quotient_normalized normalized))
      have quotientFactorization := previous (adjunction.quotient_normalized normalized)
      rewrite [quotientNormalized] at quotientFactorization
      rewrite [linear, quotientFactorization, DensePolynomial.mul_scale,
        adjunction.quotient_leadingCoeff normalized] at mapped
      change (Map.map
        (fun value => remaining.embed (Cyclic.Element.scalar adjunction.table value)) polynomial).normalize =
        DensePolynomial.scale (remaining.embed (Cyclic.Element.scalar adjunction.table polynomial.leadingCoeff))
          (product (⟨remaining.embed adjunction.root, 1, Nat.zero_lt_succ 0⟩ :: remaining.blocks))
      rewrite [source, product_cons_one]
      exact mapped

end Purelib.Polynomial.Dense.Roots.Tower

end
