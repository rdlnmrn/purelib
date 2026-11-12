module

import Purelib.Polynomial.Dense.Roots.Product.Derivative
import Purelib.Algebra.Quadratic.Pair.Basic
import Purelib.Data.Gaussian.Field

/-!
# Original simple-root cofactors over a ring with zero divisors

Three original occurrences include two distinct nilpotent perturbations whose
difference is a nonunit. Literal first coefficients and a nonunit leading
factor verify the original indexed cofactor readbacks without a root bank.
-/

namespace TestPurelib.Polynomial.Dense.Roots.Product

open Purelib.Algebra.Quadratic
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Roots
open Purelib.Polynomial.Recurrence.Mode

/-- The original square-zero quadratic coefficient ring. -/
private abbrev Dual := Pair Purelib.Data.Gaussian.Basic.Canonical 0

/-- The original nonzero square-zero coordinate. -/
private def epsilon : Dual := Pair.generator

/-- The three original indexed simple-root occurrences. -/
private def blocks : List (Block Dual) :=
  [⟨0, 1, by decide⟩, ⟨1 + epsilon, 1, by decide⟩, ⟨1 - epsilon, 1, by decide⟩]

/-- Every retained original block has multiplicity one. -/
private theorem simple : ∀ index : Fin blocks.length, (blocks[index.val]'index.isLt).multiplicity = 1 := by
  decide +kernel

/-- The actual original product certifies its cofactor reading at each original bounded occurrence. -/
private theorem all_readbacks (index : Fin blocks.length) :
    coefficientRow (product blocks).coeffs (blocks[index.val]'index.isLt).point 1 0 =
      ((blocks.eraseIdx index.val).map (fun other => (blocks[index.val]'index.isLt).point - other.point)).prod :=
  Product.firstJet_at blocks simple index

/-- The actual product's first readings agree with an independent literal table. -/
private theorem literal_first_coefficients : ∀ index : Fin blocks.length,
    coefficientRow (product blocks).coeffs (blocks[index.val]'index.isLt).point 1 0 =
      if index.val = 0 then 1 else if index.val = 1 then 2 * epsilon else -(2 * epsilon) := by
  decide +kernel

/-- The same actual indexed difference product retains an arbitrary displayed leading factor. -/
private theorem leading_readback (index : Fin blocks.length) :
    coefficientRow (DensePolynomial.scale epsilon (product blocks)).coeffs
        (blocks[index.val]'index.isLt).point 1 0 =
      epsilon * ((blocks.eraseIdx index.val).map
        (fun other => (blocks[index.val]'index.isLt).point - other.point)).prod :=
  Product.scale_firstJet_at epsilon blocks simple index

/-- A nonzero nilpotent leading factor survives the original first reading and kills the other two. -/
private theorem literal_scaled_coefficients : ∀ index : Fin blocks.length,
    coefficientRow (DensePolynomial.scale epsilon (product blocks)).coeffs
        (blocks[index.val]'index.isLt).point 1 0 =
      if index.val = 0 then epsilon else 0 := by
  decide +kernel

/-- Two original simple roots have actual unit differences over the same ring. -/
private def unitBlocks : List (Block Dual) := [⟨0, 1, by decide⟩, ⟨1 + epsilon, 1, by decide⟩]

/-- The two retained unit-difference blocks are simple at their original bounded indices. -/
private theorem unitSimple : ∀ index : Fin unitBlocks.length,
    (unitBlocks[index.val]'index.isLt).multiplicity = 1 := by decide +kernel

/-- The actual inverse of the scaled whole product at the displayed arbitrary point. -/
private def wholeInverse : Dual := Pair.scalar (1 / 4) - Pair.scalar (1 / 8) * epsilon

/-- The first original target extracts its cofactor and unit from that same scaled whole inverse. -/
private def arbitraryFirst := Product.DifferenceInverse.ofEvalUnit unitBlocks unitSimple
  (2 + epsilon) ⟨0, by decide⟩ 2 wholeInverse (by decide +kernel)

/-- The second original target consumes the same supplied whole inverse. -/
private def arbitrarySecond := Product.DifferenceInverse.ofEvalUnit unitBlocks unitSimple
  (2 + epsilon) ⟨1, by decide⟩ 2 wholeInverse (by decide +kernel)

/-- Both arbitrary-point caches retain their independently calculated original cofactor products. -/
private theorem arbitrary_cofactors : arbitraryFirst.cofactor = 1 ∧ arbitrarySecond.cofactor = 2 + epsilon := by
  decide +kernel

/-- The same cached cofactors produce the independent original target-difference inverses. -/
private theorem arbitrary_inverses :
    arbitraryFirst.inverse.val = Pair.scalar (1 / 2) - Pair.scalar (1 / 4) * epsilon ∧
      arbitrarySecond.inverse.val = 1 := by decide +kernel

/-- Deleting the earlier original root retains the later original target through its checked rebound index. -/
private def laterTarget := Product.DifferenceInverse.ofFirstJetUnit unitBlocks unitSimple
  ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide) 1 (-(1 - epsilon)) (by decide +kernel)

/-- Deleting the later original root retains the earlier original target through the same checked operation. -/
private def earlierTarget := Product.DifferenceInverse.ofFirstJetUnit unitBlocks unitSimple
  ⟨1, by decide⟩ ⟨0, by decide⟩ (by decide) 1 (1 - epsilon) (by decide +kernel)

/-- The two original-order cases retain their same empty double-cofactor product once. -/
private theorem double_cofactors : laterTarget.cofactor = 1 ∧ earlierTarget.cofactor = 1 := by
  decide +kernel

/-- Both retained first-derivative inverses produce the independently specified original difference inverses. -/
private theorem double_inverses : laterTarget.inverse.val = -(1 - epsilon) ∧
    earlierTarget.inverse.val = 1 - epsilon := by decide +kernel

/-- The original root-to-target difference retains its unit certificate directly from the cache. -/
private theorem later_original_unit : (0 - (1 + epsilon)) * laterTarget.inverse.val = 1 :=
  laterTarget.inverse.property

/-- The reversed original root-to-target difference retains its same direct unit certificate. -/
private theorem earlier_original_unit : ((1 + epsilon) - 0) * earlierTarget.inverse.val = 1 :=
  earlierTarget.inverse.property

end TestPurelib.Polynomial.Dense.Roots.Product
