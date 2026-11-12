module

public import Purelib.Approximation.Gaussian.Division.Prepared.Basic
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
public import Purelib.Approximation.Gaussian.Division.Prepared.Quotient.Inverse
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic
import Purelib.Approximation.Gaussian.Division.Cancellation
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Apart.Preparation
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Gaussian.Field

/-!
# Division preparation after an exact nonzero right factor

The original coherent product remains the input owner. Its source's existing
whole-ball apartness and the exact factor's positive squared norm derive a
possible-reading lower bound. Existing finite apartification prepares that
same original product, retaining its operational comparison and actual state.
-/

public section

namespace Purelib.Approximation.Gaussian.Division.Prepared

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat

/-- Possible readings of a coherent exact-factor product inherit the original source's quantitative lower bound. -/
def exactRightPossibleApart (source : CoherentNamed) (factor : Canonical)
    (nonzero : factor ≠ 0) (apart : Named.Apart source.name) :
    Process.Apart.Possible.PossibleApart (source.mul (Coherence.exact factor)).name.process where
  lowerSq := apart.certificate.lowerSq * Norm.Basic.normSq factor
  positive := Fraction.Order.Arithmetic.mul_pos_direct apart.certificate.positive (Norm.Basic.normSq_pos nonzero)
  lower := by
    intro state value possible
    rcases possible with ⟨candidate, scalar, rootPossible, scalarPossible, rfl⟩
    change scalar = factor at scalarPossible
    rewrite [scalarPossible, Norm.Basic.normSq_mul]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (apart.certificate.lower state.1 (source.name.process.possible_inside rootPossible)) (Norm.Basic.normSq_nonneg _)

/-- Read the exact retained root floor and factor norm used by the computed possible-reading payment. -/
theorem exactRightPossibleApart_lowerSq (source : CoherentNamed) (factor : Canonical)
    (nonzero : factor ≠ 0) (apart : Named.Apart source.name) :
    (exactRightPossibleApart source factor nonzero apart).lowerSq =
      apart.certificate.lowerSq * Norm.Basic.normSq factor := by
  unfold exactRightPossibleApart
  rfl

/-- Prepare the identical retained exact-factor product for division by deriving its finite apartification schedule.

The full product and source remain inputs. Their exact construction equation
transports only the candidate certificate; the actual preparation refines the
retained original product state and compares its own two original names.
-/
def ofExactRight (product source : CoherentNamed) (factor : Canonical)
    (retained : product = source.mul (Coherence.exact factor))
    (nonzero : factor ≠ 0) (apart : Named.Apart source.name) : Division.Prepared product := by
  let originalLower := exactRightPossibleApart source factor nonzero apart
  let lower := Eq.mp (congrArg (fun value : CoherentNamed => Process.Apart.Possible.PossibleApart value.name.process)
    retained.symm) originalLower
  exact
    { denominator := product.apartify lower
      apart := ⟨Process.Apart.Preparation.apartifyApart lower⟩
      equivalent := product.apartifyEquivalent lower }

/-- The actual prepared reciprocal factors through the original source reciprocal and the exact scalar inverse.

The complete product construction and its supplied preparation remain
retained. Product-to-unit cancellation compares the actual prepared quotient
to the original source channel's reciprocal times the exact inverse factor.
-/
def reciprocal_exactRight {product : CoherentNamed} (prepared : Division.Prepared product)
    (source : CoherentNamed) (factor : Canonical)
    (retained : product = source.mul (Coherence.exact factor))
    (nonzero : factor ≠ 0) (apart : Named.Apart source.name) :
    NamedEquivalent (prepared.quotient (Coherence.exact 1)).name
      (((Coherence.exact 1).div source apart).mul (Coherence.exact factor⁻¹)).name := by
  let reciprocal := (Coherence.exact 1).div source apart
  let scalarInverse := Coherence.exact factor⁻¹
  let inverse := reciprocal.mul scalarInverse
  have sourceUnit : NamedEquivalent (source.mul reciprocal).name (Coherence.exact 1).name :=
    (Product.Laws.coherentMul_comm source reciprocal).trans
      (Cancellation.reciprocal_mul_cancel source apart)
  have scalarUnit : NamedEquivalent ((Coherence.exact factor).mul scalarInverse).name (Coherence.exact 1).name :=
    NamedEquivalent.transport rfl
      (congrArg (fun value : Canonical => (Coherence.exact value).name) (show factor * factor⁻¹ = 1 from by
        rewrite [Field.inv_eq]
        exact Field.mul_inv factor nonzero))
      (Name.Coherent.Exact.Arithmetic.exact_mul factor factor⁻¹)
  have identity : NamedEquivalent (product.mul inverse).name (Coherence.exact 1).name := by
    rewrite [retained]
    exact (Product.Laws.coherentMul_interchange source (Coherence.exact factor) reciprocal scalarInverse).trans
      ((Product.Congruence.coherentMul_respects (source.mul reciprocal) (Coherence.exact 1)
        ((Coherence.exact factor).mul scalarInverse) (Coherence.exact 1) sourceUnit scalarUnit).trans
          (Name.Coherent.Exact.Arithmetic.exact_mul 1 1))
  exact prepared.reciprocal_equivalent_of_product inverse identity

end Purelib.Approximation.Gaussian.Division.Prepared
