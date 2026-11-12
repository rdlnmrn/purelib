module
import Init.Data.Fin.Lemmas

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
public import Purelib.Polynomial.Ascending.Gaussian.InverseSquareRoot
public import Purelib.Curves.Hyperelliptic.Charts.Infinity
public import Purelib.Polynomial.Ascending.Gaussian.Dense.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Polynomial.Bounds.Horner
import Purelib.Algebra.FiniteSum.Prefix
import Purelib.Polynomial.Dense.Gaussian.Reciprocal
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Power
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Vector.Basic
public import Purelib.LinearAlgebra.Vector.Unit
public import Purelib.LinearAlgebra.Vector.Weighted
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-! # Exact finite coefficient data at hyperelliptic infinity

The reciprocal radicand is the same normalized reversed polynomial already
used by the original curve charts. Its leading coefficient is nonzero, so a
finite normalized inverse-root table is constructed without selecting another
root or sheet. In even degree its first `g+1` entries determine one normalized
Laurent coefficient functional on the `2g+1` affine remainder coordinates.

The pivot correction and its kernel certificates concern that finite
functional. Local meromorphic-chart interpretation, actual residues on the
retained two sheets, general exact-primitive independence and geometric
attachment estimates remain separate statements.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.InfinityCoefficients

open Purelib.Polynomial.Ascending.Gaussian.Dense.Evaluation
open Purelib.Data
open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts
open Purelib.Polynomial
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Polynomial.Ascending.Gaussian.Coefficient (coefficient)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.LinearAlgebra.Vector
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_ite_eq sumFin_swap sumFin_mul_left)

variable {genus : Nat}

/-- The original reversed radicand's exact ascending coefficient table.

The original dense normalization supplies the table once. No reversal or
new curve polynomial is computed while producing inverse-root coefficients. -/
@[expose] def radicand (curve : HyperellipticCurve genus) : CoefficientPolynomial :=
  ⟨curve.polynomial.normalize.coeffs⟩

/-- Dense readback is exactly the original reciprocal chart's reversed factor. -/
theorem radicand_toDense (curve : HyperellipticCurve genus) :
    toDense (radicand curve) =
      HyperellipticReciprocal.reversed curve.polynomial := rfl

/-- The finite radicand's constant is the original leading coefficient. -/
theorem radicand_zero (curve : HyperellipticCurve genus) :
    coefficient (radicand curve) 0 = curve.polynomial.leadingCoeff := by
  change Coefficient.coefficientList curve.polynomial.normalize.coeffs 0 =
    curve.polynomial.normalize.coeffs.headD 0
  cases curve.polynomial.normalize.coeffs <;> rfl

/-- Original curve nonvanishing supplies the exact denominator needed by every finite jet coefficient. -/
theorem radicand_zero_nonzero (curve : HyperellipticCurve genus) : coefficient (radicand curve) 0 ≠ 0 := by
  rewrite [radicand_zero]
  exact Dense.Basic.DensePolynomial.leadingCoeff_ne_zero curve.nonzero

/-- A finite inverse-root cache indexed by the original curve and its retained genus.

The type is an exact subtype of the original ascending Gaussian polynomial,
with the original reversed factor and order `g`; no alternate jet record is introduced. -/
abbrev Jet (curve : HyperellipticCurve genus) :=
  { jet : CoefficientPolynomial // InverseSquareRoot.Specification (radicand curve) genus jet }

/-- Construct all required finite normalized inverse-root entries from the original curve. -/
@[expose] def prepare (curve : HyperellipticCurve genus) : Jet curve :=
  InverseSquareRoot.build (radicand curve) genus (radicand_zero_nonzero curve)

/-- The prepared cache retains exactly `g+1` physical coefficient entries. -/
theorem prepare_length (curve : HyperellipticCurve genus) :
    (prepare curve).val.coefficients.length = genus + 1 := (prepare curve).property.1

/-- The same retained inverse-root cache clears the original reversed radicand through degree `g`.

The constant is the original curve leading coefficient, rather than a newly
selected root or a substituted monic curve. -/
theorem Jet.product_truncation (curve : HyperellipticCurve genus) (jet : Jet curve) :
    Coefficient.EqualBelow (genus + 1) (InverseSquareRoot.product (radicand curve) jet.val)
      (Ascending.Gaussian.Basic.constant curve.polynomial.leadingCoeff) := by
  have truncated := jet.property.product_truncation
  rewrite [radicand_zero] at truncated
  exact truncated

/-- The exact finite product of the original padded numerator and the same retained inverse-root jet.

The subtype fixes the original polynomial, scale and jet as its parents.
Its stored polynomial is the actual finite convolution C=(-scale B)H,
shared by coefficient extraction and the low-block/regular-tail split.
-/
abbrev Jet.Principal {curve : HyperellipticCurve genus} (jet : Jet curve)
    (polynomial : Dense.Basic.DensePolynomial Canonical) (scale : Canonical) :=
  { retained : CoefficientPolynomial // retained = Arithmetic.mul
      (Arithmetic.scale (-scale) (fromDense polynomial)) jet.val }

/-- Compute the original scaled numerator and its convolution with the supplied jet once. -/
def Jet.principal {curve : HyperellipticCurve genus} (jet : Jet curve)
    (polynomial : Dense.Basic.DensePolynomial Canonical) (scale : Canonical) : jet.Principal polynomial scale :=
  let numerator := Arithmetic.scale (-scale) (fromDense polynomial)
  let retained := Arithmetic.mul numerator jet.val
  ⟨retained, rfl⟩

namespace Jet.Principal

variable {curve : HyperellipticCurve genus} {jet : Jet curve}
  {polynomial : Dense.Basic.DensePolynomial Canonical} {scale : Canonical}

/-- Evaluation consumes the stored original convolution and reads its exact numerator/jet product. -/
theorem eval (retained : jet.Principal polynomial scale) (point : Canonical) :
    Evaluation.eval retained.val point = (-scale * polynomial.eval point) * Evaluation.eval jet.val point := by
  rewrite [retained.property, Evaluation.eval_mul, Evaluation.eval_scale,
    fromDense_eval]
  rfl

/-- An actual cleared numerator reads the same retained principal polynomial divided by the omitted jet power.

The supplied clearing equation concerns the original padded numerator at
this coordinate. The actual nonzero witness cancels its displayed power;
no new square-root value or limiting expansion is used.
-/
theorem cleared (retained : jet.Principal polynomial scale) (point numerator : Canonical)
    (nonzero : point ≠ 0) (clearing : numerator * point ^ (genus + 1) = -scale * polynomial.eval point) :
    numerator * Evaluation.eval jet.val point = Evaluation.eval retained.val point * (point ^ (genus + 1))⁻¹ := by
  have powerNonzero := Purelib.Data.Gaussian.Power.pow_ne_zero_direct point nonzero (genus + 1)
  calc
    _ = (numerator * Evaluation.eval jet.val point) *
        (point ^ (genus + 1) * (point ^ (genus + 1))⁻¹) := by
      rewrite [Purelib.Algebra.Field.ExplicitField.mul_inv_cancel _ powerNonzero,
        Gaussian.Basic.mul_one]
      rfl
    _ = (numerator * point ^ (genus + 1)) * Evaluation.eval jet.val point * (point ^ (genus + 1))⁻¹ := by
      ring1
    _ = _ := by rewrite [clearing, eval]; rfl

/-- The same actual principal product splits into a finite polar block and its literal regular polynomial tail.

Both parts consume the supplied retained C polynomial. The statement
includes genus zero and coefficient tables shorter than the split degree;
it is an exact finite identity, without identifying an analytic residue.
-/
theorem split (retained : jet.Principal polynomial scale) (point numerator : Canonical)
    (nonzero : point ≠ 0) (clearing : numerator * point ^ (genus + 1) = -scale * polynomial.eval point) :
    numerator * Evaluation.eval jet.val point =
      Evaluation.eval ⟨retained.val.coefficients.take (genus + 1)⟩ point * (point ^ (genus + 1))⁻¹ +
        Evaluation.eval (Arithmetic.divideByPower (genus + 1) retained.val) point :=
  (cleared retained point numerator nonzero clearing).trans
    (Evaluation.eval_mul_inverse_power retained.val (genus + 1) point nonzero)

end Jet.Principal

section JetBounds

open Purelib.Polynomial.Dense.Gaussian
open Purelib.Data.Gaussian
open Purelib.Polynomial.Ascending.Gaussian.Evaluation (eval eval_at_zero)
open Purelib.Polynomial.Bounds (Horner)
open Purelib.Geometry.Rational (Box)

/-- The original finite jet's retained value/slope fold, indexed by that same jet and box.

This exact subtype uses the original Horner carrier and original box fold.
Its parent equation prevents substituting bounds for a different jet,
coefficient order or box while keeping the actual computed pair once.
-/
abbrev Jet.Bounds {curve : HyperellipticCurve genus} (jet : Jet curve) (box : Box) :=
  { retained : Horner // retained = Bounds.Box.denseHornerNormBounds
      (toDense jet.val) box }

/-- Compute the original dense view and its actual joint value/slope Horner cache once. -/
@[expose] def Jet.bounds {curve : HyperellipticCurve genus} (jet : Jet curve) (box : Box) : jet.Bounds box :=
  let polynomial := toDense jet.val
  let retained := Bounds.Box.denseHornerNormBounds polynomial box
  ⟨retained, rfl⟩

/-- The retained actual jet value ceiling is nonnegative. -/
theorem Jet.Bounds.value_nonnegative {curve : HyperellipticCurve genus} {jet : Jet curve} {box : Box}
    (bounds : jet.Bounds box) : 0 ≤ bounds.val.value := by
  rewrite [bounds.property]
  exact (Bounds.Box.denseHornerNormBounds_nonneg _ _).1

/-- The retained actual jet slope ceiling is nonnegative. -/
theorem Jet.Bounds.slope_nonnegative {curve : HyperellipticCurve genus} {jet : Jet curve} {box : Box}
    (bounds : jet.Bounds box) : 0 ≤ bounds.val.slope := by
  rewrite [bounds.property]
  exact (Bounds.Box.denseHornerNormBounds_nonneg _ _).2

/-- The original jet reading in the retained box satisfies the same actual cached value ceiling. -/
theorem Jet.Bounds.value_le {curve : HyperellipticCurve genus} {jet : Jet curve} {box : Box}
    (bounds : jet.Bounds box) {point : Canonical} (inside : box.Contains point) :
    Norm.Basic.normSq (eval jet.val point) ≤ bounds.val.value := by
  have bounded := Bounds.Box.normSq_eval_le_denseEvalNormBound
    (toDense jet.val) inside
  rewrite [toDense_eval] at bounded
  rewrite [bounds.property]
  exact bounded

/-- The same actual jet slope cache bounds its reading's departure from the retained constant one. -/
theorem Jet.Bounds.increment_le {curve : HyperellipticCurve genus} {jet : Jet curve} {box : Box}
    (bounds : jet.Bounds box) (originInside : box.Contains 0) {point : Canonical} (inside : box.Contains point) :
    Norm.Basic.normSq (eval jet.val point - 1) ≤
      bounds.val.slope * Norm.Basic.normSq point := by
  have bounded := Bounds.Box.normSq_eval_sub_eval_le
    (toDense jet.val) inside originInside
  rewrite [toDense_eval,
    toDense_eval, eval_at_zero, jet.property.2.1,
    Gaussian.Basic.sub_zero] at bounded
  rewrite [bounds.property]
  exact bounded

end JetBounds

/-- The odd-degree affine remainder has exactly the expected `2g` possible coordinates. -/
theorem affineDimension_odd (curve : HyperellipticCurve genus)
    (degree : curve.polynomial.natDegree = 2 * genus + 1) :
    curve.polynomial.natDegree - 1 = 2 * genus := by omega

/-- The even-degree affine remainder has one additional coordinate before the infinity constraint. -/
theorem affineDimension_even (curve : HyperellipticCurve genus)
    (degree : curve.polynomial.natDegree = 2 * genus + 2) :
    curve.polynomial.natDegree - 1 = 2 * genus + 1 := by omega

/-- Read the potential `t^-1` coefficient of an odd-degree monomial pullback.

The finite schema is `-2 t^(2g-2-2i) H(t²)`. A negative leading exponent
requires the odd square-substitution coordinate `2(i-g)+1`; nonnegative
leading exponents contribute zero. The actual chart bridge remains separate. -/
@[expose] def oddWeight (curve : HyperellipticCurve genus) (jet : Jet curve) (index : Fin (2 * genus)) :
    Canonical :=
  if index.val < genus then 0 else
    -2 * Coefficient.coefficientList (Infinity.evenCoefficients jet.val.coefficients)
      (2 * (index.val - genus) + 1)

/-- The computed odd-degree `t^-1` coefficient vanishes by exact finite coefficient parity. -/
theorem oddWeight_zero (curve : HyperellipticCurve genus) (jet : Jet curve) (index : Fin (2 * genus)) :
    oddWeight curve jet index = 0 := by
  unfold oddWeight
  split
  · rfl
  · rewrite [Infinity.evenCoefficients_odd]
    exact Gaussian.Basic.mul_zero _

/-- Compute the odd-degree potential infinity coefficient on the actual affine remainder coordinates. -/
@[expose] def oddFunctional (curve : HyperellipticCurve genus) (jet : Jet curve)
    (numerator : Purelib.Data.Vector Canonical (2 * genus)) : Canonical :=
  sumFin fun index => oddWeight curve jet index * numerator index

/-- Every finite odd-degree affine remainder satisfies the computed parity constraint. -/
theorem oddFunctional_zero (curve : HyperellipticCurve genus) (jet : Jet curve)
    (numerator : Purelib.Data.Vector Canonical (2 * genus)) : oddFunctional curve jet numerator = 0 := by
  unfold oddFunctional
  exact (sumFin_congr (fun index => by
    rewrite [oddWeight_zero]
    exact Gaussian.Basic.zero_mul _)).trans FiniteSum.Fin.sumFin_zero

/-- The pivot's original bounded affine coordinate is `g` among the `2g+1` entries. -/
@[expose] def pivot (genus : Nat) : Fin (2 * genus + 1) := ⟨genus, by omega⟩

/-- The normalized even-degree Laurent coefficient weights of one retained cache.

For an affine numerator coefficient `r_i`, only `i≥g` contributes; its weight
is the original cached entry `h_(i-g)`. When the local even-degree chart bridge
is established, its sheet factor and inversion sign identify actual residues. -/
@[expose] def evenWeights (curve : HyperellipticCurve genus) (jet : Jet curve) :
    Purelib.Data.Vector Canonical (2 * genus + 1) :=
  vectorOfFn fun index => if index.val < genus then 0 else coefficient jet.val (index.val - genus)

/-- Reading a finite Laurent coefficient weight consumes the actual cached entry. -/
theorem evenWeights_apply (curve : HyperellipticCurve genus) (jet : Jet curve)
    (index : Fin (2 * genus + 1)) :
    evenWeights curve jet index = if index.val < genus then 0 else coefficient jet.val (index.val - genus) :=
  vectorOfFn_apply _ index

/-- The chosen pivot has unit normalized weight, so no curve-dependent pivot division is needed. -/
theorem evenWeights_pivot (curve : HyperellipticCurve genus) (jet : Jet curve) :
    evenWeights curve jet (pivot genus) = 1 := by
  rewrite [evenWeights_apply]
  change (if genus < genus then 0 else coefficient jet.val (genus - genus)) = 1
  rewrite [if_neg (Nat.lt_irrefl genus), Nat.sub_self]
  exact jet.property.2.1

/-- Compute the normalized infinity coefficient from the actual affine remainder entries.

This finite weighted sum is the algebraic candidate for the even-degree
residue constraint; it does not assert a completed curve or analytic residue. -/
@[expose] def evenFunctional (curve : HyperellipticCurve genus) (jet : Jet curve)
    (numerator : Purelib.Data.Vector Canonical (2 * genus + 1)) : Canonical :=
  Weighted.weighted (evenWeights curve jet) numerator

/-- The normalized even infinity coefficient is the actual retained jet paired with the original upper numerator block.

The original bounded sum splits after the first `g` entries, whose weights
are zero. Each remaining original coordinate is `g+j`, so its weight is
the same retained jet coefficient `h_j`. This includes the genus-zero
case without selecting or discarding a coordinate.
-/
theorem evenFunctional_tail (curve : HyperellipticCurve genus) (jet : Jet curve)
    (numerator : Purelib.Data.Vector Canonical (2 * genus + 1)) :
    evenFunctional curve jet numerator =
      sumFin (fun index : Fin (genus + 1) => coefficient jet.val index.val *
        numerator ⟨genus + index.val, by omega0⟩) := by
  let term := fun index : Fin (2 * genus + 1) => evenWeights curve jet index * numerator index
  have size : genus + (genus + 1) = 2 * genus + 1 := by omega0
  have castSum := FiniteSum.Fin.sumFin_cast size term
  have split := FiniteSum.Fin.sumFin_split
    (fun index : Fin (genus + (genus + 1)) => term (Fin.cast size index))
  have lower : sumFin (fun index : Fin genus => term (Fin.cast size (Fin.castAdd (genus + 1) index))) = 0 := by
    calc
      _ = sumFin (fun _index : Fin genus => (0 : Canonical)) := by
        apply sumFin_congr
        intro index
        dsimp only [term]
        rewrite [evenWeights_apply, Fin.val_cast, Fin.val_castAdd, if_pos index.isLt]
        exact Gaussian.Basic.zero_mul _
      _ = 0 := FiniteSum.Fin.sumFin_zero
  have upper : sumFin (fun index : Fin (genus + 1) => term (Fin.cast size (Fin.natAdd genus index))) =
      sumFin (fun index : Fin (genus + 1) => coefficient jet.val index.val *
        numerator ⟨genus + index.val, by omega0⟩) := by
    apply sumFin_congr
    intro index
    dsimp only [term]
    rewrite [evenWeights_apply, Fin.val_cast, Fin.val_natAdd,
      if_neg (show ¬genus + index.val < genus by omega0),
      show genus + index.val - genus = index.val by omega0]
    rfl
  change sumFin term = _
  exact castSum.symm.trans (split.trans (by rewrite [lower, upper, Gaussian.Basic.zero_add]; rfl))

namespace Jet.Principal

open Purelib.Algebra.FiniteSum

/-- The same actual finite principal product reads the original even infinity functional at its polar pivot.

The original padded numerator and retained jet determine every convolution
entry. Finite reversed coefficient readback identifies the pivot coefficient
with the original bounded numerator functional, including genus zero and
zero numerator tables. This is an exact coefficient identity, not a physical
residue or an assumed chart comparison.
-/
theorem even_coefficient (curve : HyperellipticCurve genus) (jet : Jet curve)
    (numerator : Dense.Basic.DensePolynomial Canonical) (scale : Canonical)
    (bound : numerator.degreeCount ≤ 2 * genus + 1)
    (polynomial : { value : Dense.Basic.DensePolynomial Canonical //
      value = Dense.Gaussian.Reciprocal.padded numerator (2 * genus) })
    (retained : jet.Principal polynomial.val scale) :
    coefficient retained.val genus = -scale * evenFunctional curve jet
      (toVector (2 * genus + 1)
        (fromDense numerator.normalize)) := by
  let entry := fun index => coefficient (fromDense numerator.normalize) index
  let value := fun index => coefficient jet.val index
  have functional := evenFunctional_tail curve jet
    (toVector (2 * genus + 1)
      (fromDense numerator.normalize))
  have functionalReadback : evenFunctional curve jet
      (toVector (2 * genus + 1)
        (fromDense numerator.normalize)) =
      Prefix.prefixSum (genus + 1) (fun index => value index * entry (genus + index)) := by
    exact functional.trans
      ((sumFin_congr (fun index => congrArg (fun coefficient => value index.val * coefficient)
        (toVector_apply (2 * genus + 1)
          (fromDense numerator.normalize) ⟨genus + index.val, by omega0⟩))).trans
        (Prefix.sumFin_eq_prefixSum (K := Canonical) (genus + 1)
          (fun index => value index * entry (genus + index))))
  rewrite [retained.property, Arithmetic.coefficient_mul]
  calc
    _ = Prefix.prefixSum (genus + 1) (fun index => (-scale) * (entry (2 * genus - index) * value (genus - index))) :=
      Prefix.prefixSum_congr (genus + 1) _ _ (fun index inside => by
        rewrite [Arithmetic.coefficient_scale, polynomial.property,
          Dense.Gaussian.Reciprocal.padded_coefficient numerator (2 * genus) bound index (by omega0)]
        ring1)
    _ = (-scale) * Prefix.prefixSum (genus + 1)
        (fun index => entry (2 * genus - index) * value (genus - index)) :=
      Prefix.prefixSum_mul_left (genus + 1) (-scale) _
    _ = (-scale) * Prefix.prefixSum (genus + 1) (fun index => value index * entry (genus + index)) := by
      apply congrArg (fun total : Canonical => (-scale) * total)
      have reverseSum := Prefix.prefixSum_reverse (genus + 1)
        (fun index => entry (2 * genus - index) * value (genus - index))
      exact reverseSum.trans (Prefix.prefixSum_congr (genus + 1) _ _ (fun index inside => by
        rewrite [show genus + 1 - 1 - index = genus - index by omega0,
          show 2 * genus - (genus - index) = genus + index by omega0,
          show genus - (genus - index) = index by omega0]
        exact Gaussian.Basic.mul_comm _ _))
    _ = _ := congrArg (fun total : Canonical => (-scale) * total) functionalReadback.symm

end Jet.Principal

/-- Finite extraction of the even principal part's coefficient at exponent minus one reads the original functional.

The displayed terms are `r_i h_j w^(g-1-i+j)`. Both bounded indices
refer to the original numerator vector and actual retained jet. The unique
possible contributing index is `j=i-g`; its actual cached coefficient is
exactly the original weight. This is a finite coefficient identity and
asserts no chart interpretation or meromorphic regularity.
-/
theorem evenLaurent_coefficient (curve : HyperellipticCurve genus) (jet : Jet curve)
    (numerator : Purelib.Data.Vector Canonical (2 * genus + 1)) :
    sumFin (fun index : Fin (2 * genus + 1) =>
      sumFin (fun jetIndex : Fin (genus + 1) =>
        if (genus : Int) - 1 - (index.val : Int) + (jetIndex.val : Int) = -1 then
          coefficient jet.val jetIndex.val * numerator index else 0)) = evenFunctional curve jet numerator := by
  change _ = sumFin (fun index => evenWeights curve jet index * numerator index)
  apply sumFin_congr
  intro index
  rewrite [evenWeights_apply]
  by_cases low : index.val < genus
  · rewrite [if_pos low, Gaussian.Basic.zero_mul]
    calc
      _ = sumFin (fun _jetIndex : Fin (genus + 1) => (0 : Canonical)) := by
        apply sumFin_congr
        intro jetIndex
        rewrite [if_neg (show ¬(genus : Int) - 1 - (index.val : Int) + (jetIndex.val : Int) = -1 by omega0)]
        rfl
      _ = 0 := FiniteSum.Fin.sumFin_zero
  · rewrite [if_neg low]
    let selected : Fin (genus + 1) := ⟨index.val - genus, by omega0⟩
    calc
      _ = sumFin (fun jetIndex : Fin (genus + 1) =>
          if jetIndex = selected then coefficient jet.val selected.val * numerator index else 0) := by
        apply sumFin_congr
        intro jetIndex
        by_cases same : jetIndex = selected
        · cases same
          rewrite [if_pos rfl,
            if_pos (show (genus : Int) - 1 - (index.val : Int) + (selected.val : Int) = -1 by
              dsimp only [selected]
              omega0)]
          rfl
        · have different : ¬(genus : Int) - 1 - (index.val : Int) + (jetIndex.val : Int) = -1 := by
            intro equal
            apply same
            apply Fin.ext
            dsimp only [selected]
            omega0
          rewrite [if_neg different, if_neg same]
          rfl
      _ = _ := sumFin_ite_eq selected _

/-- Finite extraction at exponent minus one vanishes for the odd chart's actual even-power principal terms.

Its terms are `r_i h_j t^(2g-2-2i+2j)`, using the original bounded
numerator and retained jet. Every displayed exponent is even, so none
is minus one. This finite parity calculation does not assume a completed
local expansion or identify a sampled coordinate with an exact root.
-/
theorem oddLaurent_coefficient (curve : HyperellipticCurve genus) (jet : Jet curve)
    (numerator : Purelib.Data.Vector Canonical (2 * genus)) :
    sumFin (fun index : Fin (2 * genus) =>
      sumFin (fun jetIndex : Fin (genus + 1) =>
        if 2 * (genus : Int) - 2 - 2 * (index.val : Int) + 2 * (jetIndex.val : Int) = -1 then
          coefficient jet.val jetIndex.val * numerator index else 0)) = 0 := by
  calc
    _ = sumFin (fun _index : Fin (2 * genus) => (0 : Canonical)) := by
      apply sumFin_congr
      intro index
      calc
        _ = sumFin (fun _jetIndex : Fin (genus + 1) => (0 : Canonical)) := by
          apply sumFin_congr
          intro jetIndex
          rewrite [if_neg (show ¬2 * (genus : Int) - 2 - 2 * (index.val : Int) +
            2 * (jetIndex.val : Int) = -1 by omega0)]
          rfl
        _ = 0 := FiniteSum.Fin.sumFin_zero
    _ = 0 := FiniteSum.Fin.sumFin_zero

/-- Clear the single normalized even-degree coefficient at its original bounded pivot.

The original weighted sum is computed once by `removePivot`. Each nonpivot
entry retains the identical original numerator value. -/
@[expose] def correctEven (curve : HyperellipticCurve genus) (jet : Jet curve)
    (numerator : Purelib.Data.Vector Canonical (2 * genus + 1)) :
    Purelib.Data.Vector Canonical (2 * genus + 1) :=
  Weighted.removePivot (evenWeights curve jet) numerator (pivot genus)

/-- The computed correction satisfies the finite normalized infinity constraint. -/
theorem correctEven_zero (curve : HyperellipticCurve genus) (jet : Jet curve)
    (numerator : Purelib.Data.Vector Canonical (2 * genus + 1)) :
    evenFunctional curve jet (correctEven curve jet numerator) = 0 :=
  Weighted.weighted_removePivot (evenWeights curve jet) numerator (pivot genus) (evenWeights_pivot curve jet)

/-- Each unselected original coefficient survives the correction exactly. -/
theorem correctEven_other (curve : HyperellipticCurve genus) (jet : Jet curve)
    (numerator : Purelib.Data.Vector Canonical (2 * genus + 1))
    (index : Fin (2 * genus + 1)) (different : index ≠ pivot genus) :
    correctEven curve jet numerator index = numerator index :=
  Weighted.removePivot_other (evenWeights curve jet) numerator (pivot genus) index different

/-- The selected coefficient is reduced by the one computed original weighted value. -/
theorem correctEven_pivot (curve : HyperellipticCurve genus) (jet : Jet curve)
    (numerator : Purelib.Data.Vector Canonical (2 * genus + 1)) :
    correctEven curve jet numerator (pivot genus) = numerator (pivot genus) - evenFunctional curve jet numerator :=
  Weighted.removePivot_same (evenWeights curve jet) numerator (pivot genus)

/-- A numerator satisfying the finite constraint is retained as the complete same vector. -/
theorem correctEven_of_zero (curve : HyperellipticCurve genus) (jet : Jet curve)
    (numerator : Purelib.Data.Vector Canonical (2 * genus + 1)) (zero : evenFunctional curve jet numerator = 0) :
    correctEven curve jet numerator = numerator :=
  Weighted.removePivot_of_zero (evenWeights curve jet) numerator (pivot genus) zero

/-- Enumerate the `2g` original affine coordinates other than the retained pivot. -/
@[expose] def nonpivot (index : Fin (2 * genus)) : Fin (2 * genus + 1) :=
  if before : index.val < genus then ⟨index.val, by omega⟩ else ⟨index.val + 1, by omega⟩

/-- Every enumerated coordinate is distinct from the omitted pivot. -/
theorem nonpivot_ne (index : Fin (2 * genus)) : nonpivot index ≠ pivot genus := by
  unfold nonpivot
  split
  · intro equal
    have same := congrArg Fin.val equal
    change index.val = genus at same
    omega
  · intro equal
    have same := congrArg Fin.val equal
    change index.val + 1 = genus at same
    omega

/-- The explicit nonpivot enumeration preserves distinct original indices. -/
theorem nonpivot_injective {left right : Fin (2 * genus)} (same : nonpivot left = nonpivot right) :
    left = right := by
  apply Fin.ext
  have values := congrArg Fin.val same
  unfold nonpivot at values
  by_cases leftBefore : left.val < genus
  · rewrite [dif_pos leftBefore] at values
    by_cases rightBefore : right.val < genus
    · rewrite [dif_pos rightBefore] at values
      exact values
    · rewrite [dif_neg rightBefore] at values
      change left.val = right.val + 1 at values
      omega
  · rewrite [dif_neg leftBefore] at values
    by_cases rightBefore : right.val < genus
    · rewrite [dif_pos rightBefore] at values
      change left.val + 1 = right.val at values
      omega
    · rewrite [dif_neg rightBefore] at values
      change left.val + 1 = right.val + 1 at values
      omega

/-- Every original affine coordinate other than the pivot occurs in the bounded enumeration. -/
def nonpivotIndex (position : Fin (2 * genus + 1)) (different : position ≠ pivot genus) : Fin (2 * genus) :=
  if before : position.val < genus then ⟨position.val, by omega⟩ else
    ⟨position.val - 1, by
      have unequal : position.val ≠ genus := fun equal => different (Fin.ext equal)
      omega⟩

/-- The finite inverse enumeration retains the identical original affine coordinate. -/
theorem nonpivot_nonpivotIndex (position : Fin (2 * genus + 1)) (different : position ≠ pivot genus) :
    nonpivot (nonpivotIndex position different) = position := by
  apply Fin.ext
  unfold nonpivotIndex
  split
  · unfold nonpivot
    rewrite [dif_pos (by assumption)]
    rfl
  · have unequal : position.val ≠ genus := fun equal => different (Fin.ext equal)
    have after : genus ≤ position.val - 1 := by omega
    unfold nonpivot
    rewrite [dif_neg (Nat.not_lt_of_ge after)]
    change position.val - 1 + 1 = position.val
    omega

/-- A corrected coordinate column in the kernel of the computed infinity functional.

The original structural coordinate unit and one-pivot update construct the
column. Its index is one of the `2g` explicitly enumerated nonpivot entries. -/
@[expose] def evenColumn (curve : HyperellipticCurve genus) (jet : Jet curve) (index : Fin (2 * genus)) :
    Purelib.Data.Vector Canonical (2 * genus + 1) :=
  correctEven curve jet (Unit.unitVector (nonpivot index))

/-- Every constructed column satisfies the normalized finite infinity constraint. -/
theorem evenColumn_zero (curve : HyperellipticCurve genus) (jet : Jet curve) (index : Fin (2 * genus)) :
    evenFunctional curve jet (evenColumn curve jet index) = 0 :=
  correctEven_zero curve jet _

/-- Nonpivot readback of a column is the same original coordinate unit. -/
theorem evenColumn_other (curve : HyperellipticCurve genus) (jet : Jet curve)
    (index : Fin (2 * genus)) (position : Fin (2 * genus + 1)) (different : position ≠ pivot genus) :
    evenColumn curve jet index position = if position = nonpivot index then 1 else 0 :=
  (correctEven_other curve jet _ position different).trans (Unit.unitVector_apply _ _)

/-- A coordinate unit reads its actual normalized weight in the finite functional. -/
theorem evenFunctional_unit (curve : HyperellipticCurve genus) (jet : Jet curve)
    (index : Fin (2 * genus + 1)) :
    evenFunctional curve jet (Unit.unitVector index) = evenWeights curve jet index :=
  Unit.weighted_right_unit (evenWeights curve jet) index

/-- The column pivot is the opposite of its original cached weight. -/
theorem evenColumn_pivot (curve : HyperellipticCurve genus) (jet : Jet curve) (index : Fin (2 * genus)) :
    evenColumn curve jet index (pivot genus) = -evenWeights curve jet (nonpivot index) := by
  rewrite [evenColumn, correctEven_pivot, evenFunctional_unit, Unit.unitVector_apply,
    if_neg (Ne.symm (nonpivot_ne index))]
  ring1

/-- Read a corrected column at another original nonpivot coordinate. -/
theorem evenColumn_coordinate (curve : HyperellipticCurve genus) (jet : Jet curve)
    (index position : Fin (2 * genus)) :
    evenColumn curve jet index (nonpivot position) = if position = index then 1 else 0 := by
  rewrite [evenColumn_other curve jet index (nonpivot position) (nonpivot_ne position)]
  by_cases same : position = index
  · subst position
    rewrite [if_pos rfl, if_pos rfl]
    rfl
  · rewrite [if_neg same, if_neg (fun equal => same (nonpivot_injective equal))]
    rfl

/-- Materialize all corrected columns once using one original retained weight vector.

The expensive inverse-root entries and their normalized weights remain outside
the column-producing function. Each column stores original structural vector data. -/
@[expose] def evenColumns (curve : HyperellipticCurve genus) (jet : Jet curve) :
    Purelib.Data.Vector (Purelib.Data.Vector Canonical (2 * genus + 1)) (2 * genus) :=
  let retainedWeights := evenWeights curve jet
  vectorOfFn fun index => Weighted.removePivot retainedWeights (Unit.unitVector (nonpivot index)) (pivot genus)

/-- Reading the actual column cache recovers its complete original column. -/
theorem evenColumns_apply (curve : HyperellipticCurve genus) (jet : Jet curve) (index : Fin (2 * genus)) :
    evenColumns curve jet index = evenColumn curve jet index := vectorOfFn_apply _ index

/-- Assemble a finite linear combination of the actual corrected columns.

The structural output vector stores every bounded coordinate once. Its
coefficients are an original structural `2g` vector and the jet is shared. -/
@[expose] def evenCombination (curve : HyperellipticCurve genus) (jet : Jet curve)
    (coordinates : Purelib.Data.Vector Canonical (2 * genus)) :
    Purelib.Data.Vector Canonical (2 * genus + 1) :=
  let retainedColumns := evenColumns curve jet
  vectorOfFn fun position => sumFin fun index => coordinates index * retainedColumns index position

/-- The assembled coordinate reads the actual retained column cache with the original finite weights. -/
theorem evenCombination_apply (curve : HyperellipticCurve genus) (jet : Jet curve)
    (coordinates : Purelib.Data.Vector Canonical (2 * genus)) (position : Fin (2 * genus + 1)) :
    evenCombination curve jet coordinates position =
      sumFin (fun index => coordinates index * evenColumn curve jet index position) := by
  rewrite [evenCombination, vectorOfFn_apply]
  apply sumFin_congr
  intro index
  rewrite [evenColumns_apply]
  rfl

/-- Nonpivot readback of the retained combination recovers its original coefficient vector. -/
theorem evenCombination_coordinate (curve : HyperellipticCurve genus) (jet : Jet curve)
    (coordinates : Purelib.Data.Vector Canonical (2 * genus)) (position : Fin (2 * genus)) :
    evenCombination curve jet coordinates (nonpivot position) = coordinates position := by
  rewrite [evenCombination_apply]
  calc
    _ = sumFin (fun index => if index = position then coordinates index else 0) := by
      apply sumFin_congr
      intro index
      rewrite [evenColumn_coordinate]
      by_cases same : index = position
      · subst index
        rewrite [if_pos rfl, if_pos rfl]
        exact Gaussian.Basic.mul_one _
      · rewrite [if_neg same, if_neg (Ne.symm same)]
        exact Gaussian.Basic.mul_zero _
    _ = _ := sumFin_ite_eq position coordinates

/-- All retained linear combinations satisfy the computed infinity coefficient constraint. -/
theorem evenCombination_zero (curve : HyperellipticCurve genus) (jet : Jet curve)
    (coordinates : Purelib.Data.Vector Canonical (2 * genus)) :
    evenFunctional curve jet (evenCombination curve jet coordinates) = 0 := by
  unfold evenFunctional Weighted.weighted
  calc
    _ = sumFin (fun position => sumFin (fun index =>
        coordinates index * (evenWeights curve jet position * evenColumn curve jet index position))) := by
      apply sumFin_congr
      intro position
      rewrite [evenCombination_apply]
      exact (sumFin_mul_left _ _).symm.trans (sumFin_congr (fun index => by ring1))
    _ = sumFin (fun index => coordinates index *
        sumFin (fun position => evenWeights curve jet position * evenColumn curve jet index position)) :=
      (sumFin_swap _).trans (sumFin_congr (fun _ => sumFin_mul_left _ _))
    _ = 0 := by
      apply (sumFin_congr (fun index => ?_)).trans FiniteSum.Fin.sumFin_zero
      change coordinates index * evenFunctional curve jet (evenColumn curve jet index) = 0
      rewrite [evenColumn_zero]
      exact Gaussian.Basic.mul_zero _

/-- The corrected columns are linearly independent as finite coefficient vectors.

The statement is coefficient independence, with exact recovery at every
nonpivot coordinate; independence modulo arbitrary rational exact forms is separate. -/
theorem evenCombination_injective (curve : HyperellipticCurve genus) (jet : Jet curve)
    {left right : Purelib.Data.Vector Canonical (2 * genus)}
    (same : evenCombination curve jet left = evenCombination curve jet right) : left = right := by
  apply Purelib.Data.Vector.Basic.vector_ext
  intro index
  have selected := congrArg
    (fun values : Purelib.Data.Vector Canonical (2 * genus + 1) => values (nonpivot index)) same
  rewrite [evenCombination_coordinate, evenCombination_coordinate] at selected
  exact selected

/-- Read all original nonpivot entries once into the complete finite coefficient vector. -/
@[expose] def evenCoordinates (numerator : Purelib.Data.Vector Canonical (2 * genus + 1)) :
    Purelib.Data.Vector Canonical (2 * genus) := vectorOfFn fun index => numerator (nonpivot index)

/-- Every numerator satisfying the finite constraint is spanned by the actual corrected columns.

The original numerator and cached jet determine the coefficient vector. The
unit pivot weight and identical remaining entries identify complete vectors. -/
theorem evenCombination_coordinates (curve : HyperellipticCurve genus) (jet : Jet curve)
    (numerator : Purelib.Data.Vector Canonical (2 * genus + 1)) (zero : evenFunctional curve jet numerator = 0) :
    evenCombination curve jet (evenCoordinates numerator) = numerator := by
  apply Weighted.eq_of_weighted_eq_of_other (evenWeights curve jet) _ _ (pivot genus)
    (evenWeights_pivot curve jet)
  · exact (evenCombination_zero curve jet _).trans zero.symm
  · intro position different
    have readback := evenCombination_coordinate curve jet (evenCoordinates numerator)
      (nonpivotIndex position different)
    rewrite [nonpivot_nonpivotIndex] at readback
    rewrite [evenCoordinates, vectorOfFn_apply, nonpivot_nonpivotIndex] at readback
    exact readback

/-- The exact finite outcomes for decomposing one original numerator.

Success retains the computed bounded coefficients and complete original
vector identity. Obstruction retains the actual nonzero computed functional
value, linked to the same original curve, jet and numerator. -/
abbrev EvenDecomposition (curve : HyperellipticCurve genus) (jet : Jet curve)
    (numerator : Purelib.Data.Vector Canonical (2 * genus + 1)) :=
  ({ coordinates : Purelib.Data.Vector Canonical (2 * genus) //
      evenCombination curve jet coordinates = numerator } ⊕
    { obstruction : Canonical // obstruction = evenFunctional curve jet numerator ∧ obstruction ≠ 0 })

/-- Compute coefficient spanning or its exact original infinity-functional obstruction.

The actual functional is computed once and compared with zero. No successful
decomposition or zero-functional certificate is requested from the caller.
An obstruction concerns this finite constraint, not global curve invalidity. -/
@[expose] def decomposeEven (curve : HyperellipticCurve genus) (jet : Jet curve)
    (numerator : Purelib.Data.Vector Canonical (2 * genus + 1)) : EvenDecomposition curve jet numerator :=
  let retained := evenFunctional curve jet numerator
  if zero : retained = 0 then
    .inl ⟨evenCoordinates numerator, evenCombination_coordinates curve jet numerator zero⟩
  else .inr ⟨retained, rfl, zero⟩

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.InfinityCoefficients
end
