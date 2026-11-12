module

public import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Polynomial.Dense.Gaussian.Factorization.Identity
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Tactic.Ring

/-! # Inverse models for an original polynomial factor

If q=f*g, the actual inverse models A of q and B of g give the polynomial
g*B*A for the inverse of f. Its residual is rho_q+rho_g-rho_q*rho_g on the
original common box. Both old model caches remain inputs; no inverse or
root observation is acquired and no channel or sheet relation is assumed.
-/

public section

namespace Purelib.Riemann.Normalization.InverseRootPolynomial.Model

open Purelib
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Polynomial.Dense.Gaussian.Factorization
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction
open Purelib.Data.Rat.Fraction.Order
open Purelib.Approximation.Rational.Geometric.Basic

variable {source factor cofactor : Polynomial} {sourceBox cofactorBox common : Box}

/-- Every actual later refinement preserves the original nonnegative residual ceiling. -/
theorem refine_bound_le (model : Model source sourceBox) (index : Nat) : (model.refine index).bound ≤ model.bound :=
  (model.refine_bound index).trans_le (quarterRadius_le_scale model.bound_nonnegative index)

/-- An actual refinement at stage at least two has residual ceiling at most1/256. -/
theorem refine_bound_small_two (model : Model source sourceBox) (index : Nat) (later : 2 ≤ index) :
    (model.refine index).bound ≤ 1 / 256 := by
  have stage := quarterRadius_antitone model.bound_nonnegative later
  have initial := quarterRadius_scale_mono model.bound_small 2
  have closed : quarterRadius (1 / 16 : Coordinate) 2 = 1 / 256 := by decide +kernel
  exact (model.refine_bound index).trans_le (stage.trans (initial.trans_eq closed))

/-- The actual two residual ceilings give the retained finite product-factor error ceiling. -/
def factorBound (first : Model source sourceBox) (second : Model cofactor cofactorBox) : Coordinate :=
  2 * first.bound + 4 * second.bound + 4 * first.bound * second.bound

/-- The original model residual ceilings make the factor ceiling nonnegative. -/
private theorem packaged_factorBound_nonnegative
    (first : Model source sourceBox) (second : Model cofactor cofactorBox) : 0 ≤ factorBound first second := by
  have left := Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Coordinate) ≤ 2) first.bound_nonnegative
  have right := Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Coordinate) ≤ 4) second.bound_nonnegative
  have product := Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Coordinate) ≤ 4) first.bound_nonnegative)
    second.bound_nonnegative
  have sum := Arithmetic.add_le_add_direct (Arithmetic.add_le_add_direct left right) product
  unfold factorBound
  simpa only [Field.zero_add] using sum

/-- The original model residual ceilings make the factor ceiling nonnegative. -/
theorem factorBound_nonnegative
    (first : Model source sourceBox) (second : Model cofactor cofactorBox) : 0 ≤ factorBound first second :=
  packaged_factorBound_nonnegative first second

/-- Two retained ceilings of at most1/256 pay the original model's required1/16 ceiling. -/
private theorem packaged_factorBound_small
    (first : Model source sourceBox) (second : Model cofactor cofactorBox)
    (firstSmall : first.bound ≤ 1 / 256) (secondSmall : second.bound ≤ 1 / 256) :
    factorBound first second ≤ 1 / 16 := by
  have left := Arithmetic.mul_le_mul_of_nonneg_left_direct firstSmall (by decide +kernel : (0 : Coordinate) ≤ 2)
  have right := Arithmetic.mul_le_mul_of_nonneg_left_direct secondSmall (by decide +kernel : (0 : Coordinate) ≤ 4)
  have pair := Arithmetic.mul_le_mul_direct firstSmall secondSmall second.bound_nonnegative
    (by decide +kernel : (0 : Coordinate) ≤ 1 / 256)
  have product := Arithmetic.mul_le_mul_of_nonneg_left_direct pair (by decide +kernel : (0 : Coordinate) ≤ 4)
  have sum := Arithmetic.add_le_add_direct (Arithmetic.add_le_add_direct left right) product
  unfold factorBound
  calc
    _ = 2 * first.bound + 4 * second.bound + 4 * (first.bound * second.bound) := by ring1
    _ ≤ 2 * (1 / 256) + 4 * (1 / 256) + 4 * ((1 / 256) * (1 / 256)) := sum
    _ ≤ 1 / 16 := by decide +kernel

/-- Two retained ceilings of at most1/256 pay the original model's required1/16 ceiling. -/
theorem factorBound_small
    (first : Model source sourceBox) (second : Model cofactor cofactorBox)
    (firstSmall : first.bound ≤ 1 / 256) (secondSmall : second.bound ≤ 1 / 256) :
    factorBound first second ≤ 1 / 16 := packaged_factorBound_small first second firstSmall secondSmall

/-- The exact original factorization gives the combined inverse-model residual without selecting a root sign. -/
private theorem packaged_factorResidual_eq (identity : Identity.ProductIdentity source factor cofactor)
    (first : Model source sourceBox) (second : Model cofactor cofactorBox) (point : Gaussian) :
    (first.residual + second.residual - first.residual * second.residual).eval point =
      1 - factor.eval point * ((cofactor * second.value * first.value).eval point) ^ 2 := by
  rewrite [eval_sub, eval_add, eval_mul, first.residual_eq, second.residual_eq,
    eval_mul, eval_mul, Identity.eval_factorization identity point]
  ring1

/-- The exact original factorization gives the combined inverse-model residual without selecting a root sign. -/
theorem factorResidual_eq (identity : Identity.ProductIdentity source factor cofactor)
    (first : Model source sourceBox) (second : Model cofactor cofactorBox) (point : Gaussian) :
    (first.residual + second.residual - first.residual * second.residual).eval point =
      1 - factor.eval point * ((cofactor * second.value * first.value).eval point) ^ 2 :=
  packaged_factorResidual_eq identity first second point

/-- Both original domain refinements retain the actual finite residual bound on the same common box. -/
private theorem packaged_factorResidual_bound
    (first : Model source sourceBox) (second : Model cofactor cofactorBox)
    (inFirst : common.Refines sourceBox) (inSecond : common.Refines cofactorBox)
    (point : Gaussian) (inside : common.Contains point) :
    Norm.Basic.normSq ((first.residual + second.residual - first.residual * second.residual).eval point) ≤
      factorBound first second := by
  have firstBound : Norm.Basic.normSq (first.residual.eval point) ≤ first.bound :=
    (Norm.Basic.normSq_eq_canonical _).trans_le (first.residualBound point (inFirst.contains inside))
  have secondBound : Norm.Basic.normSq (second.residual.eval point) ≤ second.bound :=
    (Norm.Basic.normSq_eq_canonical _).trans_le (second.residualBound point (inSecond.contains inside))
  have product := Arithmetic.mul_le_mul_direct firstBound secondBound (Norm.Basic.normSq_nonneg _)
    first.bound_nonnegative
  have productBound := (Norm.Basic.normSq_mul _ _).trans_le product
  have subtract := Norm.Bounds.normSq_sub_le_two (second.residual.eval point)
    (first.residual.eval point * second.residual.eval point)
  have subtraction := subtract.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct secondBound productBound) (by decide +kernel : (0 : Coordinate) ≤ 2))
  have add := Norm.Bounds.normSq_add_le_two (first.residual.eval point)
    (second.residual.eval point - first.residual.eval point * second.residual.eval point)
  have all := add.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct firstBound subtraction) (by decide +kernel : (0 : Coordinate) ≤ 2))
  have scalar : (first.residual + second.residual - first.residual * second.residual).eval point =
      first.residual.eval point +
        (second.residual.eval point - first.residual.eval point * second.residual.eval point) := by
    rewrite [eval_sub, eval_add, eval_mul]
    ring1
  exact (congrArg Norm.Basic.normSq scalar).trans_le (all.trans_eq (by unfold factorBound; ring1))

/-- Both original domain refinements retain the actual finite residual bound on the same common box. -/
theorem factorResidual_bound
    (first : Model source sourceBox) (second : Model cofactor cofactorBox)
    (inFirst : common.Refines sourceBox) (inSecond : common.Refines cofactorBox)
    (point : Gaussian) (inside : common.Contains point) :
    Norm.Basic.normSq ((first.residual + second.residual - first.residual * second.residual).eval point) ≤
      factorBound first second := packaged_factorResidual_bound first second inFirst inSecond point inside

/-- Construct the original inverse model of a polynomial factor from the two actual supplied model caches.

The factorization, two domain refinements and two actual finite ceilings
are the full prerequisites. The output stores the actual cofactor*B*A
polynomial, actual combined residual and derived bound; it supplies no new
root-channel equivalence or sheet identification.
-/
def ofFactors (identity : Identity.ProductIdentity source factor cofactor)
    (first : Model source sourceBox) (second : Model cofactor cofactorBox)
    (inFirst : common.Refines sourceBox) (inSecond : common.Refines cofactorBox)
    (firstSmall : first.bound ≤ 1 / 256) (secondSmall : second.bound ≤ 1 / 256) : Model factor common :=
  let value := cofactor * second.value * first.value
  let residual := first.residual + second.residual - first.residual * second.residual
  let bound := factorBound first second
  ⟨value, residual, factorResidual_eq identity first second, bound, factorBound_nonnegative first second,
    factorBound_small first second firstSmall secondSmall, (fun point inside =>
      (Norm.Basic.normSq_eq_canonical (residual.eval point)).symm.trans_le
        (factorResidual_bound (common := common) first second inFirst inSecond point inside))⟩

/-- The whole original Model factory contains exactly the derived value, residual and bound with their owned laws. -/
private theorem packaged_ofFactors_factory (identity : Identity.ProductIdentity source factor cofactor)
    (first : Model source sourceBox) (second : Model cofactor cofactorBox)
    (inFirst : common.Refines sourceBox) (inSecond : common.Refines cofactorBox)
    (firstSmall : first.bound ≤ 1 / 256) (secondSmall : second.bound ≤ 1 / 256) :
    ofFactors identity first second inFirst inSecond firstSmall secondSmall =
      (let value := cofactor * second.value * first.value
       let residual := first.residual + second.residual - first.residual * second.residual
       let bound := factorBound first second
       ⟨value, residual, factorResidual_eq identity first second, bound, factorBound_nonnegative first second,
         factorBound_small first second firstSmall secondSmall,
         (fun point inside =>
           (Norm.Basic.normSq_eq_canonical (residual.eval point)).symm.trans_le
             (factorResidual_bound (common := common) first second inFirst inSecond point inside))⟩ :
        Model factor common) := by rfl

/-- The whole original Model factory contains exactly the derived value, residual and bound with their owned laws. -/
theorem ofFactors_factory (identity : Identity.ProductIdentity source factor cofactor)
    (first : Model source sourceBox) (second : Model cofactor cofactorBox)
    (inFirst : common.Refines sourceBox) (inSecond : common.Refines cofactorBox)
    (firstSmall : first.bound ≤ 1 / 256) (secondSmall : second.bound ≤ 1 / 256) :
    ofFactors identity first second inFirst inSecond firstSmall secondSmall =
      (let value := cofactor * second.value * first.value
       let residual := first.residual + second.residual - first.residual * second.residual
       let bound := factorBound first second
       ⟨value, residual, factorResidual_eq identity first second, bound, factorBound_nonnegative first second,
         factorBound_small first second firstSmall secondSmall,
         (fun point inside =>
           (Norm.Basic.normSq_eq_canonical (residual.eval point)).symm.trans_le
             (factorResidual_bound (common := common) first second inFirst inSecond point inside))⟩ :
        Model factor common) :=
  packaged_ofFactors_factory identity first second inFirst inSecond firstSmall secondSmall

end Purelib.Riemann.Normalization.InverseRootPolynomial.Model

end
