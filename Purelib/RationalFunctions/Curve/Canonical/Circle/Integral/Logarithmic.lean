module

public import Purelib.RationalFunctions.Curve.Canonical.Circle.Integral
public import Purelib.RationalFunctions.Curve.Canonical.Circle.Integral.Dyadic
import Purelib.Polynomial.Ascending.Gaussian.Antiderivative.Taylor
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Integration.CertifiedProgram.Comparison
public import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Integration.Program.Comparison
import Purelib.Integration.Program.Gaussian.Name
import Purelib.Integration.Polynomial.Gaussian.Path.Concatenation
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Tactic.Ring

/-! # Comparing actual dyadic dw/w samples with the retained logarithmic polynomial programme -/

public section

namespace Purelib.RationalFunctions.Curve.Canonical.Circle.Integral.Logarithmic

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Polynomial
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Geometry.Gaussian.UnitCircle
open Purelib.Riemann.Branches.ClearSheetContinuation
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Algebra.Field
open Purelib.Integration
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Rational.Geometric

variable {base : Canonical}

/-- A retained parameter endpoint lies in the original real parameter box. -/
private theorem endpoint_inside (endpoint : Endpoint) :
    parameterAmbient.Contains (⟨endpoint.parameter, 0⟩ : Canonical) :=
  ⟨endpoint.inside.1, endpoint.inside.2, Fraction.Order.Basic.le_refl _, Fraction.Order.Basic.le_refl _⟩

/-- The actual logarithmic constant cell is bounded by the supplied polynomial primitive and original tangent error. -/
private theorem cell_error_le (nonzero : base ≠ 0)
    (actual : { value : RationalCurve // value = circle base }) (index : Nat)
    (source : { value : CoefficientPolynomial // value = Stereographic.Integral.polynomial (index + 4) })
    (primitive : { value : CoefficientPolynomial // value = Antiderivative.antiderivative source.val })
    (preparation : Antiderivative.BoxPreparation source.val primitive parameterAmbient)
    (first last : Endpoint) :
    Norm.Basic.normSq (Evaluation.eval primitive.val ⟨last.parameter, 0⟩ -
      Evaluation.eval primitive.val ⟨first.parameter, 0⟩ -
        (coefficientCell base actual (fun point => point⁻¹) first.parameter
          (last.parameter - first.parameter)).integralSample) ≤
      (2 * preparation.1.val.remainderBound) * (last.parameter - first.parameter) ^ 4 +
        (2 * Stereographic.Integral.allowance index) * (last.parameter - first.parameter) ^ 2 := by
  let certificate := preparation.1.val.quadraticCertificate
    ⟨first.parameter, 0⟩ ⟨last.parameter, 0⟩ (endpoint_inside first) (endpoint_inside last)
  let coefficient := velocity base first.parameter * (actual.val.point first.parameter)⁻¹
  have primitiveValue (point : Canonical) :
      preparation.1.val.value.eval point = Evaluation.eval primitive.val point := by
    rewrite [preparation.1.property, Antiderivative.inBox_value,
      Ascending.Gaussian.Dense.Evaluation.toDense_eval]
    rfl
  have displacement : (coefficientCell base actual (fun point => point⁻¹) first.parameter
      (last.parameter - first.parameter)).displacement =
        (⟨last.parameter, 0⟩ : Canonical) - ⟨first.parameter, 0⟩ := by
    rewrite [coefficientCell_displacement]
    apply Data.Gaussian.Basic.ext
    · rfl
    · change (0 : Fraction.Rational) = 0 - 0
      ring1
  have original := CellModel.quadratic_integral_error_le certificate
    (coefficientCell base actual (fun point => point⁻¹) first.parameter (last.parameter - first.parameter))
    coefficient displacement rfl
  have square : Norm.Basic.normSq ((⟨last.parameter, 0⟩ : Canonical) - ⟨first.parameter, 0⟩) =
      (last.parameter - first.parameter) ^ 2 := by
    change (last.parameter - first.parameter) ^ 2 + (0 - 0 : Fraction.Rational) ^ 2 = _
    ring1
  have coefficientEq : coefficient = logarithmicVelocity base first.parameter actual := by
    unfold coefficient logarithmicVelocity
    rewrite [ExplicitField.div_eq_mul_inv]
    rfl
  have discrepancy : Norm.Basic.normSq
      (Evaluation.eval source.val ⟨first.parameter, 0⟩ - coefficient) ≤ Stereographic.Integral.allowance index := by
    rewrite [coefficientEq, logarithmicVelocity_eq base nonzero first.parameter actual, source.property]
    exact Stereographic.Integral.stage_error_le index first.parameter first.inside.1 first.inside.2
  change Norm.Basic.normSq (preparation.1.val.value.eval ⟨last.parameter, 0⟩ -
    preparation.1.val.value.eval ⟨first.parameter, 0⟩ - _) ≤
      2 * (preparation.1.val.remainderBound *
        Norm.Basic.normSq ((⟨last.parameter, 0⟩ : Canonical) - ⟨first.parameter, 0⟩) ^ 2 +
          Norm.Basic.normSq ((⟨last.parameter, 0⟩ : Canonical) - ⟨first.parameter, 0⟩) *
            Norm.Basic.normSq ((Dense.Evaluation.toDense source.val).eval
              ⟨first.parameter, 0⟩ - coefficient)) at original
  rewrite [primitiveValue, primitiveValue, square, Ascending.Gaussian.Dense.Evaluation.toDense_eval] at original
  have paid := Arithmetic.mul_le_mul_of_nonneg_left_direct discrepancy
    (Arithmetic.sq_nonneg_direct (last.parameter - first.parameter))
  have enlarged := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl
      (preparation.1.val.remainderBound * ((last.parameter - first.parameter) ^ 2) ^ 2)) paid)
    (by decide +kernel : (0 : Fraction.Rational) ≤ 2)
  exact original.trans (enlarged.trans_eq (by ring1))

/-- The actual dyadic dw/w sample is compared with the original retained logarithmic polynomial sample.

The supplied polynomial, antiderivative and boxed preparation are consumed
at every original edge. Its finite Taylor term shrinks with the dyadic
mesh; the independently paid Cayley approximation contributes its separate
original stage allowance. Neither programme's samples are identified by
winding or by an assumed integral comparison.
-/
theorem sample_error_le (nonzero : base ≠ 0)
    (actual : { value : RationalCurve // value = circle base }) (index : Nat)
    (source : { value : CoefficientPolynomial // value = Stereographic.Integral.polynomial (index + 4) })
    (primitive : { value : CoefficientPolynomial // value = Antiderivative.antiderivative source.val })
    (preparation : Antiderivative.BoxPreparation source.val primitive parameterAmbient) (depth : Nat) :
    Norm.Basic.normSq
      ((Dyadic.model base actual (fun point => point⁻¹) depth
        ⟨0, by decide +kernel⟩ ⟨1, by decide +kernel⟩).integralSample -
        ((program base nonzero actual).model index).integralSample) ≤
      quarterRadius (2 * preparation.1.val.remainderBound) depth + 2 * Stereographic.Integral.allowance index := by
  have bounded := Dyadic.model_primitive_error_le base actual (fun point => point⁻¹)
    (fun time => Evaluation.eval primitive.val ⟨time, 0⟩) (2 * preparation.1.val.remainderBound)
    (2 * Stereographic.Integral.allowance index) (cell_error_le nonzero actual index source primitive preparation)
    depth ⟨0, by decide +kernel⟩ ⟨1, by decide +kernel⟩
  have endpoint : Evaluation.eval primitive.val 1 - Evaluation.eval primitive.val 0 =
      ((program base nonzero actual).model index).integralSample := by
    rewrite [program_sample]
    change Evaluation.eval primitive.val 1 - Evaluation.eval primitive.val 0 =
      (Stereographic.Integral.model index).integralSample
    rewrite [Stereographic.Integral.model_integralSample, primitive.property, source.property]
    rfl
  change Norm.Basic.normSq (Evaluation.eval primitive.val 1 - Evaluation.eval primitive.val 0 - _) ≤ _ at bounded
  rewrite [endpoint, Norm.Bounds.normSq_sub_symm] at bounded
  exact bounded.trans_eq (by
    change (2 * preparation.1.val.remainderBound) * ((1 : Fraction.Rational) - 0) ^ 2 *
      quarterRadius (((1 : Fraction.Rational) - 0) ^ 2) depth +
        (2 * Stereographic.Integral.allowance index) * ((1 : Fraction.Rational) - 0) ^ 2 = _
    rewrite [show ((1 : Fraction.Rational) - 0) ^ 2 = 1 by decide +kernel,
      Fraction.Field.mul_one_direct, Fraction.Field.mul_one_direct,
      Purelib.Approximation.Rational.Geometric.Basic.quarterRadius_eq_mul_pow,
      Purelib.Approximation.Rational.Geometric.Basic.quarterRadius_eq_mul_pow]
    ring1)

/-- The genuine four-quarter logarithmic mesh is bounded against the same supplied original circuit sample.

One supplied polynomial primitive and one actual boxed Taylor ceiling are
shared by all four quarter comparisons. The finite balanced sum retains
its factor sixteen; the original Cayley allowance remains separate.
-/
theorem model_error_le {nonzero : base ≠ 0} (circuit : Circuit base nonzero) (index : Nat)
    (source : { value : CoefficientPolynomial // value = Stereographic.Integral.polynomial (index + 4) })
    (primitive : { value : CoefficientPolynomial // value = Antiderivative.antiderivative source.val })
    (preparation : Antiderivative.BoxPreparation source.val primitive parameterAmbient) (depth : Nat) :
    Norm.Basic.normSq ((circuit.1.dyadicModel (fun point => point⁻¹) depth).integralSample -
      (circuit.2.val.model index).integralSample) ≤
      quarterRadius (32 * preparation.1.val.remainderBound) depth + 32 * Stereographic.Integral.allowance index := by
  let error := quarterRadius (2 * preparation.1.val.remainderBound) depth +
    2 * Stereographic.Integral.allowance index
  let first := fun quarter : Fin quarters.length =>
    (Dyadic.model (quarterBase base (quarters[quarter.val]'quarter.isLt)) (circuit.1.get quarter).1
      (fun point => point⁻¹) depth ⟨0, by decide +kernel⟩ ⟨1, by decide +kernel⟩).integralSample
  let last := fun quarter : Fin quarters.length => ((circuit.1.get quarter).2.val.model index).integralSample
  have close (quarter : Fin quarters.length) : Norm.Basic.normSq (first quarter - last quarter) ≤ error := by
    have original := sample_error_le (quarterBase_ne_zero base nonzero (quarters[quarter.val]'quarter.isLt))
      (circuit.1.get quarter).1 index source primitive preparation depth
    rewrite [← (circuit.1.get quarter).2.property] at original
    exact original
  have pair {first last third fourth : Canonical}
      (earlier : Norm.Basic.normSq (first - third) ≤ error)
      (later : Norm.Basic.normSq (last - fourth) ≤ error) :
      Norm.Basic.normSq ((first + last) - (third + fourth)) ≤ 4 * error :=
    (Norm.Bounds.normSq_add_sub_add_le first last third fourth).trans
      ((Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct earlier later)
        (by decide +kernel : (0 : Fraction.Rational) ≤ 2)).trans_eq (by ring1))
  have earlier := pair (close ⟨0, by decide +kernel⟩) (close ⟨1, by decide +kernel⟩)
  have later := pair (close ⟨2, by decide +kernel⟩) (close ⟨3, by decide +kernel⟩)
  have whole := (Norm.Bounds.normSq_add_sub_add_le
    (first ⟨0, by decide +kernel⟩ + first ⟨1, by decide +kernel⟩)
    (first ⟨2, by decide +kernel⟩ + first ⟨3, by decide +kernel⟩)
    (last ⟨0, by decide +kernel⟩ + last ⟨1, by decide +kernel⟩)
    (last ⟨2, by decide +kernel⟩ + last ⟨3, by decide +kernel⟩)).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct earlier later) (by decide +kernel))
  unfold Entries.dyadicModel
  rewrite [circuit.2.property, Entries.concatenate_model,
    PathModel.integralSample_concat,
    PathModel.integralSample_concat,
    PathModel.integralSample_concat,
    PathModel.integralSample_concat,
    PathModel.integralSample_concat,
    PathModel.integralSample_concat]
  exact whole.trans_eq (by
    dsimp only [error]
    rewrite [Purelib.Approximation.Rational.Geometric.Basic.quarterRadius_eq_mul_pow,
      Purelib.Approximation.Rational.Geometric.Basic.quarterRadius_eq_mul_pow]
    ring1)

/-- An original four-quarter logarithmic path model with its actual retained dyadic depth and producer identity. -/
abbrev Model {nonzero : base ≠ 0} (circuit : Circuit base nonzero) :=
  (depth : Nat) × { value : PathModel // value = circuit.1.dyadicModel (fun point => point⁻¹) depth }

/-- Read the original sample and allowance from the same actual retained four-quarter model. -/
def operations {nonzero : base ≠ 0} (circuit : Circuit base nonzero) :
    CertifiedProgram.ModelOperations (Model circuit) where
  sample cached := cached.2.val.integralSample
  allowance cached := cached.2.val.aggregateAllowance

/-- The sample operation consumes the retained original path directly. -/
theorem operations_sample {nonzero : base ≠ 0} (circuit : Circuit base nonzero) (cached : Model circuit) :
    (operations circuit).sample cached = cached.2.val.integralSample := by unfold operations; rfl

/-- The allowance operation consumes that same retained original path. -/
theorem operations_allowance {nonzero : base ≠ 0} (circuit : Circuit base nonzero) (cached : Model circuit) :
    (operations circuit).allowance cached = cached.2.val.aggregateAllowance := by unfold operations; rfl

/-- Compute one actual polynomial calibration and pay one dyadic depth before constructing the original circle cells. -/
private def stage {nonzero : base ≠ 0} (circuit : Circuit base nonzero) (index : Nat) :
    CertifiedProgram.CachedModel (operations circuit) :=
  let source := Stereographic.Integral.polynomial (index + 4)
  let primitive : { value : CoefficientPolynomial // value = Antiderivative.antiderivative source } :=
    ⟨Antiderivative.antiderivative source, rfl⟩
  let preparation := Antiderivative.prepareInBox source primitive parameterAmbient
  let depth := Search.firstQuarterBelow (32 * preparation.1.val.remainderBound) index (quarterRadius 1 index)
  let actual := circuit.1.dyadicModel (fun point => point⁻¹) depth
  .canonical ⟨depth, ⟨actual, rfl⟩⟩

/-- The actual retained calibrated stage is geometrically close to the same original logarithmic circuit stage. -/
private theorem stage_distance {nonzero : base ≠ 0} (circuit : Circuit base nonzero) (index : Nat) :
    Norm.Basic.normSq ((stage circuit index).sample - (circuit.2.val.model index).integralSample) ≤
      quarterRadius (9 / 8) index := by
  let source : { value : CoefficientPolynomial // value = Stereographic.Integral.polynomial (index + 4) } :=
    ⟨Stereographic.Integral.polynomial (index + 4), rfl⟩
  let primitive : { value : CoefficientPolynomial // value = Antiderivative.antiderivative source.val } :=
    ⟨Antiderivative.antiderivative source.val, rfl⟩
  let preparation := Antiderivative.prepareInBox source.val primitive parameterAmbient
  let depth := Search.firstQuarterBelow (32 * preparation.1.val.remainderBound) index (quarterRadius 1 index)
  have nonnegative : 0 ≤ 32 * preparation.1.val.remainderBound :=
    Arithmetic.mul_nonneg_direct (by decide +kernel) preparation.1.val.remainderBound_nonnegative
  have paid := Search.firstQuarterBelow_accurate (32 * preparation.1.val.remainderBound) nonnegative index
    (quarterRadius 1 index) (Basic.quarterRadius_pos (by decide +kernel) index)
  have bounded := model_error_le circuit index source primitive preparation depth
  change Norm.Basic.normSq ((circuit.1.dyadicModel (fun point => point⁻¹) depth).integralSample -
    (circuit.2.val.model index).integralSample) ≤ _
  exact bounded.trans ((Arithmetic.add_le_add_direct paid.le
    (Fraction.Order.Basic.le_refl _)).trans_eq (by
      have scalar : (1 : Fraction.Rational) + 32 * (1 / 256) = 9 / 8 := by decide +kernel
      rewrite [← scalar]
      unfold Stereographic.Integral.allowance
      rewrite [Basic.quarterRadius_eq_mul_pow, Basic.quarterRadius_eq_mul_pow, Basic.quarterRadius_eq_mul_pow]
      ring1))

/-- Every calibrated original four-quarter model has zero actual allowance. -/
private theorem stage_allowance {nonzero : base ≠ 0} (circuit : Circuit base nonzero) (index : Nat) :
    (stage circuit index).allowance = 0 := by
  unfold stage
  change (circuit.1.dyadicModel (fun point => point⁻¹) _).aggregateAllowance = 0
  exact circuit.1.dyadicModel_allowance (fun point => point⁻¹) _

/-- Construct the actual dyadic dw/w programme and compare its output with the retained logarithmic circuit.

Each stage computes one finite polynomial, one original antiderivative and
one original boxed preparation. Its chosen mesh depth pays that actual
Taylor ceiling before materializing four same-curve dyadic paths. The
original circuit's Cauchy and center certificates derive the new programme
and its executable comparison with the same actual logarithmic channel.
-/
def program {nonzero : base ≠ 0} (circuit : Circuit base nonzero) :
    (dyadic : CertifiedProgram.Program (operations circuit)) ×
      NamedEquivalent circuit.channel.name dyadic.output.name := by
  let reference := circuit.2.val.certifiedView.program
  let produced := stage circuit
  have positive : 0 ≤ (9 / 8 : Fraction.Rational) := by decide +kernel
  have distance (index : Nat) : Norm.Basic.normSq ((produced index).sample - (reference.stage index).sample) ≤
      quarterRadius (9 / 8) index := stage_distance circuit index
  have allowances : CertifiedProgram.Allowances produced (reference.perturbationScale (9 / 8)) := by
    intro index
    rewrite [stage_allowance]
    exact Basic.quarterRadius_nonneg (reference.perturbationScale_nonnegative (9 / 8) positive) index
  let changed := reference.perturb produced (9 / 8) positive distance allowances
  have close (index : Nat) : Norm.Basic.normSq ((reference.stage index).sample - (changed.stage index).sample) ≤
      quarterRadius (9 / 8) index := by
    have cacheEq := CertifiedProgram.Program.perturb_stage reference produced (9 / 8) positive distance allowances index
    have sampleEq := congrArg (fun value => value.sample) cacheEq
    exact (congrArg (fun value => Norm.Basic.normSq ((reference.stage index).sample - value)) sampleEq).trans_le
      ((Norm.Bounds.normSq_sub_symm _ _).trans_le (distance index))
  let compared := reference.output_equivalent_of_samples_close changed (9 / 8) positive close
  have original : NamedEquivalent circuit.channel.name reference.output.name :=
    (Integration.Program.Comparison.output_equivalent_geometric circuit.2.val).symm
  exact ⟨changed, original.trans compared⟩

/-- Every actual calibrated logarithmic stage retains a dyadic depth above its original requested stage. -/
theorem program_depth_ge {nonzero : base ≠ 0} (circuit : Circuit base nonzero) (index : Nat) :
    index ≤ (((program circuit).1.stage index).model.1) := by
  unfold program
  rewrite [CertifiedProgram.Program.perturb_stage]
  unfold stage
  exact Search.firstQuarterBelow_ge _ _ _

end Purelib.RationalFunctions.Curve.Canonical.Circle.Integral.Logarithmic

end
