module

public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Continued
public import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Comparison
import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Tactic.Ring

/-! # Uniform polynomial cells from original ordinary primitive requests

A retained uniform request selects an inverse-model depth before the same
numerator is compiled on an actual segment. Original continued Points are
supplied to observation construction; only their new requested root readings
are refined. Whole-model and integral laws preserve the original cache owners.
-/

public section

namespace Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.UniformRequest

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients)
open Purelib.Algebra.Quadratic.Pair.Gaussian (ReadingPrecision)
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell)
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Polynomial.Dense.Power (OddPowers)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Model)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point

variable {genus count floor : Nat} {curve : HyperellipticCurve genus}
    {differential : OddPowerDifferential curve.polynomial}
    {patch : ContinuedNeighborhood curve.polynomial count} {bounds : UniformBounds patch}
    {start finish : Canonical} {allowance : Rational}

/-- The original request's cached ceiling bounds its actual numerator throughout the same continued box. -/
theorem numerator_le {pairs : Fin 3} {numerator : Coefficients} {target : Rational}
    (request : UniformRequest bounds pairs numerator floor target) (point : Canonical)
    (inside : patch.box.Contains point) : Norm.Basic.normSq (numerator.eval point) ≤ request.numeratorUpper := by
  have bounded := Polynomial.Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormBound numerator inside
  exact bounded.trans_eq request.numeratorUpper_eq.symm

/-- Retarget the same numerator-wide ceiling and residual scale with one new finite selection.

Only the original selection is executed. The complete numerator ceiling,
scale, neighborhood and odd-power indices are retained from the supplied request.
-/
def retarget {pairs : Fin 3} {numerator : Coefficients} {target : Rational}
    (request : UniformRequest bounds pairs numerator floor target) (nextFloor : Nat)
    (nextTarget : Rational) (positive : 0 < nextTarget) :
    UniformRequest bounds pairs numerator nextFloor nextTarget :=
  let selection := Approximation.Rational.Geometric.Search.Selection.build request.scale
    request.selection.scaleNonnegative nextFloor nextTarget positive
  ⟨request.numeratorUpper, request.numeratorUpper_eq, request.scale, request.scale_eq, selection⟩

/-- Retargeting consumes the same complete scalar caches before the one new selection. -/
private theorem packaged_retarget_factory {pairs : Fin 3} {numerator : Coefficients} {target : Rational}
    (request : UniformRequest bounds pairs numerator floor target) (nextFloor : Nat)
    (nextTarget : Rational) (positive : 0 < nextTarget) :
    request.retarget nextFloor nextTarget positive =
      let selection := Approximation.Rational.Geometric.Search.Selection.build request.scale
        request.selection.scaleNonnegative nextFloor nextTarget positive
      ⟨request.numeratorUpper, request.numeratorUpper_eq, request.scale, request.scale_eq, selection⟩ := by rfl

/-- Retargeting consumes the same complete scalar caches before the one new selection. -/
theorem retarget_factory {pairs : Fin 3} {numerator : Coefficients} {target : Rational}
    (request : UniformRequest bounds pairs numerator floor target) (nextFloor : Nat)
    (nextTarget : Rational) (positive : 0 < nextTarget) :
    request.retarget nextFloor nextTarget positive =
      let selection := Approximation.Rational.Geometric.Search.Selection.build request.scale
        request.selection.scaleNonnegative nextFloor nextTarget positive
      ⟨request.numeratorUpper, request.numeratorUpper_eq, request.scale, request.scale_eq, selection⟩ :=
  packaged_retarget_factory request nextFloor nextTarget positive

/-- The ordered programme uses its original first request at zero and retargets only positive stages. -/
def atStage {pairs : Fin 3} {numerator : Coefficients}
    (request : UniformRequest bounds pairs numerator floor (quarterRadius 1 0 / 4)) :
    (stage : Nat) → UniformRequest bounds pairs numerator floor (quarterRadius 1 stage / 4)
  | 0 => request
  | stage + 1 => request.retarget floor (quarterRadius 1 (stage + 1) / 4)
      (Data.Rat.Fraction.Order.Field.div_pos_direct
        (quarterRadius_pos (by decide +kernel) _) (by decide +kernel))

/-- Stage zero retains the same complete originally selected request. -/
private theorem packaged_atStage_zero {pairs : Fin 3} {numerator : Coefficients}
    (request : UniformRequest bounds pairs numerator floor (quarterRadius 1 0 / 4)) :
    request.atStage 0 = request := by rfl

/-- Stage zero retains the same complete originally selected request. -/
theorem atStage_zero {pairs : Fin 3} {numerator : Coefficients}
    (request : UniformRequest bounds pairs numerator floor (quarterRadius 1 0 / 4)) :
    request.atStage 0 = request := packaged_atStage_zero request

/-- A positive stage performs exactly one retargeting with the same retained numerator ceiling and scale. -/
private theorem packaged_atStage_succ {pairs : Fin 3} {numerator : Coefficients}
    (request : UniformRequest bounds pairs numerator floor (quarterRadius 1 0 / 4)) (stage : Nat) :
    request.atStage (stage + 1) = request.retarget floor (quarterRadius 1 (stage + 1) / 4)
      (Data.Rat.Fraction.Order.Field.div_pos_direct
        (quarterRadius_pos (by decide +kernel) _) (by decide +kernel)) := by rfl

/-- A positive stage performs exactly one retargeting with the same retained numerator ceiling and scale. -/
theorem atStage_succ {pairs : Fin 3} {numerator : Coefficients}
    (request : UniformRequest bounds pairs numerator floor (quarterRadius 1 0 / 4)) (stage : Nat) :
    request.atStage (stage + 1) = request.retarget floor (quarterRadius 1 (stage + 1) / 4)
      (Data.Rat.Fraction.Order.Field.div_pos_direct
        (quarterRadius_pos (by decide +kernel) _) (by decide +kernel)) := packaged_atStage_succ request stage

/-- The original inverse, shared powers, primitive and pullback caches at one paid ordinary request.

The actual numerator is retained in the full spatial polynomial. Every
complete cache has its original factory equation, and no child constant
model or changed source coefficient process is substituted.
-/
@[expose] def PolynomialModel
    (request : UniformRequest bounds 0 (differential.numerator.scale differential.scale) floor (allowance / 4))
    (coordinate : Spatial.Coordinate start finish) (positive : 0 < allowance) : Type _ :=
  (inverse : { value : Model curve.polynomial patch.base.box //
    value = patch.base.refine request.selection.stage }) ×
  (_powers : { value : OddPowers inverse.val.value // value = OddPowers.build inverse.val.value }) ×
  (primitive : { value : PrimitiveModel patch request.selection.stage
    (differential.numerator.scale differential.scale) //
    value = PrimitiveModel.ofModel patch request.selection.stage
      (differential.numerator.scale differential.scale) inverse.val
      (congrArg (fun model => model.value) inverse.property) }) ×
  { pulled : Spatial.Pullback coordinate primitive.val.coefficient allowance //
    pulled = Spatial.Pullback.build coordinate primitive.val.coefficient allowance positive.le }

namespace PolynomialModel

variable {request : UniformRequest bounds 0 (differential.numerator.scale differential.scale) floor (allowance / 4)}
    {coordinate : Spatial.Coordinate start finish} {positive : 0 < allowance}

/-- Read the same selected original inverse polynomial from the retained cache. -/
@[expose] def inverse (retained : PolynomialModel (differential := differential) request coordinate positive) :
    Model curve.polynomial patch.base.box :=
  retained.1.val

/-- Read the original cached powers of that same inverse polynomial. -/
@[expose] def powers (retained : PolynomialModel (differential := differential) request coordinate positive) :
    OddPowers retained.inverse.value :=
  retained.2.1.val

/-- Read the complete numerator primitive at the actual retained request stage. -/
@[expose] def primitive (retained : PolynomialModel (differential := differential) request coordinate positive) :
    PrimitiveModel patch request.selection.stage (differential.numerator.scale differential.scale) :=
  retained.2.2.1.val

/-- Read the original spatial pullback consuming that retained primitive's coefficient table. -/
@[expose] def pullback (retained : PolynomialModel (differential := differential) request coordinate positive) :
    Spatial.Pullback coordinate retained.primitive.coefficient allowance := retained.2.2.2.val

/-- The retained inverse polynomial is the original selected neighborhood refinement. -/
theorem inverse_eq (retained : PolynomialModel (differential := differential) request coordinate positive) :
    retained.inverse = patch.base.refine request.selection.stage := retained.1.property

/-- The retained power cache is the original whole factory on the same inverse table. -/
theorem powers_eq (retained : PolynomialModel (differential := differential) request coordinate positive) :
    retained.powers = OddPowers.build retained.inverse.value := retained.2.1.property

/-- The retained primitive factory consumes the original cached inverse without repeating its refinement. -/
theorem primitive_eq (retained : PolynomialModel (differential := differential) request coordinate positive) :
    retained.primitive = PrimitiveModel.ofModel patch request.selection.stage
      (differential.numerator.scale differential.scale) retained.inverse
        (congrArg (fun model => model.value) retained.inverse_eq) :=
  retained.2.2.1.property

/-- The complete retained pullback is the original factory on the same coordinate and coefficient cache. -/
theorem pullback_eq (retained : PolynomialModel (differential := differential) request coordinate positive) :
    retained.pullback = Spatial.Pullback.build coordinate retained.primitive.coefficient allowance positive.le :=
  retained.2.2.2.property

/-- Build one polynomial cell after the original numerator-wide request has selected its actual model stage.

The inverse polynomial is computed once. The original powers and primitive
consume that cache, then the existing spatial pullback compiles its complete
coefficient polynomial once on the retained coordinate.
-/
def build
    (request : UniformRequest bounds 0 (differential.numerator.scale differential.scale) floor (allowance / 4))
    (coordinate : Spatial.Coordinate start finish) (positive : 0 < allowance) :
    PolynomialModel (differential := differential) request coordinate positive :=
  let inverse := patch.base.refine request.selection.stage
  let powers := OddPowers.build inverse.value
  let primitive := PrimitiveModel.ofModel patch request.selection.stage
    (differential.numerator.scale differential.scale) inverse rfl
  let pulled := Spatial.Pullback.build coordinate primitive.coefficient allowance positive.le
  ⟨⟨inverse, rfl⟩, ⟨powers, rfl⟩, ⟨primitive, rfl⟩, ⟨pulled, rfl⟩⟩

/-- The whole polynomial model preserves the original four factory values and their execution order. -/
private theorem packaged_build_factory
    (request : UniformRequest bounds 0 (differential.numerator.scale differential.scale) floor (allowance / 4))
    (coordinate : Spatial.Coordinate start finish) (positive : 0 < allowance) :
    build (differential := differential) request coordinate positive =
  let inverse := patch.base.refine request.selection.stage
  let powers := OddPowers.build inverse.value
  let primitive := PrimitiveModel.ofModel patch request.selection.stage
    (differential.numerator.scale differential.scale) inverse rfl
  let pulled := Spatial.Pullback.build coordinate primitive.coefficient allowance positive.le
  ⟨⟨inverse, rfl⟩, ⟨powers, rfl⟩, ⟨primitive, rfl⟩, ⟨pulled, rfl⟩⟩ := by rfl

/-- The whole polynomial model preserves the original four factory values and their execution order. -/
theorem build_factory
    (request : UniformRequest bounds 0 (differential.numerator.scale differential.scale) floor (allowance / 4))
    (coordinate : Spatial.Coordinate start finish) (positive : 0 < allowance) :
    build (differential := differential) request coordinate positive =
  let inverse := patch.base.refine request.selection.stage
  let powers := OddPowers.build inverse.value
  let primitive := PrimitiveModel.ofModel patch request.selection.stage
    (differential.numerator.scale differential.scale) inverse rfl
  let pulled := Spatial.Pullback.build coordinate primitive.coefficient allowance positive.le
  ⟨⟨inverse, rfl⟩, ⟨powers, rfl⟩, ⟨primitive, rfl⟩, ⟨pulled, rfl⟩⟩ :=
  packaged_build_factory request coordinate positive

/-- The actual retained integration sample is the exact primitive increment between the original ordered endpoints. -/
theorem integralSample_eq (retained : PolynomialModel (differential := differential) request coordinate positive) :
    retained.pullback.model.integralSample =
      retained.primitive.primitive.value.eval finish - retained.primitive.primitive.value.eval start :=
  retained.pullback.integralSample_primitive retained.primitive.primitive.value
    retained.primitive.primitive.derivative_eq

/-- The actual retained cell allowance has its original displacement weight and requested local scalar. -/
theorem weightedAllowance_eq (retained : PolynomialModel (differential := differential) request coordinate positive) :
    retained.pullback.model.weightedAllowance = Norm.Basic.normSq coordinate.displacement * allowance := by
  have original := retained.pullback.weightedAllowance_eq
  rewrite [← coordinate.displacement_eq, ← Norm.Basic.normSq_eq_canonical] at original
  exact original

/-- Answer one ordinary numerator query from the actual supplied Point and the retained polynomial cache.

The original Point is not acquired again. Its denotation, requested root
refinement and same-model reading are constructed once; the existing uniform
observation constructor pays both residual and reading radius internally.
-/
def observe {liftedStart liftedFinish : LiftedPoint 2}
    {coordinate : Spatial.Coordinate liftedStart.coordinate liftedFinish.coordinate}
    (retained : PolynomialModel (differential := differential) request coordinate positive)
    (ordinary : differential.denominatorPairs = 0) (lifted : LiftedCell liftedStart liftedFinish)
    (input : Rational) (sample : ContinuedNeighborhood.Point patch (coordinate.point input))
    (inside : patch.box.Contains (coordinate.point input)) :
    Jets.UniformObservation curve differential lifted retained.pullback.model input := by
  let localBounds := sample.primitiveBounds
  let factor := (differential.numerator.scale differential.scale).eval (coordinate.point input)
  let original := retainPrimitiveDenotation sample localBounds 0
    (differential.numerator.scale differential.scale) ⟨factor, rfl⟩
  let ceiling := Norm.Basic.normSq original.value.im
  let precision := ReadingPrecision.build ceiling allowance (Norm.Basic.normSq_nonneg _) positive
  let root := selectPrimitiveRoot sample request.selection.stage precision.target precision.target_positive
  let reading := root.readModel retained.inverse retained.inverse_eq retained.powers
  have compiled : retained.primitive.coefficient.eval (coordinate.point input) =
      (differential.numerator.scale differential.scale).eval (coordinate.point input) *
        (primitivePolynomial retained.powers 0).eval (coordinate.point input) := by
    change _ = _ * retained.inverse.value.eval (coordinate.point input)
    rewrite [retained.primitive.coefficient_eq, retained.inverse_eq]
    rfl
  let value := retainPrimitiveValue reading 0 (differential.numerator.scale differential.scale)
    original retained.primitive.coefficient compiled ⟨factor, rfl⟩
  exact Jets.UniformObservation.ofContinuedPrimitive curve differential 0 ordinary lifted retained.pullback input
    sample inside request retained.inverse_eq precision root reading rfl original value (Nat.le_refl _)
    (Data.Rat.Fraction.Order.Basic.le_refl _)

/-- The observation retains the supplied Point's original generator after its actual new requested refinement. -/
private theorem packaged_observe_root_name {liftedStart liftedFinish : LiftedPoint 2}
    {coordinate : Spatial.Coordinate liftedStart.coordinate liftedFinish.coordinate}
    (retained : PolynomialModel (differential := differential) request coordinate positive)
    (ordinary : differential.denominatorPairs = 0) (lifted : LiftedCell liftedStart liftedFinish)
    (input : Rational) (sample : ContinuedNeighborhood.Point patch (coordinate.point input))
    (inside : patch.box.Contains (coordinate.point input)) :
    (retained.observe ordinary lifted input sample inside).algebraic.sheetValue.value.name =
      sample.certificate.value.name := by
  unfold observe
  apply Jets.UniformObservation.ofContinuedPrimitive_root_name

/-- The observation retains the supplied Point's original generator after its actual new requested refinement. -/
theorem observe_root_name {liftedStart liftedFinish : LiftedPoint 2}
    {coordinate : Spatial.Coordinate liftedStart.coordinate liftedFinish.coordinate}
    (retained : PolynomialModel (differential := differential) request coordinate positive)
    (ordinary : differential.denominatorPairs = 0) (lifted : LiftedCell liftedStart liftedFinish)
    (input : Rational) (sample : ContinuedNeighborhood.Point patch (coordinate.point input))
    (inside : patch.box.Contains (coordinate.point input)) :
    (retained.observe ordinary lifted input sample inside).algebraic.sheetValue.value.name =
      sample.certificate.value.name :=
  packaged_observe_root_name retained ordinary lifted input sample inside

/-- Certify the whole polynomial cell using original supplied Points over the same covered segment.

The Point provider is retained input data. Every new requested coefficient
reading consumes its actual supplied Point and the one already constructed
polynomial model; the constructor does not acquire a replacement Point.
-/
def certificate {liftedStart liftedFinish : LiftedPoint 2}
    {coordinate : Spatial.Coordinate liftedStart.coordinate liftedFinish.coordinate}
    (retained : PolynomialModel (differential := differential) request coordinate positive)
    (ordinary : differential.denominatorPairs = 0) (lifted : LiftedCell liftedStart liftedFinish)
    (startInside : patch.box.Contains liftedStart.coordinate)
    (finishInside : patch.box.Contains liftedFinish.coordinate)
    (samples : ∀ (input : Rational), 0 ≤ input → input ≤ 1 →
      ContinuedNeighborhood.Point patch (coordinate.point input)) :
    Jets.UniformCellCertificate curve differential lifted retained.pullback.model where
  query := fun input lower upper =>
    retained.observe ordinary lifted input (samples input lower upper)
      (coordinate.point_inside startInside finishInside lower upper)

/-- The certified query retains the same supplied original Point's root-name readback. -/
private theorem packaged_certificate_root_name {liftedStart liftedFinish : LiftedPoint 2}
    {coordinate : Spatial.Coordinate liftedStart.coordinate liftedFinish.coordinate}
    (retained : PolynomialModel (differential := differential) request coordinate positive)
    (ordinary : differential.denominatorPairs = 0) (lifted : LiftedCell liftedStart liftedFinish)
    (startInside : patch.box.Contains liftedStart.coordinate)
    (finishInside : patch.box.Contains liftedFinish.coordinate)
    (samples : ∀ (input : Rational), 0 ≤ input → input ≤ 1 →
      ContinuedNeighborhood.Point patch (coordinate.point input))
    (input : Rational) (lower : 0 ≤ input) (upper : input ≤ 1) :
    ((retained.certificate ordinary lifted startInside finishInside samples).query
      input lower upper).algebraic.sheetValue.value.name = (samples input lower upper).certificate.value.name := by
  unfold certificate
  exact retained.observe_root_name ordinary lifted input (samples input lower upper)
    (coordinate.point_inside startInside finishInside lower upper)

/-- The certified query retains the same supplied original Point's root-name readback. -/
theorem certificate_root_name {liftedStart liftedFinish : LiftedPoint 2}
    {coordinate : Spatial.Coordinate liftedStart.coordinate liftedFinish.coordinate}
    (retained : PolynomialModel (differential := differential) request coordinate positive)
    (ordinary : differential.denominatorPairs = 0) (lifted : LiftedCell liftedStart liftedFinish)
    (startInside : patch.box.Contains liftedStart.coordinate)
    (finishInside : patch.box.Contains liftedFinish.coordinate)
    (samples : ∀ (input : Rational), 0 ≤ input → input ≤ 1 →
      ContinuedNeighborhood.Point patch (coordinate.point input))
    (input : Rational) (lower : 0 ≤ input) (upper : input ≤ 1) :
    ((retained.certificate ordinary lifted startInside finishInside samples).query
      input lower upper).algebraic.sheetValue.value.name = (samples input lower upper).certificate.value.name :=
  packaged_certificate_root_name retained ordinary lifted startInside finishInside samples input lower upper

section Comparison

variable {firstFloor lastFloor : Nat} {firstAllowance lastAllowance : Rational}
    {firstPositive : 0 < firstAllowance} {lastPositive : 0 < lastAllowance}
    {firstRequest : UniformRequest bounds 0 (differential.numerator.scale differential.scale)
      firstFloor (firstAllowance / 4)}
    {lastRequest : UniformRequest bounds 0 (differential.numerator.scale differential.scale)
      lastFloor (lastAllowance / 4)}
    {liftedStart liftedFinish : LiftedPoint 2}
    {coordinate : Spatial.Coordinate liftedStart.coordinate liftedFinish.coordinate}

/-- Two actual polynomial models on the same retained Points have internally bounded integral samples.

Their original selected depths, requests and complete primitive caches remain
independent. The root-name equality is derived from the common supplied
Point at each query, rather than accepted as a sample comparison premise.
-/
theorem integral_difference_le
    (first : PolynomialModel (differential := differential) firstRequest coordinate firstPositive)
    (last : PolynomialModel (differential := differential) lastRequest coordinate lastPositive)
    (ordinary : differential.denominatorPairs = 0) (lifted : LiftedCell liftedStart liftedFinish)
    (startInside : patch.box.Contains liftedStart.coordinate)
    (finishInside : patch.box.Contains liftedFinish.coordinate)
    (samples : ∀ (input : Rational), 0 ≤ input → input ≤ 1 →
      ContinuedNeighborhood.Point patch (coordinate.point input)) :
    Norm.Basic.normSq (first.pullback.model.integralSample - last.pullback.model.integralSample) ≤
      16 * (firstAllowance + lastAllowance) * Norm.Basic.normSq coordinate.displacement := by
  let firstCertificate := first.certificate ordinary lifted startInside finishInside samples
  let lastCertificate := last.certificate ordinary lifted startInside finishInside samples
  have original := Jets.UniformCellCertificate.integral_difference_le firstCertificate lastCertificate
    (first.pullback.start_eq.trans last.pullback.start_eq.symm)
    (first.pullback.finish_eq.trans last.pullback.finish_eq.symm)
    (by
      intro input lower upper
      have same :=
        (first.certificate_root_name ordinary lifted startInside finishInside samples input lower upper).trans
          (last.certificate_root_name ordinary lifted startInside finishInside samples input lower upper).symm
      rewrite [same]
      exact NamedEquivalent.refl _)
    (by
      rewrite [first.pullback.allowance_eq, last.pullback.allowance_eq]
      exact Arithmetic.add_pos_of_pos_of_nonneg_direct firstPositive lastPositive.le)
  rewrite [first.pullback.allowance_eq, last.pullback.allowance_eq, first.pullback.displacement_eq] at original
  exact original

end Comparison

section Geometric

variable {earlier later firstFloor lastFloor : Nat}
    {firstRequest : UniformRequest bounds 0 (differential.numerator.scale differential.scale)
      firstFloor (quarterRadius 1 earlier / 4)}
    {lastRequest : UniformRequest bounds 0 (differential.numerator.scale differential.scale)
      lastFloor (quarterRadius 1 later / 4)}
    {firstPositive : 0 < quarterRadius 1 earlier} {lastPositive : 0 < quarterRadius 1 later}
    {liftedStart liftedFinish : LiftedPoint 2}
    {coordinate : Spatial.Coordinate liftedStart.coordinate liftedFinish.coordinate}

/-- The actual unit-quarter allowance policy pays every later same-parent polynomial comparison.

The constant thirty-two pays both original local model allowances. No
monotonicity of independently selected model depths is assumed; each retained
request already pays its actual numerator-wide observation tolerance.
-/
theorem later_integral_difference_le
    (first : PolynomialModel (differential := differential) firstRequest coordinate firstPositive)
    (last : PolynomialModel (differential := differential) lastRequest coordinate lastPositive)
    (ordinary : differential.denominatorPairs = 0) (lifted : LiftedCell liftedStart liftedFinish)
    (startInside : patch.box.Contains liftedStart.coordinate)
    (finishInside : patch.box.Contains liftedFinish.coordinate)
    (samples : ∀ (input : Rational), 0 ≤ input → input ≤ 1 →
      ContinuedNeighborhood.Point patch (coordinate.point input)) (order : earlier ≤ later) :
    Norm.Basic.normSq (last.pullback.model.integralSample - first.pullback.model.integralSample) ≤
      quarterRadius (32 * Norm.Basic.normSq coordinate.displacement) earlier := by
  have forward := first.integral_difference_le last ordinary lifted startInside finishInside samples
  have original := (Norm.Bounds.normSq_sub_symm last.pullback.model.integralSample
    first.pullback.model.integralSample).trans_le forward
  have laterAllowance := quarterRadius_antitone (by decide +kernel : (0 : Rational) ≤ 1) order
  have total := Arithmetic.add_le_add_direct
    (Data.Rat.Fraction.Order.Basic.le_refl (quarterRadius 1 earlier)) laterAllowance
  have enlarged := Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Arithmetic.mul_le_mul_of_nonneg_left_direct total (by decide +kernel : (0 : Rational) ≤ 16))
    (Norm.Basic.normSq_nonneg coordinate.displacement)
  exact original.trans (enlarged.trans_eq (by
    simp only [quarterRadius_eq_mul_pow]
    ring1))

end Geometric

end PolynomialModel

end Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.UniformRequest

end
