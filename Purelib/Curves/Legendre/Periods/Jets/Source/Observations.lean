module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Integrands
public import Purelib.Curves.Legendre.Periods.Jets.Source.Cells
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path
public import Purelib.Curves.Legendre.Periods.Jets.Specification
public import Purelib.Curves.Legendre.Periods.Fibre
public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Continued
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Shared six-channel Legendre observations

One original segment query acquires one continued point. Its parameter
inverse, divided coefficients, generator precision and actual root witness
are shared by the six literal source tables and their original differential
observations. The source model was selected before the point query.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients Expression)
open Purelib.Algebra.Quadratic.Pair.Gaussian (ReadingPrecision)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform
open Purelib.Riemann.Normalization.ContinuedInverseRoot
open ContinuedNeighborhood (UniformBounds UniformRequest)
open ContinuedNeighborhood.Point
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell)
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Power (OddPowers)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Model)

attribute [local irreducible] Riemann.RootContinuation.CertifiedSquareRoot.rawRoot

variable {parameter : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count} {point : Canonical}

/-- The exact scaled numerator of an original odd-power differential. -/
@[expose] def numerator (differential : OddPowerDifferential (Paths.polynomial parameter)) : Coefficients :=
  differential.numerator.scale differential.scale

/-- The original primitive denotation type of one displayed differential at the same continued point. -/
@[expose] def ChannelDenotation (sample : ContinuedNeighborhood.Point patch point)
    (differential : OddPowerDifferential (Paths.polynomial parameter)) (pairs : Fin 3) :=
  PrimitiveDenotation sample pairs (numerator differential)

set_option genInjectivity false in
/-- One original differential's cached numerator factor and original selected-generator denotation.

The actual retained numerator is indexed separately from its exact scaled
specification. Its scalar evaluation occurs once, and the divided pair
consumes the shared parameter-inverse multiplier. -/
structure Channel {sample : ContinuedNeighborhood.Point patch point}
    (differential : OddPowerDifferential (Paths.polynomial parameter)) (pairs : Fin 3)
    (originalNumerator : Coefficients) where
  /-- The cached scalar evaluation of the actual original numerator at the query point. -/
  factor : Canonical
  /-- The scalar factor consumes the retained original numerator. -/
  factor_eq : factor = originalNumerator.eval point
  /-- The original numerator is exactly the differential's scaled specification. -/
  numerator_eq : originalNumerator = numerator differential
  /-- The original divided coefficient pair and channel at the same selected generator. -/
  denotation : ChannelDenotation sample differential pairs

constructive_injectivity Channel

namespace Channel

/-- Evaluate one original numerator once and reuse the shared inverse multiplier in its original denotation. -/
def retain (sample : ContinuedNeighborhood.Point patch point) (bounds : PrimitiveBounds sample)
    (differential : OddPowerDifferential (Paths.polynomial parameter)) (pairs : Fin 3)
    (originalNumerator : Coefficients) (equal : originalNumerator = numerator differential)
    (multiplier : {scalar : Canonical // scalar = bounds.parameterInverse ^ (pairs.val + 1)}) :
    Channel (sample := sample) differential pairs originalNumerator :=
  let factor := originalNumerator.eval point
  have readback : factor = (numerator differential).eval point :=
    congrArg (fun polynomial => polynomial.eval point) equal
  let denotation := retainPrimitiveDenotation sample bounds pairs (numerator differential)
    ⟨factor, readback⟩ multiplier
  ⟨factor, rfl, equal, denotation⟩

/-- The cached original factor also reads the exact original scaled differential numerator. -/
theorem factor_readback {sample : ContinuedNeighborhood.Point patch point}
    {differential : OddPowerDifferential (Paths.polynomial parameter)} {pairs : Fin 3}
    {originalNumerator : Coefficients} (channel : Channel (sample := sample) differential pairs originalNumerator) :
    channel.factor = (numerator differential).eval point :=
  channel.factor_eq.trans (congrArg (fun polynomial => polynomial.eval point) channel.numerator_eq)

end Channel

namespace CellModels

variable {cache : Cache patch} {sourceFloor : Nat} {sourceTarget : Rational}
    {request : Request cache sourceFloor sourceTarget} {start finish : Canonical} {allowance : Rational}
    {uniformBounds : UniformBounds patch} {floor : Nat}

/-- The unit numerator's scale-one representation is its original normalized table. -/
private theorem valueZero_numerator (parameter : Canonical) :
    Basic.constantOnePolynomial = numerator (Specification.valueSpecification parameter 0) := by
  change Basic.constantOnePolynomial = Basic.constantOnePolynomial.scale 1
  rewrite [Polynomial.Dense.Basic.DensePolynomial.scale_one_left]
  decide +kernel

/-- The coordinate numerator's scale-one representation is its original normalized table. -/
private theorem valueOne_numerator (parameter : Canonical) :
    Basic.coordinatePolynomial = numerator (Specification.valueSpecification parameter 1) := by
  change Basic.coordinatePolynomial = Basic.coordinatePolynomial.scale 1
  rewrite [Polynomial.Dense.Basic.DensePolynomial.scale_one_left]
  decide +kernel

/-- The actual original continued-point type at a retained shared segment query. -/
@[expose] def PointAt (models : CellModels request start finish allowance) (input : Rational) :=
  ContinuedNeighborhood.Point patch (models.coordinate.point input)

set_option genInjectivity false in
/-- The six original divided coefficient caches and one common original root reading for an actual segment query.

The selected source model and uniform request owner remain indexed. The
parameter inverse and its two higher multipliers are computed once; each
numerator factor is evaluated once before choosing a shared root precision.
One original model reading supplies the inverse, cube and fifth observations. -/
structure Readings (models : CellModels request start finish allowance)
    (requests : IntegrandRequests uniformBounds floor (allowance / 4)) (input : Rational) where
  /-- The one original continued point acquired for this actual segment query. -/
  sample : PointAt models input
  /-- The original point's retained parameter inverse and scalar bound factors. -/
  bounds : PrimitiveBounds sample
  /-- The cached square of the same parameter reciprocal. -/
  inverseSquare : Canonical
  /-- The cached square reads the original point's parameter inverse. -/
  inverseSquare_eq : inverseSquare = bounds.parameterInverse ^ 2
  /-- The cached cube of that same reciprocal. -/
  inverseCube : Canonical
  /-- The cached cube reads the same retained original parameter inverse. -/
  inverseCube_eq : inverseCube = bounds.parameterInverse ^ 3
  /-- The original unweighted value channel's retained factor and divided coefficients. -/
  valueZero : Channel (sample := sample) (Specification.valueSpecification parameter 0) 0 Basic.constantOnePolynomial
  /-- The original coordinate-weighted value channel's retained scalar data. -/
  valueOne : Channel (sample := sample) (Specification.valueSpecification parameter 1) 0 Basic.coordinatePolynomial
  /-- The original first differentiated channel's retained actual scaled numerator. -/
  firstZero : Channel (sample := sample) (Specification.firstDerivativeSpecification parameter 0) 1
    requests.firstNumeratorZero
  /-- The original coordinate-weighted differentiated channel's retained scaled numerator. -/
  firstOne : Channel (sample := sample) (Specification.firstDerivativeSpecification parameter 1) 1
    requests.firstNumeratorOne
  /-- The original second differentiated channel's retained actual scaled numerator. -/
  secondZero : Channel (sample := sample) (Specification.secondDerivativeSpecification parameter 0) 2
    requests.secondNumeratorZero
  /-- The original coordinate-weighted second differentiated channel's retained numerator. -/
  secondOne : Channel (sample := sample) (Specification.secondDerivativeSpecification parameter 1) 2
    requests.secondNumeratorOne
  /-- The additional retained nonnegative coefficient ceiling for concurrent endpoint readings. -/
  extra : Rational
  /-- The additional coefficient allocation cannot reduce the shared precision ceiling. -/
  extra_nonnegative : 0 ≤ extra
  /-- The cached sum of the six actual divided generator-coefficient quadrances. -/
  sixCeiling : Rational
  /-- The six-channel sum reads exactly these retained original coefficient pairs. -/
  sixCeiling_eq : sixCeiling = Norm.Basic.normSq valueZero.denotation.value.im +
    (Norm.Basic.normSq valueOne.denotation.value.im + (Norm.Basic.normSq firstZero.denotation.value.im +
      (Norm.Basic.normSq firstOne.denotation.value.im + (Norm.Basic.normSq secondZero.denotation.value.im +
        Norm.Basic.normSq secondOne.denotation.value.im))))
  /-- The cached combined integrand and endpoint coefficient ceiling. -/
  ceiling : Rational
  /-- The common precision consumes both original retained allocations. -/
  ceiling_eq : ceiling = sixCeiling + extra
  /-- The one retained root precision paying all six actual coefficient radii. -/
  precision : ReadingPrecision ceiling allowance
  /-- The original root witness selected once at the actual source model stage. -/
  root : PrimitiveRoot sample request.selection.stage precision.target
  /-- The one cached observation of the original source model and its shared odd-power tables. -/
  reading : PrimitiveReading sample request.selection.stage request.model request.models.powers
  /-- The cached model reading consumes this same original shared root witness. -/
  reading_eq : reading = root.readModel request.model request.model_eq request.models.powers

constructive_injectivity Readings

/-- Construct all six original coefficient channels and their shared point, inverse factors and root reading once. -/
@[noinline, nospecialize] def readings (models : CellModels request start finish allowance)
    (requests : IntegrandRequests uniformBounds floor (allowance / 4)) (input : Rational)
    (lower : 0 ≤ input) (upper : input ≤ 1) (positive : 0 < allowance)
    (startInside : patch.box.Contains start) (finishInside : patch.box.Contains finish)
    (extra : Rational := 0) (extraNonnegative : 0 ≤ extra := by decide +kernel) :
    Readings models requests input := by
  let point := models.coordinate.point input
  have inside : patch.box.Contains point := models.coordinate.point_inside startInside finishInside lower upper
  let sample := ContinuedNeighborhood.Point.acquire patch point inside
  let bounds := sample.primitiveBounds
  let inverseSquare := bounds.parameterInverse * bounds.parameterInverse
  have inverseSquareEq : inverseSquare = bounds.parameterInverse ^ 2 := by ring1
  let inverseCube := inverseSquare * bounds.parameterInverse
  have inverseCubeEq : inverseCube = bounds.parameterInverse ^ 3 := by
    change inverseSquare * bounds.parameterInverse = _
    rewrite [inverseSquareEq]
    ring1
  let valueZero := Channel.retain sample bounds (Specification.valueSpecification parameter 0) 0
    Basic.constantOnePolynomial (valueZero_numerator parameter) ⟨bounds.parameterInverse, by exact (pow_one _).symm⟩
  let valueOne := Channel.retain sample bounds (Specification.valueSpecification parameter 1) 0
    Basic.coordinatePolynomial (valueOne_numerator parameter) ⟨bounds.parameterInverse, by exact (pow_one _).symm⟩
  let firstZero := Channel.retain sample bounds (Specification.firstDerivativeSpecification parameter 0) 1
    requests.firstNumeratorZero requests.firstNumeratorZero_eq ⟨inverseSquare, inverseSquareEq⟩
  let firstOne := Channel.retain sample bounds (Specification.firstDerivativeSpecification parameter 1) 1
    requests.firstNumeratorOne requests.firstNumeratorOne_eq ⟨inverseSquare, inverseSquareEq⟩
  let secondZero := Channel.retain sample bounds (Specification.secondDerivativeSpecification parameter 0) 2
    requests.secondNumeratorZero requests.secondNumeratorZero_eq ⟨inverseCube, inverseCubeEq⟩
  let secondOne := Channel.retain sample bounds (Specification.secondDerivativeSpecification parameter 1) 2
    requests.secondNumeratorOne requests.secondNumeratorOne_eq ⟨inverseCube, inverseCubeEq⟩
  let sixCeiling := Norm.Basic.normSq valueZero.denotation.value.im +
    (Norm.Basic.normSq valueOne.denotation.value.im + (Norm.Basic.normSq firstZero.denotation.value.im +
      (Norm.Basic.normSq firstOne.denotation.value.im + (Norm.Basic.normSq secondZero.denotation.value.im +
        Norm.Basic.normSq secondOne.denotation.value.im))))
  have sixNonnegative : 0 ≤ sixCeiling :=
    add_nonneg (Norm.Basic.normSq_nonneg _) (add_nonneg (Norm.Basic.normSq_nonneg _)
      (add_nonneg (Norm.Basic.normSq_nonneg _) (add_nonneg (Norm.Basic.normSq_nonneg _)
        (add_nonneg (Norm.Basic.normSq_nonneg _) (Norm.Basic.normSq_nonneg _)))))
  let ceiling := sixCeiling + extra
  have nonnegative : 0 ≤ ceiling := add_nonneg sixNonnegative extraNonnegative
  let precision := ReadingPrecision.build ceiling allowance nonnegative positive
  let root := selectPrimitiveRoot sample request.selection.stage precision.target precision.target_positive
  let reading := root.readModel request.model request.model_eq request.models.powers
  exact ⟨sample, bounds, inverseSquare, inverseSquareEq, inverseCube, inverseCubeEq,
    valueZero, valueOne, firstZero, firstOne, secondZero, secondOne, extra, extraNonnegative,
    sixCeiling, rfl, ceiling, rfl, precision, root, reading, rfl⟩

/-- The shared reading constructor preserves the supplied additional coefficient allocation. -/
theorem readings_extra (models : CellModels request start finish allowance)
    (requests : IntegrandRequests uniformBounds floor (allowance / 4)) (input : Rational)
    (lower : 0 ≤ input) (upper : input ≤ 1) (positive : 0 < allowance)
    (startInside : patch.box.Contains start) (finishInside : patch.box.Contains finish)
    (extra : Rational) (extraNonnegative : 0 ≤ extra) :
    (models.readings requests input lower upper positive startInside finishInside extra extraNonnegative).extra =
      extra := by
  unfold readings
  rfl

/-- The original reading constructor retains the exact point-acquisition cache at the actual shared coordinate. -/
theorem readings_sample (models : CellModels request start finish allowance)
    (requests : IntegrandRequests uniformBounds floor (allowance / 4)) (input : Rational)
    (lower : 0 ≤ input) (upper : input ≤ 1) (positive : 0 < allowance)
    (startInside : patch.box.Contains start) (finishInside : patch.box.Contains finish)
    (extra : Rational) (extraNonnegative : 0 ≤ extra) :
    (models.readings requests input lower upper positive startInside finishInside extra extraNonnegative).sample =
      ContinuedNeighborhood.Point.acquire patch (models.coordinate.point input)
        (models.coordinate.point_inside startInside finishInside lower upper) := by
  unfold readings
  rfl

/-- The additional endpoint allocation is paid by the same combined precision ceiling. -/
theorem Readings.extra_le {models : CellModels request start finish allowance}
    {requests : IntegrandRequests uniformBounds floor (allowance / 4)} {input : Rational}
    (retained : Readings models requests input) : retained.extra ≤ retained.ceiling := by
  have nonnegative : 0 ≤ retained.sixCeiling := by
    rewrite [retained.sixCeiling_eq]
    exact add_nonneg (Norm.Basic.normSq_nonneg _) (add_nonneg (Norm.Basic.normSq_nonneg _)
      (add_nonneg (Norm.Basic.normSq_nonneg _) (add_nonneg (Norm.Basic.normSq_nonneg _)
        (add_nonneg (Norm.Basic.normSq_nonneg _) (Norm.Basic.normSq_nonneg _)))))
  rewrite [retained.ceiling_eq]
  exact le_add_of_nonneg_left nonnegative

/-- Six retained nonnegative quadrances each lie below their original sum. -/
private theorem six_bounds (a b c d e f : Rational)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f) :
    let total := a + (b + (c + (d + (e + f))))
    a ≤ total ∧ b ≤ total ∧ c ≤ total ∧ d ≤ total ∧ e ≤ total ∧ f ≤ total := by
  dsimp only
  have ef := add_nonneg he hf
  have defNonnegative := add_nonneg hd ef
  have cdefNonnegative := add_nonneg hc defNonnegative
  have bcdefNonnegative := add_nonneg hb cdefNonnegative
  have tail : b + (c + (d + (e + f))) ≤ a + (b + (c + (d + (e + f)))) := le_add_of_nonneg_left ha
  have middle : c + (d + (e + f)) ≤ a + (b + (c + (d + (e + f)))) :=
    (le_add_of_nonneg_left hb).trans tail
  have right : d + (e + f) ≤ a + (b + (c + (d + (e + f)))) :=
    (le_add_of_nonneg_left hc).trans middle
  have last : e + f ≤ a + (b + (c + (d + (e + f)))) := (le_add_of_nonneg_left hd).trans right
  exact ⟨le_add_of_nonneg_right bcdefNonnegative, (le_add_of_nonneg_right cdefNonnegative).trans tail,
    (le_add_of_nonneg_right defNonnegative).trans middle, (le_add_of_nonneg_right ef).trans right,
    (le_add_of_nonneg_right hf).trans last, (le_add_of_nonneg_left he).trans last⟩

/-- The retained sum pays each actual original divided generator coefficient. -/
private theorem coefficient_bounds {models : CellModels request start finish allowance}
    {requests : IntegrandRequests uniformBounds floor (allowance / 4)} {input : Rational}
    (retained : Readings models requests input) :
    Norm.Basic.normSq retained.valueZero.denotation.value.im ≤ retained.ceiling ∧
      Norm.Basic.normSq retained.valueOne.denotation.value.im ≤ retained.ceiling ∧
      Norm.Basic.normSq retained.firstZero.denotation.value.im ≤ retained.ceiling ∧
      Norm.Basic.normSq retained.firstOne.denotation.value.im ≤ retained.ceiling ∧
      Norm.Basic.normSq retained.secondZero.denotation.value.im ≤ retained.ceiling ∧
      Norm.Basic.normSq retained.secondOne.denotation.value.im ≤ retained.ceiling := by
  have bounds : Norm.Basic.normSq retained.valueZero.denotation.value.im ≤ retained.sixCeiling ∧
      Norm.Basic.normSq retained.valueOne.denotation.value.im ≤ retained.sixCeiling ∧
      Norm.Basic.normSq retained.firstZero.denotation.value.im ≤ retained.sixCeiling ∧
      Norm.Basic.normSq retained.firstOne.denotation.value.im ≤ retained.sixCeiling ∧
      Norm.Basic.normSq retained.secondZero.denotation.value.im ≤ retained.sixCeiling ∧
      Norm.Basic.normSq retained.secondOne.denotation.value.im ≤ retained.sixCeiling := by
    rewrite [retained.sixCeiling_eq]
    exact six_bounds _ _ _ _ _ _ (Norm.Basic.normSq_nonneg _) (Norm.Basic.normSq_nonneg _)
      (Norm.Basic.normSq_nonneg _) (Norm.Basic.normSq_nonneg _)
      (Norm.Basic.normSq_nonneg _) (Norm.Basic.normSq_nonneg _)
  have larger : retained.sixCeiling ≤ retained.ceiling := by
    rewrite [retained.ceiling_eq]
    exact le_add_of_nonneg_right retained.extra_nonnegative
  exact ⟨bounds.1.trans larger, bounds.2.1.trans larger, bounds.2.2.1.trans larger,
    bounds.2.2.2.1.trans larger, bounds.2.2.2.2.1.trans larger, bounds.2.2.2.2.2.trans larger⟩

/-- Convert one retained channel using the same original model reading and exact original source table. -/
private def observeChannel (frame : Paths.Frame parameter)
    {liftedStart liftedFinish : LiftedPoint 2} (liftedCell : LiftedCell liftedStart liftedFinish)
    {coordinate : Spatial.Coordinate liftedStart.coordinate liftedFinish.coordinate}
    {source : Coefficients} (pullback : Spatial.Pullback coordinate source allowance) (input : Rational)
    {sample : ContinuedNeighborhood.Point patch (coordinate.point input)}
    {differential : OddPowerDifferential (Paths.polynomial parameter)}
    {pairs : Fin 3} {originalNumerator : Coefficients}
    (channel : Channel (sample := sample) differential pairs originalNumerator)
    (pairs_eq : differential.denominatorPairs = pairs.val)
    (uniformRequest : UniformRequest uniformBounds pairs originalNumerator floor (allowance / 4))
    {depth : Nat} {model : Model (Paths.polynomial parameter) patch.base.box} {powers : OddPowers model.value}
    (sameModel : model = patch.base.refine depth) {ceiling : Rational}
    (precision : ReadingPrecision ceiling allowance) (root : PrimitiveRoot sample depth precision.target)
    (reading : PrimitiveReading sample depth model powers)
    (sameReading : reading = root.readModel model sameModel powers)
    (compiled : source.eval (coordinate.point input) = originalNumerator.eval (coordinate.point input) *
      (primitivePolynomial powers pairs).eval (coordinate.point input))
    (inside : patch.box.Contains (coordinate.point input)) (stage : uniformRequest.selection.stage ≤ depth)
    (coefficient_le : Norm.Basic.normSq channel.denotation.value.im ≤ ceiling) :
    Jets.UniformObservation (Fibre.frameCurve frame) differential liftedCell pullback.model input := by
  have numeratorReading := congrArg
    (fun polynomial : Coefficients => polynomial.eval (coordinate.point input) *
      (primitivePolynomial powers pairs).eval (coordinate.point input)) channel.numerator_eq
  let value := retainPrimitiveValue reading pairs (numerator differential) channel.denotation source
    (compiled.trans numeratorReading) ⟨channel.factor, channel.factor_readback⟩
  let actualRequest := uniformRequest.castNumerator (numerator differential) channel.numerator_eq
  have paid : actualRequest.selection.stage ≤ depth := by
    rewrite [UniformRequest.castNumerator_stage]
    exact stage
  exact Jets.UniformObservation.ofContinuedPrimitive (Fibre.frameCurve frame) differential pairs pairs_eq
    liftedCell pullback input sample inside actualRequest sameModel precision root reading sameReading
    channel.denotation value paid coefficient_le

/-- The single-channel constructor retains the same input point certificate as its actual algebraic generator. -/
private theorem observeChannel_root_name (frame : Paths.Frame parameter)
    {liftedStart liftedFinish : LiftedPoint 2} (liftedCell : LiftedCell liftedStart liftedFinish)
    {coordinate : Spatial.Coordinate liftedStart.coordinate liftedFinish.coordinate}
    {source : Coefficients} (pullback : Spatial.Pullback coordinate source allowance) (input : Rational)
    {sample : ContinuedNeighborhood.Point patch (coordinate.point input)}
    {differential : OddPowerDifferential (Paths.polynomial parameter)}
    {pairs : Fin 3} {originalNumerator : Coefficients}
    (channel : Channel (sample := sample) differential pairs originalNumerator)
    (pairs_eq : differential.denominatorPairs = pairs.val)
    (uniformRequest : UniformRequest uniformBounds pairs originalNumerator floor (allowance / 4))
    {depth : Nat} {model : Model (Paths.polynomial parameter) patch.base.box} {powers : OddPowers model.value}
    (sameModel : model = patch.base.refine depth) {ceiling : Rational}
    (precision : ReadingPrecision ceiling allowance) (root : PrimitiveRoot sample depth precision.target)
    (reading : PrimitiveReading sample depth model powers)
    (sameReading : reading = root.readModel model sameModel powers)
    (compiled : source.eval (coordinate.point input) = originalNumerator.eval (coordinate.point input) *
      (primitivePolynomial powers pairs).eval (coordinate.point input))
    (inside : patch.box.Contains (coordinate.point input)) (stage : uniformRequest.selection.stage ≤ depth)
    (coefficient_le : Norm.Basic.normSq channel.denotation.value.im ≤ ceiling) :
    (observeChannel frame liftedCell pullback input channel pairs_eq uniformRequest sameModel precision root reading
      sameReading compiled inside stage coefficient_le).algebraic.sheetValue.value.name =
      sample.certificate.value.name := by
  unfold observeChannel
  apply Jets.UniformObservation.ofContinuedPrimitive_root_name

set_option genInjectivity false in
/-- Six original differential observations consuming one actual retained segment-query reading cache.

The original curve frame, lifted cell, source request, local models and six
uniform depth requests remain indexed. Every returned observation consumes
the same selected point, actual root witness and model-power readings. -/
structure Observations (frame : Paths.Frame parameter) {liftedStart liftedFinish : LiftedPoint 2}
    (liftedCell : LiftedCell liftedStart liftedFinish)
    (models : CellModels request liftedStart.coordinate liftedFinish.coordinate allowance)
    (requests : IntegrandRequests uniformBounds floor (allowance / 4)) (input : Rational) where
  /-- The one shared original point, factor, denotation and root-reading cache. -/
  retained : Readings models requests input
  /-- The first original value differential on this exact original local model. -/
  valueZero : Jets.UniformObservation (Fibre.frameCurve frame) (Specification.valueSpecification parameter 0)
    liftedCell models.valueZero.model input
  /-- The second original value differential on its exact retained local model. -/
  valueOne : Jets.UniformObservation (Fibre.frameCurve frame) (Specification.valueSpecification parameter 1)
    liftedCell models.valueOne.model input
  /-- The first original first-derivative differential on this same source segment. -/
  firstZero : Jets.UniformObservation (Fibre.frameCurve frame) (Specification.firstDerivativeSpecification parameter 0)
    liftedCell models.firstZero.model input
  /-- The second original first-derivative differential on its actual retained table. -/
  firstOne : Jets.UniformObservation (Fibre.frameCurve frame) (Specification.firstDerivativeSpecification parameter 1)
    liftedCell models.firstOne.model input
  /-- The first original second-derivative differential on its exact retained table. -/
  secondZero : Jets.UniformObservation (Fibre.frameCurve frame)
    (Specification.secondDerivativeSpecification parameter 0)
    liftedCell models.secondZero.model input
  /-- The second original second-derivative differential on this same source segment. -/
  secondOne : Jets.UniformObservation (Fibre.frameCurve frame) (Specification.secondDerivativeSpecification parameter 1)
    liftedCell models.secondOne.model input

constructive_injectivity Observations

/-- Answer all six original differential queries from one same-point root and one source-model reading.

The actual six uniform floors were selected before this source model. Their
individual payments and the cached coefficient ceiling derive the original
local and semantic error guarantees; the source tables are never reevaluated. -/
@[noinline, nospecialize] def observations (frame : Paths.Frame parameter)
    {liftedStart liftedFinish : LiftedPoint 2} (liftedCell : LiftedCell liftedStart liftedFinish)
    (models : CellModels request liftedStart.coordinate liftedFinish.coordinate allowance)
    (requests : IntegrandRequests uniformBounds floor (allowance / 4)) (input : Rational)
    (lower : 0 ≤ input) (upper : input ≤ 1) (positive : 0 < allowance)
    (startInside : patch.box.Contains liftedStart.coordinate)
    (finishInside : patch.box.Contains liftedFinish.coordinate)
    (stage : requests.stage ≤ request.selection.stage)
    (extra : Rational := 0) (extraNonnegative : 0 ≤ extra := by decide +kernel) :
    Observations frame liftedCell models requests input := by
  let retained := models.readings requests input lower upper positive startInside finishInside
    extra extraNonnegative
  have inside := models.coordinate.point_inside startInside finishInside lower upper
  have bounds := coefficient_bounds retained
  let valueZero := observeChannel frame liftedCell models.valueZero input retained.valueZero rfl requests.valueZero
    request.model_eq retained.precision retained.root retained.reading retained.reading_eq
    (IntegrandRequests.valueZero_readback request.models _) inside (requests.valueZero_stage_le.trans stage) bounds.1
  let valueOne := observeChannel frame liftedCell models.valueOne input retained.valueOne rfl requests.valueOne
    request.model_eq retained.precision retained.root retained.reading retained.reading_eq
    (IntegrandRequests.valueOne_readback request.models _) inside (requests.valueOne_stage_le.trans stage) bounds.2.1
  let firstZero := observeChannel frame liftedCell models.firstZero input retained.firstZero rfl requests.firstZero
    request.model_eq retained.precision retained.root retained.reading retained.reading_eq
    (requests.firstZero_readback request.models _) inside (requests.firstZero_stage_le.trans stage) bounds.2.2.1
  let firstOne := observeChannel frame liftedCell models.firstOne input retained.firstOne rfl requests.firstOne
    request.model_eq retained.precision retained.root retained.reading retained.reading_eq
    (requests.firstOne_readback request.models _) inside (requests.firstOne_stage_le.trans stage) bounds.2.2.2.1
  let secondZero := observeChannel frame liftedCell models.secondZero input retained.secondZero rfl requests.secondZero
    request.model_eq retained.precision retained.root retained.reading retained.reading_eq
    (requests.secondZero_readback request.models _) inside (requests.secondZero_stage_le.trans stage) bounds.2.2.2.2.1
  let secondOne := observeChannel frame liftedCell models.secondOne input retained.secondOne rfl requests.secondOne
    request.model_eq retained.precision retained.root retained.reading retained.reading_eq
    (requests.secondOne_readback request.models _) inside (requests.secondOne_stage_le.trans stage) bounds.2.2.2.2.2
  exact ⟨retained, valueZero, valueOne, firstZero, firstOne, secondZero, secondOne⟩

/-- The six-observation constructor retains the supplied concurrent endpoint coefficient allocation. -/
theorem observations_extra (frame : Paths.Frame parameter)
    {liftedStart liftedFinish : LiftedPoint 2} (liftedCell : LiftedCell liftedStart liftedFinish)
    (models : CellModels request liftedStart.coordinate liftedFinish.coordinate allowance)
    (requests : IntegrandRequests uniformBounds floor (allowance / 4)) (input : Rational)
    (lower : 0 ≤ input) (upper : input ≤ 1) (positive : 0 < allowance)
    (startInside : patch.box.Contains liftedStart.coordinate)
    (finishInside : patch.box.Contains liftedFinish.coordinate) (stage : requests.stage ≤ request.selection.stage)
    (extra : Rational) (extraNonnegative : 0 ≤ extra) :
    (models.observations frame liftedCell requests input lower upper positive startInside finishInside stage
      extra extraNonnegative).retained.extra = extra := by
  unfold observations
  exact readings_extra models requests input lower upper positive startInside finishInside extra extraNonnegative

/-- The actual observation bundle retains its complete original shared reading cache without another point request. -/
theorem observations_retained (frame : Paths.Frame parameter)
    {liftedStart liftedFinish : LiftedPoint 2} (liftedCell : LiftedCell liftedStart liftedFinish)
    (models : CellModels request liftedStart.coordinate liftedFinish.coordinate allowance)
    (requests : IntegrandRequests uniformBounds floor (allowance / 4)) (input : Rational)
    (lower : 0 ≤ input) (upper : input ≤ 1) (positive : 0 < allowance)
    (startInside : patch.box.Contains liftedStart.coordinate)
    (finishInside : patch.box.Contains liftedFinish.coordinate)
    (stage : requests.stage ≤ request.selection.stage)
    (extra : Rational) (extraNonnegative : 0 ≤ extra) :
    (observations frame liftedCell models requests input lower upper positive startInside finishInside stage
      extra extraNonnegative).retained =
        models.readings requests input lower upper positive startInside finishInside extra extraNonnegative := by
  unfold observations
  rfl

section ObservationFactory

variable (frame : Paths.Frame parameter)
    {liftedStart liftedFinish : LiftedPoint 2} (liftedCell : LiftedCell liftedStart liftedFinish)
    (models : CellModels request liftedStart.coordinate liftedFinish.coordinate allowance)
    (requests : IntegrandRequests uniformBounds floor (allowance / 4)) (input : Rational)
    (lower : 0 ≤ input) (upper : input ≤ 1) (positive : 0 < allowance)
    (startInside : patch.box.Contains liftedStart.coordinate)
    (finishInside : patch.box.Contains liftedFinish.coordinate) (stage : requests.stage ≤ request.selection.stage)
    (extra : Rational) (extraNonnegative : 0 ≤ extra)

/-- The actual valueZero observation keeps the exact original point-acquisition generator. -/
theorem observations_valueZero_root_name :
    (models.observations frame liftedCell requests input lower upper positive startInside finishInside stage
      extra extraNonnegative).valueZero.algebraic.sheetValue.value.name =
      (ContinuedNeighborhood.Point.acquire patch (models.coordinate.point input)
        (models.coordinate.point_inside startInside finishInside lower upper)).certificate.value.name := by
  have retained :
      (models.observations frame liftedCell requests input lower upper positive startInside finishInside stage
        extra extraNonnegative).valueZero.algebraic.sheetValue.value.name =
          (models.readings requests input lower upper positive startInside finishInside
            extra extraNonnegative).sample.certificate.value.name := by
    unfold observations
    apply observeChannel_root_name
    · exact IntegrandRequests.valueZero_readback request.models _
    · exact requests.valueZero_stage_le.trans stage
  exact retained.trans (congrArg (fun sample : PointAt models input => sample.certificate.value.name)
    (readings_sample models requests input lower upper positive startInside finishInside extra extraNonnegative))

/-- The actual valueOne observation keeps the exact original point-acquisition generator. -/
theorem observations_valueOne_root_name :
    (models.observations frame liftedCell requests input lower upper positive startInside finishInside stage
      extra extraNonnegative).valueOne.algebraic.sheetValue.value.name =
      (ContinuedNeighborhood.Point.acquire patch (models.coordinate.point input)
        (models.coordinate.point_inside startInside finishInside lower upper)).certificate.value.name := by
  have retained :
      (models.observations frame liftedCell requests input lower upper positive startInside finishInside stage
        extra extraNonnegative).valueOne.algebraic.sheetValue.value.name =
          (models.readings requests input lower upper positive startInside finishInside
            extra extraNonnegative).sample.certificate.value.name := by
    unfold observations
    apply observeChannel_root_name
    · exact IntegrandRequests.valueOne_readback request.models _
    · exact requests.valueOne_stage_le.trans stage
  exact retained.trans (congrArg (fun sample : PointAt models input => sample.certificate.value.name)
    (readings_sample models requests input lower upper positive startInside finishInside extra extraNonnegative))

/-- The actual firstZero observation keeps the exact original point-acquisition generator. -/
theorem observations_firstZero_root_name :
    (models.observations frame liftedCell requests input lower upper positive startInside finishInside stage
      extra extraNonnegative).firstZero.algebraic.sheetValue.value.name =
      (ContinuedNeighborhood.Point.acquire patch (models.coordinate.point input)
        (models.coordinate.point_inside startInside finishInside lower upper)).certificate.value.name := by
  have retained :
      (models.observations frame liftedCell requests input lower upper positive startInside finishInside stage
        extra extraNonnegative).firstZero.algebraic.sheetValue.value.name =
          (models.readings requests input lower upper positive startInside finishInside
            extra extraNonnegative).sample.certificate.value.name := by
    unfold observations
    apply observeChannel_root_name
    · exact requests.firstZero_readback request.models _
    · exact requests.firstZero_stage_le.trans stage
  exact retained.trans (congrArg (fun sample : PointAt models input => sample.certificate.value.name)
    (readings_sample models requests input lower upper positive startInside finishInside extra extraNonnegative))

/-- The actual firstOne observation keeps the exact original point-acquisition generator. -/
theorem observations_firstOne_root_name :
    (models.observations frame liftedCell requests input lower upper positive startInside finishInside stage
      extra extraNonnegative).firstOne.algebraic.sheetValue.value.name =
      (ContinuedNeighborhood.Point.acquire patch (models.coordinate.point input)
        (models.coordinate.point_inside startInside finishInside lower upper)).certificate.value.name := by
  have retained :
      (models.observations frame liftedCell requests input lower upper positive startInside finishInside stage
        extra extraNonnegative).firstOne.algebraic.sheetValue.value.name =
          (models.readings requests input lower upper positive startInside finishInside
            extra extraNonnegative).sample.certificate.value.name := by
    unfold observations
    apply observeChannel_root_name
    · exact requests.firstOne_readback request.models _
    · exact requests.firstOne_stage_le.trans stage
  exact retained.trans (congrArg (fun sample : PointAt models input => sample.certificate.value.name)
    (readings_sample models requests input lower upper positive startInside finishInside extra extraNonnegative))

/-- The actual secondZero observation keeps the exact original point-acquisition generator. -/
theorem observations_secondZero_root_name :
    (models.observations frame liftedCell requests input lower upper positive startInside finishInside stage
      extra extraNonnegative).secondZero.algebraic.sheetValue.value.name =
      (ContinuedNeighborhood.Point.acquire patch (models.coordinate.point input)
        (models.coordinate.point_inside startInside finishInside lower upper)).certificate.value.name := by
  have retained :
      (models.observations frame liftedCell requests input lower upper positive startInside finishInside stage
        extra extraNonnegative).secondZero.algebraic.sheetValue.value.name =
          (models.readings requests input lower upper positive startInside finishInside
            extra extraNonnegative).sample.certificate.value.name := by
    unfold observations
    apply observeChannel_root_name
    · exact requests.secondZero_readback request.models _
    · exact requests.secondZero_stage_le.trans stage
  exact retained.trans (congrArg (fun sample : PointAt models input => sample.certificate.value.name)
    (readings_sample models requests input lower upper positive startInside finishInside extra extraNonnegative))

/-- The actual secondOne observation keeps the exact original point-acquisition generator. -/
theorem observations_secondOne_root_name :
    (models.observations frame liftedCell requests input lower upper positive startInside finishInside stage
      extra extraNonnegative).secondOne.algebraic.sheetValue.value.name =
      (ContinuedNeighborhood.Point.acquire patch (models.coordinate.point input)
        (models.coordinate.point_inside startInside finishInside lower upper)).certificate.value.name := by
  have retained :
      (models.observations frame liftedCell requests input lower upper positive startInside finishInside stage
        extra extraNonnegative).secondOne.algebraic.sheetValue.value.name =
          (models.readings requests input lower upper positive startInside finishInside
            extra extraNonnegative).sample.certificate.value.name := by
    unfold observations
    apply observeChannel_root_name
    · exact requests.secondOne_readback request.models _
    · exact requests.secondOne_stage_le.trans stage
  exact retained.trans (congrArg (fun sample : PointAt models input => sample.certificate.value.name)
    (readings_sample models requests input lower upper positive startInside finishInside extra extraNonnegative))

end ObservationFactory

end CellModels

namespace Cell

/-- Answer one bundled six-channel query using this original source cell's actual retained request and local models.

The caller evaluates the bundle once and consumes its six projections. The
request is read from this same source-cell record, so the source model and
odd-power tables are reused rather than regenerated by a stage callback.
-/
@[noinline, nospecialize] def observations (frame : Paths.Frame parameter)
    {start finish : LiftedPoint 2} {lifted : LiftedCell start finish} (cell : Cell (parameter := parameter) lifted)
    {bounds : UniformBounds cell.patch} {floor : Nat}
    (requests : IntegrandRequests bounds floor (cell.allowance / 4)) (input : Rational)
    (lower : 0 ≤ input) (upper : input ≤ 1) (positive : 0 < cell.allowance)
    (stage : requests.stage ≤ cell.request.selection.stage) :
    CellModels.Observations frame lifted cell.models requests input :=
  cell.models.observations frame lifted requests input lower upper positive cell.startInside cell.finishInside stage

set_option genInjectivity false in
/-- A paid six-channel query retaining its original source cell and uniform request owners.

The source model already exists. The request cache and local allowance
are tied to that exact cell, so a later point query reads its retained
model and odd-power tables without executing another source selection.
-/
structure Query {start finish : LiftedPoint 2} {lifted : LiftedCell start finish}
    (cell : Cell (parameter := parameter) lifted) where
  /-- The actual retained original source cell used when executing the point query. -/
  owner : Cell (parameter := parameter) lifted
  /-- The retained cell is the original indexed input, including all its model caches. -/
  owner_eq : owner = cell
  /-- The original chart-wide bounds retained when the six requests were selected. -/
  bounds : UniformBounds cell.patch
  /-- The original request depth floor. -/
  floor : Nat
  /-- The six actual original differential request caches. -/
  requests : IntegrandRequests bounds floor (cell.allowance / 4)
  /-- The same retained local allowance is positive. -/
  positive : 0 < cell.allowance
  /-- The actual retained source stage pays every request floor. -/
  stage : requests.stage ≤ cell.request.selection.stage

constructive_injectivity Query

namespace Query

variable {start finish : LiftedPoint 2} {lifted : LiftedCell start finish}
    {cell replacement : Cell (parameter := parameter) lifted}

/-- Transport the same query data to an equal original cell without rebuilding its model or requests. -/
@[expose] def castCell (query : Query cell) (equal : cell = replacement) : Query replacement := by
  cases equal
  exact query

/-- Retain paid uniform requests at a cell built from the original cached models. -/
@[expose] def ofModels {cache : Cache patch} {sourceFloor : Nat} {target allowance : Rational}
    (request : Request cache sourceFloor target)
    (models : CellModels request start.coordinate finish.coordinate allowance)
    (startInside : patch.box.Contains start.coordinate) (finishInside : patch.box.Contains finish.coordinate)
    {bounds : UniformBounds patch} {floor : Nat}
    (requests : IntegrandRequests bounds floor (allowance / 4)) (positive : 0 < allowance)
    (stage : requests.stage ≤ request.selection.stage)
    (cell : Cell (parameter := parameter) lifted)
    (equal : cell = Cell.ofModels request lifted models startInside finishInside) : Query cell :=
  let original : Query (Cell.ofModels request lifted models startInside finishInside) :=
    ⟨cell, equal, bounds, floor, requests, positive, stage⟩
  original.castCell equal.symm

/-- Answer one actual point query with a retained bundle of all six original observations. -/
@[noinline, nospecialize] def observe (query : Query cell) (frame : Paths.Frame parameter)
    (input : Rational) (lower : 0 ≤ input) (upper : input ≤ 1) :
    CellModels.Observations frame lifted cell.models query.requests input := by
  cases query with
  | mk owner equal bounds floor requests positive stage =>
    subst cell
    exact Cell.observations frame owner requests input lower upper positive stage

section QueryFactory

variable (query : Query cell) (frame : Paths.Frame parameter)
    (input : Rational) (lower : 0 ≤ input) (upper : input ≤ 1)

/-- The actual retained query bundle preserves the complete original acquired point cache on its physical coordinate. -/
theorem observe_sample :
    (query.observe frame input lower upper).retained.sample =
      ContinuedNeighborhood.Point.acquire cell.patch (cell.models.coordinate.point input)
        (cell.models.coordinate.point_inside cell.startInside cell.finishInside lower upper) := by
  cases query with
  | mk owner equal bounds floor requests positive stage =>
    subst cell
    unfold observe Cell.observations
    rewrite [CellModels.observations_retained]
    exact CellModels.readings_sample owner.models requests input lower upper positive
      owner.startInside owner.finishInside 0 (by decide +kernel)

/-- The retained query's actual valueZero answer uses the original cell's point-acquisition factory. -/
theorem observe_valueZero_root_name :
    (query.observe frame input lower upper).valueZero.algebraic.sheetValue.value.name =
      (ContinuedNeighborhood.Point.acquire cell.patch (cell.models.coordinate.point input)
        (cell.models.coordinate.point_inside cell.startInside cell.finishInside lower upper)).certificate.value.name
        := by
  cases query with
  | mk owner equal bounds floor requests positive stage =>
    subst cell
    unfold observe Cell.observations
    exact CellModels.observations_valueZero_root_name frame lifted owner.models requests input lower upper positive
      owner.startInside owner.finishInside stage 0 (by decide +kernel)

/-- The retained query's actual valueOne answer uses the original cell's point-acquisition factory. -/
theorem observe_valueOne_root_name :
    (query.observe frame input lower upper).valueOne.algebraic.sheetValue.value.name =
      (ContinuedNeighborhood.Point.acquire cell.patch (cell.models.coordinate.point input)
        (cell.models.coordinate.point_inside cell.startInside cell.finishInside lower upper)).certificate.value.name
        := by
  cases query with
  | mk owner equal bounds floor requests positive stage =>
    subst cell
    unfold observe Cell.observations
    exact CellModels.observations_valueOne_root_name frame lifted owner.models requests input lower upper positive
      owner.startInside owner.finishInside stage 0 (by decide +kernel)

/-- The retained query's actual firstZero answer uses the original cell's point-acquisition factory. -/
theorem observe_firstZero_root_name :
    (query.observe frame input lower upper).firstZero.algebraic.sheetValue.value.name =
      (ContinuedNeighborhood.Point.acquire cell.patch (cell.models.coordinate.point input)
        (cell.models.coordinate.point_inside cell.startInside cell.finishInside lower upper)).certificate.value.name
        := by
  cases query with
  | mk owner equal bounds floor requests positive stage =>
    subst cell
    unfold observe Cell.observations
    exact CellModels.observations_firstZero_root_name frame lifted owner.models requests input lower upper positive
      owner.startInside owner.finishInside stage 0 (by decide +kernel)

/-- The retained query's actual firstOne answer uses the original cell's point-acquisition factory. -/
theorem observe_firstOne_root_name :
    (query.observe frame input lower upper).firstOne.algebraic.sheetValue.value.name =
      (ContinuedNeighborhood.Point.acquire cell.patch (cell.models.coordinate.point input)
        (cell.models.coordinate.point_inside cell.startInside cell.finishInside lower upper)).certificate.value.name
        := by
  cases query with
  | mk owner equal bounds floor requests positive stage =>
    subst cell
    unfold observe Cell.observations
    exact CellModels.observations_firstOne_root_name frame lifted owner.models requests input lower upper positive
      owner.startInside owner.finishInside stage 0 (by decide +kernel)

/-- The retained query's actual secondZero answer uses the original cell's point-acquisition factory. -/
theorem observe_secondZero_root_name :
    (query.observe frame input lower upper).secondZero.algebraic.sheetValue.value.name =
      (ContinuedNeighborhood.Point.acquire cell.patch (cell.models.coordinate.point input)
        (cell.models.coordinate.point_inside cell.startInside cell.finishInside lower upper)).certificate.value.name
        := by
  cases query with
  | mk owner equal bounds floor requests positive stage =>
    subst cell
    unfold observe Cell.observations
    exact CellModels.observations_secondZero_root_name frame lifted owner.models requests input lower upper positive
      owner.startInside owner.finishInside stage 0 (by decide +kernel)

/-- The retained query's actual secondOne answer uses the original cell's point-acquisition factory. -/
theorem observe_secondOne_root_name :
    (query.observe frame input lower upper).secondOne.algebraic.sheetValue.value.name =
      (ContinuedNeighborhood.Point.acquire cell.patch (cell.models.coordinate.point input)
        (cell.models.coordinate.point_inside cell.startInside cell.finishInside lower upper)).certificate.value.name
        := by
  cases query with
  | mk owner equal bounds floor requests positive stage =>
    subst cell
    unfold observe Cell.observations
    exact CellModels.observations_secondOne_root_name frame lifted owner.models requests input lower upper positive
      owner.startInside owner.finishInside stage 0 (by decide +kernel)

end QueryFactory

/-- Read the six actual integrand samples after evaluating one bundled original query.

The ordered samples are the two values, two first derivatives and two
second derivatives. The retained observation bundle is evaluated once;
all six projections consume that same point, root and source-model reading.
-/
@[noinline, nospecialize] def samples (query : Query cell) (frame : Paths.Frame parameter)
    (input : Rational) (lower : 0 ≤ input) (upper : input ≤ 1) : List Canonical :=
  let observed := query.observe frame input lower upper
  [observed.valueZero.observation.integrandReading, observed.valueOne.observation.integrandReading,
    observed.firstZero.observation.integrandReading, observed.firstOne.observation.integrandReading,
    observed.secondZero.observation.integrandReading, observed.secondOne.observation.integrandReading]

end Query

end Cell

end Purelib.Curves.Legendre.Periods.Jets.Source

end
