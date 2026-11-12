module

public import Purelib.Polynomial.Clearance.Circle.Collar
public import Purelib.RootIsolation.Isolation.Coprime.UniformResidual
public import Purelib.Geometry.Projective.Hermitian.Box.Sign
public import Purelib.Geometry.Projective.Hermitian.Radial
public import Purelib.Geometry.Rational.Box.Sample
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Automatic radial separation of original winding-one tracks

One retained request caches all coefficient bounds for a factor. Each original
track then performs the original uniform-residual refinement and one explicit
Hermitian-variation refinement. The resulting original state has a certified
strict radial sign, without a caller-supplied separation budget.
-/

namespace Purelib.RootIsolation.Track.Circle

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Geometry.Rational
open Purelib.Geometry.Projective
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian
open Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Clearance.Circle (Certificate Collar)
open Purelib.RootIsolation.Track.Basic (WindingOneTrack)
open Purelib.RootIsolation.State.WindingOne.Basic (WindingOneState)
open Isolation.Coprime
open Rat.Fraction (Rational)
open Rat.Fraction.Order

set_option genInjectivity false in
/-- Shared sufficient requests for every original track of one polynomial factor.

The original circle margin and ambient box remain indices. Both original
coefficient folds and the Hermitian variation coefficient are computed once;
all tracks consume their same retained residual and sign requests. -/
public structure Request {polynomial : CoefficientPolynomial} (clearance : Certificate polynomial) (ambient : Box) where
  /-- The retained coefficient-computed collar. -/ collar : Collar clearance ambient
  /-- The original ambient value/slope fold, shared by every track. -/ bounds : Polynomial.Bounds.Horner
  /-- The fold uses the original polynomial and original ambient box. -/ bounds_eq :
    bounds = Bounds.Box.denseHornerNormBounds polynomial ambient
  /-- The retained small-residual threshold. -/ threshold : Rational
  /-- The threshold is one eighth of the original circle margin. -/ threshold_eq : threshold = clearance.bound / 8
  /-- The retained threshold is strictly positive. -/ threshold_positive : 0 < threshold
  /-- The original uniform-residual accuracy, computed once. -/ residualRadius : Rational
  /-- The radius is exactly the original coefficient-computed request. -/ residualRadius_eq :
    residualRadius = Bounds.Box.Target.uniformResidualRadius polynomial ambient threshold
  /-- The original uniform-residual request is strictly positive. -/ residualRadius_positive : 0 < residualRadius
  /-- The retained coefficient controlling squared radial variation. -/ variation : Rational
  /-- The coefficient is the original Hermitian form's ambient variation bound. -/ variation_eq :
    variation = Hermitian.Box.variationCoefficient (Hermitian.affineNormComparisonForm 1) ambient
  /-- The second accuracy request, shared by every track. -/ accuracy : Rational
  /-- The accuracy pays the same retained collar width and variation coefficient. -/ accuracy_eq :
    accuracy = min 1 (collar.width ^ 2 / (2 * (1 + variation)))
  /-- The retained sign request is strictly positive. -/ accuracy_positive : 0 < accuracy

constructive_injectivity Request

namespace Request

/-- Cache one sufficient pair of requests from the original polynomial, ambient box and whole-circle margin. -/
@[expose] public def prepare {polynomial : CoefficientPolynomial} (clearance : Certificate polynomial) (ambient : Box) :
    Request clearance ambient :=
  let collar := Collar.prepare clearance ambient
  let bounds := Bounds.Box.denseHornerNormBounds polynomial ambient
  let threshold := clearance.bound / 8
  have thresholdPositive : 0 < threshold := Field.div_pos_direct clearance.positive (by decide)
  let residualRadius := min 1 (threshold / (8 * max 1 bounds.slope))
  have residualRadiusEq : residualRadius = Bounds.Box.Target.uniformResidualRadius polynomial ambient threshold := rfl
  let variation := Hermitian.Box.variationCoefficient (Hermitian.affineNormComparisonForm 1) ambient
  have variationNonnegative : 0 ≤ variation := Hermitian.Box.variationCoefficient_nonneg _ _
  let accuracy := min 1 (collar.width ^ 2 / (2 * (1 + variation)))
  { collar, bounds, bounds_eq := rfl, threshold, threshold_eq := rfl, threshold_positive := thresholdPositive
    residualRadius, residualRadius_eq := residualRadiusEq
    residualRadius_positive := residualRadiusEq.symm ▸ Bounds.Box.Target.uniformResidualRadius_pos
      polynomial ambient thresholdPositive
    variation, variation_eq := rfl, accuracy, accuracy_eq := rfl
    accuracy_positive := Fraction.Order.Basic.lt_min (by decide)
      (Field.div_pos_direct (Arithmetic.pow_pos_direct collar.positive 2)
        (Arithmetic.mul_pos_direct (by decide)
          (Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide) variationNonnegative))) }

/-- Using the retained residual request returns the complete original uniform-residual state. -/
public theorem refine_eq_uniformlySmallState {polynomial : CoefficientPolynomial} {ambient : Box}
    {clearance : Certificate polynomial} (request : Request clearance ambient)
    (track : WindingOneTrack polynomial ambient) (current : WindingOneState polynomial ambient) :
    track.refine current request.residualRadius request.residualRadius_positive =
      UniformResidual.uniformlySmallState track current request.threshold request.threshold_positive := by
  have radiusEq : (⟨request.residualRadius, request.residualRadius_positive⟩ : {radius : Rational // 0 < radius}) =
      ⟨Bounds.Box.Target.uniformResidualRadius polynomial ambient request.threshold,
        Bounds.Box.Target.uniformResidualRadius_pos polynomial ambient request.threshold_positive⟩ :=
    Subtype.ext request.residualRadius_eq
  exact congrArg (fun radius : {radius : Rational // 0 < radius} =>
    track.refine current radius.val radius.property) radiusEq

/-- The squared sign-accuracy request is no larger than its own positive value. -/
public theorem accuracy_sq_le {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial} {ambient : Box}
    (request : Request clearance ambient) : request.accuracy ^ 2 ≤ request.accuracy := by
  have atMostOne : request.accuracy ≤ 1 := by rw [request.accuracy_eq]; exact Fraction.Order.Basic.min_le_left _ _
  have bound := Arithmetic.mul_le_mul_of_nonneg_left_direct atMostOne request.accuracy_positive.le
  simpa only [pow_two, Rat.Fraction.Field.mul_one_direct] using bound

/-- The exact retained second request pays a strict radial-variation margin. -/
public theorem variation_lt {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial} {ambient : Box}
    (request : Request clearance ambient) {box : Box}
    (accurate : box.diagonalSq ≤ request.accuracy ^ 2) :
    Hermitian.Box.variationSqBound (Hermitian.affineNormComparisonForm 1) ambient box < request.collar.width ^ 2 := by
  have variationNonnegative : 0 ≤ request.variation := by
    rw [request.variation_eq]
    exact Hermitian.Box.variationCoefficient_nonneg _ _
  have scalePositive : 0 < 1 + request.variation :=
    Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide) variationNonnegative
  have coefficientBound : request.variation ≤ 1 + request.variation := by
    have bound := Arithmetic.add_le_add_right_direct (show (0 : Rational) ≤ 1 by decide) request.variation
    rw [Rat.Fraction.Field.zero_add] at bound
    exact bound
  have payment : request.accuracy * (2 * (1 + request.variation)) ≤ request.collar.width ^ 2 := by
    apply (Field.le_div_iff_pos (Arithmetic.mul_pos_direct (by decide) scalePositive)).mp
    rw [request.accuracy_eq]
    exact Fraction.Order.Basic.min_le_right _ _
  calc
    Hermitian.Box.variationSqBound (Hermitian.affineNormComparisonForm 1) ambient box =
        request.variation * box.diagonalSq := by rw [Hermitian.Box.variationSqBound, request.variation_eq]
    _ ≤ request.variation * request.accuracy ^ 2 :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct accurate variationNonnegative
    _ ≤ request.variation * request.accuracy :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct request.accuracy_sq_le variationNonnegative
    _ ≤ (1 + request.variation) * request.accuracy :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct coefficientBound request.accuracy_positive.le
    _ < 2 * ((1 + request.variation) * request.accuracy) := by
      have positive := Arithmetic.mul_pos_direct scalePositive request.accuracy_positive
      have scaled := Arithmetic.mul_lt_mul_of_pos_right_direct (show (1 : Rational) < 2 by decide) positive
      simpa only [Rat.Fraction.Field.one_mul] using scaled
    _ = request.accuracy * (2 * (1 + request.variation)) := by ring1
    _ ≤ request.collar.width ^ 2 := payment

end Request

set_option genInjectivity false in
/-- A radial refinement retaining both actual original track states and their numerical certificates.

The original track, preceding state and shared request remain indices. Both
refinement calls and the original Hermitian sign selection carry exact equations;
the rational sample and its exact unit-circle retraction are retained once. -/
public structure Refinement {polynomial : CoefficientPolynomial} {ambient : Box}
    {clearance : Certificate polynomial} (request : Request clearance ambient)
    (track : WindingOneTrack polynomial ambient) (current : WindingOneState polynomial ambient) where
  /-- The original polynomial has positive degree. -/ degreePositive : 0 < polynomial.natDegree
  /-- The actual first original track refinement. -/ small : WindingOneState polynomial ambient
  /-- The first state consumes the retained original residual radius. -/ small_eq :
    small = track.refine current request.residualRadius request.residualRadius_positive
  /-- The actual second original track refinement. -/ next : WindingOneState polynomial ambient
  /-- The second state consumes the same retained sign accuracy. -/ next_eq :
    next = track.refine small request.accuracy request.accuracy_positive
  /-- The retained original box sample. -/ sample : Gaussian.Basic.Canonical
  /-- The sample is exactly the returned box's original anchor. -/ sample_eq : sample = next.box.anchor
  /-- The once-computed rational unit-circle retraction of that same sample. -/ retraction :
    Geometry.Rational.Circle.Retraction sample
  /-- The retraction is the original exact constructor's result. -/ retraction_eq :
    retraction = Geometry.Rational.Circle.Retraction.prepare sample
  /-- The original Hermitian certificate on this exact returned box. -/ certificate :
    Hermitian.Box.Certificate (Hermitian.affineNormComparisonForm 1) ambient next.box
  /-- The Hermitian certificate consumes the retained original sample. -/ certificate_sample :
    certificate.sample = sample
  /-- The once-computed uniform strict sign. -/ side :
    Hermitian.Box.Certificate.StrictSign (Hermitian.affineNormComparisonForm 1) next.box
  /-- The sign is the original certificate's exact selection. -/ side_eq : side = certificate.strictSign

constructive_injectivity Refinement

namespace Refinement

/-- Retain two checked original refinement states and compute their same certified strict radial sign.

Both complete state equalities concern the original track, preceding state
and shared requests. The returned sample, retraction and Hermitian certificate
consume those retained states without invoking either refiner again. -/
@[expose] public def ofStates {polynomial : CoefficientPolynomial} {ambient : Box}
    {clearance : Certificate polynomial} (request : Request clearance ambient)
    (track : WindingOneTrack polynomial ambient) (current : WindingOneState polynomial ambient)
    (degreePositive : 0 < polynomial.natDegree)
    (small : WindingOneState polynomial ambient)
    (smallEq : small = track.refine current request.residualRadius request.residualRadius_positive)
    (next : WindingOneState polynomial ambient)
    (nextEq : next = track.refine small request.accuracy request.accuracy_positive) :
    Refinement request track current := by
  let sample := next.box.anchor
  let retraction := Geometry.Rational.Circle.Retraction.prepare sample
  have sampleInside : next.box.Contains sample := next.box.contains_anchor
  have smallInside : small.box.Contains sample := by
    have nested := track.nested small request.accuracy request.accuracy_positive
    rw [← nextEq] at nested
    exact nested.contains sampleInside
  have smallUniform : small = UniformResidual.uniformlySmallState track current request.threshold
      request.threshold_positive := smallEq.trans (request.refine_eq_uniformlySmallState track current)
  have residual : Gaussian.Norm.Basic.normSq (polynomial.eval sample) < clearance.bound / 8 := by
    have smallInsideOriginal := smallUniform ▸ smallInside
    have residual := UniformResidual.uniformlySmallState_residual_lt degreePositive track current
      request.threshold_positive smallInsideOriginal
    rw [request.threshold_eq] at residual
    exact residual
  have gap := request.collar.small_residual_away (next.refinesAmbient.contains sampleInside) residual
  have margin : Hermitian.Box.variationSqBound (Hermitian.affineNormComparisonForm 1) ambient next.box <
      (Hermitian.affineNormComparisonForm 1).eval sample ^ 2 := by
    rw [Hermitian.eval_affineNormComparisonForm, Gaussian.Norm.Basic.normSq_eq_canonical]
    have accurate : next.box.diagonalSq ≤ request.accuracy ^ 2 := by
      rw [nextEq]
      exact track.accurate small request.accuracy request.accuracy_positive
    exact (request.variation_lt accurate).trans gap
  let certificate : Hermitian.Box.Certificate (Hermitian.affineNormComparisonForm 1) ambient next.box :=
    ⟨next.refinesAmbient, sample, sampleInside, margin⟩
  exact
    { degreePositive, small, small_eq := smallEq, next, next_eq := nextEq, sample, sample_eq := rfl
      retraction, retraction_eq := rfl, certificate, certificate_sample := rfl
      side := certificate.strictSign, side_eq := rfl }

/-- Refine an original track twice at the sufficient shared requests and retain its certified strict radial sign. -/
@[expose] public def prepare {polynomial : CoefficientPolynomial} {ambient : Box}
    {clearance : Certificate polynomial} (request : Request clearance ambient)
    (track : WindingOneTrack polynomial ambient) (current : WindingOneState polynomial ambient)
    (degreePositive : 0 < polynomial.natDegree) : Refinement request track current :=
  let small := track.refine current request.residualRadius request.residualRadius_positive
  let next := track.refine small request.accuracy request.accuracy_positive
  ofStates request track current degreePositive small rfl next rfl

/-- Restoring both complete original states preserves the complete original radial-refinement result. -/
public theorem ofStates_eq_prepare {polynomial : CoefficientPolynomial} {ambient : Box}
    {clearance : Certificate polynomial} (request : Request clearance ambient)
    (track : WindingOneTrack polynomial ambient) (current : WindingOneState polynomial ambient)
    (degreePositive : 0 < polynomial.natDegree)
    (small : WindingOneState polynomial ambient)
    (smallEq : small = track.refine current request.residualRadius request.residualRadius_positive)
    (next : WindingOneState polynomial ambient)
    (nextEq : next = track.refine small request.accuracy request.accuracy_positive) :
    ofStates request track current degreePositive small smallEq next nextEq =
      prepare request track current degreePositive := by
  cases smallEq
  cases nextEq
  rfl

/-- The actual returned radial state refines the original preceding state. -/
public theorem refines {polynomial : CoefficientPolynomial} {ambient : Box}
    {clearance : Certificate polynomial} {request : Request clearance ambient}
    {track : WindingOneTrack polynomial ambient} {current : WindingOneState polynomial ambient}
    (result : Refinement request track current) : result.next.box.Refines current.box := by
  have first : result.small.box.Refines current.box := by
    rw [result.small_eq]
    exact track.nested current request.residualRadius request.residualRadius_positive
  have second : result.next.box.Refines result.small.box := by
    rw [result.next_eq]
    exact track.nested result.small request.accuracy request.accuracy_positive
  exact second.trans first

/-- Every rational point of the actual returned state has the requested small original-polynomial residual. -/
public theorem small_residual {polynomial : CoefficientPolynomial} {ambient : Box}
    {clearance : Certificate polynomial} {request : Request clearance ambient}
    {track : WindingOneTrack polynomial ambient} {current : WindingOneState polynomial ambient}
    (result : Refinement request track current) {point : Gaussian.Basic.Canonical}
    (inside : result.next.box.Contains point) :
    Gaussian.Norm.Basic.normSq (polynomial.eval point) < clearance.bound / 8 := by
  have second : result.next.box.Refines result.small.box := by
    rw [result.next_eq]
    exact track.nested result.small request.accuracy request.accuracy_positive
  have smallEq := result.small_eq.trans (request.refine_eq_uniformlySmallState track current)
  have originalInside := smallEq ▸ second.contains inside
  have residual := UniformResidual.uniformlySmallState_residual_lt result.degreePositive track current
    request.threshold_positive originalInside
  rw [request.threshold_eq] at residual
  exact residual

/-- The actual returned state has a uniform strict squared norm-defect gap from the original unit boundary. -/
public theorem radial_gap {polynomial : CoefficientPolynomial} {ambient : Box}
    {clearance : Certificate polynomial} {request : Request clearance ambient}
    {track : WindingOneTrack polynomial ambient} {current : WindingOneState polynomial ambient}
    (result : Refinement request track current) {point : Gaussian.Basic.Canonical}
    (inside : result.next.box.Contains point) :
    request.collar.width ^ 2 < (point.normSq - 1) ^ 2 :=
  request.collar.small_residual_away (result.next.refinesAmbient.contains inside) (result.small_residual inside)

end Refinement
end Purelib.RootIsolation.Track.Circle
