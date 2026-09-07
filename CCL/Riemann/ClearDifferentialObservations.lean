import CCL.Riemann.BranchCutLifts
import CCL.Riemann.ClearSheetContinuation

/-!
# Automatic differential observations on clear lifted segments

Branch-cut clearance proves `f(x) != 0` at every rational unit-interval
sample.  The finite square-root sheet constructor then supplies `y`, its
apartness, and `y^2 = f(x)`.  This module packages one actual rational witness
of `x^k/y` as a Gaussian-constant local polynomial observation.  Sheet-switch
cells have zero displacement and need no integrand observation.
-/

namespace CCL.Riemann.ClearDifferentialObservations

open CCL.Riemann.AlgebraicDifferentials
open CCL.Riemann.BranchCuts
open CCL.Riemann.BranchCutLifts
open CCL.Riemann.LiftedPaths
open RFAP.ConstructiveGaussian.Gaussian

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev CellModel := CCL.ProgressiveGaussianIntegration.CellModel
abbrev LocalObservation :=
  CCL.ProgressiveGaussianIntegration.LocalObservation
abbrev Owner := CCL.Riemann.SquareRootContinuationChain.Owner

/-- One integration cell together with all algebraic certificates required by
the corresponding lifted edge. -/
structure CertifiedCell {genus : Nat}
    (curve : HyperellipticCurve genus) (differential : Differential genus)
    {start finish : LiftedPoint 2} (liftedCell : LiftedCell start finish) where
  model : CellModel
  start_eq : model.start = start.coordinate
  finish_eq : model.finish = finish.coordinate
  observations : ObservationCertificates curve differential liftedCell model
    model.observations

/-- Select one explicit rational reading admitted by the initial state of a
coherent differential coefficient. -/
def initialReading (value : CCL.ProgressiveCoherence.CoherentNamed) : Gaussian :=
  (value.name.process.witness value.name.state).val

/-- The selected initial reading is genuinely admitted by that finite state. -/
theorem initialReading_possible
    (value : CCL.ProgressiveCoherence.CoherentNamed) :
    value.name.process.Possible value.name.state (initialReading value) :=
  (value.name.process.witness value.name.state).property

/-- Automatically certify one Gaussian-constant observation of `x^k/y` on a
clear segment.  The local polynomial has zero discrepancy at the displayed
sample because Gaussian coefficients can represent the complex reading
exactly. -/
def clearSample {genus : Nat} (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (sheet : Fin 2) (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1) :
    CertifiedCell curve differential
      (CCL.Riemann.BranchCutLifts.ClearSegment.liftOnSheet sheet segment) := by
  let point := segment.pointAt parameter
  let radicandNonzero := segment.pointAt_eval_ne_zero parameter inside
  let sheetValue := AlgebraicSheetValue.automatic curve point
    radicandNonzero sheet
  let coefficient := differentialValue differential point sheetValue.value
    sheetValue.apart
  let state := coefficient.name.state
  let reading := initialReading coefficient
  let polynomial := CCL.FiniteGaussianPolynomial.constant reading
  let observation : LocalObservation polynomial 0 :=
    { parameter := parameter
      integrandReading := reading
      error := 0
      decomposition := by
        dsimp only [polynomial]
        rw [CCL.FiniteGaussianPolynomial.eval_constant]
        change reading - reading = 0
        exact RFAP.ConstructiveGaussian.Gaussian.sub_self reading
      error_le := by
        change RFAP.ConstructiveGaussian.Gaussian.normSq (0 : Gaussian) <= 0
        exact le_rfl }
  let model : CellModel :=
    { start := start
      finish := finish
      polynomial := polynomial
      localAllowance := 0
      localAllowance_nonneg := le_rfl
      observations := [observation] }
  let algebraic : AlgebraicObservation curve differential
      (CCL.Riemann.BranchCutLifts.ClearSegment.liftOnSheet sheet segment)
      model observation := by
    refine
      { point := point
        point_eq := rfl
        sheetValue := sheetValue
        chosenSheet_eq := ?_
        readingState := state
        readingPossible := ?_ }
    · change sheet = sheet
      rfl
    · change coefficient.name.process.Possible state reading
      exact initialReading_possible coefficient
  exact
    { model := model
      start_eq := rfl
      finish_eq := rfl
      observations := .cons algebraic (.nil) }

/-- Certify an observation using the endpoint of a finite same-owner
continuation chain.  Unlike `clearSample`, this constructor never asks the
root isolator to re-index the two owners at the observation point. -/
def continuedSample {genus : Nat} (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    {source : Gaussian} (sourceNonzero : source ≠ 0)
    (chain : CCL.Riemann.SquareRootContinuationChain.SeededChain
      source sourceNonzero)
    (endpoint_eq : chain.endpoint.parameter =
      curve.polynomial.eval (segment.pointAt parameter)) :
    CertifiedCell curve differential
      (CCL.Riemann.BranchCutLifts.ClearSegment.liftOnSheet
        chain.sheet segment) := by
  let point := segment.pointAt parameter
  let radicandNonzero := segment.pointAt_eval_ne_zero parameter inside
  let sheetValue := chain.algebraicSheetValue curve point source
    sourceNonzero endpoint_eq
  let coefficient := differentialValue differential point sheetValue.value
    sheetValue.apart
  let state := coefficient.name.state
  let reading := initialReading coefficient
  let polynomial := CCL.FiniteGaussianPolynomial.constant reading
  let observation : LocalObservation polynomial 0 :=
    { parameter := parameter
      integrandReading := reading
      error := 0
      decomposition := by
        dsimp only [polynomial]
        rw [CCL.FiniteGaussianPolynomial.eval_constant]
        change reading - reading = 0
        exact RFAP.ConstructiveGaussian.Gaussian.sub_self reading
      error_le := by
        change RFAP.ConstructiveGaussian.Gaussian.normSq (0 : Gaussian) <= 0
        exact le_rfl }
  let model : CellModel :=
    { start := start
      finish := finish
      polynomial := polynomial
      localAllowance := 0
      localAllowance_nonneg := le_rfl
      observations := [observation] }
  let algebraic : AlgebraicObservation curve differential
      (CCL.Riemann.BranchCutLifts.ClearSegment.liftOnSheet
        chain.sheet segment) model observation := by
    refine
      { point := point
        point_eq := rfl
        sheetValue := sheetValue
        chosenSheet_eq := ?_
        readingState := state
        readingPossible := ?_ }
    · change chain.sheet = chain.sheet
      rfl
    · change coefficient.name.process.Possible state reading
      exact initialReading_possible coefficient
  exact
    { model := model
      start_eq := rfl
      finish_eq := rfl
      observations := .cons algebraic (.nil) }

/-- Specialization of `continuedSample` to the computed endpoint of a finite
adaptive clear-segment subdivision. -/
def continuedEndpointSample {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left : Coordinate)
    (leftInside : (0 : Coordinate) <= left ∧ left <= 1)
    (sheet : Fin 2)
    (subdivision : CCL.Riemann.ClearSheetContinuation.Subdivision
      segment within left leftInside
        (CCL.Riemann.SquareRootContinuationChain.Owner.independent
          (segment.pointAt_eval_ne_zero left leftInside) sheet)) :
    CertifiedCell curve differential
      (CCL.Riemann.BranchCutLifts.ClearSegment.liftOnSheet sheet segment) := by
  let chain := subdivision.seeded sheet
  have endpoint_eq : chain.endpoint.parameter =
      curve.polynomial.eval
        (segment.pointAt subdivision.endpoint.parameter) := by
    exact subdivision.toChain_endpoint_parameter
  exact continuedSample curve differential segment
    subdivision.endpoint.parameter subdivision.endpoint.inside
    (segment.pointAt_eval_ne_zero left leftInside) chain endpoint_eq

/-- Certify the endpoint reading of one clear edge from an already inherited
square-root owner.  The owner is indexed by `f(finish)`, so this constructor
does not perform a fresh two-root isolation and cannot silently relabel the
sheet between adjacent subdivision cells. -/
def inheritedEndpointSample {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (sheet : Fin 2)
    (owner : Owner (curve.polynomial.eval finish)) :
    CertifiedCell curve differential
      (CCL.Riemann.BranchCutLifts.ClearSegment.liftOnSheet sheet segment) := by
  let radicandNonzero := segment.finish_eval_ne_zero
  let root := owner.certificate radicandNonzero
  let sheetValue : AlgebraicSheetValue curve finish :=
    { value := root.value
      apart := root.apart
      sheet := sheet
      curveEquation :=
        CCL.OperationalEquivalence.NamedEquivalent.trans root.square
          (CCL.OperationalEquivalence.NamedEquivalent.symm
            (CCL.ProjectiveRationalEvaluation.polynomialEval_exact
              curve.polynomial finish)) }
  let coefficient := differentialValue differential finish sheetValue.value
    sheetValue.apart
  let state := coefficient.name.state
  let reading := initialReading coefficient
  let polynomial := CCL.FiniteGaussianPolynomial.constant reading
  let observation : LocalObservation polynomial 0 :=
    { parameter := 1
      integrandReading := reading
      error := 0
      decomposition := by
        dsimp only [polynomial]
        rw [CCL.FiniteGaussianPolynomial.eval_constant]
        exact RFAP.ConstructiveGaussian.Gaussian.sub_self reading
      error_le := by
        change RFAP.ConstructiveGaussian.Gaussian.normSq (0 : Gaussian) <= 0
        exact le_rfl }
  let model : CellModel :=
    { start := start
      finish := finish
      polynomial := polynomial
      localAllowance := 0
      localAllowance_nonneg := le_rfl
      observations := [observation] }
  let algebraic : AlgebraicObservation curve differential
      (CCL.Riemann.BranchCutLifts.ClearSegment.liftOnSheet sheet segment)
      model observation := by
    refine
      { point := finish
        point_eq := ?_
        sheetValue := sheetValue
        chosenSheet_eq := rfl
        readingState := state
        readingPossible := ?_ }
    · apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [observationPoint, model,
          CCL.ProgressiveGaussianIntegration.CellModel.displacement,
          CCL.FiniteExp.scale_re, CCL.FiniteExp.scale_im, add_re, add_im,
          sub_re, sub_im] <;> ring1
    · change coefficient.name.process.Possible state reading
      exact initialReading_possible coefficient
  exact
    { model := model
      start_eq := rfl
      finish_eq := rfl
      observations := .cons algebraic (.nil) }

/-- Algebraically certified integration cells aligned with the geometric path
of one successful dependent subdivision. -/
structure CertifiedSubdivision {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) <= left ∧ left <= 1}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left))}
    (sheet : Fin 2)
    (subdivision : CCL.Riemann.ClearSheetContinuation.Subdivision
      segment within left leftInside owner) where
  cells : List CellModel
  certificates : PathCertificates curve differential cells
    (CCL.Riemann.BranchCutLifts.ClearPath.liftOnSheet sheet
      subdivision.toClearPath)

/-- Build the cell-for-cell algebraic certificates from the same recursive
subdivision that transported the square-root owner. -/
def certifySubdivision {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) <= left ∧ left <= 1}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left))}
    (sheet : Fin 2) :
    (subdivision : CCL.Riemann.ClearSheetContinuation.Subdivision
      segment within left leftInside owner) →
      CertifiedSubdivision curve differential sheet subdivision
  | .stop _ _ _ =>
      { cells := []
        certificates := .nil _ }
  | .next left leftInside owner right rightInside small remaining => by
      let restricted :=
        segment.restrict within left right leftInside rightInside
      let head := inheritedEndpointSample curve differential restricted sheet
        (CCL.Riemann.ClearSheetContinuation.advance segment within
          left right leftInside rightInside owner small)
      let tail := certifySubdivision curve differential sheet remaining
      exact
        { cells := head.model :: tail.cells
          certificates := .cons head.start_eq head.finish_eq
            head.observations tail.certificates }

@[simp] theorem certifySubdivision_cellCount {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) <= left ∧ left <= 1}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left))}
    (sheet : Fin 2)
    (subdivision : CCL.Riemann.ClearSheetContinuation.Subdivision
      segment within left leftInside owner) :
    (certifySubdivision curve differential sheet subdivision).cells.length =
      subdivision.stepCount := by
  induction subdivision with
  | stop => rfl
  | next left leftInside owner right rightInside small remaining
      inductionHypothesis =>
      exact congrArg Nat.succ inductionHypothesis

/-- A sheet switch contributes no affine displacement.  Its exact zero local
model therefore needs no sampled quotient while still following the same
lifted edge. -/
def switch {genus : Nat} (curve : HyperellipticCurve genus)
    (differential : Differential genus) (coordinate : Gaussian)
    (sheet : Fin 2) :
    CertifiedCell curve differential (switchCell coordinate sheet) := by
  let model : CellModel := CCL.ProgressiveGaussianIntegration.CellModel.exact
    coordinate coordinate CCL.FiniteGaussianPolynomial.zero
  exact
    { model := model
      start_eq := rfl
      finish_eq := rfl
      observations := .nil }

end CCL.Riemann.ClearDifferentialObservations
