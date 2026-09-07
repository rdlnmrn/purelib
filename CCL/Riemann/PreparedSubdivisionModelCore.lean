import CCL.Riemann.PreparedBoundaryEquivalence

/-!
# Uniform models for a complete prepared subdivision

This module folds the shrinking constant-cell constructor over a successful
dependent continuation mesh.  The result is a finite path model together with
cell-for-cell uniform algebraic certification on the inherited sheet.
-/

namespace CCL.Riemann.PreparedSubdivisionModels

open CCL.Riemann.AlgebraicDifferentials
open CCL.Riemann.BranchCuts
open CCL.Riemann.BranchCutLifts
open CCL.Riemann.LiftedPaths

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Box := RFAP.Boxes.Box
abbrev Owner := CCL.Riemann.SquareRootContinuationChain.Owner
abbrev Endpoint := CCL.Riemann.ClearSheetContinuation.Subdivision.Endpoint
abbrev StepRequest := CCL.Riemann.PreparedSheetContinuation.StepRequest
abbrev CellModel := CCL.ProgressiveGaussianIntegration.CellModel
abbrev PathModel := CCL.ProgressiveGaussianIntegration.PathModel
abbrev NamedEquivalent := CCL.OperationalEquivalence.NamedEquivalent
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev PreparedEdge {genus : Nat} (curve : HyperellipticCurve genus)
    (differential : Differential genus) :=
  CCL.Riemann.PreparedConstantModels.PreparedEdge curve differential
abbrev PreparedSubdivision {polynomial :
    RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left : CCL.Riemann.ClearSheetContinuation.Subdivision.Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter))) :=
  CCL.Riemann.PreparedSheetContinuation.Subdivision segment within left owner

/-- A squared Gaussian movement bound gives the real-coordinate lower
endpoint needed by literal path certificates. -/
theorem real_sub_radius_le_of_normSq_sub_le
    {left right : Gaussian} {radius : Coordinate}
    (radiusNonnegative : 0 <= radius)
    (bounded : RFAP.ConstructiveGaussian.Gaussian.normSq (left - right) <=
      radius ^ 2) :
    left.re - radius <= right.re := by
  have realSquare : (left - right).re ^ 2 <= radius ^ 2 := by
    calc
      (left - right).re ^ 2 <=
          (left - right).re ^ 2 + (left - right).im ^ 2 :=
        le_add_of_nonneg_right
          (RFAP.ConstructiveFraction.sq_nonneg_direct (left - right).im)
      _ = RFAP.ConstructiveGaussian.Gaussian.normSq (left - right) := rfl
      _ <= radius ^ 2 := bounded
  have realUpper : (left - right).re <= radius :=
    RFAP.ConstructiveFraction.le_of_sq_le_sq_direct radiusNonnegative
      realSquare
  calc
    left.re - radius <= left.re - (left - right).re :=
      RFAP.ConstructiveFraction.sub_le_sub_left_direct realUpper left.re
    _ = right.re := by
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re]
      ring1

/-- A squared movement bound stated in the operational `right - left`
orientation gives the same real-coordinate lower endpoint.  Keeping the
subtraction symmetry generic prevents concrete prepared models from being
expanded merely to reverse their difference. -/
theorem real_sub_radius_le_of_normSq_reverse_sub_le
    {left right : Gaussian} {radius : Coordinate}
    (radiusNonnegative : 0 <= radius)
    (bounded : RFAP.ConstructiveGaussian.Gaussian.normSq (right - left) <=
      radius ^ 2) :
    left.re - radius <= right.re := by
  apply real_sub_radius_le_of_normSq_sub_le radiusNonnegative
  have reverse : left - right = -(right - left) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.neg_re,
        RFAP.ConstructiveGaussian.Gaussian.neg_im] <;> ring1
  rw [reverse, RFAP.ConstructiveGaussian.Gaussian.normSq_neg]
  exact bounded

/-- The terminal interval parameter lies in the closed unit interval.  This
small shared certificate is exposed so the independently elaborated automatic
model layer can reuse the kernel proof. -/
theorem endpointInside :
    (0 : Coordinate) <= 1 ∧ (1 : Coordinate) <= 1 := by decide

/-- Repackage one accepted dependent-subdivision step as its prepared edge.
This is the common constructor shared by the core fold and automatic model
layer. -/
def edgeOfStep {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left : Endpoint)
    (owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CCL.Riemann.PreparedSheetContinuation.CachedSource segment left
      owner request)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (CCL.Riemann.PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (sheet : Fin 2) : PreparedEdge curve differential where
  ambient := ambient
  start := start
  finish := finish
  segment := segment
  within := within
  left := left
  owner := owner
  request := request
  cached := cached
  ordered := ordered
  small := small
  sheet := sheet

/-- Forget only the dependent subdivision spine, exposing its accepted
prepared edges before any coefficient centres are requested. -/
def preparedEdges {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    PreparedSubdivision segment within left owner ->
      List (PreparedEdge curve differential)
  | .stop _ _ => []
  | .next left owner request cached ordered small remaining =>
      edgeOfStep curve differential segment within left owner request cached
          ordered small sheet ::
        preparedEdges curve differential sheet remaining

/-- Two adjacent coefficient names together with their finite operational
comparison.  The surrounding dependent fold determines which two edges the
names came from without forcing those large indices into the structure type. -/
structure BoundaryWitness where
  parentName : CCL.ProgressiveTransducer.Named
  childName : CCL.ProgressiveTransducer.Named
  equivalent : NamedEquivalent parentName childName

/-- One accepted prepared chart together with its operational certificate that
the local wedge of two standard hyperelliptic differentials vanishes at every
rational point of the chart.  The pointwise argument retains its finite
interval witness, so no completed function space is introduced. -/
structure WedgeChart {genus : Nat}
    (curve : HyperellipticCurve genus)
    (leftDifferential rightDifferential : Differential genus) where
  coefficient : (fraction : Coordinate) ->
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) -> CoherentNamed
  zero : forall (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1),
    NamedEquivalent (coefficient fraction inside).name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name

/-- Package the zero-wedge theorem for one actual step of a prepared
subdivision.  Both differential values use the same owner-backed sheet root. -/
private def wedgeChartOfStep {genus : Nat}
    (curve : HyperellipticCurve genus)
    (leftDifferential rightDifferential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left : Endpoint)
    (owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (CCL.Riemann.PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (sheet : Fin 2) :
    WedgeChart curve leftDifferential rightDifferential where
  coefficient := fun fraction inside =>
    CCL.Riemann.PreparedDifferentialModels.wedgeCoefficientAt curve
      leftDifferential rightDifferential segment within left owner request
        ordered small sheet fraction inside
  zero := fun fraction inside =>
    CCL.Riemann.PreparedDifferentialModels.wedgeCoefficientAt_zero curve
      leftDifferential rightDifferential segment within left owner request
        ordered small sheet fraction inside

/-- The complete finite list of local zero-wedge charts carried by a
successful dependent subdivision. -/
def wedgeCharts {genus : Nat}
    (curve : HyperellipticCurve genus)
    (leftDifferential rightDifferential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    (subdivision : PreparedSubdivision segment within left owner) ->
      List (WedgeChart curve leftDifferential rightDifferential)
  | .stop _ _ => []
  | .next left owner request _cached ordered small remaining =>
      wedgeChartOfStep curve leftDifferential rightDifferential segment within
          left owner request ordered small sheet ::
        wedgeCharts curve leftDifferential rightDifferential sheet remaining

/-- The zero-wedge fold contains exactly one certified chart for every
accepted continuation step. -/
@[simp] theorem wedgeCharts_length {genus : Nat}
    (curve : HyperellipticCurve genus)
    (leftDifferential rightDifferential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (subdivision : PreparedSubdivision segment within left owner) :
    (wedgeCharts curve leftDifferential rightDifferential sheet
      subdivision).length = subdivision.stepCount := by
  induction subdivision with
  | stop => rfl
  | next left owner request cached ordered small remaining
      inductionHypothesis =>
      exact congrArg Nat.succ inductionHypothesis

/-- The finite integration model and its uniform algebraic semantics for one
successful prepared continuation subdivision. -/
structure CertifiedSubdivision {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : CCL.Riemann.ClearSheetContinuation.Subdivision.Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (subdivision : PreparedSubdivision segment within left owner) where
  cells : List CellModel
  certificates : UniformPathCertificates curve differential cells
    (ClearPath.liftOnSheet sheet subdivision.toClearPath)

/-- One persisted coefficient-centre choice for every edge of a successful
prepared subdivision.  The choices are dependent because each later edge
carries the freshly reconditioned square-root owner computed by the previous
step. -/
def CenterStates {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : CCL.Riemann.ClearSheetContinuation.Subdivision.Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    (subdivision : PreparedSubdivision segment within left owner) -> Type
  | .stop _ _ => Unit
  | .next left owner request cached ordered small remaining =>
      let head := edgeOfStep curve differential segment within left owner
        request cached ordered small sheet
      CCL.Riemann.PreparedConstantModels.PreparedEdge.CenterState head ×
        CenterStates curve differential sheet remaining

/-- One accepted prepared edge together with the persisted coefficient centre
selected for its constant integration model. -/
structure CenteredEdge {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus) where
  edge : PreparedEdge curve differential
  center : CCL.Riemann.PreparedConstantModels.PreparedEdge.CenterState edge

namespace CenteredEdge

def model {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (centered : CenteredEdge curve differential) : CellModel :=
  centered.edge.centeredModel centered.center

/-- One untrusted literal coefficient/denominator pair for a centred edge,
together with the two exact local checks that make it a valid recache. -/
structure RecacheCertificate {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (centered : CenteredEdge curve differential) where
  value : Gaussian
  denominator : Gaussian
  denominatorPossible :
    (centered.edge.sheetValue 0
      centered.edge.baseInside).value.name.process.Possible
        centered.center.state.2 denominator
  valueEq :
    value = centered.edge.point 0 ^ differential.exponent / denominator

namespace RecacheCertificate

/-- The locally checked literal pair as an ordinary persisted centre. -/
def center {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {centered : CenteredEdge curve differential}
    (certificate : RecacheCertificate centered) :=
  centered.center.recache certificate.value certificate.denominator
    certificate.denominatorPossible certificate.valueEq

/-- Constant cell whose coefficient is the supplied literal rational. -/
def model {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {centered : CenteredEdge curve differential}
    (certificate : RecacheCertificate centered) : CellModel :=
  centered.edge.centeredModel certificate.center

/-- Recaching changes only the constant coefficient.  The geometric segment
and its local allowance are definitionally identical to the canonical cell. -/
@[simp] theorem model_weightedAllowance {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {centered : CenteredEdge curve differential}
    (certificate : RecacheCertificate centered) :
    certificate.model.weightedAllowance = centered.model.weightedAllowance :=
  rfl

/-- The literal cell is a checked one-cell partition of the canonical
centred cell at the same process state. -/
def partitionCertificate {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {centered : CenteredEdge curve differential}
    (certificate : RecacheCertificate centered) :
    CCL.ProgressiveGaussianIntegration.PathModel.ConstantPartitionCertificate
      centered.model
      (CCL.ProgressiveGaussianIntegration.PathModel.mk [certificate.model]) :=
  centered.edge.centeredModelRecachePartitionCertificate centered.center
    certificate.value certificate.denominator certificate.denominatorPossible
      certificate.valueEq

end RecacheCertificate

/-- Sign-aware rational lower endpoint for the real integral of one centred
genus-one prepared edge. -/
def integralRealLower {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (centered : CenteredEdge curve differential) : Coordinate :=
  centered.edge.centeredModelIntegralRealDyadicLower centered.center

/-- The retained owner box and sheet apartness certify the displayed lower
endpoint for one centred edge. -/
theorem integralRealLower_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (centered : CenteredEdge curve differential)
    (exponentZero : differential.exponent = 0) :
    centered.integralRealLower <= centered.model.integralSample.re :=
  centered.edge.centeredModelIntegralRealDyadicLower_le centered.center
    exponentZero

/-- Centre-free endpoint for the negative real projection of one centred
prepared edge. -/
def negatedIntegralRealLower {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (centered : CenteredEdge curve differential) : Coordinate :=
  centered.edge.geometricNegatedIntegralRealDyadicLower

theorem negatedIntegralRealLower_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (centered : CenteredEdge curve differential)
    (exponentZero : differential.exponent = 0) :
    centered.negatedIntegralRealLower <= -centered.model.integralSample.re :=
  centered.edge.geometricNegatedIntegralRealDyadicLower_le centered.center
    exponentZero

/-- Centre-free endpoint for one arbitrary rational projection of a centred
prepared edge. -/
def directionalIntegralLower {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (centered : CenteredEdge curve differential)
    (direction : Gaussian) : Coordinate :=
  centered.edge.geometricDirectionalIntegralDyadicLower direction

theorem directionalIntegralLower_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (centered : CenteredEdge curve differential)
    (direction : Gaussian)
    (exponentZero : differential.exponent = 0) :
    centered.directionalIntegralLower direction <=
      direction.re * centered.model.integralSample.re +
        direction.im * centered.model.integralSample.im :=
  centered.edge.geometricDirectionalIntegralDyadicLower_le centered.center
    direction exponentZero

/-- Sharper cell endpoint obtained from the finite process ball retained by
the selected centre. -/
def ballIntegralRealLower {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (centered : CenteredEdge curve differential) : Coordinate :=
  centered.edge.centeredBallIntegralRealDyadicLower centered.center

theorem ballIntegralRealLower_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (centered : CenteredEdge curve differential)
    (exponentZero : differential.exponent = 0) :
    centered.ballIntegralRealLower <= centered.model.integralSample.re :=
  centered.edge.centeredBallIntegralRealDyadicLower_le centered.center
    exponentZero

/-- Sharp negative-real counterpart using the same retained process ball. -/
def ballNegatedIntegralRealLower {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (centered : CenteredEdge curve differential) : Coordinate :=
  centered.edge.centeredBallNegatedIntegralRealDyadicLower centered.center

theorem ballNegatedIntegralRealLower_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (centered : CenteredEdge curve differential)
    (exponentZero : differential.exponent = 0) :
    centered.ballNegatedIntegralRealLower <=
      -centered.model.integralSample.re :=
  centered.edge.centeredBallNegatedIntegralRealDyadicLower_le centered.center
    exponentZero

/-- Sharp arbitrary-direction endpoint from the retained coefficient process
ball. -/
def ballDirectionalIntegralLower {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (centered : CenteredEdge curve differential)
    (direction : Gaussian) : Coordinate :=
  centered.edge.centeredBallDirectionalIntegralDyadicLower centered.center
    direction

theorem ballDirectionalIntegralLower_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (centered : CenteredEdge curve differential)
    (direction : Gaussian)
    (exponentZero : differential.exponent = 0) :
    centered.ballDirectionalIntegralLower direction <=
      direction.re * centered.model.integralSample.re +
        direction.im * centered.model.integralSample.im :=
  centered.edge.centeredBallDirectionalIntegralDyadicLower_le centered.center
    direction exponentZero

def parameterEdge {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (centered : CenteredEdge curve differential) :
    CCL.Riemann.ClearSheetContinuation.Subdivision.ParameterEdge :=
  { left := centered.edge.left
    right := centered.edge.request.endpoint }

/-- The displayed constant cell retains the exact geometric displacement of
its accepted prepared edge. -/
theorem model_displacement {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (centered : CenteredEdge curve differential) :
    centered.model.displacement =
      centered.edge.segment.pointAt centered.edge.request.endpoint.parameter -
        centered.edge.segment.pointAt centered.edge.left.parameter := by
  unfold model CCL.Riemann.PreparedConstantModels.PreparedEdge.centeredModel
    CCL.ProgressiveGaussianIntegration.CellModel.displacement
  change centered.edge.point 1 - centered.edge.point 0 = _
  have pointZero : centered.edge.point 0 =
      centered.edge.segment.pointAt centered.edge.left.parameter := by
    change
      (CCL.Riemann.PreparedDifferentialModels.edge curve centered.edge.segment
        centered.edge.within centered.edge.left
          centered.edge.request).pointAt 0 = _
    unfold CCL.Riemann.PreparedDifferentialModels.edge
    simpa only [CCL.Riemann.PreparedSheetContinuation.parameterAt_zero] using
      (CCL.Riemann.PreparedSheetContinuation.pointAt_parameterAt
        centered.edge.segment centered.edge.within centered.edge.left
          centered.edge.request 0).symm
  have pointOne : centered.edge.point 1 =
      centered.edge.segment.pointAt
        centered.edge.request.endpoint.parameter := by
    change
      (CCL.Riemann.PreparedDifferentialModels.edge curve centered.edge.segment
        centered.edge.within centered.edge.left
          centered.edge.request).pointAt 1 = _
    unfold CCL.Riemann.PreparedDifferentialModels.edge
    simpa only [CCL.Riemann.PreparedSheetContinuation.parameterAt_one] using
      (CCL.Riemann.PreparedSheetContinuation.pointAt_parameterAt
        centered.edge.segment centered.edge.within centered.edge.left
          centered.edge.request 1).symm
  rw [pointZero, pointOne]

end CenteredEdge

/-- A cell-for-cell literal recache of one finite centred path.  The
dependent shape forces every supplied coefficient to be checked against the
exact edge and process state it replaces. -/
inductive CenteredPathRecache {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    List (CenteredEdge curve differential) -> Type
  | nil : CenteredPathRecache []
  | cons {head : CenteredEdge curve differential}
      {tail : List (CenteredEdge curve differential)}
      (certificate : head.RecacheCertificate)
      (remaining : CenteredPathRecache tail) :
      CenteredPathRecache (head :: tail)

namespace CenteredPathRecache

/-- Concatenate independently checked certificate chunks without rebuilding
either chunk.  Large generated payloads can therefore stay below ordinary
elaboration limits while their final path remains definitionally ordered. -/
def append {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    {first second : List (CenteredEdge curve differential)} ->
      CenteredPathRecache first -> CenteredPathRecache second ->
        CenteredPathRecache (first ++ second)
  | [], _, .nil, second => second
  | _ :: _, _, .cons certificate remaining, second =>
      .cons certificate (remaining.append second)

/-- The literal constant cells retained by a complete recache. -/
def models {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    {edges : List (CenteredEdge curve differential)} ->
      CenteredPathRecache edges -> List CellModel
  | [], .nil => []
  | _ :: _, .cons certificate remaining =>
      certificate.model :: remaining.models

/-- Chunk concatenation preserves the exact literal cell order. -/
@[simp] theorem models_append {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {first second : List (CenteredEdge curve differential)}
      (left : CenteredPathRecache first)
      (right : CenteredPathRecache second),
      (left.append right).models = left.models ++ right.models
  | [], _, .nil, _ => rfl
  | _ :: _, _, .cons _ remaining, right => by
      simp only [append, models, List.cons_append]
      rw [remaining.models_append right]

/-- Cellwise recache certificates compose to one exact constant path
refinement.  Its standard child aggregate allowance bounds the complete
literal-minus-canonical integral discrepancy. -/
def toConstantPathRefinement {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    {edges : List (CenteredEdge curve differential)} ->
      (recache : CenteredPathRecache edges) ->
      CCL.ProgressiveGaussianIntegration.PathModel.ConstantPathRefinement
        (edges.map CenteredEdge.model) recache.models
  | [], .nil => .nil
  | _ :: _, .cons certificate remaining =>
      .cons certificate.partitionCertificate
        remaining.toConstantPathRefinement

def literalModel {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {edges : List (CenteredEdge curve differential)}
    (recache : CenteredPathRecache edges) : PathModel :=
  ⟨recache.models⟩

def canonicalModel {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (edges : List (CenteredEdge curve differential)) : PathModel :=
  ⟨edges.map CenteredEdge.model⟩

/-- A cell-for-cell literal recache has exactly the canonical path length. -/
@[simp] theorem models_length {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {edges : List (CenteredEdge curve differential)}
      (recache : CenteredPathRecache edges),
      recache.models.length = edges.length
  | [], .nil => rfl
  | _ :: _, .cons _ remaining => by
      simp only [models, List.length_cons]
      rw [remaining.models_length]

/-- Literal coefficients do not alter the finite weighted error budget. -/
theorem totalWeightedAllowance_eq {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {edges : List (CenteredEdge curve differential)}
      (recache : CenteredPathRecache edges),
      recache.literalModel.totalWeightedAllowance =
        (canonicalModel edges).totalWeightedAllowance
  | [], .nil => rfl
  | head :: tail, .cons certificate remaining => by
      change certificate.model.weightedAllowance +
          remaining.literalModel.totalWeightedAllowance =
        head.model.weightedAllowance +
          (canonicalModel tail).totalWeightedAllowance
      rw [certificate.model_weightedAllowance,
        remaining.totalWeightedAllowance_eq]

/-- The complete aggregate allowance is invariant under a literal recache. -/
theorem aggregateAllowance_eq {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {edges : List (CenteredEdge curve differential)}
    (recache : CenteredPathRecache edges) :
    recache.literalModel.aggregateAllowance =
      (canonicalModel edges).aggregateAllowance := by
  unfold CCL.ProgressiveGaussianIntegration.PathModel.aggregateAllowance
  rw [recache.totalWeightedAllowance_eq]
  change (recache.models.length : Coordinate) * _ =
    ((edges.map CenteredEdge.model).length : Coordinate) * _
  rw [recache.models_length, List.length_map]

/-- Exact finite error accounting for the complete literal recache. -/
theorem integralDifference_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {edges : List (CenteredEdge curve differential)}
    (recache : CenteredPathRecache edges) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (recache.literalModel.integralSample -
          (canonicalModel edges).integralSample) <=
      recache.literalModel.aggregateAllowance :=
  recache.toConstantPathRefinement.integral_difference_le

/-- A displayed rational movement radius turns the exact recache error into
a lower endpoint for the canonical path's real integral. -/
theorem literalRealLower_le_canonical {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {edges : List (CenteredEdge curve differential)}
    (recache : CenteredPathRecache edges)
    (movement : Coordinate) (movementNonnegative : 0 <= movement)
    (allowanceLe : recache.literalModel.aggregateAllowance <= movement ^ 2) :
    recache.literalModel.integralSample.re - movement <=
      (canonicalModel edges).integralSample.re :=
  real_sub_radius_le_of_normSq_sub_le movementNonnegative
    (recache.integralDifference_le.trans allowanceLe)

/-- Canonical model bounds can be reused verbatim for a literal recache,
because recaching changes neither cell geometry nor local allowances. -/
theorem literalRealLower_le_canonical_of_canonicalAllowance {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {edges : List (CenteredEdge curve differential)}
    (recache : CenteredPathRecache edges)
    (movement : Coordinate) (movementNonnegative : 0 <= movement)
    (allowanceLe : (canonicalModel edges).aggregateAllowance <= movement ^ 2) :
    recache.literalModel.integralSample.re - movement <=
      (canonicalModel edges).integralSample.re :=
  recache.literalRealLower_le_canonical movement movementNonnegative (by
    rw [recache.aggregateAllowance_eq]
    exact allowanceLe)

/-- Compact theorem-facing payload for a positive displayed real lower bound.
Its only numerical obligations concern the literal finite model and one
canonical allowance radius; the path comparison itself is supplied by the
checked recache above. -/
structure PositiveLiteralRealLowerCertificate {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (edges : List (CenteredEdge curve differential)) where
  recache : CenteredPathRecache edges
  movement : Coordinate
  movementNonnegative : 0 <= movement
  allowanceLe : (canonicalModel edges).aggregateAllowance <= movement ^ 2
  lower : Coordinate
  lowerPositive : 0 < lower
  literalLower : lower <=
    recache.literalModel.integralSample.re - movement

namespace PositiveLiteralRealLowerCertificate

/-- The displayed positive endpoint bounds the canonical finite path sample. -/
theorem lower_le_canonical {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {edges : List (CenteredEdge curve differential)}
    (certificate : PositiveLiteralRealLowerCertificate edges) :
    certificate.lower <= (canonicalModel edges).integralSample.re :=
  certificate.literalLower.trans
    (certificate.recache.literalRealLower_le_canonical_of_canonicalAllowance
      certificate.movement certificate.movementNonnegative
        certificate.allowanceLe)

/-- In particular the canonical real sample is strictly positive. -/
theorem canonical_positive {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {edges : List (CenteredEdge curve differential)}
    (certificate : PositiveLiteralRealLowerCertificate edges) :
    0 < (canonicalModel edges).integralSample.re :=
  certificate.lowerPositive.trans_le certificate.lower_le_canonical

end PositiveLiteralRealLowerCertificate

end CenteredPathRecache

/-- Sum of the finite sign-aware lower endpoints attached to a list of
centred prepared edges. -/
def centeredEdgesIntegralRealLower {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (edges : List (CenteredEdge curve differential)) : Coordinate :=
  edges.foldr (fun edge total => edge.integralRealLower + total) 0

theorem centeredEdgesIntegralRealLower_append {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (first second : List (CenteredEdge curve differential)) :
    centeredEdgesIntegralRealLower (first ++ second) =
      centeredEdgesIntegralRealLower first +
        centeredEdgesIntegralRealLower second := by
  induction first with
  | nil =>
      unfold centeredEdgesIntegralRealLower
      simp only [List.nil_append, List.foldr_nil,
        RFAP.ConstructiveFraction.zero_add]
  | cons edge remaining inductionHypothesis =>
      unfold centeredEdgesIntegralRealLower at inductionHypothesis ⊢
      simp only [List.cons_append, List.foldr_cons]
      rw [inductionHypothesis]
      ring1

/-- Cellwise rational lower endpoints add to a lower bound for the real part
of the complete finite path sample. -/
theorem centeredEdgesIntegralRealLower_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (exponentZero : differential.exponent = 0) :
    forall edges : List (CenteredEdge curve differential),
      centeredEdgesIntegralRealLower edges <=
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          (edges.map CenteredEdge.model)).integralSample.re
  | [] => by
      unfold centeredEdgesIntegralRealLower
        CCL.ProgressiveGaussianIntegration.PathModel.integralSample
      rfl
  | edge :: remaining => by
      unfold centeredEdgesIntegralRealLower
      simp only [List.foldr_cons, List.map_cons,
        CCL.ProgressiveGaussianIntegration.PathModel.integralSample]
      exact add_le_add (edge.integralRealLower_le exponentZero)
        (centeredEdgesIntegralRealLower_le exponentZero remaining)

/-- Sum of cellwise lower endpoints for the negative real projection. -/
def centeredEdgesNegatedIntegralRealLower {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (edges : List (CenteredEdge curve differential)) : Coordinate :=
  edges.foldr (fun edge total => edge.negatedIntegralRealLower + total) 0

theorem centeredEdgesNegatedIntegralRealLower_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (exponentZero : differential.exponent = 0) :
    forall edges : List (CenteredEdge curve differential),
      centeredEdgesNegatedIntegralRealLower edges <=
        -(CCL.ProgressiveGaussianIntegration.PathModel.mk
          (edges.map CenteredEdge.model)).integralSample.re
  | [] => by
      unfold centeredEdgesNegatedIntegralRealLower
        CCL.ProgressiveGaussianIntegration.PathModel.integralSample
      rfl
  | edge :: remaining => by
      unfold centeredEdgesNegatedIntegralRealLower
      simp only [List.foldr_cons, List.map_cons,
        CCL.ProgressiveGaussianIntegration.PathModel.integralSample]
      have combined := add_le_add
        (edge.negatedIntegralRealLower_le exponentZero)
        (centeredEdgesNegatedIntegralRealLower_le exponentZero remaining)
      unfold centeredEdgesNegatedIntegralRealLower at combined
      unfold CCL.ProgressiveGaussianIntegration.PathModel.integralSample at combined
      rw [RFAP.ConstructiveGaussian.Gaussian.add_re]
      exact combined.trans_eq (by ring1)

/-- Sum of the centre-free endpoints for one fixed rational projection. -/
def centeredEdgesDirectionalIntegralLower {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (direction : Gaussian)
    (edges : List (CenteredEdge curve differential)) : Coordinate :=
  edges.foldr (fun edge total =>
    edge.directionalIntegralLower direction + total) 0

theorem centeredEdgesDirectionalIntegralLower_append {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (direction : Gaussian)
    (first second : List (CenteredEdge curve differential)) :
    centeredEdgesDirectionalIntegralLower direction (first ++ second) =
      centeredEdgesDirectionalIntegralLower direction first +
        centeredEdgesDirectionalIntegralLower direction second := by
  induction first with
  | nil =>
      unfold centeredEdgesDirectionalIntegralLower
      simp only [List.nil_append, List.foldr_nil,
        RFAP.ConstructiveFraction.zero_add]
  | cons edge remaining inductionHypothesis =>
      unfold centeredEdgesDirectionalIntegralLower at inductionHypothesis ⊢
      simp only [List.cons_append, List.foldr_cons]
      rw [inductionHypothesis]
      ring1

/-- Directional endpoints add to a lower bound for the same projection of
the complete finite path sample. -/
theorem centeredEdgesDirectionalIntegralLower_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (direction : Gaussian)
    (exponentZero : differential.exponent = 0) :
    forall edges : List (CenteredEdge curve differential),
      centeredEdgesDirectionalIntegralLower direction edges <=
        direction.re *
            (CCL.ProgressiveGaussianIntegration.PathModel.mk
              (edges.map CenteredEdge.model)).integralSample.re +
          direction.im *
            (CCL.ProgressiveGaussianIntegration.PathModel.mk
              (edges.map CenteredEdge.model)).integralSample.im
  | [] => by
      unfold centeredEdgesDirectionalIntegralLower
        CCL.ProgressiveGaussianIntegration.PathModel.integralSample
      simp only [List.map_nil, List.foldr_nil,
        RFAP.ConstructiveGaussian.Gaussian.zero_re,
        RFAP.ConstructiveGaussian.Gaussian.zero_im,
        RFAP.ConstructiveFraction.mul_zero_direct, zero_add]
      exact (le_refl (0 : Coordinate))
  | edge :: remaining => by
      unfold centeredEdgesDirectionalIntegralLower
      simp only [List.foldr_cons, List.map_cons,
        CCL.ProgressiveGaussianIntegration.PathModel.integralSample,
        RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im]
      have combined := add_le_add
        (edge.directionalIntegralLower_le direction exponentZero)
        (centeredEdgesDirectionalIntegralLower_le direction exponentZero
          remaining)
      unfold centeredEdgesDirectionalIntegralLower at combined
      unfold CCL.ProgressiveGaussianIntegration.PathModel.integralSample at combined
      exact combined.trans_eq (by ring1)

/-- Sum of the sharp process-ball endpoints over a finite centred edge list. -/
def centeredEdgesBallIntegralRealLower {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (edges : List (CenteredEdge curve differential)) : Coordinate :=
  edges.foldr (fun edge total => edge.ballIntegralRealLower + total) 0

theorem centeredEdgesBallIntegralRealLower_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (exponentZero : differential.exponent = 0) :
    forall edges : List (CenteredEdge curve differential),
      centeredEdgesBallIntegralRealLower edges <=
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          (edges.map CenteredEdge.model)).integralSample.re
  | [] => by
      unfold centeredEdgesBallIntegralRealLower
        CCL.ProgressiveGaussianIntegration.PathModel.integralSample
      rfl
  | edge :: remaining => by
      unfold centeredEdgesBallIntegralRealLower
      simp only [List.foldr_cons, List.map_cons,
        CCL.ProgressiveGaussianIntegration.PathModel.integralSample]
      exact add_le_add (edge.ballIntegralRealLower_le exponentZero)
        (centeredEdgesBallIntegralRealLower_le exponentZero remaining)

/-- Sum of the sharp negative-real process-ball endpoints. -/
def centeredEdgesBallNegatedIntegralRealLower {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (edges : List (CenteredEdge curve differential)) : Coordinate :=
  edges.foldr (fun edge total => edge.ballNegatedIntegralRealLower + total) 0

theorem centeredEdgesBallNegatedIntegralRealLower_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (exponentZero : differential.exponent = 0) :
    forall edges : List (CenteredEdge curve differential),
      centeredEdgesBallNegatedIntegralRealLower edges <=
        -(CCL.ProgressiveGaussianIntegration.PathModel.mk
          (edges.map CenteredEdge.model)).integralSample.re
  | [] => by
      unfold centeredEdgesBallNegatedIntegralRealLower
        CCL.ProgressiveGaussianIntegration.PathModel.integralSample
      rfl
  | edge :: remaining => by
      unfold centeredEdgesBallNegatedIntegralRealLower
      simp only [List.foldr_cons, List.map_cons,
        CCL.ProgressiveGaussianIntegration.PathModel.integralSample]
      have combined := add_le_add
        (edge.ballNegatedIntegralRealLower_le exponentZero)
        (centeredEdgesBallNegatedIntegralRealLower_le exponentZero remaining)
      unfold centeredEdgesBallNegatedIntegralRealLower at combined
      unfold CCL.ProgressiveGaussianIntegration.PathModel.integralSample at combined
      rw [RFAP.ConstructiveGaussian.Gaussian.add_re]
      exact combined.trans_eq (by ring1)

/-- Sum of sharp process-ball endpoints for one fixed rational projection. -/
def centeredEdgesBallDirectionalIntegralLower {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (direction : Gaussian)
    (edges : List (CenteredEdge curve differential)) : Coordinate :=
  edges.foldr (fun edge total =>
    edge.ballDirectionalIntegralLower direction + total) 0

theorem centeredEdgesBallDirectionalIntegralLower_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (direction : Gaussian)
    (exponentZero : differential.exponent = 0) :
    forall edges : List (CenteredEdge curve differential),
      centeredEdgesBallDirectionalIntegralLower direction edges <=
        direction.re *
            (CCL.ProgressiveGaussianIntegration.PathModel.mk
              (edges.map CenteredEdge.model)).integralSample.re +
          direction.im *
            (CCL.ProgressiveGaussianIntegration.PathModel.mk
              (edges.map CenteredEdge.model)).integralSample.im
  | [] => by
      unfold centeredEdgesBallDirectionalIntegralLower
        CCL.ProgressiveGaussianIntegration.PathModel.integralSample
      simp only [List.map_nil, List.foldr_nil,
        RFAP.ConstructiveGaussian.Gaussian.zero_re,
        RFAP.ConstructiveGaussian.Gaussian.zero_im,
        RFAP.ConstructiveFraction.mul_zero_direct, zero_add]
      exact (le_refl (0 : Coordinate))
  | edge :: remaining => by
      unfold centeredEdgesBallDirectionalIntegralLower
      simp only [List.foldr_cons, List.map_cons,
        CCL.ProgressiveGaussianIntegration.PathModel.integralSample,
        RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im]
      have combined := add_le_add
        (edge.ballDirectionalIntegralLower_le direction exponentZero)
        (centeredEdgesBallDirectionalIntegralLower_le direction exponentZero
          remaining)
      unfold centeredEdgesBallDirectionalIntegralLower at combined
      unfold CCL.ProgressiveGaussianIntegration.PathModel.integralSample at combined
      exact combined.trans_eq (by ring1)

/-- Fold the same sign-aware endpoints directly over preparation geometry.
Unlike `centeredEdgesIntegralRealLower`, evaluating this definition never
constructs a coefficient centre. -/
def preparedSubdivisionIntegralRealLower {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    PreparedSubdivision segment within left owner -> Coordinate
  | .stop _ _ => 0
  | .next current owner request cached ordered small remaining =>
      let edge := edgeOfStep curve differential segment within current owner
        request cached ordered small sheet
      edge.geometricIntegralRealDyadicLower +
        preparedSubdivisionIntegralRealLower curve differential sheet remaining

/-- Centre-free negative-real counterpart of
`preparedSubdivisionIntegralRealLower`. -/
def preparedSubdivisionNegatedIntegralRealLower {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    PreparedSubdivision segment within left owner -> Coordinate
  | .stop _ _ => 0
  | .next current owner request cached ordered small remaining =>
      let edge := edgeOfStep curve differential segment within current owner
        request cached ordered small sheet
      edge.geometricNegatedIntegralRealDyadicLower +
        preparedSubdivisionNegatedIntegralRealLower curve differential sheet
          remaining

/-- Centre-free geometric fold for one arbitrary rational projection. -/
def preparedSubdivisionDirectionalIntegralLower {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) (direction : Gaussian) :
    PreparedSubdivision segment within left owner -> Coordinate
  | .stop _ _ => 0
  | .next current owner request cached ordered small remaining =>
      let edge := edgeOfStep curve differential segment within current owner
        request cached ordered small sheet
      edge.geometricDirectionalIntegralDyadicLower direction +
        preparedSubdivisionDirectionalIntegralLower curve differential sheet
          direction remaining

/-- A displayed endpoint written in the local unit coordinate of one coarse
prepared edge.  This is finite geometric data: no inverse path or completed
parameterization is stored. -/
structure ParentPosition {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : PreparedEdge curve differential) (current : Endpoint) where
  fraction : Coordinate
  inside : (0 : Coordinate) <= fraction ∧ fraction <= 1
  parameter_eq :
    CCL.Riemann.PreparedSheetContinuation.parameterAt parent.left
      parent.request fraction = current.parameter

namespace ParentPosition

/-- The parent's direct query and the fixed prepared-source query at the
displayed endpoint are literally the same productive root after rewriting
the finite parameter equality. -/
def directRootEquivalent {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parent : PreparedEdge curve differential} {current : Endpoint}
    (position : ParentPosition parent current)
    (sourceCurrentSmall :
      CCL.Riemann.PreparedSheetContinuation.Subdivision.DirectMoveSmall
        parent.segment parent.left
          (CCL.Riemann.PreparedSheetContinuation.prepared parent.segment
            parent.left parent.owner parent.request) current) :
    NamedEquivalent
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        (parent.segment.pointAt_eval_ne_zero
          (CCL.Riemann.PreparedSheetContinuation.parameterAt parent.left
            parent.request position.fraction)
          (CCL.Riemann.PreparedSheetContinuation.parameterAt_inside parent.left
            parent.request parent.ordered position.fraction position.inside))
        (parent.directQueryOwner position.fraction position.inside))
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        (parent.segment.pointAt_eval_ne_zero current.parameter current.inside)
        (CCL.Riemann.PreparedSheetContinuation.Subdivision.directOwnerAt
          parent.left
          (CCL.Riemann.PreparedSheetContinuation.prepared parent.segment
            parent.left parent.owner parent.request)
          current sourceCurrentSmall)) := by
  cases current with
  | mk parameter currentInside =>
      cases position with
      | mk fraction inside parameterEq =>
          dsimp only at parameterEq
          subst parameter
          have cachedName_eq : parent.rootName fraction inside =
              CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
                (parent.segment.pointAt_eval_ne_zero
                  (CCL.Riemann.PreparedSheetContinuation.parameterAt parent.left
                    parent.request fraction)
                  (CCL.Riemann.PreparedSheetContinuation.parameterAt_inside
                    parent.left parent.request parent.ordered fraction inside))
                (CCL.Riemann.ExactQuadraticOwnerClearance.reservedTransport
                  (CCL.Riemann.PreparedSheetContinuation.prepared parent.segment
                    parent.left parent.owner parent.request)
                  (parent.segment.pointAt_eval_ne_zero
                    (CCL.Riemann.PreparedSheetContinuation.parameterAt parent.left
                      parent.request fraction)
                    (CCL.Riemann.PreparedSheetContinuation.parameterAt_inside
                      parent.left parent.request parent.ordered fraction inside))
                  (CCL.Riemann.PreparedSheetContinuation.pointNormSmall
                    parent.segment parent.within parent.left parent.owner
                      parent.request parent.ordered parent.small fraction inside)
                  (CCL.Riemann.PreparedSheetContinuation.transportReserve
                    parent.segment parent.left parent.request)) := by
            unfold CCL.Riemann.PreparedConstantModels.PreparedEdge.rootName
            rw [CCL.Riemann.PreparedSheetContinuation.CachedSource.eq_canonical
              parent.cached]
            unfold CCL.Riemann.PreparedDifferentialModels.rootAtCached
            apply
              CCL.Riemann.PreparedSheetContinuation.reservedTransportRootName_proof_irrel
          have directName_eq :=
            parent.rootName_eq_directQueryOwnerRootName fraction inside
          have directToCanonical := directName_eq.symm.trans cachedName_eq
          rw [directToCanonical]
          exact
            (CCL.Riemann.PreparedSheetContinuation.reservedTransportRootEquivalentGeneric
              (CCL.Riemann.PreparedSheetContinuation.prepared parent.segment
                parent.left parent.owner parent.request)
              (parent.segment.pointAt_eval_ne_zero
                (CCL.Riemann.PreparedSheetContinuation.parameterAt parent.left
                  parent.request fraction)
                (CCL.Riemann.PreparedSheetContinuation.parameterAt_inside
                  parent.left parent.request parent.ordered fraction inside))
              sourceCurrentSmall.proof
              (CCL.Riemann.PreparedSheetContinuation.transportReserve
                parent.segment parent.left parent.request)).symm

/-- The accepted coarse edge supplies the direct-move inequality for every
displayed position inside it. -/
theorem directMoveSmall {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parent : PreparedEdge curve differential} {current : Endpoint}
    (position : ParentPosition parent current) :
    CCL.Riemann.PreparedSheetContinuation.Subdivision.DirectMoveSmall
      parent.segment parent.left
        (CCL.Riemann.PreparedSheetContinuation.prepared parent.segment
          parent.left parent.owner parent.request) current := by
  constructor
  cases current with
  | mk parameter currentInside =>
      cases position with
      | mk fraction inside parameterEq =>
          dsimp only at parameterEq
          subst parameter
          exact CCL.Riemann.PreparedSheetContinuation.pointNormSmall
            parent.segment parent.within parent.left parent.owner
              parent.request parent.ordered parent.small fraction inside

/-- The same parent-position move indexed by the prepared owner already
stored on the edge.  The specification equality is proof-only, so executable
child construction consumes the cached owner rather than rebuilding it. -/
theorem cachedDirectMoveSmall {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parent : PreparedEdge curve differential} {current : Endpoint}
    (position : ParentPosition parent current) :
    CCL.Riemann.PreparedSheetContinuation.Subdivision.DirectMoveSmall
      parent.segment parent.left parent.cached.preparedOwner current := by
  rw [parent.cached.preparedOwner_eq]
  exact position.directMoveSmall

private theorem directOwnerAt_eq_of_source_eq
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    (origin current : Endpoint)
    {first second : Owner
      (polynomial.eval (segment.pointAt origin.parameter))}
    (equal : first = second)
    (firstSmall :
      CCL.Riemann.PreparedSheetContinuation.Subdivision.DirectMoveSmall
        segment origin first current)
    (secondSmall :
      CCL.Riemann.PreparedSheetContinuation.Subdivision.DirectMoveSmall
        segment origin second current) :
    CCL.Riemann.PreparedSheetContinuation.Subdivision.directOwnerAt
        origin first current firstSmall =
      CCL.Riemann.PreparedSheetContinuation.Subdivision.directOwnerAt
        origin second current secondSmall := by
  cases equal
  rfl

/-- The cached parent source gives the same productive root at a displayed
child endpoint as the canonical prepared-source presentation. -/
def cachedDirectRootEquivalent {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parent : PreparedEdge curve differential} {current : Endpoint}
    (position : ParentPosition parent current) :
    NamedEquivalent
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        (parent.segment.pointAt_eval_ne_zero
          (CCL.Riemann.PreparedSheetContinuation.parameterAt parent.left
            parent.request position.fraction)
          (CCL.Riemann.PreparedSheetContinuation.parameterAt_inside parent.left
            parent.request parent.ordered position.fraction position.inside))
        (parent.directQueryOwner position.fraction position.inside))
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        (parent.segment.pointAt_eval_ne_zero current.parameter current.inside)
        (CCL.Riemann.PreparedSheetContinuation.Subdivision.directOwnerAt
          parent.left parent.cached.preparedOwner current
            position.cachedDirectMoveSmall)) := by
  rw [directOwnerAt_eq_of_source_eq parent.left current
    parent.cached.preparedOwner_eq position.cachedDirectMoveSmall
      position.directMoveSmall]
  exact position.directRootEquivalent position.directMoveSmall

/-- Canonical local fraction of an endpoint lying between the two distinct
parent endpoints. -/
def ofBetween {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parent : PreparedEdge curve differential} {current : Endpoint}
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (between : parent.left.parameter <= current.parameter ∧
      current.parameter <= parent.request.endpoint.parameter) :
    ParentPosition parent current := by
  let width := parent.request.endpoint.parameter - parent.left.parameter
  let offset := current.parameter - parent.left.parameter
  have widthPositive : 0 < width :=
    RFAP.ConstructiveFraction.sub_pos_direct proper
  have offsetNonnegative : 0 <= offset :=
    RFAP.ConstructiveFraction.sub_nonneg_direct between.1
  let fraction := offset / width
  have fractionNonnegative : 0 <= fraction :=
    RFAP.ConstructiveFraction.div_nonneg_direct offsetNonnegative
      widthPositive.le
  have offsetLeWidth : offset <= width :=
    RFAP.ConstructiveFraction.sub_le_sub_right_direct between.2
      parent.left.parameter
  have fractionLeOne : fraction <= 1 := by
    apply (RFAP.ConstructiveFraction.div_le_iff_pos widthPositive).2
    simpa only [RFAP.ConstructiveFraction.one_mul] using offsetLeWidth
  exact
    { fraction := fraction
      inside := ⟨fractionNonnegative, fractionLeOne⟩
      parameter_eq := by
        rw [CCL.Riemann.PreparedSheetContinuation.parameterAt_eq_affine]
        change parent.left.parameter + offset / width * width =
          current.parameter
        rw [RFAP.ConstructiveFraction.div_mul_cancel_of_ne offset width
          widthPositive.ne']
        ring1 }

end ParentPosition

/-- One fine centred edge starting at a displayed point of a coarse centred
edge, with the sheet occurrence identified at that common point. -/
structure RootChildAt {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent child : CenteredEdge curve differential) where
  fraction : Coordinate
  inside : (0 : Coordinate) <= fraction ∧ fraction <= 1
  point_eq : parent.edge.point fraction = child.edge.point 0
  rootEquivalent : NamedEquivalent
    (parent.edge.rootName fraction inside)
    (child.edge.rootName 0 child.edge.baseInside)

namespace RootChildAt

/-- Forget the root-only presentation after deriving the differential
coefficient relation and its canonical finite query state. -/
def toCenteredChildAt {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parent child : CenteredEdge curve differential}
    (relation : RootChildAt parent child) :
    CCL.Riemann.PreparedConstantModels.PreparedEdge.CenteredChildAt
      parent.edge parent.center :=
  CCL.Riemann.PreparedConstantModels.PreparedEdge.CenteredChildAt.ofRootEquivalent
    parent.edge child.edge parent.center child.center relation.fraction
      relation.inside relation.point_eq relation.rootEquivalent

@[simp] theorem toCenteredChildAt_model {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parent child : CenteredEdge curve differential}
    (relation : RootChildAt parent child) :
    relation.toCenteredChildAt.model = child.model := rfl

end RootChildAt

/-- Convert one directly coherent fine step into the root-only child witness
for a displayed coarse parent.  The parent uses its fixed prepared source;
the child uses the recursively transported fine owner. -/
def rootChildAtOfDirectStep {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CenteredEdge curve differential)
    (current : Endpoint)
    (owner : Owner
      (curve.polynomial.eval (parent.edge.segment.pointAt current.parameter)))
    (request : StepRequest)
    (cached : CCL.Riemann.PreparedSheetContinuation.CachedSource
      parent.edge.segment current owner request)
    (ordered : current.parameter <= request.endpoint.parameter)
    (childSmall : CCL.Riemann.ClearSheetContinuation.variationBound
      parent.edge.segment current.parameter request.endpoint.parameter <
        (CCL.Riemann.PreparedSheetContinuation.prepared parent.edge.segment
          current owner request).track.initial.clearance.bound)
    (center :
      CCL.Riemann.PreparedConstantModels.PreparedEdge.CenterState
        (edgeOfStep curve differential parent.edge.segment parent.edge.within
          current owner request cached ordered childSmall parent.edge.sheet))
    (sourceCurrentSmall :
      CCL.Riemann.PreparedSheetContinuation.Subdivision.DirectMoveSmall
        parent.edge.segment parent.edge.left
          (CCL.Riemann.PreparedSheetContinuation.prepared parent.edge.segment
            parent.edge.left parent.edge.owner parent.edge.request) current)
    (currentEquivalent :
      CCL.Riemann.PreparedSheetContinuation.Subdivision.RootEquivalentAt
        parent.edge.segment current
          (CCL.Riemann.PreparedSheetContinuation.Subdivision.directOwnerAt
            parent.edge.left
            (CCL.Riemann.PreparedSheetContinuation.prepared parent.edge.segment
              parent.edge.left parent.edge.owner parent.edge.request)
            current sourceCurrentSmall)
          owner)
    (position : ParentPosition parent.edge current) :
    RootChildAt parent
      { edge := edgeOfStep curve differential parent.edge.segment
          parent.edge.within current owner request cached ordered childSmall
            parent.edge.sheet
        center := center } := by
  let childEdge := edgeOfStep curve differential parent.edge.segment
    parent.edge.within current owner request cached ordered childSmall
      parent.edge.sheet
  let child : CenteredEdge curve differential :=
    { edge := childEdge
      center := center }
  have parentPoint : parent.edge.point position.fraction =
      parent.edge.segment.pointAt
        (CCL.Riemann.PreparedSheetContinuation.parameterAt parent.edge.left
          parent.edge.request position.fraction) :=
    (CCL.Riemann.PreparedSheetContinuation.pointAt_parameterAt
      parent.edge.segment parent.edge.within parent.edge.left
        parent.edge.request position.fraction).symm
  have childPoint : parent.edge.segment.pointAt current.parameter =
      childEdge.point 0 := by
    change parent.edge.segment.pointAt current.parameter =
      (CCL.Riemann.PreparedDifferentialModels.edge curve parent.edge.segment
        parent.edge.within current request).pointAt 0
    unfold CCL.Riemann.PreparedDifferentialModels.edge
    simpa only [CCL.Riemann.PreparedSheetContinuation.parameterAt_zero] using
      CCL.Riemann.PreparedSheetContinuation.pointAt_parameterAt
        parent.edge.segment parent.edge.within current request 0
  have pointEqual : parent.edge.point position.fraction = childEdge.point 0 :=
    parentPoint.trans ((congrArg parent.edge.segment.pointAt
      position.parameter_eq).trans childPoint)
  have queryToDirect := position.directRootEquivalent sourceCurrentSmall
  have directToOwner := currentEquivalent.toNamedEquivalent
  have ownerToChild := childEdge.ownerRootEquivalent_baseQuery
  exact
    { fraction := position.fraction
      inside := position.inside
      point_eq := pointEqual
      rootEquivalent := by
        rw [parent.edge.rootName_eq_directQueryOwnerRootName position.fraction
          position.inside]
        exact CCL.OperationalEquivalence.NamedEquivalent.trans queryToDirect
          (CCL.OperationalEquivalence.NamedEquivalent.trans directToOwner
            ownerToChild) }

/-- Ordered sheet-occurrence evidence for every fine edge in one coarse
parent block. -/
inductive RootChildBlock {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CenteredEdge curve differential) :
    List (CenteredEdge curve differential) -> Type
  | nil : RootChildBlock parent []
  | cons {child : CenteredEdge curve differential}
      {children : List (CenteredEdge curve differential)}
      (head : RootChildAt parent child)
      (tail : RootChildBlock parent children) :
      RootChildBlock parent (child :: children)

namespace RootChildBlock

def childAts {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parent : CenteredEdge curve differential} :
    forall {children : List (CenteredEdge curve differential)},
      RootChildBlock parent children ->
        List
          (CCL.Riemann.PreparedConstantModels.PreparedEdge.CenteredChildAt
            parent.edge parent.center)
  | [], .nil => []
  | _ :: _, .cons head tail => head.toCenteredChildAt :: tail.childAts

@[simp] theorem childAts_models {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parent : CenteredEdge curve differential} :
    forall {children : List (CenteredEdge curve differential)}
      (block : RootChildBlock parent children),
      block.childAts.map
          CCL.Riemann.PreparedConstantModels.PreparedEdge.CenteredChildAt.model =
        children.map CenteredEdge.model
  | [], .nil => rfl
  | _ :: _, .cons head tail => by
      simp only [childAts, List.map_cons, RootChildAt.toCenteredChildAt_model,
        childAts_models tail]

/-- Root coherence plus exact finite geometry gives the comparison-aware
partition certificate for one coarse parent. -/
def partitionCertificate {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parent : CenteredEdge curve differential}
    {children : List (CenteredEdge curve differential)}
    (block : RootChildBlock parent children)
    (displacement_eq :
      CCL.ProgressiveGaussianIntegration.PathModel.displacementSum
          (children.map CenteredEdge.model) = parent.model.displacement) :
    CCL.ProgressiveGaussianIntegration.PathModel.ConstantPartitionCertificate
      parent.model
      (CCL.ProgressiveGaussianIntegration.PathModel.comparisonBlock
        parent.model
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          (children.map CenteredEdge.model))) := by
  have modelsEqual := block.childAts_models
  rw [← modelsEqual]
  exact
    CCL.Riemann.PreparedConstantModels.PreparedEdge.CenteredChildAt.partitionCertificate
      block.childAts (by
        rw [modelsEqual]
        simpa only [CenteredEdge.model] using displacement_eq)

end RootChildBlock

/-- Whole-list refinement of centred prepared edges, grouped parent by parent
and carrying only finite sheet-occurrence and displacement evidence. -/
inductive CenteredEdgeRefinement {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    List (CenteredEdge curve differential) ->
      List (CenteredEdge curve differential) -> Type
  | nil : CenteredEdgeRefinement [] []
  | cons
      (parent : CenteredEdge curve differential)
      {parents childEdges children : List (CenteredEdge curve differential)}
      (block : RootChildBlock parent childEdges)
      (displacement_eq :
        CCL.ProgressiveGaussianIntegration.PathModel.displacementSum
            (childEdges.map CenteredEdge.model) = parent.model.displacement)
      (remaining : CenteredEdgeRefinement
        (curve := curve) (differential := differential) parents children) :
      CenteredEdgeRefinement (parent :: parents) (childEdges ++ children)

namespace CenteredEdgeRefinement

/-- The root-coherent centred-edge relation constructs the integration
kernel's compatible constant refinement. -/
def toCompatible {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {parents children : List (CenteredEdge curve differential)},
      CenteredEdgeRefinement parents children ->
        CCL.ProgressiveGaussianIntegration.PathModel.CompatibleConstantPathRefinement
          (parents.map CenteredEdge.model) (children.map CenteredEdge.model)
  | [], [], .nil => .nil
  | _, _, .cons parent block displacement_eq remaining => by
      simp only [List.map_cons, List.map_append]
      exact .cons (block.partitionCertificate displacement_eq)
        (toCompatible remaining)

end CenteredEdgeRefinement

/-- Expose the dependent accepted steps and centre family as one ordinary
finite list. -/
def centeredEdges {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : CCL.Riemann.ClearSheetContinuation.Subdivision.Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    (subdivision : PreparedSubdivision segment within left owner) ->
      CenterStates curve differential sheet subdivision ->
        List (CenteredEdge curve differential)
  | .stop _ _, _ => []
  | .next left owner request cached ordered small remaining, centers =>
      { edge := edgeOfStep curve differential segment within left owner request
          cached ordered small sheet
        center := centers.1 } ::
        centeredEdges curve differential sheet remaining centers.2

/-- The centre-free geometric fold is definitionally the endpoint fold of
every centred presentation of the same prepared subdivision. -/
theorem preparedSubdivisionIntegralRealLower_eq_centeredEdges
    {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    forall (subdivision : PreparedSubdivision segment within left owner)
      (centers : CenterStates curve differential sheet subdivision),
      preparedSubdivisionIntegralRealLower curve differential sheet subdivision =
        centeredEdgesIntegralRealLower
          (centeredEdges curve differential sheet subdivision centers)
  | .stop _ _, _centers => rfl
  | .next current owner request cached ordered small remaining, centers => by
      simp only [preparedSubdivisionIntegralRealLower, centeredEdges,
        centeredEdgesIntegralRealLower, List.foldr_cons,
        CenteredEdge.integralRealLower,
        CCL.Riemann.PreparedConstantModels.PreparedEdge.centeredModelIntegralRealDyadicLower]
      rw [preparedSubdivisionIntegralRealLower_eq_centeredEdges curve
        differential sheet remaining centers.2]
      rfl

/-- Preparation geometry alone computes a lower endpoint for every centred
model built over the same subdivision. -/
theorem preparedSubdivisionIntegralRealLower_le {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (subdivision : PreparedSubdivision segment within left owner)
    (centers : CenterStates curve differential sheet subdivision)
    (exponentZero : differential.exponent = 0) :
    preparedSubdivisionIntegralRealLower curve differential sheet subdivision <=
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        ((centeredEdges curve differential sheet subdivision centers).map
          CenteredEdge.model)).integralSample.re := by
  rw [preparedSubdivisionIntegralRealLower_eq_centeredEdges curve differential
    sheet subdivision centers]
  exact centeredEdgesIntegralRealLower_le exponentZero _

/-- The centre-free directional fold is definitionally the corresponding
endpoint fold of every centred presentation. -/
theorem preparedSubdivisionDirectionalIntegralLower_eq_centeredEdges
    {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) (direction : Gaussian) :
    forall (subdivision : PreparedSubdivision segment within left owner)
      (centers : CenterStates curve differential sheet subdivision),
      preparedSubdivisionDirectionalIntegralLower curve differential sheet
          direction subdivision =
        centeredEdgesDirectionalIntegralLower direction
          (centeredEdges curve differential sheet subdivision centers)
  | .stop _ _, _centers => rfl
  | .next current owner request cached ordered small remaining, centers => by
      simp only [preparedSubdivisionDirectionalIntegralLower, centeredEdges,
        centeredEdgesDirectionalIntegralLower, List.foldr_cons,
        CenteredEdge.directionalIntegralLower]
      rw [preparedSubdivisionDirectionalIntegralLower_eq_centeredEdges curve
        differential sheet direction remaining centers.2]
      rfl

/-- Preparation geometry alone bounds the requested projection of every
centred model over the same subdivision. -/
theorem preparedSubdivisionDirectionalIntegralLower_le {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) (direction : Gaussian)
    (subdivision : PreparedSubdivision segment within left owner)
    (centers : CenterStates curve differential sheet subdivision)
    (exponentZero : differential.exponent = 0) :
    preparedSubdivisionDirectionalIntegralLower curve differential sheet
        direction subdivision <=
      direction.re *
          (CCL.ProgressiveGaussianIntegration.PathModel.mk
            ((centeredEdges curve differential sheet subdivision centers).map
              CenteredEdge.model)).integralSample.re +
        direction.im *
          (CCL.ProgressiveGaussianIntegration.PathModel.mk
            ((centeredEdges curve differential sheet subdivision centers).map
              CenteredEdge.model)).integralSample.im := by
  rw [preparedSubdivisionDirectionalIntegralLower_eq_centeredEdges curve
    differential sheet direction subdivision centers]
  exact centeredEdgesDirectionalIntegralLower_le direction exponentZero _

/-- Centre-free and centred negative-real folds agree on the same prepared
subdivision. -/
theorem preparedSubdivisionNegatedIntegralRealLower_eq_centeredEdges
    {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    forall (subdivision : PreparedSubdivision segment within left owner)
      (centers : CenterStates curve differential sheet subdivision),
      preparedSubdivisionNegatedIntegralRealLower curve differential sheet
          subdivision =
        centeredEdgesNegatedIntegralRealLower
          (centeredEdges curve differential sheet subdivision centers)
  | .stop _ _, _centers => rfl
  | .next current owner request cached ordered small remaining, centers => by
      simp only [preparedSubdivisionNegatedIntegralRealLower, centeredEdges,
        centeredEdgesNegatedIntegralRealLower, List.foldr_cons,
        CenteredEdge.negatedIntegralRealLower]
      rw [preparedSubdivisionNegatedIntegralRealLower_eq_centeredEdges curve
        differential sheet remaining centers.2]
      rfl

/-- Preparation geometry alone computes a lower endpoint for the negative
real part of every centred model on the subdivision. -/
theorem preparedSubdivisionNegatedIntegralRealLower_le {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (subdivision : PreparedSubdivision segment within left owner)
    (centers : CenterStates curve differential sheet subdivision)
    (exponentZero : differential.exponent = 0) :
    preparedSubdivisionNegatedIntegralRealLower curve differential sheet
        subdivision <=
      -(CCL.ProgressiveGaussianIntegration.PathModel.mk
        ((centeredEdges curve differential sheet subdivision centers).map
          CenteredEdge.model)).integralSample.re := by
  rw [preparedSubdivisionNegatedIntegralRealLower_eq_centeredEdges curve
    differential sheet subdivision centers]
  exact centeredEdgesNegatedIntegralRealLower_le exponentZero _

/-- The ordinary centred-edge view has exactly one entry for every accepted
prepared subdivision step. -/
@[simp] theorem centeredEdges_length {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : CCL.Riemann.ClearSheetContinuation.Subdivision.Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    forall (subdivision : PreparedSubdivision segment within left owner)
      (centers : CenterStates curve differential sheet subdivision),
      (centeredEdges curve differential sheet subdivision centers).length =
        subdivision.stepCount
  | .stop _ _, _ => rfl
  | .next left owner request cached ordered small remaining, centers => by
      simp only [centeredEdges, List.length_cons,
        CCL.Riemann.PreparedSheetContinuation.Subdivision.stepCount]
      rw [centeredEdges_length curve differential sheet remaining centers.2]

/-- The exposed centred-edge list retains exactly the accepted subdivision's
parameter mesh. -/
theorem centeredEdges_parameterEdges {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : CCL.Riemann.ClearSheetContinuation.Subdivision.Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    forall (subdivision : PreparedSubdivision segment within left owner)
      (centers : CenterStates curve differential sheet subdivision),
      (centeredEdges curve differential sheet subdivision centers).map
          CenteredEdge.parameterEdge = subdivision.parameterEdges
  | .stop _ _, _ => rfl
  | .next left owner request cached ordered small remaining, centers => by
      simp only [centeredEdges, List.map_cons,
        CCL.Riemann.PreparedSheetContinuation.Subdivision.parameterEdges,
        CenteredEdge.parameterEdge]
      rw [centeredEdges_parameterEdges curve differential sheet remaining
        centers.2]
      rfl

/-- The displacements of all displayed cells telescope exactly from the
subdivision's current endpoint to its terminal endpoint. -/
theorem centeredEdges_displacementSum {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : CCL.Riemann.ClearSheetContinuation.Subdivision.Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    forall (subdivision : PreparedSubdivision segment within left owner)
      (centers : CenterStates curve differential sheet subdivision),
      CCL.ProgressiveGaussianIntegration.PathModel.displacementSum
          ((centeredEdges curve differential sheet subdivision centers).map
            CenteredEdge.model) =
        segment.pointAt subdivision.endpoint.parameter -
          segment.pointAt left.parameter
  | .stop current owner, _ => by
      simp only [centeredEdges, List.map_nil,
        CCL.ProgressiveGaussianIntegration.PathModel.displacementSum_nil,
        CCL.Riemann.PreparedSheetContinuation.Subdivision.endpoint]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.zero_re,
          RFAP.ConstructiveGaussian.Gaussian.zero_im,
          RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im] <;> ring1
  | .next current owner request cached ordered small remaining, centers => by
      simp only [centeredEdges, List.map_cons,
        CCL.ProgressiveGaussianIntegration.PathModel.displacementSum_cons]
      rw [CenteredEdge.model_displacement]
      rw [centeredEdges_displacementSum curve differential sheet remaining
        centers.2]
      change
        (segment.pointAt request.endpoint.parameter -
            segment.pointAt current.parameter) +
          (segment.pointAt remaining.endpoint.parameter -
            segment.pointAt request.endpoint.parameter) =
        segment.pointAt remaining.endpoint.parameter -
          segment.pointAt current.parameter
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im,
          RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im] <;> ring1

/-- A fine subdivision with the coarse parent's terminal parameter has
exactly the parent's displacement. -/
theorem centeredEdges_displacement_eq_parent {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CenteredEdge curve differential)
    (subdivision : PreparedSubdivision parent.edge.segment parent.edge.within
      parent.edge.left parent.edge.owner)
    (centers : CenterStates curve differential parent.edge.sheet subdivision)
    (endpoint_eq : subdivision.endpoint.parameter =
      parent.edge.request.endpoint.parameter) :
    CCL.ProgressiveGaussianIntegration.PathModel.displacementSum
        ((centeredEdges curve differential parent.edge.sheet subdivision
          centers).map CenteredEdge.model) = parent.model.displacement := by
  rw [centeredEdges_displacementSum]
  rw [endpoint_eq]
  exact (CenteredEdge.model_displacement parent).symm

end CCL.Riemann.PreparedSubdivisionModels
