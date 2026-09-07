import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeRing
import CCL.Calculus.FiniteIntegration
import CCL.Progressive.FiniteTable

/-!
# General certified integration by finite path refinements

An integrand is supplied operationally: at each natural refinement it returns
one finite path of rational polynomial cell models and finite rational sample
certificates.  The integration program sums the exact polynomial cell
integrals.  A rational geometric modulus and a finite later-refinement
certificate turn those displayed sums into an ordinary productive CCL name.

There is no measure, completed partition, function-as-an-infinite-set, or
infinitesimal.  The only universal refinements are natural-number calls to the
supplied finite program.
-/

namespace CCL.ProgressiveIntegration

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Polynomial := CCL.FinitePolynomial.Polynomial
abbrev Approximation :=
  CCL.ProgressiveApproximation.Approximation
abbrev CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed

open RFAP.ConstructiveGaussian.Gaussian

/-- One displayed observation checked against a local finite polynomial
model. -/
structure LocalObservation (polynomial : Polynomial)
    (allowance : Coordinate) where
  parameter : Coordinate
  integrandReading : Gaussian
  error : Gaussian
  decomposition :
    integrandReading - CCL.FinitePolynomial.eval polynomial
      ⟨parameter, 0⟩ = error
  error_le : normSq error ≤ allowance

/-- A rationally parameterized segment with one finite polynomial integrand
model and finitely many checked readings. -/
structure CellModel where
  start : Gaussian
  finish : Gaussian
  polynomial : Polynomial
  localAllowance : Coordinate
  localAllowance_nonneg : 0 ≤ localAllowance
  observations : List (LocalObservation polynomial localAllowance)

namespace CellModel

def displacement (cell : CellModel) : Gaussian := cell.finish - cell.start

/-- Exact integral of the finite local polynomial against its affine segment
parameter. -/
def integralSample (cell : CellModel) : Gaussian :=
  cell.displacement *
    CCL.FiniteIntegration.definiteIntegral cell.polynomial 0 1

/-- Squared-error contribution after multiplying a local integrand error by
the displayed segment displacement. -/
def weightedAllowance (cell : CellModel) : Coordinate :=
  normSq cell.displacement * cell.localAllowance

/-- A local polynomial with no model discrepancy. -/
def exact (start finish : Gaussian) (polynomial : Polynomial) : CellModel :=
  { start := start
    finish := finish
    polynomial := polynomial
    localAllowance := 0
    localAllowance_nonneg := le_rfl
    observations := [] }

/-- Exact compatibility with the existing finite-polynomial integrator. -/
theorem exact_integralSample (start finish : Gaussian)
    (polynomial : Polynomial) :
    (exact start finish polynomial).integralSample =
      (finish - start) *
        CCL.FiniteIntegration.definiteIntegral polynomial 0 1 :=
  rfl

theorem weightedAllowance_nonneg (cell : CellModel) :
    0 ≤ cell.weightedAllowance :=
  RFAP.ConstructiveFraction.mul_nonneg_direct
    (normSq_nonneg cell.displacement) cell.localAllowance_nonneg

/-- The explicit cell-weight error transport. -/
theorem weighted_error_le (cell : CellModel) {error : Gaussian}
    (bounded : normSq error ≤ cell.localAllowance) :
    normSq (cell.displacement * error) ≤ cell.weightedAllowance := by
  rw [normSq_mul]
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct bounded
    (normSq_nonneg cell.displacement)

/-- Certificate needed to reverse a local parameterization.  It records the
finite polynomial obtained after the caller's explicit substitution and the
exact rational equality of its parameter integral. -/
structure ReversalCertificate (cell : CellModel) where
  reversedPolynomial : Polynomial
  integral_eq :
    CCL.FiniteIntegration.definiteIntegral reversedPolynomial 0 1 =
      CCL.FiniteIntegration.definiteIntegral cell.polynomial 0 1

/-- Reverse one certified cell, using an explicitly supplied finite
reparameterization certificate. -/
def reverse (cell : CellModel) (certificate : ReversalCertificate cell) :
    CellModel :=
  { start := cell.finish
    finish := cell.start
    polynomial := certificate.reversedPolynomial
    localAllowance := cell.localAllowance
    localAllowance_nonneg := cell.localAllowance_nonneg
    observations := [] }

theorem reverse_integralSample (cell : CellModel)
    (certificate : ReversalCertificate cell) :
    (cell.reverse certificate).integralSample = -cell.integralSample := by
  unfold reverse integralSample displacement
  rw [certificate.integral_eq]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [sub_re, sub_im, mul_re, mul_im, neg_re, neg_im] <;> ring1

/-- Add two local integrand models on the first cell's displayed segment. -/
def addIntegrand (left right : CellModel) : CellModel :=
  { start := left.start
    finish := left.finish
    polynomial := CCL.FinitePolynomial.add
      left.polynomial right.polynomial
    localAllowance := 2 * (left.localAllowance + right.localAllowance)
    localAllowance_nonneg :=
      RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (add_nonneg left.localAllowance_nonneg right.localAllowance_nonneg)
    observations := [] }

/-- Finite polynomial integration is linear on a common displayed segment. -/
theorem addIntegrand_integralSample (left right : CellModel)
    (sameStart : right.start = left.start)
    (sameFinish : right.finish = left.finish) :
    (left.addIntegrand right).integralSample =
      left.integralSample + right.integralSample := by
  unfold addIntegrand integralSample displacement
  rw [CCL.FiniteIntegration.definiteIntegral_add,
    sameStart, sameFinish]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;> ring1

/-- Scale a local integrand by one displayed rational. -/
def scaleIntegrand (factor : Coordinate) (cell : CellModel) : CellModel :=
  { start := cell.start
    finish := cell.finish
    polynomial := CCL.FinitePolynomial.scale factor cell.polynomial
    localAllowance := factor ^ 2 * cell.localAllowance
    localAllowance_nonneg :=
      RFAP.ConstructiveFraction.mul_nonneg_direct
        (RFAP.ConstructiveFraction.sq_nonneg_direct factor)
        cell.localAllowance_nonneg
    observations := [] }

theorem scaleIntegrand_integralSample (factor : Coordinate)
    (cell : CellModel) :
    (cell.scaleIntegrand factor).integralSample =
      CCL.FiniteExp.scale factor cell.integralSample := by
  unfold scaleIntegrand integralSample displacement
  rw [CCL.FiniteIntegration.definiteIntegral_scale]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [CCL.FiniteExp.scale_re,
      CCL.FiniteExp.scale_im, mul_re, mul_im] <;> ring1

theorem scaleIntegrand_weightedAllowance (factor : Coordinate)
    (cell : CellModel) :
    (cell.scaleIntegrand factor).weightedAllowance =
      factor ^ 2 * cell.weightedAllowance := by
  unfold scaleIntegrand weightedAllowance displacement
  ring1

end CellModel

/-- A displayed finite path model.  Cells may be used for one segment or for
an explicitly supplied piecewise path. -/
structure PathModel where
  cells : List CellModel

namespace PathModel

def integralSample (path : PathModel) : Gaussian :=
  path.cells.foldr (fun cell total => cell.integralSample + total) 0

@[simp] theorem singleton_integralSample (cell : CellModel) :
    (PathModel.mk [cell]).integralSample = cell.integralSample := by
  unfold integralSample
  simp only [List.foldr_cons, List.foldr_nil]
  exact RFAP.ConstructiveGaussian.Gaussian.add_zero _

/-- Coarse but completely explicit squared allowance for the finite sum.  The
factor two at each displayed cell is the ordinary two-term quadrance bound. -/
def aggregateAllowance (path : PathModel) : Coordinate :=
  path.cells.foldr
    (fun cell total => 2 * (cell.weightedAllowance + total)) 0

theorem aggregateAllowance_nonneg (path : PathModel) :
    0 ≤ path.aggregateAllowance := by
  unfold aggregateAllowance
  induction path.cells with
  | nil => exact le_rfl
  | cons cell remaining induction =>
      simp only [List.foldr_cons]
      exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (add_nonneg cell.weightedAllowance_nonneg induction)

/-- Weighted finite error sum aligned with the displayed path cells. -/
def weightedErrorSum : List CellModel → List Gaussian → Gaussian
  | cell :: cells, error :: errors =>
      cell.displacement * error + weightedErrorSum cells errors
  | _, _ => 0

/-- Every supplied error is bounded by the corresponding cell certificate,
with no missing or extra entry. -/
def ErrorsValid : List CellModel → List Gaussian → Prop
  | [], [] => True
  | cell :: cells, error :: errors =>
      normSq error ≤ cell.localAllowance ∧ ErrorsValid cells errors
  | _, _ => False

/-- Local rational allowances and finite cell weights compute a rational
allowance for the whole path integral. -/
theorem weightedErrorSum_le : ∀ (cells : List CellModel)
    (errors : List Gaussian), ErrorsValid cells errors →
      normSq (weightedErrorSum cells errors) ≤
        (PathModel.mk cells).aggregateAllowance
  | [], [], _valid => by
      change normSq (0 : Gaussian) ≤ 0
      rw [normSq_zero]
  | [], _ :: _, valid => by simp only [ErrorsValid] at valid
  | _ :: _, [], valid => by simp only [ErrorsValid] at valid
  | cell :: cells, error :: errors, valid => by
      rcases valid with ⟨errorBound, remainingValid⟩
      change
        normSq
            (cell.displacement * error + weightedErrorSum cells errors) ≤
          2 * (cell.weightedAllowance +
            (PathModel.mk cells).aggregateAllowance)
      exact (normSq_add_le_two _ _).trans
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add (cell.weighted_error_le errorBound)
            (weightedErrorSum_le cells errors remainingValid))
          (by decide))

/-- Concatenation is literal finite-list concatenation. -/
def concat (first second : PathModel) : PathModel :=
  ⟨first.cells ++ second.cells⟩

theorem integralSample_concat (first second : PathModel) :
    (first.concat second).integralSample =
      first.integralSample + second.integralSample := by
  unfold concat integralSample
  rw [QuotientFreeList.foldr_append]
  induction first.cells with
  | nil => exact (RFAP.ConstructiveGaussian.Gaussian.zero_add _).symm
  | cons cell remaining induction =>
      simp only [List.foldr_cons]
      rw [induction]
      exact (RFAP.ConstructiveGaussian.Gaussian.add_assoc _ _ _).symm

/-- Scale every displayed local integrand model on a finite path. -/
def scaleIntegrand (factor : Coordinate) (path : PathModel) : PathModel :=
  ⟨path.cells.map (CellModel.scaleIntegrand factor)⟩

theorem integralSample_scaleIntegrand (factor : Coordinate)
    (path : PathModel) :
    (path.scaleIntegrand factor).integralSample =
      CCL.FiniteExp.scale factor path.integralSample := by
  unfold scaleIntegrand integralSample
  induction path.cells with
  | nil =>
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [List.map_nil, List.foldr_nil,
          CCL.FiniteExp.scale_re,
          CCL.FiniteExp.scale_im, zero_re, zero_im] <;> ring1
  | cons cell remaining induction =>
      simp only [List.map_cons, List.foldr_cons]
      rw [CellModel.scaleIntegrand_integralSample, induction]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [CCL.FiniteExp.scale_re,
          CCL.FiniteExp.scale_im, add_re, add_im] <;> ring1

theorem aggregateAllowance_scaleIntegrand (factor : Coordinate)
    (path : PathModel) :
    (path.scaleIntegrand factor).aggregateAllowance =
      factor ^ 2 * path.aggregateAllowance := by
  unfold scaleIntegrand aggregateAllowance
  induction path.cells with
  | nil =>
      simp only [List.map_nil, List.foldr_nil,
        RFAP.ConstructiveFraction.mul_zero_direct]
  | cons cell remaining induction =>
      simp only [List.map_cons, List.foldr_cons]
      rw [CellModel.scaleIntegrand_weightedAllowance, induction]
      ring1

/-- Cell-by-cell finite evidence for reversing a whole displayed path.  The
order is reversed as well as each affine parameterization. -/
inductive ReversalCells : List CellModel → Type
  | nil : ReversalCells []
  | cons {cell : CellModel} {remaining : List CellModel}
      (head : CellModel.ReversalCertificate cell)
      (tail : ReversalCells remaining) : ReversalCells (cell :: remaining)

namespace ReversalCells

def reversed : {cells : List CellModel} → ReversalCells cells → List CellModel
  | [], .nil => []
  | _ :: _, .cons head tail => tail.reversed ++ [CellModel.reverse _ head]

theorem integralSample_reversed : ∀ {cells : List CellModel}
    (certificate : ReversalCells cells),
    (PathModel.mk certificate.reversed).integralSample =
      -(PathModel.mk cells).integralSample
  | [], .nil => by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [reversed, integralSample, List.foldr_nil, neg_re, neg_im,
          zero_re, zero_im] <;> ring1
  | cell :: remaining, .cons head tail => by
      change
        (PathModel.mk (tail.reversed ++ [CellModel.reverse cell head])).integralSample =
          -(PathModel.mk (cell :: remaining)).integralSample
      rw [show PathModel.mk (tail.reversed ++ [CellModel.reverse cell head]) =
          (PathModel.mk tail.reversed).concat
            (PathModel.mk [CellModel.reverse cell head]) from rfl,
        integralSample_concat, integralSample_reversed tail,
        singleton_integralSample, CellModel.reverse_integralSample]
      change
        -(PathModel.mk remaining).integralSample + -cell.integralSample =
          -(cell.integralSample + (PathModel.mk remaining).integralSample)
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [add_re, add_im, neg_re, neg_im] <;> ring1

end ReversalCells

/-- A structural reversal certificate for one finite displayed path. -/
structure Reversal (path : PathModel) where
  cells : ReversalCells path.cells

def reverse (path : PathModel) (certificate : Reversal path) : PathModel :=
  ⟨certificate.cells.reversed⟩

theorem reverse_integralSample (path : PathModel)
    (certificate : Reversal path) :
    (path.reverse certificate).integralSample = -path.integralSample :=
  certificate.cells.integralSample_reversed

end PathModel

/-! ## Supplied finite antiderivatives -/

/-- One finite polynomial antiderivative certificate for one local cell. -/
structure CellAntiderivative (cell : CellModel) where
  primitive : Polynomial
  derivative_eq :
    CCL.FinitePolynomial.derivative primitive = cell.polynomial
  endpoint_eq :
    cell.displacement *
        (CCL.FinitePolynomial.eval primitive 1 -
          CCL.FinitePolynomial.eval primitive 0) =
      cell.integralSample

namespace CellAntiderivative

/-- The canonical coefficient antiderivative already constructed by the
finite integration layer. -/
def canonical (cell : CellModel) : CellAntiderivative cell :=
  { primitive := CCL.FiniteIntegration.antiderivative 0
      cell.polynomial
    derivative_eq :=
      CCL.FiniteIntegration.derivative_antiderivative 0
        cell.polynomial
    endpoint_eq := by
      unfold CellModel.integralSample
        CCL.FiniteIntegration.definiteIntegral
      rfl }

end CellAntiderivative

/-- A displayed finite path paired cell-by-cell with supplied finite
antiderivative certificates. -/
structure PathAntiderivative where
  entries : List (Sigma fun cell : CellModel => CellAntiderivative cell)

namespace PathAntiderivative

def path (certificate : PathAntiderivative) : PathModel :=
  ⟨certificate.entries.map Sigma.fst⟩

def differenceSample (certificate : PathAntiderivative) : Gaussian :=
  certificate.entries.foldr
    (fun entry total =>
      entry.1.displacement *
          (CCL.FinitePolynomial.eval entry.2.primitive 1 -
            CCL.FinitePolynomial.eval entry.2.primitive 0) +
        total)
    0

/-- The finite FTC: summing supplied antiderivative endpoint differences is
literally the finite polynomial path integral. -/
theorem differenceSample_eq_integralSample
    (certificate : PathAntiderivative) :
    certificate.differenceSample = certificate.path.integralSample := by
  unfold differenceSample path PathModel.integralSample
  induction certificate.entries with
  | nil => rfl
  | cons entry remaining induction =>
      simp only [List.foldr_cons, List.map_cons]
      rw [entry.2.endpoint_eq, induction]

end PathAntiderivative

/-- A finite-refinement integration oracle.  Each call returns a finite path
model.  The geometric radius and explicit later-close proof are a computable
modulus for the displayed integral samples. -/
structure RefinementProgram where
  model : Nat → PathModel
  errorScale : Coordinate
  errorScale_nonneg : 0 ≤ errorScale
  modelAllowance_le : ∀ index,
    (model index).aggregateAllowance ≤
      CCL.FiniteGeometric.quarterRadius errorScale index
  later_close : ∀ {earlier later : Nat}, earlier ≤ later →
    normSq ((model later).integralSample - (model earlier).integralSample) ≤
      CCL.FiniteGeometric.quarterRadius errorScale earlier
  centerBound : Coordinate
  centerBound_nonneg : 0 ≤ centerBound
  sample_bounded : ∀ index,
    normSq (model index).integralSample ≤ centerBound

namespace RefinementProgram

/-- The constant refinement program for one exact finite polynomial segment. -/
def exactPolynomial (start finish : Gaussian) (polynomial : Polynomial) :
    RefinementProgram := by
  let cell := CellModel.exact start finish polynomial
  let path : PathModel := ⟨[cell]⟩
  let sample := path.integralSample
  exact
    { model := fun _ => path
      errorScale := 0
      errorScale_nonneg := le_rfl
      modelAllowance_le := by
        intro index
        change 2 * (normSq cell.displacement * 0 + 0) ≤
          CCL.FiniteGeometric.quarterRadius 0 index
        rw [RFAP.ConstructiveFraction.mul_zero_direct,
          RFAP.ConstructiveFraction.zero_add,
          RFAP.ConstructiveFraction.mul_zero_direct,
          CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
          RFAP.ConstructiveFraction.zero_mul_direct]
      later_close := by
        intro earlier later order
        change normSq (sample - sample) ≤
          CCL.FiniteGeometric.quarterRadius 0 earlier
        rw [sub_self, normSq_zero,
          CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
          RFAP.ConstructiveFraction.zero_mul_direct]
      centerBound := normSq sample
      centerBound_nonneg := normSq_nonneg sample
      sample_bounded := by intro index; exact le_rfl }

/-- Scaling a progressive integrand scales its exact finite path sums and all
quadrance allowances by the displayed rational square. -/
def scale (factor : Coordinate) (program : RefinementProgram) :
    RefinementProgram :=
  { model := fun index => (program.model index).scaleIntegrand factor
    errorScale := factor ^ 2 * program.errorScale
    errorScale_nonneg :=
      RFAP.ConstructiveFraction.mul_nonneg_direct
        (RFAP.ConstructiveFraction.sq_nonneg_direct factor)
        program.errorScale_nonneg
    modelAllowance_le := by
      intro index
      rw [PathModel.aggregateAllowance_scaleIntegrand,
        CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
      have scaled :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (program.modelAllowance_le index)
            (RFAP.ConstructiveFraction.sq_nonneg_direct factor)
      rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow] at scaled
      simpa only [RFAP.ConstructiveFraction.mul_assoc] using scaled
    later_close := by
      intro earlier later order
      rw [PathModel.integralSample_scaleIntegrand,
        PathModel.integralSample_scaleIntegrand]
      have identity :
          CCL.FiniteExp.scale factor
                (program.model later).integralSample -
              CCL.FiniteExp.scale factor
                (program.model earlier).integralSample =
            CCL.FiniteExp.scale factor
              ((program.model later).integralSample -
                (program.model earlier).integralSample) := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [CCL.FiniteExp.scale_re,
            CCL.FiniteExp.scale_im, sub_re, sub_im] <;> ring1
      rw [identity, CCL.FiniteExp.normSq_scale,
        CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
      have scaled :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (program.later_close order)
            (RFAP.ConstructiveFraction.sq_nonneg_direct factor)
      rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow] at scaled
      simpa only [RFAP.ConstructiveFraction.mul_assoc] using scaled
    centerBound := factor ^ 2 * program.centerBound
    centerBound_nonneg :=
      RFAP.ConstructiveFraction.mul_nonneg_direct
        (RFAP.ConstructiveFraction.sq_nonneg_direct factor)
        program.centerBound_nonneg
    sample_bounded := by
      intro index
      rw [PathModel.integralSample_scaleIntegrand,
        CCL.FiniteExp.normSq_scale]
      exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (program.sample_bounded index)
          (RFAP.ConstructiveFraction.sq_nonneg_direct factor) }

@[simp] theorem scale_model (factor : Coordinate)
    (program : RefinementProgram) (index : Nat) :
    (scale factor program).model index =
      (program.model index).scaleIntegrand factor :=
  rfl

theorem scale_integralSample (factor : Coordinate)
    (program : RefinementProgram) (index : Nat) :
    ((scale factor program).model index).integralSample =
      CCL.FiniteExp.scale factor
        (program.model index).integralSample :=
  PathModel.integralSample_scaleIntegrand factor (program.model index)

/-- Finite local data for adding two progressive integrands.  The model at
each displayed refinement may be built by cellwise polynomial addition or by
any equivalent finite re-partitioning; its exact path sum and transported
aggregate allowance are checked explicitly. -/
structure SumModels (left right : RefinementProgram) where
  model : Nat → PathModel
  integral_eq : ∀ index,
    (model index).integralSample =
      (left.model index).integralSample + (right.model index).integralSample
  aggregate_le : ∀ index,
    (model index).aggregateAllowance ≤
      CCL.FiniteGeometric.quarterRadius
        (2 * (left.errorScale + right.errorScale)) index

/-- Progressive linear addition.  Once the finite local sum models are
supplied, convergence and the global rational bound are computed from the
two operand programs. -/
def add (left right : RefinementProgram) (models : SumModels left right) :
    RefinementProgram :=
  { model := models.model
    errorScale := 2 * (left.errorScale + right.errorScale)
    errorScale_nonneg :=
      RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (add_nonneg left.errorScale_nonneg right.errorScale_nonneg)
    modelAllowance_le := models.aggregate_le
    later_close := by
      intro earlier later order
      rw [models.integral_eq, models.integral_eq]
      have identity :
          ((left.model later).integralSample +
                (right.model later).integralSample) -
              ((left.model earlier).integralSample +
                (right.model earlier).integralSample) =
            ((left.model later).integralSample -
                (left.model earlier).integralSample) +
              ((right.model later).integralSample -
                (right.model earlier).integralSample) := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [add_re, add_im, sub_re, sub_im] <;> ring1
      rw [identity]
      calc
        normSq
            (((left.model later).integralSample -
                (left.model earlier).integralSample) +
              ((right.model later).integralSample -
                (right.model earlier).integralSample)) ≤
            2 *
              (normSq ((left.model later).integralSample -
                  (left.model earlier).integralSample) +
                normSq ((right.model later).integralSample -
                  (right.model earlier).integralSample)) :=
          normSq_add_le_two _ _
        _ ≤ 2 *
              (CCL.FiniteGeometric.quarterRadius
                  left.errorScale earlier +
                CCL.FiniteGeometric.quarterRadius
                  right.errorScale earlier) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (add_le_add (left.later_close order) (right.later_close order))
            (by decide)
        _ = CCL.FiniteGeometric.quarterRadius
              (2 * (left.errorScale + right.errorScale)) earlier := by
          rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
            CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
            CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
          ring1
    centerBound := 2 * (left.centerBound + right.centerBound)
    centerBound_nonneg :=
      RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (add_nonneg left.centerBound_nonneg right.centerBound_nonneg)
    sample_bounded := by
      intro index
      rw [models.integral_eq]
      exact (normSq_add_le_two _ _).trans
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add (left.sample_bounded index)
            (right.sample_bounded index)) (by decide)) }

@[simp] theorem add_integralSample (left right : RefinementProgram)
    (models : SumModels left right) (index : Nat) :
    ((add left right models).model index).integralSample =
      (left.model index).integralSample +
        (right.model index).integralSample :=
  models.integral_eq index

/-- The only extra certificate required for path concatenation is the finite
aggregate-allowance calculation for the concatenated cell lists. -/
structure ConcatenationAllowance (left right : RefinementProgram) where
  aggregate_le : ∀ index,
    ((left.model index).concat (right.model index)).aggregateAllowance ≤
      CCL.FiniteGeometric.quarterRadius
        (2 * (left.errorScale + right.errorScale)) index

def concat (left right : RefinementProgram)
    (allowance : ConcatenationAllowance left right) : RefinementProgram :=
  add left right
    { model := fun index => (left.model index).concat (right.model index)
      integral_eq := by
        intro index
        exact PathModel.integralSample_concat _ _
      aggregate_le := allowance.aggregate_le }

@[simp] theorem concat_model (left right : RefinementProgram)
    (allowance : ConcatenationAllowance left right) (index : Nat) :
    (concat left right allowance).model index =
      (left.model index).concat (right.model index) :=
  rfl

theorem concat_integralSample (left right : RefinementProgram)
    (allowance : ConcatenationAllowance left right) (index : Nat) :
    ((concat left right allowance).model index).integralSample =
      (left.model index).integralSample +
        (right.model index).integralSample :=
  PathModel.integralSample_concat _ _

/-- Explicit finite path reversal data.  Reparameterization remains visible:
the caller supplies each reversed finite model, its exact sign law, and its
transported allowance calculation. -/
structure ReversalModels (program : RefinementProgram) where
  model : Nat → PathModel
  integral_eq : ∀ index,
    (model index).integralSample = -(program.model index).integralSample
  aggregate_le : ∀ index,
    (model index).aggregateAllowance ≤
      CCL.FiniteGeometric.quarterRadius program.errorScale index

namespace ReversalModels

/-- Build progressive orientation data from genuine cellwise finite path
reversals, plus the explicit aggregate allowance for the reversed order. -/
def ofPathReversals (program : RefinementProgram)
    (reversals : ∀ index, PathModel.Reversal (program.model index))
    (aggregate_le : ∀ index,
      ((program.model index).reverse (reversals index)).aggregateAllowance ≤
        CCL.FiniteGeometric.quarterRadius
          program.errorScale index) : ReversalModels program :=
  { model := fun index => (program.model index).reverse (reversals index)
    integral_eq := by
      intro index
      exact PathModel.reverse_integralSample _ _
    aggregate_le := aggregate_le }

end ReversalModels

def reverse (program : RefinementProgram) (models : ReversalModels program) :
    RefinementProgram :=
  { model := models.model
    errorScale := program.errorScale
    errorScale_nonneg := program.errorScale_nonneg
    modelAllowance_le := models.aggregate_le
    later_close := by
      intro earlier later order
      rw [models.integral_eq, models.integral_eq]
      have identity :
          -(program.model later).integralSample -
              -(program.model earlier).integralSample =
            -((program.model later).integralSample -
              (program.model earlier).integralSample) := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [neg_re, neg_im, sub_re, sub_im] <;> ring1
      rw [identity, normSq_neg]
      exact program.later_close order
    centerBound := program.centerBound
    centerBound_nonneg := program.centerBound_nonneg
    sample_bounded := by
      intro index
      rw [models.integral_eq, normSq_neg]
      exact program.sample_bounded index }

@[simp] theorem reverse_integralSample (program : RefinementProgram)
    (models : ReversalModels program) (index : Nat) :
    ((reverse program models).model index).integralSample =
      -(program.model index).integralSample :=
  models.integral_eq index

/-- Forget the local-model presentation while retaining its finite rational
samples and computable modulus. -/
def approximation (program : RefinementProgram) : Approximation where
  sample index := (program.model index).integralSample
  radiusSq := CCL.FiniteGeometric.quarterRadius program.errorScale
  radiusSq_nonneg :=
    CCL.FiniteGeometric.quarterRadius_nonneg
      program.errorScale_nonneg
  later_close := program.later_close
  refineIndex current target _positive :=
    CCL.FiniteGeometric.firstQuarterBelow program.errorScale
      current target
  refineIndex_ge := by
    intro current target _positive
    exact CCL.FiniteGeometric.firstQuarterBelow_ge
      program.errorScale current target
  refineIndex_accurate :=
    CCL.FiniteGeometric.firstQuarterBelow_accurate
      program.errorScale program.errorScale_nonneg
  centerBound := program.centerBound
  centerBound_nonneg := program.centerBound_nonneg
  sample_bounded := program.sample_bounded

/-- The productive coherent CCL integral output. -/
def output (program : RefinementProgram) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
    program.approximation

/-- A supplied finite antiderivative certificate at every natural
refinement, explicitly tied to the path model returned at that refinement. -/
structure AntiderivativeProcess (program : RefinementProgram) where
  certificate : Nat → PathAntiderivative
  path_eq : ∀ index, (certificate index).path = program.model index

namespace AntiderivativeProcess

theorem differenceSample_eq (program : RefinementProgram)
    (antiderivative : AntiderivativeProcess program) (index : Nat) :
    (antiderivative.certificate index).differenceSample =
      (program.model index).integralSample := by
  rw [PathAntiderivative.differenceSample_eq_integralSample,
    antiderivative.path_eq]

/-- The endpoint-difference process with the same computable modulus as the
integral process. -/
def differenceApproximation (program : RefinementProgram)
    (antiderivative : AntiderivativeProcess program) : Approximation where
  sample index := (antiderivative.certificate index).differenceSample
  radiusSq := CCL.FiniteGeometric.quarterRadius program.errorScale
  radiusSq_nonneg :=
    CCL.FiniteGeometric.quarterRadius_nonneg
      program.errorScale_nonneg
  later_close := by
    intro earlier later order
    rw [antiderivative.differenceSample_eq,
      antiderivative.differenceSample_eq]
    exact program.later_close order
  refineIndex current target _positive :=
    CCL.FiniteGeometric.firstQuarterBelow program.errorScale
      current target
  refineIndex_ge := by
    intro current target _positive
    exact CCL.FiniteGeometric.firstQuarterBelow_ge
      program.errorScale current target
  refineIndex_accurate :=
    CCL.FiniteGeometric.firstQuarterBelow_accurate
      program.errorScale program.errorScale_nonneg
  centerBound := program.centerBound
  centerBound_nonneg := program.centerBound_nonneg
  sample_bounded := by
    intro index
    rw [antiderivative.differenceSample_eq]
    exact program.sample_bounded index

def differenceOutput (program : RefinementProgram)
    (antiderivative : AntiderivativeProcess program) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
    (antiderivative.differenceApproximation program)

/-- Progressive finite FTC: the productive integral CCL is operationally
equivalent to the productive CCL of the supplied finite antiderivative
endpoint differences. -/
def ftc_equivalent (program : RefinementProgram)
    (antiderivative : AntiderivativeProcess program) :
    CCL.OperationalEquivalence.NamedEquivalent
      program.output.name (antiderivative.differenceOutput program).name :=
  CCL.TranscendentalCoherence.approximationEquivalent_toNamed
    (CCL.TranscendentalCoherence.approximationEquivalentOfSamplesEq
      program.approximation (antiderivative.differenceApproximation program)
      (by
        intro index
        exact (antiderivative.differenceSample_eq program index).symm))

end AntiderivativeProcess

/-- The exact-polynomial refinement output is operationally the terminating
Gaussian-rational result computed by the existing polynomial integrator. -/
def exactPolynomial_equivalent (start finish : Gaussian)
    (polynomial : Polynomial) :
    CCL.OperationalEquivalence.NamedEquivalent
      (exactPolynomial start finish polynomial).output.name
      (CCL.ProgressiveTransducer.Named.exact
        ((PathModel.mk [CellModel.exact start finish polynomial]).integralSample)) := by
  let program := exactPolynomial start finish polynomial
  let value :=
    (PathModel.mk [CellModel.exact start finish polynomial]).integralSample
  let constant :=
    CCL.TranscendentalLaws.constantApproximation value
  have samples : ∀ index, program.approximation.sample index =
      constant.sample index := by
    intro index
    change
      (PathModel.mk [CellModel.exact start finish polynomial]).integralSample =
        value
    rfl
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.TranscendentalCoherence.approximationEquivalent_toNamed
      (CCL.TranscendentalCoherence.approximationEquivalentOfSamplesEq
        program.approximation constant samples))
    (CCL.OperationalEquivalence.NamedEquivalent.symm
      (CCL.TranscendentalCoherence.exact_toConstantNamed value))

/-- Exact specialization stated directly against the pre-existing finite
polynomial integral, rather than against the implementation's singleton path
wrapper. -/
def exactPolynomial_equivalent_finiteIntegral (start finish : Gaussian)
    (polynomial : Polynomial) :
    CCL.OperationalEquivalence.NamedEquivalent
      (exactPolynomial start finish polynomial).output.name
      (CCL.ProgressiveTransducer.Named.exact
        ((finish - start) *
          CCL.FiniteIntegration.definiteIntegral polynomial 0 1)) := by
  simpa only [PathModel.singleton_integralSample,
    CellModel.exact_integralSample] using
      exactPolynomial_equivalent start finish polynomial

/-- Every positive rational target selects a finite subdivision index whose
aggregate transported local allowance is already below the target. -/
theorem finite_subdivision_accurate (program : RefinementProgram)
    (current : Nat) (target : Coordinate) (positive : 0 < target) :
    let index := program.approximation.refineIndex current target positive
    (program.model index).aggregateAllowance < target := by
  let index := program.approximation.refineIndex current target positive
  exact (program.modelAllowance_le index).trans_lt
    (program.approximation.refineIndex_accurate current target positive)

/-- End-to-end certified integration: after one finite refinement the output
enclosure is below the requested rational target and its ordinary CCL cursor
emits exactly the requested number of bits with exact parser semantics. -/
theorem output_bitstream_and_error (program : RefinementProgram)
    (target : Coordinate) (positive : 0 < target) (count : Nat) :
    let refined := CCL.TranscendentalOutput.refined
      program.output.name target positive
    (refined.process.ball refined.state).radiusSq < target ∧
      refined.machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          refined.machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
        refined.machine count).emitted.length = count ∧
      CCL.ProgressiveMachineSemantics.ExactCursor
        refined.process refined.state
        (CCL.ProgressiveTransducer.advance refined.machine count) :=
  CCL.TranscendentalOutput.refined_bitstream_and_error
    program.output.name target positive count

end RefinementProgram

end CCL.ProgressiveIntegration
