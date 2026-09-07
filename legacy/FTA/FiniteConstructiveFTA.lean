import FTA.CCLZeroTerminalSeparation
import FTA.BoxFTA

/-!
# Finite constructive FTA family assembly

This module places the direct nonzero-constant controller, the distinguished
exact-zero terminal, and the constructively deflated quotient controller
behind one finite request interface.  The assembled list has exactly the
input natural degree and its initial numerical regions are pairwise separated.
-/

namespace FTA
namespace FiniteConstructiveFTA

open CCL CCL.GaussianRat
open FTA.AxisSafeCuts
open FTA.AxisExecutableResultant
open FTA.CCLActiveMetricProgress
open FTA.CCLActiveMetricTrack
open FTA.CCLActiveObservedEnvelopeProgress
open FTA.CCLDenominator
open FTA.CCLFiniteTaggedEnvelope
open FTA.CCLGeometry
open FTA.CCLZeroDeflatedFamily
open FTA.CCLZeroTerminalSeparation
open FTA.GaussianZeroDeflation
open FTA.GlobalWinding
open FTA.LocalExtraction

abbrev QI := FTA.BoxFTA.QI
abbrev GaussianPolynomial := FTA.BoxFTA.GaussianPolynomial

/-- A fully explicit negative root condition over the Gaussian rationals. -/
def NoGaussianRationalRoot (p : GaussianPolynomial) : Prop :=
  ∀ point : QI, p.eval point ≠ 0

/-- An irreducible Gaussian-rational polynomial of degree greater than one
has no Gaussian-rational root. -/
theorem noGaussianRationalRoot_of_primitive_degree_gt_one
    {p : GaussianPolynomial} (primitive : FTA.Primitive p.toPolynomial)
    (degree : 1 < p.natDegree) : NoGaussianRationalRoot p := by
  intro point root
  have nonzero : p.isZero = false :=
    FTA.GlobalWinding.isZero_false_of_natDegree_pos
      (Nat.zero_lt_of_lt degree)
  have sparseDegree : p.toPolynomial.natDegree = p.natDegree :=
    FTA.ComputablePolynomial.DensePolynomial.natDegree_toPolynomial nonzero
  have degreeNeOne : p.toPolynomial.natDegree ≠ 1 := by
    rw [sparseDegree]
    omega
  have sparseRoot : p.toPolynomial.IsRoot point := by
    rw [Polynomial.IsRoot.def,
      FTA.ComputablePolynomial.DensePolynomial.eval_toPolynomial]
    exact root
  exact primitive.2.not_isRoot_of_natDegree_ne_one degreeNeOne sparseRoot

/-- Singleton rational box used by exact nonzero terminal records. -/
def singletonBox (point : QI) : RatBox where
  xLower := point.re
  xUpper := point.re
  yLower := point.im
  yUpper := point.im
  x_valid := le_rfl
  y_valid := le_rfl

@[simp] theorem singletonBox_contains (point : QI) :
    (singletonBox point).Contains point := by
  simp [singletonBox, RatBox.Contains]

/-- Numerical center residual for every carrier winding-one state. -/
theorem carrier_center_residual_le
    {carrier : GaussianPolynomial} {ambient : RatBox}
    (state : RootTrackSeparation.WindingOneState carrier ambient) :
    normSq (carrier.eval state.box.center) ≤
      centerResidualBound carrier ambient state.box :=
  center_residual_le_of_boxWinding_ne_zero carrier state.refinesAmbient
    state.proper state.winding_ne_zero

/-- Any persisted rational sample inside an active carrier box has the same
coefficient-linear residual order as the box center. -/
theorem carrier_sample_residual_le
    {carrier : GaussianPolynomial} {ambient : RatBox}
    (state : CCLActiveMetricTrack.State carrier ambient) :
    normSq (carrier.eval state.currentSample.point) ≤
      4 * centerResidualBound carrier ambient state.core.numerical.box := by
  let numerical := state.core.numerical
  let sample := state.currentSample
  have centerResidual := carrier_center_residual_le numerical
  have variation := normSq_eval_sub_center_le carrier
    numerical.refinesAmbient sample.inside
  have variationValue :
      (carrier - gaussianConstant
        (carrier.eval numerical.box.center)).eval sample.point =
        carrier.eval sample.point + -(carrier.eval numerical.box.center) := by
    rw [FTA.ComputablePolynomial.DensePolynomial.eval_sub,
      gaussianConstant,
      FTA.ComputablePolynomial.DensePolynomial.eval_constant]
    rfl
  rw [variationValue] at variation
  have decomposition :
      (carrier.eval sample.point + -(carrier.eval numerical.box.center)) +
          carrier.eval numerical.box.center = carrier.eval sample.point := by
    ext <;> simp only [add_re, add_im, neg_re, neg_im] <;> ring
  have sum := normSq_add_le_two
    (carrier.eval sample.point + -(carrier.eval numerical.box.center))
    (carrier.eval numerical.box.center)
  rw [decomposition] at sum
  linarith

/-- Coefficient-computable clause-(c) constant for a direct active track. -/
def directResidualConstant (p : GaussianPolynomial) : ℚ :=
  4 * GaussianPolynomialBounds.denseLipschitzBound p (largeSquareBox p)

theorem directResidualConstant_nonneg (p : GaussianPolynomial) :
    0 ≤ directResidualConstant p := by
  exact mul_nonneg (by norm_num)
    (GaussianPolynomialBounds.denseLipschitzBound_pos
      p (largeSquareBox p)).le

theorem direct_sample_residual_le
    {p : GaussianPolynomial}
    (state : CCLActiveMetricTrack.State p (largeSquareBox p)) :
    normSq (p.eval state.currentSample.point) ≤
      directResidualConstant p * state.core.numerical.box.diagonalSq := by
  have residual := carrier_sample_residual_le state
  rw [centerResidualBound] at residual
  calc
    normSq (p.eval state.currentSample.point) ≤
        4 * (GaussianPolynomialBounds.denseLipschitzBound p
          (largeSquareBox p) * state.core.numerical.box.diagonalSq) := residual
    _ = directResidualConstant p *
        state.core.numerical.box.diagonalSq := by
      simp only [directResidualConstant]
      ring

/-- Coefficient-computable clause-(c) constant for a zero-deflated track. -/
def deflatedResidualConstant (p : GaussianPolynomial) : ℚ :=
  8 * (largeSquareBox (quotient p)).coordinateRadius ^ 2 *
    GaussianPolynomialBounds.denseLipschitzBound
      (quotient p) (largeSquareBox (quotient p))

theorem deflatedResidualConstant_nonneg (p : GaussianPolynomial) :
    0 ≤ deflatedResidualConstant p := by
  exact mul_nonneg
    (mul_nonneg (by norm_num) (sq_nonneg _))
    (GaussianPolynomialBounds.denseLipschitzBound_pos
      (quotient p) (largeSquareBox (quotient p))).le

/-- Original-polynomial residual bound for the actual nonzero rational
sample returned by a zero-deflated active state. -/
theorem deflated_sample_residual_le
    {p : GaussianPolynomial} (nonzero : p.isZero = false)
    (zero : p.eval 0 = 0)
    (state : CCLActiveMetricTrack.State (quotient p)
      (largeSquareBox (quotient p))) :
    normSq (p.eval state.currentSample.point) ≤
      deflatedResidualConstant p *
        state.core.numerical.box.diagonalSq := by
  have quotientResidual := carrier_sample_residual_le state
  have sampleInside : (largeSquareBox (quotient p)).Contains
      state.currentSample.point :=
    state.core.numerical.refinesAmbient.contains state.currentSample.inside
  have sampleBound :=
    CCLChordalEnvelope.normSq_le_two_coordinateRadius_sq sampleInside
  have residualNonnegative :
      0 ≤ centerResidualBound (quotient p)
        (largeSquareBox (quotient p)) state.core.numerical.box := by
    exact mul_nonneg
      (GaussianPolynomialBounds.denseLipschitzBound_pos
        (quotient p) (largeSquareBox (quotient p))).le
      state.core.numerical.box.diagonalSq_nonneg
  rw [eval_eq_quotient_mul_of_nonzero nonzero zero state.currentSample.point,
    normSq_mul]
  calc
    normSq ((quotient p).eval state.currentSample.point) *
          normSq state.currentSample.point ≤
        (4 * centerResidualBound (quotient p)
            (largeSquareBox (quotient p)) state.core.numerical.box) *
          (2 * (largeSquareBox (quotient p)).coordinateRadius ^ 2) :=
      mul_le_mul quotientResidual sampleBound (normSq_nonneg _)
        (mul_nonneg (by norm_num) residualNonnegative)
    _ = deflatedResidualConstant p *
        state.core.numerical.box.diagonalSq := by
      simp only [deflatedResidualConstant, centerResidualBound]
      ring

/-- One finite root transducer.  An active implementation may run either on
the original polynomial or on a deflated carrier; `rootLift` certifies that
every exact carrier root is an exact root of the requested polynomial. -/
inductive RootTransducer (p : GaussianPolynomial) where
  | zero (root : p.eval 0 = 0) : RootTransducer p
  | terminal (point : QI) (root : p.eval point = 0) (nonzero : point ≠ 0)
      (completeWord : Prefix.Word)
      (complete : completeWord = RationalEncoder.encode point nonzero) :
      RootTransducer p
  | active
      {carrier : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
      (machine : Machine carrier R hR)
      (current : State carrier (RatBox.symmetric R hR))
      (originalWinding : ∀ next : State carrier (RatBox.symmetric R hR),
        ¬next.core.numerical.box.Contains 0 →
          RootTrackSeparation.WindingOneState p next.core.numerical.box)
      (residualConstant : ℚ)
      (residualConstantNonnegative : 0 ≤ residualConstant)
      (originalResidual : ∀ next : State carrier (RatBox.symmetric R hR),
        normSq (p.eval next.currentSample.point) ≤
          residualConstant * next.core.numerical.box.diagonalSq)
      (rootLift : ∀ {z : QI}, carrier.eval z = 0 → p.eval z = 0)
      (excludesZero : ¬current.core.numerical.box.Contains 0) :
      RootTransducer p

namespace RootTransducer

/-- Constructor-level statement that a transducer still carries an active
winding/CCL machine rather than an exact Gaussian-rational terminal. -/
def IsNonterminal {p : GaussianPolynomial} : RootTransducer p → Prop
  | .active _ _ _ _ _ _ _ _ => True
  | .zero _ => False
  | .terminal _ _ _ _ _ => False

/-- In the absence of Gaussian-rational roots, every root transducer is
necessarily nonterminal. -/
theorem isNonterminal_of_noGaussianRationalRoot
    {p : GaussianPolynomial} (noRoot : NoGaussianRationalRoot p)
    (current : RootTransducer p) : current.IsNonterminal := by
  cases current with
  | zero root => exact (noRoot 0 root).elim
  | terminal point root nonzero completeWord complete =>
      exact (noRoot point root).elim
  | active machine state originalWinding constant constantNonnegative
      originalResidual rootLift excludesZero =>
      trivial

/-- Initial or current finite numerical region, treating an exact zero as a
singleton box. -/
def box {p : GaussianPolynomial} : RootTransducer p → RatBox
  | .zero _ => zeroBox
  | .terminal point _ _ _ _ => singletonBox point
  | .active _ current _ _ _ _ _ _ => current.core.numerical.box

/-- Raw CCL prefix of an active state; exact zero deliberately has no raw
encoder word. -/
def word {p : GaussianPolynomial} : RootTransducer p → Option Prefix.Word
  | .zero _ => none
  | .terminal _ _ _ completeWord _ => some completeWord
  | .active _ current _ _ _ _ _ _ => some current.core.word

/-- Rational numerical approximation carried by the current finite state. -/
def approximant {p : GaussianPolynomial} : RootTransducer p → QI
  | .zero _ => 0
  | .terminal point _ _ _ _ => point
  | .active _ current _ _ _ _ _ _ => current.currentSample.point

/-- Coefficient-computable residual constant attached persistently to a root
transducer.  Exact terminals use zero. -/
def residualConstant {p : GaussianPolynomial} : RootTransducer p → ℚ
  | .zero _ => 0
  | .terminal _ _ _ _ _ => 0
  | .active _ _ _ constant _ _ _ _ => constant

theorem residualConstant_nonneg
    {p : GaussianPolynomial} (current : RootTransducer p) :
    0 ≤ current.residualConstant := by
  cases current with
  | zero root => norm_num [residualConstant]
  | terminal point root nonzero completeWord complete =>
      norm_num [residualConstant]
  | active machine state originalWinding constant constantNonnegative
      originalResidual rootLift excludesZero =>
      exact constantNonnegative

/-- Every displayed rational approximant satisfies the original-polynomial
residual bound, including residual zero in both terminal cases. -/
theorem approximant_residual_le
    {p : GaussianPolynomial} (current : RootTransducer p) :
    normSq (p.eval current.approximant) ≤
      current.residualConstant * current.box.diagonalSq := by
  cases current with
  | zero root => simp [approximant, residualConstant, root]
  | terminal point root nonzero completeWord complete =>
      simp [approximant, residualConstant, root]
  | active machine state originalWinding constant constantNonnegative
      originalResidual rootLift excludesZero =>
      exact originalResidual state

/-- Every active carrier state exposes a complete winding-one certificate
for the original polynomial on the displayed rational box. -/
def originalNumerical
    {p : GaussianPolynomial} (current : RootTransducer p) :
    Option (RootTrackSeparation.WindingOneState p current.box) :=
  match current with
  | .zero _ => none
  | .terminal _ _ _ _ _ => none
  | .active _ state originalWinding _ _ _ _ excludesZero =>
      some (originalWinding state excludesZero)

theorem approximant_inside
    {p : GaussianPolynomial} (current : RootTransducer p) :
    current.box.Contains current.approximant := by
  cases current with
  | zero root => exact zeroBox_contains_zero
  | terminal point root nonzero completeWord complete =>
      exact singletonBox_contains point
  | active machine state originalWinding constant constantNonnegative
      originalResidual rootLift excludesZero =>
      exact state.currentSample.inside

theorem active_approximant_nonzero
    {p carrier : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (machine : Machine carrier R hR)
    (current : State carrier (RatBox.symmetric R hR))
    (originalWinding : ∀ next : State carrier (RatBox.symmetric R hR),
      ¬next.core.numerical.box.Contains 0 →
        RootTrackSeparation.WindingOneState p next.core.numerical.box)
    (residualConstant : ℚ) (residualConstantNonnegative : 0 ≤ residualConstant)
    (originalResidual : ∀ next : State carrier (RatBox.symmetric R hR),
      normSq (p.eval next.currentSample.point) ≤
        residualConstant * next.core.numerical.box.diagonalSq)
    (rootLift : ∀ {z : QI}, carrier.eval z = 0 → p.eval z = 0)
    (excludesZero : ¬current.core.numerical.box.Contains 0) :
    RootTransducer.approximant
      (RootTransducer.active machine current originalWinding residualConstant
        residualConstantNonnegative originalResidual rootLift excludesZero) ≠
          0 := by
  intro zero
  apply excludesZero
  have inside := current.currentSample.inside
  have pointZero : current.currentSample.point = 0 := by
    simpa only [approximant] using zero
  rw [← pointZero]
  exact inside

/-- Common result of one positive shrinking-envelope request. -/
inductive RequestResult
    {p : GaussianPolynomial} (current : RootTransducer p) (target : ℚ) where
  | zero (root : p.eval 0 = 0) : RequestResult current target
  | terminal (point : QI) (root : p.eval point = 0)
      (nonzero : point ≠ 0) (completeWord : Prefix.Word)
      (complete : completeWord = RationalEncoder.encode point nonzero)
      (contains : current.box.Contains point) :
      RequestResult current target
  | nonterminal
      (next : RootTransducer p)
      (originalNumerical : RootTrackSeparation.WindingOneState p next.box)
      (envelope : FiniteTaggedEnvelope)
      (box_eq : envelope.box = next.box)
      (word_eq : next.word = some envelope.tag.word)
      (boxAccurate : next.box.diagonalSq ≤ target ^ 2)
      (approximantNonzero : next.approximant ≠ 0)
      (residualConstant_eq : next.residualConstant = current.residualConstant)
      (residual : normSq (p.eval next.approximant) ≤
        next.residualConstant * next.box.diagonalSq)
      (accurate : envelope.errorSq ≤ 2 * (target ^ 2 + target)) :
      RequestResult current target

/-- Every call is a structural case split followed by the already-total
active request.  Carrier terminal roots are relabelled by `rootLift`. -/
def request
    {p : GaussianPolynomial} (current : RootTransducer p)
    (target : ℚ) (targetPositive : 0 < target) :
    RequestResult current target :=
  match current with
  | .zero root => .zero root
  | .terminal point root nonzero completeWord complete =>
      .terminal point root nonzero completeWord complete
        (singletonBox_contains point)
  | .active machine state originalWinding residualConstant
      residualConstantNonnegative originalResidual rootLift excludesZero => by
      let run := requestFinite machine state target targetPositive
      match run with
      | .zero root => exact .zero (rootLift root)
      | .terminal point root nonzero completeWord complete contains =>
          exact .terminal point (rootLift root) nonzero completeWord complete
            (by simpa only [box] using contains)
      | .nonterminal next refines envelope boxEq wordEq boxAccurate accurate =>
          let nextExcludes : ¬next.core.numerical.box.Contains 0 := by
            intro contains
            exact excludesZero (refines.box.contains contains)
          let nextTransducer : RootTransducer p :=
            .active machine next originalWinding residualConstant
              residualConstantNonnegative originalResidual rootLift
                nextExcludes
          exact .nonterminal nextTransducer (by
            simpa only [nextTransducer, box] using
              originalWinding next nextExcludes) envelope (by
            simpa only [nextTransducer, box] using boxEq) (by
              simp only [nextTransducer, word]
              exact congrArg some wordEq.symm) (by
                simpa only [nextTransducer, box] using boxAccurate)
                (active_approximant_nonzero machine next originalWinding
                  residualConstant residualConstantNonnegative
                    originalResidual rootLift nextExcludes)
                (by simp only [nextTransducer,
                  RootTransducer.residualConstant])
                nextTransducer.approximant_residual_le
                accurate

/-- Polynomial-independent refinement record exposed by the final RAT
interface.  Exact terminals never enter this constructor; both words are
therefore present and the requested finite extension is explicit. -/
structure Progresses
    {p : GaussianPolynomial} (inner outer : RootTransducer p) (count : ℕ) :
    Prop where
  box : inner.box.Refines outer.box
  words : ∃ oldWord newWord,
    outer.word = some oldWord ∧
      inner.word = some newWord ∧
      oldWord <+: newWord ∧
      oldWord.length + count ≤ newWord.length

/-- Consecutive approximants lie in the earlier displayed box, so their
squared distance is bounded by that box's squared diagonal. -/
theorem approximant_distance_le_of_progresses
    {p : GaussianPolynomial} {inner outer : RootTransducer p} {count : ℕ}
    (progresses : Progresses inner outer count) :
    normSq (inner.approximant - outer.approximant) ≤
      outer.box.diagonalSq := by
  apply RatBox.normSq_sub_le_diagonalSq
  · exact progresses.box.contains inner.approximant_inside
  · exact outer.approximant_inside

/-- Common result of a joint requested word extension and shrinking-envelope
call. -/
inductive AdvanceResult
    {p : GaussianPolynomial} (current : RootTransducer p)
    (target : ℚ) (count : ℕ) where
  | zero (root : p.eval 0 = 0) : AdvanceResult current target count
  | terminal (point : QI) (root : p.eval point = 0)
      (nonzero : point ≠ 0) (completeWord : Prefix.Word)
      (complete : completeWord = RationalEncoder.encode point nonzero)
      (contains : current.box.Contains point) :
      AdvanceResult current target count
  | nonterminal
      (next : RootTransducer p)
      (originalNumerical : RootTrackSeparation.WindingOneState p next.box)
      (progresses : Progresses next current count)
      (envelope : FiniteTaggedEnvelope)
      (box_eq : envelope.box = next.box)
      (word_eq : next.word = some envelope.tag.word)
      (boxAccurate : next.box.diagonalSq ≤ target ^ 2)
      (approximantNonzero : next.approximant ≠ 0)
      (residualConstant_eq : next.residualConstant = current.residualConstant)
      (residual : normSq (p.eval next.approximant) ≤
        next.residualConstant * next.box.diagonalSq)
      (movement : normSq (next.approximant - current.approximant) ≤
        current.box.diagonalSq)
      (accurate : envelope.errorSq ≤ 2 * (target ^ 2 + target)) :
      AdvanceResult current target count

namespace AdvanceResult

/-- Constructor-level statement that a finite request returned its
nonterminal shrinking-box/envelope record. -/
def IsNonterminal
    {p : GaussianPolynomial} {current : RootTransducer p}
    {target : ℚ} {count : ℕ} :
    AdvanceResult current target count → Prop
  | .nonterminal _ _ _ _ _ _ _ _ _ _ _ _ => True
  | .zero _ => False
  | .terminal _ _ _ _ _ _ => False

/-- A request cannot enter either exact terminal constructor when the
polynomial has no Gaussian-rational root. -/
theorem isNonterminal_of_noGaussianRationalRoot
    {p : GaussianPolynomial} (noRoot : NoGaussianRationalRoot p)
    {current : RootTransducer p} {target : ℚ} {count : ℕ}
    (result : AdvanceResult current target count) : result.IsNonterminal := by
  cases result with
  | zero root => exact (noRoot 0 root).elim
  | terminal point root nonzero completeWord complete contains =>
      exact (noRoot point root).elim
  | nonterminal next originalNumerical progresses envelope boxEq wordEq
      boxAccurate approximantNonzero residualConstantEq residual movement
      accurate =>
      trivial

end AdvanceResult

/-- Joint finite RAT call from Definition 1.4 of the paper.  First append the
requested number of raw bits, unless an exact rational root is encountered;
then run the total shrinking-envelope request from that refined state. -/
def advance
    {p : GaussianPolynomial} (current : RootTransducer p)
    (target : ℚ) (targetPositive : 0 < target) (count : ℕ) :
    AdvanceResult current target count :=
  match current with
  | .zero root => .zero root
  | .terminal point root nonzero completeWord complete =>
      .terminal point root nonzero completeWord complete
        (singletonBox_contains point)
  | .active machine state originalWinding residualConstant
      residualConstantNonnegative originalResidual rootLift excludesZero => by
      let bitRun := CCLActiveMetricProgress.request machine state target
        targetPositive count
      match bitRun with
      | .zero root => exact .zero (rootLift root)
      | .terminal point root nonzero completeWord complete contains =>
          exact .terminal point (rootLift root) nonzero completeWord complete
            (by simpa only [box] using contains)
      | .nonterminal middle middleRefines _middleAccurate middleLength =>
          let envelopeRun := requestFinite machine middle target targetPositive
          match envelopeRun with
          | .zero root => exact .zero (rootLift root)
          | .terminal point root nonzero completeWord complete contains =>
              exact .terminal point (rootLift root) nonzero completeWord
                complete (by
                  simpa only [box] using middleRefines.box.contains contains)
          | .nonterminal final finalRefines envelope boxEq wordEq boxAccurate
              accurate =>
              let finalExcludes :
                  ¬final.core.numerical.box.Contains 0 := by
                intro contains
                exact excludesZero
                  ((finalRefines.trans middleRefines).box.contains contains)
              let next : RootTransducer p := .active machine final
                originalWinding residualConstant residualConstantNonnegative
                  originalResidual rootLift finalExcludes
              have combined : StateRefines final state :=
                finalRefines.trans middleRefines
              have progress : Progresses next
                  (.active machine state originalWinding residualConstant
                    residualConstantNonnegative originalResidual rootLift
                      excludesZero) count := by
                constructor
                · simpa only [next, box] using combined.box
                · refine ⟨state.core.word, final.core.word, rfl, rfl,
                    combined.word, ?_⟩
                  have lengthLe := finalRefines.word.length_le
                  rw [middleLength] at lengthLe
                  exact lengthLe
              exact .nonterminal next (by
                simpa only [next, box] using
                  originalWinding final finalExcludes) progress envelope (by
                simpa only [next, box] using boxEq) (by
                  simp only [next, word]
                  exact congrArg some wordEq.symm) (by
                    simpa only [next, box] using boxAccurate)
                    (active_approximant_nonzero machine final originalWinding
                      residualConstant residualConstantNonnegative
                        originalResidual rootLift finalExcludes)
                    (by simp only [next, RootTransducer.residualConstant])
                    next.approximant_residual_le
                    (approximant_distance_le_of_progresses progress)
                    accurate

end RootTransducer

/-- The CCL-coupled construction consumes exactly the same mathematical input
as the standalone box theorem. -/
abbrev Input := FTA.BoxFTA.Input

namespace Input

/-- Compatibility name for the shared primitive input constructor. -/
def ofPrimitiveDegreeGtOne
    {p : GaussianPolynomial} (primitive : FTA.Primitive p.toPolynomial)
    (degree : 1 < p.natDegree) : Input p :=
  FTA.BoxFTA.Input.ofPrimitiveDegreeGtOne primitive degree

/-- Compatibility name for the shared elimination degree. -/
def eliminationDegree {p : GaussianPolynomial} (input : Input p) : ℕ :=
  FTA.BoxFTA.Input.eliminationDegree input

/-- Compatibility name for the shared computed elimination certificate. -/
def elimination {p : GaussianPolynomial} (input : Input p) :
    AxisEliminationCertificate p input.eliminationDegree :=
  FTA.BoxFTA.Input.elimination input

/-- In the zero-root branch, compute the same closed certificate for the
positive-degree quotient rather than requesting it from the caller. -/
def quotientElimination {p : GaussianPolynomial} (input : Input p)
    (zero : p.eval 0 = 0) (degree : 1 < p.natDegree) :
    Σ D, AxisEliminationCertificate (quotient p) D := by
  have originalNonzero := isZero_false_of_natDegree_pos input.degreePositive
  have quotientNonzero := quotient_isZero_false originalNonzero zero
  have quotientDegree :=
    quotient_natDegree_pos originalNonzero zero degree
  exact ⟨2 * (quotient p).natDegree ^ 2,
    computedAxisEliminationCertificate (quotient p) quotientNonzero
      quotientDegree⟩

theorem sparseDegreeNonzero
    {p : GaussianPolynomial} (input : Input p) :
    p.toPolynomial.natDegree ≠ 0 :=
  FTA.BoxFTA.Input.sparseDegreeNonzero input

def directOutput
    {p : GaussianPolynomial} (input : Input p) :
    ExactIsolation.Output p (largeSquareBox p) p.natDegree :=
  FTA.BoxFTA.Input.isolation input

def directZeroFreeNumerical
    {p : GaussianPolynomial} (input : Input p) (zeroNonzero : p.eval 0 ≠ 0)
    (index : Fin p.natDegree) :
    RootTrackSeparation.WindingOneState p (largeSquareBox p) :=
  refineAwayFromNonroot (input.directOutput.trackAt index)
    (input.directOutput.trackAt index).initial 0 zeroNonzero

theorem directZeroFreeNumerical_refines
    {p : GaussianPolynomial} (input : Input p) (zeroNonzero : p.eval 0 ≠ 0)
    (index : Fin p.natDegree) :
    (input.directZeroFreeNumerical zeroNonzero index).box.Refines
      (input.directOutput.trackAt index).initial.box :=
  refineAwayFromNonroot_refines (input.directOutput.trackAt index)
    (input.directOutput.trackAt index).initial 0 zeroNonzero

theorem directZeroFreeNumerical_excludes_zero
    {p : GaussianPolynomial} (input : Input p) (zeroNonzero : p.eval 0 ≠ 0)
    (index : Fin p.natDegree) :
    ¬(input.directZeroFreeNumerical zeroNonzero index).box.Contains 0 :=
  refineAwayFromNonroot_excludes (input.directOutput.trackAt index)
    (input.directOutput.trackAt index).initial 0 zeroNonzero

def directZeroFreeSeparation
    {p : GaussianPolynomial} (input : Input p) (zeroNonzero : p.eval 0 ≠ 0)
    (index : Fin p.natDegree) :
    CCLDenominator.SeparationOutput p (largeSquareBox p)
      (input.directZeroFreeNumerical zeroNonzero index)
      (adjugate (RawParser.parse []).matrix) :=
  CCLDenominator.separateConstantDenominator
    (input.directZeroFreeNumerical zeroNonzero index)
    (adjugate (RawParser.parse []).matrix) (by
      simp [RawParser.parse, RawParser.initialState, RawParser.identityMatrix,
        adjugate]) (by
      simp [RawParser.parse, RawParser.initialState, RawParser.identityMatrix,
        adjugate])

def directZeroFreeState
    {p : GaussianPolynomial} (input : Input p) (zeroNonzero : p.eval 0 ≠ 0)
    (index : Fin p.natDegree) : State p (largeSquareBox p) :=
  CCLActiveMetricTrack.ofInitialSeparation
    (input.directZeroFreeSeparation zeroNonzero index)

theorem directZeroFreeState_box
    {p : GaussianPolynomial} (input : Input p) (zeroNonzero : p.eval 0 ≠ 0)
    (index : Fin p.natDegree) :
    (input.directZeroFreeState zeroNonzero index).core.numerical.box =
      (input.directZeroFreeNumerical zeroNonzero index).box := by
  simp [directZeroFreeState, directZeroFreeSeparation,
    CCLActiveMetricTrack.ofInitialSeparation,
    CCLDenominator.separateConstantDenominator]

theorem directZeroFreeState_excludes_zero
    {p : GaussianPolynomial} (input : Input p) (zeroNonzero : p.eval 0 ≠ 0)
    (index : Fin p.natDegree) :
    ¬(input.directZeroFreeState zeroNonzero index).core.numerical.box.Contains
      0 := by
  rw [input.directZeroFreeState_box zeroNonzero index]
  exact input.directZeroFreeNumerical_excludes_zero zeroNonzero index

def directMember
    {p : GaussianPolynomial} (input : Input p) (zeroNonzero : p.eval 0 ≠ 0)
    (index : Fin p.natDegree) : RootTransducer p :=
  .active
    (CCLActiveMetricFamily.machineAt input.directOutput index false
      input.squarefree input.sparseDegreeNonzero zeroNonzero input.elimination)
    (input.directZeroFreeState zeroNonzero index)
    (fun next _outside =>
      GaussianZeroDeflation.WindingOneState.reambientSelf
        next.core.numerical)
    (directResidualConstant p)
    (directResidualConstant_nonneg p)
    (fun next => direct_sample_residual_le next)
    (fun root => root)
    (input.directZeroFreeState_excludes_zero zeroNonzero index)

theorem directMember_box
    {p : GaussianPolynomial} (input : Input p) (zeroNonzero : p.eval 0 ≠ 0)
    (index : Fin p.natDegree) :
    (input.directMember zeroNonzero index).box =
      (input.directZeroFreeNumerical zeroNonzero index).box := by
  exact input.directZeroFreeState_box zeroNonzero index

def deflatedInput
    {p : GaussianPolynomial} (input : Input p) (zero : p.eval 0 = 0)
    (degree : 1 < p.natDegree) : CCLZeroDeflatedFamily.Input p := by
  let elimination := input.quotientElimination zero degree
  exact
    { squarefree := input.squarefree
      degree := degree
      zero := zero
      eliminationDegree := elimination.1
      elimination := elimination.2 }

def deflatedMember
    {p : GaussianPolynomial} (input : Input p) (zero : p.eval 0 = 0)
    (degree : 1 < p.natDegree) (index : Fin (quotient p).natDegree) :
    RootTransducer p :=
  let deflated := input.deflatedInput zero degree
  .active (deflated.machineAt index false) (deflated.zeroFreeStateAt index)
    (fun next outside =>
      GaussianZeroDeflation.WindingOneState.liftQuotient
        deflated.originalNonzero zero next.core.numerical outside)
    (deflatedResidualConstant p)
    (deflatedResidualConstant_nonneg p)
    (fun next =>
      deflated_sample_residual_le deflated.originalNonzero zero next)
    (fun root => quotient_root_is_root deflated.originalNonzero zero root)
    (deflated.zeroFreeStateAt_excludes_zero index)

theorem deflatedMember_box
    {p : GaussianPolynomial} (input : Input p) (zero : p.eval 0 = 0)
    (degree : 1 < p.natDegree) (index : Fin (quotient p).natDegree) :
    (input.deflatedMember zero degree index).box =
      ((input.deflatedInput zero degree).zeroFreeStateAt index).core.numerical.box := by
  rfl

/-- Degree-sharp maximality remains a theorem about arbitrary original
`p`-winding tracks in the coefficient-computed large square.  Zero deflation
changes only the implementation of the returned CCL machines. -/
theorem maximality
    {p : GaussianPolynomial} (input : Input p) {familyCount : ℕ}
    (family : Fin familyCount →
      RootTrackSeparation.WindingOneTrack p (largeSquareBox p))
    (pairwise : ∀ i j, i ≠ j →
      (family i).initial.box.Separated (family j).initial.box) :
    familyCount ≤ p.natDegree :=
  FTA.BoxFTA.Input.familyCardLe input family pairwise

end Input

/-- Exactly-degree finite family with a witnessed initial gap for every pair. -/
structure Family (p : GaussianPolynomial) where
  members : List (RootTransducer p)
  length_eq : members.length = p.natDegree
  pairwiseSeparated : members.Pairwise fun left right =>
    left.box.Separated right.box

/-- Assemble the direct branch when `p(0) ≠ 0`; otherwise return zero first
and run the positive-degree quotient family.  Degree one with zero constant
term consists only of the distinguished exact terminal. -/
def build {p : GaussianPolynomial} (input : Input p) : Family p := by
  by_cases zero : p.eval 0 = 0
  · by_cases linear : p.natDegree = 1
    · exact
        { members := [.zero zero]
          length_eq := by simp [linear]
          pairwiseSeparated := by simp }
    · have positive := input.degreePositive
      have degree : 1 < p.natDegree := by omega
      let deflated := input.deflatedInput zero degree
      let member : Fin (quotient p).natDegree → RootTransducer p :=
        input.deflatedMember zero degree
      have count : (quotient p).natDegree + 1 = p.natDegree :=
        quotient_natDegree_add_one deflated.originalNonzero zero
      exact
        { members := .zero zero :: List.ofFn member
          length_eq := by simp [count]
          pairwiseSeparated := by
            rw [List.pairwise_cons]
            constructor
            · rw [List.forall_mem_ofFn_iff]
              intro index
              rw [input.deflatedMember_box zero degree index]
              exact RatBox.separated_symm
                (separated_zeroBox_of_excludes_zero
                  (deflated.zeroFreeStateAt_excludes_zero index))
            · rw [List.pairwise_ofFn]
              intro left right less
              rw [input.deflatedMember_box zero degree left,
                input.deflatedMember_box zero degree right]
              apply RatBox.Separated.of_refines
                (deflated.output.trackAt_pairwiseSeparated left right
                  (Fin.ne_of_lt less))
              · exact deflated.zeroFreeStateAt_refines_initial left |>.box
              · exact deflated.zeroFreeStateAt_refines_initial right |>.box }
  · let member : Fin p.natDegree → RootTransducer p :=
      input.directMember zero
    exact
      { members := List.ofFn member
        length_eq := by simp
        pairwiseSeparated := by
          rw [List.pairwise_ofFn]
          intro left right less
          rw [input.directMember_box zero left,
            input.directMember_box zero right]
          apply RatBox.Separated.of_refines
            (input.directOutput.trackAt_pairwiseSeparated left right
              (Fin.ne_of_lt less))
          · exact input.directZeroFreeNumerical_refines zero left
          · exact input.directZeroFreeNumerical_refines zero right }

namespace Family

def memberIndex
    {p : GaussianPolynomial} (family : Family p) (index : Fin p.natDegree) :
    Fin family.members.length :=
  Fin.cast family.length_eq.symm index

def memberAt
    {p : GaussianPolynomial} (family : Family p) (index : Fin p.natDegree) :
    RootTransducer p :=
  family.members.get (family.memberIndex index)

theorem memberAt_pairwiseSeparated
    {p : GaussianPolynomial} (family : Family p)
    (left right : Fin p.natDegree) (distinct : left ≠ right) :
    (family.memberAt left).box.Separated (family.memberAt right).box := by
  have indexDistinct : family.memberIndex left ≠ family.memberIndex right :=
    fun equality => distinct
      (Fin.cast_injective family.length_eq.symm equality)
  rcases lt_or_gt_of_ne indexDistinct with less | greater
  · exact family.pairwiseSeparated.rel_get_of_lt less
  · exact RatBox.separated_symm
      (family.pairwiseSeparated.rel_get_of_lt greater)

end Family

/-- Consecutive centers of nested numerical states satisfy the earlier-box
diagonal estimate from clause (c) of the main theorem. -/
theorem nested_center_distance_le
    {carrier : GaussianPolynomial} {ambient : RatBox}
    {inner outer : RootTrackSeparation.WindingOneState carrier ambient}
    (refines : inner.box.Refines outer.box) :
    normSq (inner.box.center - outer.box.center) ≤ outer.box.diagonalSq := by
  apply RatBox.normSq_sub_le_diagonalSq
  · exact refines.contains inner.box.contains_center
  · exact outer.box.contains_center

/-- Consecutive nonzero rational samples also lie in the earlier box, so the
same squared-diagonal estimate applies directly. -/
theorem nested_sample_distance_le
    {carrier : GaussianPolynomial} {ambient : RatBox}
    {inner outer : CCLActiveMetricTrack.State carrier ambient}
    (refines : StateRefines inner outer) :
    normSq (inner.currentSample.point - outer.currentSample.point) ≤
      outer.core.numerical.box.diagonalSq := by
  apply RatBox.normSq_sub_le_diagonalSq
  · exact refines.box.contains inner.currentSample.inside
  · exact outer.currentSample.inside

/-- In the zero-deflated branch, the original residual is the quotient
residual times the squared norm of the rational center.  The global quotient
box supplies the displayed coefficient-computable multiplier. -/
theorem deflated_center_residual_le
    {p : GaussianPolynomial} (nonzero : p.isZero = false)
    (zero : p.eval 0 = 0)
    (state : RootTrackSeparation.WindingOneState (quotient p)
      (largeSquareBox (quotient p))) :
    normSq (p.eval state.box.center) ≤
      2 * (largeSquareBox (quotient p)).coordinateRadius ^ 2 *
        centerResidualBound (quotient p) (largeSquareBox (quotient p))
          state.box := by
  have quotientResidual := carrier_center_residual_le state
  have centerInside : (largeSquareBox (quotient p)).Contains
      state.box.center :=
    state.refinesAmbient.contains state.box.contains_center
  have centerBound :=
    CCLChordalEnvelope.normSq_le_two_coordinateRadius_sq centerInside
  have residualNonnegative :
      0 ≤ centerResidualBound (quotient p)
        (largeSquareBox (quotient p)) state.box := by
    exact mul_nonneg
      (GaussianPolynomialBounds.denseLipschitzBound_pos
        (quotient p) (largeSquareBox (quotient p))).le
      state.box.diagonalSq_nonneg
  rw [eval_eq_quotient_mul_of_nonzero nonzero zero state.box.center,
    normSq_mul]
  calc
    normSq ((quotient p).eval state.box.center) *
          normSq state.box.center ≤
        centerResidualBound (quotient p) (largeSquareBox (quotient p))
            state.box *
          (2 * (largeSquareBox (quotient p)).coordinateRadius ^ 2) :=
      mul_le_mul quotientResidual centerBound (normSq_nonneg _)
        residualNonnegative
    _ = 2 * (largeSquareBox (quotient p)).coordinateRadius ^ 2 *
        centerResidualBound (quotient p) (largeSquareBox (quotient p))
          state.box := by ring

namespace RootTransducer

/-- Two exact points retained by separated transducers cannot coincide.  This
is the terminal counterpart of keeping two nonterminal projective envelopes
apart: terminal containment turns the same precomputed box gap into literal
Gaussian-rational inequality. -/
theorem points_ne_of_separated_containment
    {p : GaussianPolynomial} {left right : RootTransducer p}
    (separated : left.box.Separated right.box)
    {leftPoint rightPoint : QI}
    (leftContains : left.box.Contains leftPoint)
    (rightContains : right.box.Contains rightPoint) :
    leftPoint ≠ rightPoint := by
  intro equal
  apply RatBox.separated_no_common_member separated
  refine ⟨leftPoint, leftContains, ?_⟩
  rw [equal]
  exact rightContains

/-- Executable coordinate gap attached to any two currently separated root
transducers. -/
def pairGap
    {p : GaussianPolynomial} (left right : RootTransducer p)
    (separated : left.box.Separated right.box) :
    CCLMetricTrack.RegionGap left.box right.box :=
  CCLMetricTrack.RegionGap.compute _ _ separated

def pairProjectiveGap
    {p : GaussianPolynomial} (left right : RootTransducer p)
    (separated : left.box.Separated right.box) : ℚ :=
  CCLChordalEnvelope.chordalGapSq left.box right.box
    (pairGap left right separated).coordinateGap

theorem pairProjectiveGap_pos
    {p : GaussianPolynomial} (left right : RootTransducer p)
    (separated : left.box.Separated right.box) :
    0 < pairProjectiveGap left right separated :=
  CCLChordalEnvelope.chordalGapSq_pos _ _
    (pairGap left right separated).positive

def pairTarget
    {p : GaussianPolynomial} (left right : RootTransducer p)
    (separated : left.box.Separated right.box) : ℚ :=
  min 1 (pairProjectiveGap left right separated / 64)

theorem pairTarget_pos
    {p : GaussianPolynomial} (left right : RootTransducer p)
    (separated : left.box.Separated right.box) :
    0 < pairTarget left right separated := by
  rw [pairTarget, lt_min_iff]
  exact ⟨by norm_num,
    div_pos (pairProjectiveGap_pos left right separated) (by norm_num)⟩

theorem pairTarget_error_le
    {p : GaussianPolynomial} (left right : RootTransducer p)
    (separated : left.box.Separated right.box) :
    2 * (pairTarget left right separated ^ 2 +
      pairTarget left right separated) ≤
        pairProjectiveGap left right separated / 16 := by
  let target := pairTarget left right separated
  let gap := pairProjectiveGap left right separated
  have targetPositive : 0 < target := pairTarget_pos left right separated
  have targetLeOne : target ≤ 1 := min_le_left _ _
  have targetLeGap : target ≤ gap / 64 := min_le_right _ _
  have squareLe : target ^ 2 ≤ target := by nlinarith
  change 2 * (target ^ 2 + target) ≤ gap / 16
  calc
    2 * (target ^ 2 + target) ≤ 4 * target := by linarith
    _ ≤ 4 * (gap / 64) :=
      mul_le_mul_of_nonneg_left targetLeGap (by norm_num)
    _ = gap / 16 := by ring

/-- Data-bearing result of two independent finite requests at their
precomputed separation target. -/
inductive PairRequestResult
    {p : GaussianPolynomial} (left right : RootTransducer p)
    (separated : left.box.Separated right.box)
    (leftCount rightCount : ℕ) where
  | leftZero (root : p.eval 0 = 0) :
      PairRequestResult left right separated leftCount rightCount
  | leftTerminal (point : QI) (root : p.eval point = 0)
      (nonzero : point ≠ 0) (completeWord : Prefix.Word)
      (complete : completeWord = RationalEncoder.encode point nonzero)
      (contains : left.box.Contains point) :
      PairRequestResult left right separated leftCount rightCount
  | rightZero (root : p.eval 0 = 0) :
      PairRequestResult left right separated leftCount rightCount
  | rightTerminal (point : QI) (root : p.eval point = 0)
      (nonzero : point ≠ 0) (completeWord : Prefix.Word)
      (complete : completeWord = RationalEncoder.encode point nonzero)
      (contains : right.box.Contains point) :
      PairRequestResult left right separated leftCount rightCount
  | keptApart
      (nextLeft nextRight : RootTransducer p)
      (leftProgress : Progresses nextLeft left leftCount)
      (rightProgress : Progresses nextRight right rightCount)
      (leftEnvelope rightEnvelope : FiniteTaggedEnvelope)
      (leftBox : leftEnvelope.box = nextLeft.box)
      (rightBox : rightEnvelope.box = nextRight.box)
      (leftWord : nextLeft.word = some leftEnvelope.tag.word)
      (rightWord : nextRight.word = some rightEnvelope.tag.word)
      (leftAccurate : leftEnvelope.errorSq ≤
        2 * (pairTarget left right separated ^ 2 +
          pairTarget left right separated))
      (rightAccurate : rightEnvelope.errorSq ≤
        2 * (pairTarget left right separated ^ 2 +
          pairTarget left right separated))
      (centersApart :
        ¬leftEnvelope.center.Equivalent rightEnvelope.center) :
      PairRequestResult left right separated leftCount rightCount

/-- Uniform pair request implementing the final box-plus-cylinder gap
inequality.  It is independent of whether each active member came from the
original polynomial or the constructively deflated quotient. -/
def requestPair
    {p : GaussianPolynomial} (left right : RootTransducer p)
    (separated : left.box.Separated right.box)
    (leftCount rightCount : ℕ) :
    PairRequestResult left right separated leftCount rightCount := by
  let target := pairTarget left right separated
  let targetPositive := pairTarget_pos left right separated
  let leftRun := left.advance target targetPositive leftCount
  match leftRun with
  | .zero root => exact .leftZero root
  | .terminal point root nonzero completeWord complete contains =>
      exact .leftTerminal point root nonzero completeWord complete contains
  | .nonterminal nextLeft _leftOriginal leftProgress leftEnvelope leftBox
      leftWord _leftBoxAccurate _leftApproximant _leftConstant
      _leftResidual _leftMovement leftAccurate =>
      let rightRun := right.advance target targetPositive rightCount
      match rightRun with
      | .zero root => exact .rightZero root
      | .terminal point root nonzero completeWord complete contains =>
          exact .rightTerminal point root nonzero completeWord complete contains
      | .nonterminal nextRight _rightOriginal rightProgress rightEnvelope
          rightBox rightWord _rightBoxAccurate _rightApproximant
          _rightConstant _rightResidual _rightMovement rightAccurate =>
          let refinedGap := (pairGap left right separated).refine
            leftProgress.box rightProgress.box
          have initialGapLe : pairProjectiveGap left right separated ≤
              CCLChordalEnvelope.chordalGapSq nextLeft.box nextRight.box
                refinedGap.coordinateGap := by
            simpa only [pairProjectiveGap, refinedGap,
              CCLMetricTrack.RegionGap.refine] using
              CCLMetricFamily.chordalGapSq_le_of_refines leftProgress.box
                rightProgress.box (pairGap left right separated).coordinateGap
          have componentBound := pairTarget_error_le left right separated
          have leftError : leftEnvelope.errorSq ≤
              pairProjectiveGap left right separated / 16 :=
            leftAccurate.trans componentBound
          have rightError : rightEnvelope.errorSq ≤
              pairProjectiveGap left right separated / 16 :=
            rightAccurate.trans componentBound
          have initialPositive := pairProjectiveGap_pos left right separated
          have thinInitial :
              4 * (leftEnvelope.errorSq + rightEnvelope.errorSq) <
                pairProjectiveGap left right separated := by
            calc
              4 * (leftEnvelope.errorSq + rightEnvelope.errorSq) ≤
                  4 * (pairProjectiveGap left right separated / 16 +
                    pairProjectiveGap left right separated / 16) :=
                mul_le_mul_of_nonneg_left (add_le_add leftError rightError)
                  (by norm_num)
              _ < pairProjectiveGap left right separated := by linarith
          have thin : 4 *
              (leftEnvelope.errorSq + rightEnvelope.errorSq) <
                CCLChordalEnvelope.chordalGapSq nextLeft.box nextRight.box
                  refinedGap.coordinateGap :=
            thinInitial.trans_le initialGapLe
          exact .keptApart nextLeft nextRight leftProgress rightProgress
            leftEnvelope rightEnvelope leftBox rightBox leftWord rightWord
              leftAccurate rightAccurate
              (FiniteTaggedEnvelope.centers_not_equivalent_of_error_sum_lt_gap
                refinedGap.positive refinedGap.separated leftBox rightBox thin)

end RootTransducer

namespace Family

/-- Apply the uniform quantitative keep-apart request to any two distinct
members of the exactly-degree family. -/
def requestPairAt
    {p : GaussianPolynomial} (family : Family p)
    (left right : Fin p.natDegree) (distinct : left ≠ right)
    (leftCount rightCount : ℕ) :
    RootTransducer.PairRequestResult (family.memberAt left)
      (family.memberAt right)
      (family.memberAt_pairwiseSeparated left right distinct)
      leftCount rightCount :=
  RootTransducer.requestPair (family.memberAt left) (family.memberAt right)
    (family.memberAt_pairwiseSeparated left right distinct)
      leftCount rightCount

end Family

/-- Single data-bearing conclusion of the paper's finite constructive FTA.
The family field packages clauses (a)--(c): it has exactly the natural degree,
its current regions are pairwise separated, and each member is a total finite
root transducer.  The final field is the degree-sharp maximality clause (d).
Exact terminals use their singleton comparison boxes; active members expose
winding-one numerical states through `RootTransducer.advance`. -/
structure MainResult (p : GaussianPolynomial) where
  family : Family p
  maximality :
    ∀ {familyCount : ℕ}
      (candidate : Fin familyCount →
        RootTrackSeparation.WindingOneTrack p (largeSquareBox p)),
      (∀ left right, left ≠ right →
        (candidate left).initial.box.Separated
          (candidate right).initial.box) →
      familyCount ≤ p.natDegree

/-- Paper-facing finite constructive FTA algorithm.  Its input and output are
finite coefficient lists, explicit certificates, finite lists, and ordinary
natural-number recursive programs. -/
def finiteConstructiveFTA
    {p : GaussianPolynomial} (input : Input p) : MainResult p where
  family := build input
  maximality := input.maximality

/-- Primitive degree-greater-than-one specialization requested by the paper.
Its squarefree Bézout data is computed internally by dense Gaussian extended
Euclid. -/
def primitiveFiniteConstructiveFTA
    {p : GaussianPolynomial} (primitive : FTA.Primitive p.toPolynomial)
    (degree : 1 < p.natDegree) : MainResult p :=
  finiteConstructiveFTA (Input.ofPrimitiveDegreeGtOne primitive degree)

namespace MainResult

/-- Degree-indexed access to the exactly-degree output family. -/
def memberAt
    {p : GaussianPolynomial} (result : MainResult p)
    (index : Fin p.natDegree) : RootTransducer p :=
  result.family.memberAt index

theorem memberAt_isNonterminal_of_noGaussianRationalRoot
    {p : GaussianPolynomial} (result : MainResult p)
    (noRoot : NoGaussianRationalRoot p) (index : Fin p.natDegree) :
    (result.memberAt index).IsNonterminal :=
  RootTransducer.isNonterminal_of_noGaussianRationalRoot noRoot _

/-- The executable positive rational coordinate gap promised by clause (a). -/
def initialGapAt
    {p : GaussianPolynomial} (result : MainResult p)
    (left right : Fin p.natDegree) (distinct : left ≠ right) :
    CCLMetricTrack.RegionGap (result.memberAt left).box
      (result.memberAt right).box :=
  RootTransducer.pairGap (result.memberAt left) (result.memberAt right)
    (result.family.memberAt_pairwiseSeparated left right distinct)

theorem initialGapAt_positive
    {p : GaussianPolynomial} (result : MainResult p)
    (left right : Fin p.natDegree) (distinct : left ≠ right) :
    0 < (result.initialGapAt left right distinct).coordinateGap :=
  (result.initialGapAt left right distinct).positive

/-- One total clause-(b,c) request on a selected output transducer. -/
def advanceAt
    {p : GaussianPolynomial} (result : MainResult p)
    (index : Fin p.natDegree) (target : ℚ) (targetPositive : 0 < target)
    (count : ℕ) :
    RootTransducer.AdvanceResult (result.memberAt index) target count :=
  (result.memberAt index).advance target targetPositive count

theorem advanceAt_isNonterminal_of_noGaussianRationalRoot
    {p : GaussianPolynomial} (result : MainResult p)
    (noRoot : NoGaussianRationalRoot p)
    (index : Fin p.natDegree) (target : ℚ) (targetPositive : 0 < target)
    (count : ℕ) :
    (result.advanceAt index target targetPositive count).IsNonterminal :=
  RootTransducer.AdvanceResult.isNonterminal_of_noGaussianRationalRoot
    noRoot _

/-- Joint finite request exposing the box-plus-cylinder keep-apart invariant
for any two distinct members of the paper-facing result. -/
def requestPairAt
    {p : GaussianPolynomial} (result : MainResult p)
    (left right : Fin p.natDegree) (distinct : left ≠ right)
    (leftCount rightCount : ℕ) :
    RootTransducer.PairRequestResult (result.memberAt left)
      (result.memberAt right)
      (result.family.memberAt_pairwiseSeparated left right distinct)
      leftCount rightCount :=
  result.family.requestPairAt left right distinct leftCount rightCount

end MainResult

/-- Every one of the exactly-degree primitive output members is nonterminal. -/
theorem primitiveFiniteConstructiveFTA_member_isNonterminal
    {p : GaussianPolynomial} (primitive : FTA.Primitive p.toPolynomial)
    (degree : 1 < p.natDegree) (index : Fin p.natDegree) :
    RootTransducer.IsNonterminal
      ((primitiveFiniteConstructiveFTA primitive degree).memberAt index) :=
  MainResult.memberAt_isNonterminal_of_noGaussianRationalRoot
    (primitiveFiniteConstructiveFTA primitive degree)
    (noGaussianRationalRoot_of_primitive_degree_gt_one primitive degree)
    index

/-- Every finite request on a primitive degree-greater-than-one member returns
the nonterminal shrinking-box/envelope constructor. -/
theorem primitiveFiniteConstructiveFTA_advance_isNonterminal
    {p : GaussianPolynomial} (primitive : FTA.Primitive p.toPolynomial)
    (degree : 1 < p.natDegree) (index : Fin p.natDegree)
    (target : ℚ) (targetPositive : 0 < target) (count : ℕ) :
    ((primitiveFiniteConstructiveFTA primitive degree).advanceAt index target
      targetPositive count).IsNonterminal :=
  MainResult.advanceAt_isNonterminal_of_noGaussianRationalRoot
    (primitiveFiniteConstructiveFTA primitive degree)
    (noGaussianRationalRoot_of_primitive_degree_gt_one primitive degree)
    index target targetPositive count

end FiniteConstructiveFTA
end FTA
