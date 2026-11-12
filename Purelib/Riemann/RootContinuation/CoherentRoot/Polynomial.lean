module

public import Purelib.Riemann.RootContinuation.CoherentRoot
public import Purelib.Approximation.Gaussian.Name.Coherent.Difference
public import Purelib.Geometry.Rational.Box.Hull
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Process.Addition
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Nat.Subtraction
import Purelib.Approximation.Gaussian.Name.Arithmetic
public import Purelib.RootIsolation.FTA.Positive.Input
public import Purelib.Polynomial.Approximation.Gaussian.Residual
public import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner
public import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner.Power
public import Purelib.Approximation.Gaussian.Provenance.Power
import Purelib.Polynomial.Approximation.CoherentEvaluation
public import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Tactic.Ring
import Purelib.Algebra.Ring.Normalization
import Purelib.Approximation.Gaussian.Coherent.Additive
import Purelib.Approximation.Gaussian.Arithmetic.Neg

/-!
# Polynomial equations at the original coherent root channel

The original root certificate retains its actual cached approximation. The
existing Horner/geometric comparison connects coherent arithmetic on that
original channel to its finite polynomial residual bounds.
-/

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot.CertifiedName

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Data.Rat.Fraction
open Purelib.Algebra.Ring
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Rational
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Polynomial.Approximation
open Purelib.Polynomial.Approximation.Gaussian.Evaluation
open Purelib.Polynomial
open Purelib.RootIsolation
open FTA.Positive.Input (PositiveInput)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.Geometry.Rational.Box

/-- Bound all actual original difference readings by the hull of both retained initial root boxes.

Both original numerical channels and track parents remain independent.
Original sequence-backed possibility supplies actual future root samples;
the finite hull bounds their squared distance at every such pair. No
successful comparison or exact-root reading is assumed.
-/
def differenceBound
    {firstPolynomial secondPolynomial : GaussianPolynomial} {firstAmbient secondAmbient : Box}
    {firstTrack : WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : WindingOneTrack secondPolynomial secondAmbient}
    (first : CertifiedName firstTrack) (second : CertifiedName secondTrack) :
    Difference.Bound first.value second.value := by
  let hull := Hull.hull firstTrack.initial.box secondTrack.initial.box
  refine ⟨hull.diagonalSq, ?_⟩
  intro value possible
  change ∃ right negative,
    second.value.name.process.Possible second.value.name.state right ∧
      (∃ left, first.value.name.process.Possible first.value.name.state left ∧ negative = -left) ∧
        value = right + negative at possible
  rcases possible with ⟨right, negative, rightPossible, ⟨left, leftPossible, negativeEq⟩, valueEq⟩
  rewrite [valueEq, negativeEq]
  change normSq (right - left) ≤ hull.diagonalSq
  exact hull.normSq_sub_le_diagonalSq
    ((Hull.right_refines _ _).contains (second.possible_initial_inside rightPossible))
    ((Hull.left_refines _ _).contains (first.possible_initial_inside leftPossible))

/-- The retained original root difference bound is the actual initial-box hull diagonal. -/
theorem differenceBound_value
    {firstPolynomial secondPolynomial : GaussianPolynomial} {firstAmbient secondAmbient : Box}
    {firstTrack : WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : WindingOneTrack secondPolynomial secondAmbient}
    (first : CertifiedName firstTrack) (second : CertifiedName secondTrack) :
    (first.differenceBound second).val =
      (Hull.hull firstTrack.initial.box secondTrack.initial.box).diagonalSq := by
  unfold differenceBound
  rfl

/-- Read both original raw root indices from the actual ordered difference process state.

The original addition/negation keeps its two actual process-state parents.
Each original channel equation transports only its corresponding retained
state index; neither sample nor numerical root refinement is requested.
-/
def differenceStateIndices {firstPolynomial secondPolynomial : GaussianPolynomial}
    {firstAmbient secondAmbient : Box}
    {firstTrack : WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : WindingOneTrack secondPolynomial secondAmbient}
    (first : CertifiedName firstTrack) (second : CertifiedName secondTrack) (index : Nat) : Nat × Nat :=
  let difference := Difference.difference first.value second.value
  let actual := Process.Sampling.stateAt difference.name.process difference.name.state index
  (first.stateIndex actual.2, second.stateIndex actual.1)

/-- One actual difference sampling step preserves both original raw-root index floors. -/
theorem differenceStateIndices_step {firstPolynomial secondPolynomial : GaussianPolynomial}
    {firstAmbient secondAmbient : Box}
    {firstTrack : WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : WindingOneTrack secondPolynomial secondAmbient}
    (first : CertifiedName firstTrack) (second : CertifiedName secondTrack) (index : Nat) :
    (first.differenceStateIndices second index).1 ≤ (first.differenceStateIndices second (index + 1)).1 ∧
      (first.differenceStateIndices second index).2 ≤ (first.differenceStateIndices second (index + 1)).2 := by
  let difference := Difference.difference first.value second.value
  let actual := Process.Sampling.stateAt difference.name.process difference.name.state index
  let target := Process.Sampling.refinementTarget (index + 1)
  have positive := Process.Sampling.refinementTarget_pos (index + 1)
  have inputPositive := Purelib.Data.Rat.Bounds.Quarter.quarter_pos positive
  have firstReadback :
      (first.differenceStateIndices second (index + 1)).1 =
        first.stateIndex (first.value.name.process.refine actual.2 (target / 4) inputPositive) :=
    congrArg (fun state : difference.name.process.State => first.stateIndex state.2)
      (Process.Sampling.stateAt_succ difference.name.process difference.name.state index)
  have secondReadback :
      (first.differenceStateIndices second (index + 1)).2 =
        second.stateIndex (second.value.name.process.refine actual.1 (target / 4) inputPositive) :=
    congrArg (fun state : difference.name.process.State => second.stateIndex state.1)
      (Process.Sampling.stateAt_succ difference.name.process difference.name.state index)
  rewrite [firstReadback, secondReadback]
  exact ⟨first.stateIndex_refine_ge actual.2 _ _, second.stateIndex_refine_ge actual.1 _ _⟩

/-- Every later actual difference sample preserves both original raw-root stage floors. -/
theorem differenceStateIndices_mono {firstPolynomial secondPolynomial : GaussianPolynomial}
    {firstAmbient secondAmbient : Box}
    {firstTrack : WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : WindingOneTrack secondPolynomial secondAmbient}
    (first : CertifiedName firstTrack) (second : CertifiedName secondTrack)
    {earlier later : Nat} (ordered : earlier ≤ later) :
    (first.differenceStateIndices second earlier).1 ≤ (first.differenceStateIndices second later).1 ∧
      (first.differenceStateIndices second earlier).2 ≤ (first.differenceStateIndices second later).2 := by
  have extended : ∀ extra,
      (first.differenceStateIndices second earlier).1 ≤ (first.differenceStateIndices second (earlier + extra)).1 ∧
        (first.differenceStateIndices second earlier).2 ≤
          (first.differenceStateIndices second (earlier + extra)).2 := by
    intro extra
    induction extra with
    | zero => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    | succ extra previous =>
        have step := first.differenceStateIndices_step second (earlier + extra)
        exact ⟨previous.1.trans step.1, previous.2.trans step.2⟩
  have actual := extended (later - earlier)
  rewrite [Nat.add_sub_of_le ordered] at actual
  exact actual

/-- An exact view of a retained squarefree root certificate, its original input and a linked numerical channel.

The dependent tuple contains the actual original polynomial, ambient, track
and complete root certificate. It creates no root owner or numerical process.
A producer's original-view equality separately identifies the supplied parent.
-/
@[expose] def View (channel : CoherentNamed) : Type 1 :=
  Σ polynomial : GaussianPolynomial, Σ ambient : Box,
  Σ track : WindingOneTrack polynomial ambient, Σ root : CertifiedName track,
    PositiveInput polynomial × Equivalence.NamedEquivalent channel.name root.value.name ×
      Option (PLift (channel = root.value))

namespace View

/-- The defining polynomial of the same retained root certificate. -/
@[expose] def polynomial {channel : CoherentNamed} (view : View channel) : GaussianPolynomial := view.1

/-- The original ambient of the same retained root certificate. -/
@[expose] def ambient {channel : CoherentNamed} (view : View channel) : Box := view.2.1

/-- The actual original track of the same retained root certificate. -/
@[expose] def track {channel : CoherentNamed} (view : View channel) :
    WindingOneTrack view.polynomial view.ambient := view.2.2.1

/-- The complete original root certificate, including its actual shared state cache. -/
@[expose] def root {channel : CoherentNamed} (view : View channel) : CertifiedName view.track := view.2.2.2.1

/-- The original positive-degree squarefree input at this same defining polynomial. -/
@[expose] def input {channel : CoherentNamed} (view : View channel) :
    PositiveInput view.polynomial := view.2.2.2.2.1

/-- The supplied numerical channel's operational link to the same actual original root. -/
@[expose] def equivalent {channel : CoherentNamed} (view : View channel) :
    Equivalence.NamedEquivalent channel.name view.root.value.name := view.2.2.2.2.2.1

/-- A retained genuine identity of the entire supplied channel with this same original root channel. -/
@[expose] def channelEq? {channel : CoherentNamed} (view : View channel) :
    Option (PLift (channel = view.root.value)) := view.2.2.2.2.2.2

/-- Prepare a hull bound and source-floor check on the same original supplied difference channels.

Both complete channel identities are required. The original roots, tracks,
boxes and input links remain literal parents. Each actual requested sampling
index checks both retained raw-source floors; later indices preserve them.
Operational-only links leave this finite request unavailable.
-/
def differenceRequest? {first second : CoherentNamed} (left : View first) (right : View second)
    (firstStart secondStart : Nat) : Option (Difference.Request first second) :=
  match left.channelEq?, right.channelEq? with
  | some leftSame, some rightSame =>
      let retained := Eq.mp ((congrArg (fun channel : CoherentNamed =>
        Difference.Bound channel right.root.value) leftSame.down.symm).trans
        (congrArg (fun channel : CoherentNamed =>
          Difference.Bound first channel) rightSame.down.symm))
        (left.root.differenceBound right.root)
      let paid := fun index =>
        let actual := left.root.differenceStateIndices right.root index
        decide (firstStart ≤ actual.1 ∧ secondStart ≤ actual.2)
      some (retained, paid)
  | _, _ => none

/-- Missing left whole-channel identity preserves the unavailable hull-bound request. -/
theorem differenceRequest?_left_none {first second : CoherentNamed} (left : View first) (right : View second)
    (firstStart secondStart : Nat) (missing : left.channelEq? = none) :
    left.differenceRequest? right firstStart secondStart = none := by
  unfold differenceRequest?
  rewrite [missing]
  rfl

/-- Missing right whole-channel identity preserves the unavailable hull-bound request. -/
theorem differenceRequest?_right_none {first second : CoherentNamed} (left : View first) (right : View second)
    (firstStart secondStart : Nat) (missing : right.channelEq? = none) :
    left.differenceRequest? right firstStart secondStart = none := by
  unfold differenceRequest?
  rewrite [missing]
  cases left.channelEq? <;> rfl

/-- A successful retained difference request checks both original raw source floors at that actual sampling index. -/
theorem differenceRequest?_paid {first second : CoherentNamed} (left : View first) (right : View second)
    (firstStart secondStart : Nat) (request : Difference.Request first second)
    (found : left.differenceRequest? right firstStart secondStart = some request) (index : Nat)
    (paid : request.2 index = true) :
    firstStart ≤ (left.root.differenceStateIndices right.root index).1 ∧
      secondStart ≤ (left.root.differenceStateIndices right.root index).2 := by
  unfold differenceRequest? at found
  cases leftFound : left.channelEq? with
  | none =>
      rewrite [leftFound] at found
      cases found
  | some leftSame =>
      rewrite [leftFound] at found
      cases rightFound : right.channelEq? with
      | none =>
          rewrite [rightFound] at found
          cases found
      | some rightSame =>
          rewrite [rightFound] at found
          cases found
          exact of_decide_eq_true paid

/-- Every later actual root pair preserves the same checked original source floors of a successful request. -/
theorem differenceRequest?_paid_future {first second : CoherentNamed} (left : View first) (right : View second)
    (firstStart secondStart : Nat) (request : Difference.Request first second)
    (found : left.differenceRequest? right firstStart secondStart = some request)
    {earlier later : Nat} (paid : request.2 earlier = true) (ordered : earlier ≤ later) :
    firstStart ≤ (left.root.differenceStateIndices right.root later).1 ∧
      secondStart ≤ (left.root.differenceStateIndices right.root later).2 := by
  have current := left.differenceRequest?_paid right firstStart secondStart request found earlier paid
  have advanced := left.root.differenceStateIndices_mono right.root ordered
  exact ⟨current.1.trans advanced.1, current.2.trans advanced.2⟩

/-- Project an original certificate and its input without constructing another root or state cache. -/
@[expose] def ofRoot {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track)
    (input : PositiveInput polynomial) : View root.value :=
  ⟨polynomial, ambient, track, root, input, Equivalence.NamedEquivalent.refl _, some ⟨rfl⟩⟩

/-- Retain the exact root, track and input while composing the supplied original-channel comparison. -/
@[expose] def transport {first second : CoherentNamed} (view : View first)
    (equivalent : Equivalence.NamedEquivalent second.name first.name)
    (same : Option (PLift (second = first)) := none) : View second :=
  let channelEq : Option (PLift (second = view.root.value)) := match same, view.channelEq? with
    | some supplied, some retained => some ⟨supplied.down.trans retained.down⟩
    | _, _ => none
  ⟨view.polynomial, view.ambient, view.track, view.root, view.input,
    equivalent.trans view.equivalent, channelEq⟩

/-- An original root view retains the actual entire root-channel identity. -/
theorem channelEq?_ofRoot {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track)
    (input : PositiveInput polynomial) :
    (ofRoot root input).channelEq? = some ⟨rfl⟩ := rfl

/-- Operational-only transport keeps the complete original root/link tuple and records no channel identity. -/
theorem transport_none {first second : CoherentNamed} (view : View first)
    (equivalent : Equivalence.NamedEquivalent second.name first.name) :
    view.transport equivalent none =
      ⟨view.polynomial, view.ambient, view.track, view.root, view.input,
        equivalent.trans view.equivalent, none⟩ := rfl

/-- Equality transport propagates only the supplied whole identity and the same retained root identity. -/
theorem transport_channelEq {first second : CoherentNamed} (view : View first)
    (equivalent : Equivalence.NamedEquivalent second.name first.name) (same : PLift (second = first)) :
    (view.transport equivalent (some same)).channelEq? =
      match view.channelEq? with
      | some retained => some ⟨same.down.trans retained.down⟩
      | none => none := by
  change (match some same, view.channelEq? with
    | some supplied, some retained => some (⟨supplied.down.trans retained.down⟩ : PLift (second = view.root.value))
    | _, _ => none) = _
  cases view.channelEq? <;> rfl

/-- Restore a comparison of two retained roots to their actual supplied channels.

Genuine whole-channel identities transport the same relation record directly.
Without both identities, the original two operational links are composed and
retain their original comparison procedures and request payments.
-/
@[expose] def transportComparison {first second : CoherentNamed}
    (left : View first) (right : View second)
    (equivalent : Equivalence.NamedEquivalent left.root.value.name right.root.value.name) :
    Equivalence.NamedEquivalent first.name second.name :=
  match left.channelEq?, right.channelEq? with
  | some leftSame, some rightSame =>
      Eq.mp ((congrArg (fun channel : CoherentNamed =>
        Equivalence.NamedEquivalent channel.name right.root.value.name) leftSame.down.symm).trans
        (congrArg (fun channel : CoherentNamed =>
          Equivalence.NamedEquivalent first.name channel.name) rightSame.down.symm)) equivalent
  | _, _ => left.equivalent.trans (equivalent.trans right.equivalent.symm)

/-- Missing left identity retains the complete original operational comparison procedure. -/
theorem transportComparison_left_none {first second : CoherentNamed}
    (left : View first) (right : View second)
    (equivalent : Equivalence.NamedEquivalent left.root.value.name right.root.value.name)
    (missing : left.channelEq? = none) :
    left.transportComparison right equivalent =
      left.equivalent.trans (equivalent.trans right.equivalent.symm) := by
  unfold transportComparison
  rewrite [missing]
  rfl

/-- Missing right identity retains the complete original operational comparison procedure. -/
theorem transportComparison_right_none {first second : CoherentNamed}
    (left : View first) (right : View second)
    (equivalent : Equivalence.NamedEquivalent left.root.value.name right.root.value.name)
    (missing : right.channelEq? = none) :
    left.transportComparison right equivalent =
      left.equivalent.trans (equivalent.trans right.equivalent.symm) := by
  unfold transportComparison
  rewrite [missing]
  cases left.channelEq? <;> rfl

/-- Two genuine retained channel identities consume the literal supplied root comparison record. -/
theorem transportComparison_same {first second : CoherentNamed}
    (left : View first) (right : View second)
    (equivalent : Equivalence.NamedEquivalent left.root.value.name right.root.value.name)
    (leftSame : PLift (first = left.root.value)) (rightSame : PLift (second = right.root.value))
    (leftFound : left.channelEq? = some leftSame) (rightFound : right.channelEq? = some rightSame) :
    left.transportComparison right equivalent =
      Eq.mp ((congrArg (fun channel : CoherentNamed =>
        Equivalence.NamedEquivalent channel.name right.root.value.name) leftSame.down.symm).trans
        (congrArg (fun channel : CoherentNamed =>
          Equivalence.NamedEquivalent first.name channel.name) rightSame.down.symm)) equivalent := by
  unfold transportComparison
  rewrite [leftFound, rightFound]
  rfl

end View

/-- Regard the original cached root samples as their certified geometric approximation.

The original approximation supplies every sample, magnitude bound and movement
certificate. Its original track identity supplies the geometric error scale;
no root refinement or new sample sequence is constructed.
-/
@[expose] def geometric {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (certificate : CertifiedName track) :
    GeometricApproximation where
  sample := certificate.approximation.sample
  errorScale := scale track
  errorScale_nonneg := (scale_positive track).le
  later_close := by
    intro earlier later order
    have close := certificate.approximation.later_close order
    have radius : certificate.approximation.radiusSq earlier =
        Geometric.Basic.quarterRadius (scale track) earlier := by
      rewrite [certificate.approximation_eq]
      rfl
    rewrite [radius] at close
    exact close
  centerBound := certificate.approximation.centerBound
  centerBound_nonneg := certificate.approximation.centerBound_nonneg
  sample_bounded := certificate.approximation.sample_bounded

/-- Compare the original root channel to an actual retained target with the same original cached samples.

The supplied target is consumed directly. Its complete geometric data and
original sample programme remain the right comparison owner; no geometric
view, shrinking track or root cache is constructed by this operation.
-/
def geometric_agreesWith {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (certificate : CertifiedName track)
    (target : GeometricApproximation)
    (samples : ∀ index, target.sample index = certificate.approximation.sample index) :
    Equivalence.NamedEquivalent certificate.value.name target.toApproximation.toNamed := by
  rewrite [certificate.value_approximation]
  exact (Sequence.Equivalence.approximationEquivalentOfSamplesEq certificate.approximation
    target.toApproximation (fun index => (samples index).symm)).toNamed

/-- The original coherent root channel agrees with the geometric view of its actual retained samples. -/
def geometric_agrees {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (certificate : CertifiedName track) :
    Equivalence.NamedEquivalent certificate.value.name certificate.geometric.toApproximation.toNamed :=
  certificate.geometric_agreesWith certificate.geometric (fun _ => rfl)

/-- The default root comparison is the actual-target comparison on its complete original geometric view. -/
private theorem geometric_agrees_readback {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (certificate : CertifiedName track) :
    certificate.geometric_agrees = certificate.geometric_agreesWith certificate.geometric (fun _ => rfl) := rfl

/-- Read the exact complete actual-target construction retained by the default root comparison. -/
theorem geometric_agrees_eq {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (certificate : CertifiedName track) :
    certificate.geometric_agrees = certificate.geometric_agreesWith certificate.geometric (fun _ => rfl) :=
  certificate.geometric_agrees_readback

/-- Retain the original cached root samples and quantitative residual as reusable evidence on the same channel. -/
@[expose] def residualCertificate {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (certificate : CertifiedName track) :
    Polynomial.Approximation.Gaussian.Residual polynomial certificate.value :=
  Polynomial.Approximation.Gaussian.Residual.ofGeometric certificate.degreePositive certificate.geometric
    certificate.geometric_agrees (CoherentRoot.residualScale polynomial ambient track)
    (CoherentRoot.residualScale_nonneg polynomial ambient track) (by
      intro index
      have bound := certificate.residual index
      rewrite [← certificate.approximation_eq] at bound
      exact bound)

/-- Actual coherent Horner evaluation of the original root channel is operationally zero.

The existing Horner/geometric agreement theorem consumes the original channel
and cached sample view. Equal scalar polynomial readbacks connect that result
to the retained residual evaluation, whose geometric bound computes the final
all-start zero comparison.
-/
def polynomial_zero {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (certificate : CertifiedName track) :
    Equivalence.NamedEquivalent
      (Horner.polynomialEval polynomial certificate.value).name
      (CoherentNamed.Coherence.exact 0).name :=
  (CoherentEvaluation.evaluate_agrees polynomial certificate.value certificate.geometric
    certificate.geometric_agrees).trans
      (((Sequence.Equivalence.approximationEquivalentOfSamplesEq
        (Evaluation.evaluate polynomial certificate.geometric).toApproximation certificate.evaluation
        (fun _ => rfl)).toNamed).trans certificate.evaluation_zero)

/-- A retained root of a factor is operationally a root of its original product polynomial.

The scalar factorization and cached cofactor bound concern the same original
samples. Multiplicativity of squared norm combines that bound with the root's
existing geometric residual, computing a sufficient comparison scale without
asserting that any finite sample is an exact root.
-/
def factor_zero {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (certificate : CertifiedName track)
    (source cofactor : GaussianPolynomial)
    (identity : ∀ point, source.eval point = polynomial.eval point * cofactor.eval point)
    (cofactorBound : Rational) (nonnegative : 0 ≤ cofactorBound)
    (bounded : ∀ index, normSq (cofactor.eval (certificate.approximation.sample index)) ≤ cofactorBound) :
    Equivalence.NamedEquivalent
      (Horner.polynomialEval source certificate.value).name
      (CoherentNamed.Coherence.exact 0).name := by
  let evaluated := Dense.Gaussian.Approximation.evaluate source ambient certificate.approximation
    certificate.sample_inside
  let scale := cofactorBound * residualScale polynomial ambient track
  have scaleNonnegative : 0 ≤ scale := Order.Arithmetic.mul_nonneg_direct
    nonnegative (residualScale_nonneg polynomial ambient track)
  have residual : ∀ index, normSq (evaluated.sample index - 0) ≤
      Geometric.Basic.quarterRadius scale index := by
    intro index
    change normSq (source.eval (certificate.approximation.sample index) - 0) ≤ _
    rewrite [Normalization.sub_zero, identity (certificate.approximation.sample index)]
    rewrite [Purelib.Data.Gaussian.Norm.Basic.normSq_mul]
    have rootBound := certificate.residual index
    rewrite [← certificate.approximation_eq] at rootBound
    calc
      normSq (polynomial.eval (certificate.approximation.sample index)) *
          normSq (cofactor.eval (certificate.approximation.sample index)) ≤
          normSq (polynomial.eval (certificate.approximation.sample index)) * cofactorBound :=
        Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (bounded index)
          (Purelib.Data.Gaussian.Norm.Basic.normSq_nonneg _)
      _ ≤ Geometric.Basic.quarterRadius (residualScale polynomial ambient track) index * cofactorBound :=
        Order.Arithmetic.mul_le_mul_of_nonneg_right_direct rootBound nonnegative
      _ = Geometric.Basic.quarterRadius scale index := by
        rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
        dsimp only [scale]
        ring1
  let zero := Sequence.Equivalence.equivalent_constant evaluated 0 scale scaleNonnegative residual
  let agree := CoherentEvaluation.evaluate_agrees source certificate.value certificate.geometric
    certificate.geometric_agrees
  let samples := Sequence.Equivalence.approximationEquivalentOfSamplesEq
    (Evaluation.evaluate source certificate.geometric).toApproximation evaluated (fun _ => rfl)
  exact agree.trans (samples.toNamed.trans (zero.toNamed.trans
    (Sequence.Name.Exact.exact_toConstantNamed 0).symm))

/-- A certified power-polynomial root supplies its degree-generic operational power identity on the original channel.

The existing residual equation is connected through the original Horner
coefficient table. Finite additive cancellation then identifies the original
input power with the exact parameter; no approximate sample is treated as a root.
-/
def power_identity {parameter : Canonical}
    {degree : RootDegree} {ambient : Box}
    {track : WindingOneTrack (Power.Gaussian.rootPolynomial parameter degree) ambient}
    (certificate : CertifiedName track) :
    Provenance.Power.PowerIdentity certificate.value degree.value parameter := by
  let power := Name.Coherent.Power.namedPower certificate.value degree.value
  let exactParameter := CoherentNamed.Coherence.exact parameter
  have zeroDifference := (Horner.polynomialEval_rootPolynomial parameter degree certificate.value).symm.trans
    certificate.polynomial_zero
  have negative : Equivalence.NamedEquivalent (CoherentNamed.neg exactParameter).name
      (CoherentNamed.Coherence.exact (-parameter)).name := Arithmetic.Neg.exactNeg parameter
  have replaceNegative := Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects power power
    (CoherentNamed.neg exactParameter) (CoherentNamed.Coherence.exact (-parameter))
    (Equivalence.NamedEquivalent.refl _) negative
  exact Coherent.Additive.equivalent_of_sub_zero power exactParameter (replaceNegative.trans zeroDifference)

end Purelib.Riemann.RootContinuation.CoherentRoot.CertifiedName

end
