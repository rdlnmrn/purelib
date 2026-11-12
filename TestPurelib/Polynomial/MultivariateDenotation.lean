module

import Purelib.Polynomial.Multivariate.Gaussian.Dense
import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Geometric.Preparation
import Purelib.Approximation.Gaussian.Division.Prepared.Sum
import Purelib.Approximation.Gaussian.Division.Prepared.FromEvidence
import Purelib.Approximation.Gaussian.Process.Apart.Based
import Purelib.Approximation.Gaussian.Enclosure.Residual
import Purelib.Approximation.Gaussian.Process.Conjugation
import Purelib.Polynomial.Multivariate.PowerReduction
import Purelib.Polynomial.Multivariate.Gaussian.Denotation
import Purelib.Polynomial.Multivariate.Gaussian.Normalization
import Purelib.Polynomial.Multivariate.Gaussian.Normalization.Power
import Purelib.Polynomial.Multivariate.Gaussian.Renaming
import Purelib.Polynomial.Multivariate.Gaussian.Conjugation
import Purelib.Polynomial.Multivariate.Gaussian.Inverse
import Purelib.Polynomial.Approximation.CoherentEvaluation
import Purelib.Approximation.Gaussian.Arithmetic.Add
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.System.IO
import Purelib.Data.Fin
import TestPurelib.Polynomial.GaussianRootCandidates

/-!
# Literal reuse of original finite polynomial interpretation caches

The supplied monomial interpretation is arbitrary valid retained data. The
builder returns that entire input cache, including its power/product witnesses.
Recomputing another extensionally equal channel does not prove this identity.
-/

namespace TestPurelib.Polynomial.MultivariateDenotation

open Purelib
open Purelib.Polynomial.Multivariate
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Division
open Purelib.Approximation.Gaussian.Arithmetic
open Purelib.Data.Gaussian.Norm.Basic (normSq normSq_zero)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Polynomial.Approximation
open Purelib.Polynomial.Approximation.Gaussian.Evaluation
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_nonneg)
open Purelib.Approximation.Gaussian.Provenance

/-- Supply exactly the original monomial cache at its actual finite exponent key. -/
private def lookup {arity : Nat} {environment : Fin arity → CoherentNamed} {monomial : Monomial arity}
    (retained : Monomial.Denotation monomial environment) (requested : Monomial arity) :
    Option (Monomial.Denotation requested environment) :=
  if same : monomial = requested then some (same ▸ retained) else none

example {arity : Nat} (environment : Fin arity → CoherentNamed) (first : Term Canonical arity)
    (remaining : List (Term Canonical arity)) (retained : Monomial.Denotation first.monomial environment) :
    (Terms.retainWith environment (lookup retained) (first :: remaining)).findMonomial first.monomial =
      some retained := by
  apply Terms.retainWith_head
  unfold lookup
  rewrite [dif_pos rfl]
  rfl

example {arity : Nat} (environment : Fin arity → CoherentNamed) (form : Sparse Canonical arity)
    (original : CoherentNamed) (equivalent : NamedEquivalent original.name (form.denote environment).name)
    (cached : (monomial : Monomial arity) → Option (Monomial.Denotation monomial environment)) :
    (Gaussian.Normalized.ofForm environment form equivalent cached).denotation =
      Terms.retainWith environment cached form.terms :=
  Gaussian.Normalized.ofForm_denotation environment form equivalent cached

example {arity : Nat} (environment : Fin arity → CoherentNamed) (monomial : Monomial arity) :
    (monomial.retain environment).channel = monomial.denote environment :=
  (monomial.retain environment).channel_eq

/-- Completing an empty prefix retains the entire supplied power bank literally. -/
example (generator : CoherentNamed) (retained : List (Monomial.PowerEntry generator)) :
    (Monomial.retainPowerPrefix generator retained 0).val = retained := rfl

/-- Prefix construction preserves arbitrary existing channels and their order, computing only the missing powers.

The old cubic and linear channels may be any certified original caches. The
quadratic channel is constructed from that same stored linear channel, while
the cubic cache is retained without another power computation.
-/
example (generator : CoherentNamed)
    (linear : {channel : CoherentNamed // channel = Power.namedPower generator 1})
    (cubic : {channel : CoherentNamed // channel = Power.namedPower generator 3}) :
    (Monomial.retainPowerPrefix generator [⟨3, cubic⟩, ⟨1, linear⟩] 4).val =
      [⟨2, ⟨CoherentNamed.mul linear.val generator,
        congrArg (fun value => CoherentNamed.mul value generator) linear.property⟩⟩,
        ⟨0, ⟨Coherence.exact 1, rfl⟩⟩, ⟨3, cubic⟩, ⟨1, linear⟩] := rfl

/-- Any successful old monomial lookup supplies the same entire cache to the new bank-aware builder. -/
example {arity : Nat} (environment : Fin arity → CoherentNamed) (monomial : Monomial arity)
    (bounds : Fin arity → Nat) (banks : Monomial.PowerBanks environment bounds)
    (cached : Monomial.Caches environment) (below : ∀ index, monomial.exponentAt index < bounds index)
    (retained : Monomial.Denotation monomial environment)
    (found : Monomial.findCache monomial cached = some retained) :
    Monomial.retainWithBanks monomial environment bounds banks cached below = retained :=
  Monomial.retainWithBanks_existing monomial environment bounds banks cached below retained found

/-- A changed first power retains the whole unchanged old suffix, including its original dependent product owner. -/
example {arity : Nat} (environment : Fin (arity + 1) → CoherentNamed) (exponent : Nat) (remaining : Monomial arity)
    (bounds : Fin (arity + 1) → Nat) (banks : Monomial.PowerBanks environment bounds)
    (cached : Monomial.Caches environment)
    (below : ∀ index, (.cons exponent remaining : Monomial (arity + 1)).exponentAt index < bounds index)
    (missing : Monomial.findCache (.cons exponent remaining) cached = none)
    (suffix : Monomial.Denotation remaining (fun index => environment index.succ))
    (known : Monomial.findCache remaining (Monomial.tails cached) = some suffix) :
    (Monomial.retainWithBanks (.cons exponent remaining) environment bounds banks cached below).products.tail =
      suffix :=
  Monomial.retainWithBanks_suffix exponent remaining environment bounds banks cached below missing suffix known

/-- Both original input caches remain the ordered inventory of a prepared binary coefficient operation. -/
example {arity : Nat} (environment : Fin arity → CoherentNamed) (first second : CoherentNamed)
    (left : Gaussian.Normalized environment first) (right : Gaussian.Normalized environment second) :
    Gaussian.Normalized.pairedSources left right =
      [⟨left.form.terms, left.denotation⟩, ⟨right.form.terms, right.denotation⟩] := rfl

/-- A cancelled polynomial retains the input exponent bound, rather than losing its source predecessor bank. -/
example {arity : Nat} (environment : Fin arity → CoherentNamed) (original : CoherentNamed)
    (input : Gaussian.Normalized environment original) (index : Fin arity) :
    Terms.ExponentBelow index ((input.prepareSub input).bounds index) input.form.terms :=
  (input.prepareSub input).source_bounded input.denotation (Gaussian.Normalized.left_mem input input) index

/-- Negation uses the exact prepared original coefficient and complete output interpretation. -/
example {arity : Nat} (environment : Fin arity → CoherentNamed) (original : CoherentNamed)
    (input : Gaussian.Normalized environment original) :
    (input.neg (some input.prepareNeg)).denotation = input.prepareNeg.denotation :=
  Gaussian.Normalized.neg_cached_denotation input input.prepareNeg

/-- A product consumes the literal prepared output cache at both original numerical owners. -/
example {arity : Nat} (environment : Fin arity → CoherentNamed) (first second : CoherentNamed)
    (left : Gaussian.Normalized environment first) (right : Gaussian.Normalized environment second) :
    (left.mul right (some (left.prepareMul right))).denotation = (left.prepareMul right).denotation :=
  Gaussian.Normalized.mul_cached_denotation left right (left.prepareMul right)

/-- Natural powers retain the prepared output interpretation and its original source power parent. -/
example {arity : Nat} (environment : Fin arity → CoherentNamed) (original : CoherentNamed)
    (input : Gaussian.Normalized environment original) (exponent : Nat) :
    (input.pow exponent (some (input.preparePow exponent))).denotation = (input.preparePow exponent).1.denotation :=
  Gaussian.Normalized.pow_cached_denotation input exponent (input.preparePow exponent)

/-- Original source renaming keeps the entire supplied denotation without a new coefficient-product construction. -/
example {arity target : Nat} (environment : Fin arity → CoherentNamed) (original : CoherentNamed)
    (input : Gaussian.Normalized environment original) (destination : Fin target → CoherentNamed)
    (mapping : Fin arity → Fin target) :
    (input.prepareRename destination mapping).1.denotation = input.denotation := rfl

/-- Cache-aware renaming retains its exact target interpretation while the original channel remains its index. -/
example {arity target : Nat} (environment : Fin arity → CoherentNamed) (original : CoherentNamed)
    (input : Gaussian.Normalized environment original) (destination : Fin target → CoherentNamed)
    (mapping : Fin arity → Fin target)
    (equivalent : ∀ index, NamedEquivalent (environment index).name (destination (mapping index)).name) :
    (input.rename destination mapping equivalent (some (input.prepareRename destination mapping))).denotation =
      (input.prepareRename destination mapping).2.denotation :=
  Gaussian.Normalized.rename_cached_denotation input destination mapping equivalent
    (input.prepareRename destination mapping)

/-- A comparison of the actual cached product pays its own original starts and requested tolerance.

The returned index pair and tail bound belong to the new actual stored witness.
No equality with the canonical comparison procedure's payment is asserted.
-/
example {arity : Nat} (environment : Fin arity → CoherentNamed) (first second : CoherentNamed)
    (left : Gaussian.Normalized environment first) (right : Gaussian.Normalized environment second)
    (leftStart rightStart : Nat) (target : Rational) (positive : 0 < target) :
    let normalized := left.mul right (some (left.prepareMul right))
    let paid := normalized.equivalent.compare leftStart rightStart target positive
    leftStart ≤ paid.leftIndex ∧ rightStart ≤ paid.rightIndex := by
  let normalized := left.mul right (some (left.prepareMul right))
  let paid := normalized.equivalent.compare leftStart rightStart target positive
  exact ⟨paid.left_ge, paid.right_ge⟩

/-- Execute one actual retained comparison and check its paid floors and two computed sample bounds. -/
private def checkRequest {arity : Nat} {bindings : Fin arity → CoherentNamed} {original : CoherentNamed}
    (label : String) (normalized : Gaussian.Normalized bindings original) (expected : Canonical)
    (leftStart rightStart : Nat) : IO Unit := do
  let target : Rational := 1 / 16
  System.IO.println s!"cached polynomial {label}: request starts {leftStart}, {rightStart}"
  (← IO.getStdout).flush
  let paid := normalized.equivalent.compare leftStart rightStart target (by decide +kernel)
  unless leftStart ≤ paid.leftIndex ∧ rightStart ≤ paid.rightIndex do
    throw (IO.userError s!"cached polynomial {label}: comparison moved before an actual requested start")
  let left := Name.Sampling.approximation original.name
  let right := Name.Sampling.approximation normalized.channel.name
  let firstLeft := left.sample paid.leftIndex
  let firstRight := right.sample paid.rightIndex
  let firstResidual := normSq (firstLeft - firstRight)
  unless firstResidual < target ∧ firstLeft = expected ∧ firstRight = expected do
    throw (IO.userError s!"cached polynomial {label}: selected original/cache samples violate the requested bound")
  let laterLeft := left.sample (paid.leftIndex + 2)
  let laterRight := right.sample (paid.rightIndex + 3)
  let laterResidual := normSq (laterLeft - laterRight)
  unless laterResidual < target ∧ laterLeft = expected ∧ laterRight = expected do
    throw (IO.userError s!"cached polynomial {label}: later original/cache samples violate the retained tail bound")
  System.IO.println
    s!"cached polynomial {label}: paid indices {paid.leftIndex}, {paid.rightIndex}; sample bounds checked"
  (← IO.getStdout).flush

/-- Repeat actual finite comparison requests with distinct positive starts on the same retained operation cache. -/
private def checkRequests {arity : Nat} {bindings : Fin arity → CoherentNamed} {original : CoherentNamed}
    (label : String) (normalized : Gaussian.Normalized bindings original) (expected : Canonical) : IO Unit := do
  checkRequest label normalized expected 2 5
  checkRequest label normalized expected 37 41

/-- A constant original sample program retains a deliberately loose nonzero geometric allowance. -/
private def coarsePoint (point : Canonical) : GeometricApproximation :=
  { GeometricApproximation.exact point with
    errorScale := 1
    errorScale_nonneg := by decide
    later_close := by
      intro earlier later _
      rewrite [GeometricApproximation.exact_sample, GeometricApproximation.exact_sample,
        Purelib.Data.Gaussian.Basic.sub_self, normSq_zero]
      exact quarterRadius_nonneg (by decide) earlier }

/-- Retain the actual initial state and cached ball of that original coarse program. -/
private def cachedPoint (point : Canonical) :
    Prepared.Sum.Source (Geometric.Preparation.sampledChannel (coarsePoint point)) :=
  let channel := Geometric.Preparation.sampledChannel (coarsePoint point)
  let state := Refinement.State.initial channel
  Prepared.Sum.Source.ofBall channel (NamedEquivalent.refl channel.name) state
    ⟨point, 1, by decide⟩ (by
      apply Enclosure.Ball.ext
      · rfl
      · change (1 : Rational) = quarterRadius 1 0
        decide)

/-- Exercise cached sum separation and cancellation on actual original programs with observable refinement indices. -/
private def checkCachedSumPreparation (point : Canonical)
    (originalSeparated : (cachedPoint point).ball.Separated)
    (conjugateSeparated : (cachedPoint point).conj.ball.Separated) : IO Unit := do
  let cached := cachedPoint point
  let conjugated := cached.conj
  let sources := (conjugated, conjugated)
  let ball := conjugated.ball.add conjugated.ball
  have firstSeparated : conjugated.ball.Separated := conjugateSeparated
  have separated : ball.Separated := Enclosure.Ball.add_self_separated conjugated.ball firstSeparated
  let attempt := Prepared.Sum.inspect sources
  unless attempt.prepared.isSome do
    throw (IO.userError "the separated cached sum did not prepare its actual original channels")
  let prepared := Prepared.Sum.fromBalls sources ball rfl separated
  have _wholeSelected := Prepared.Sum.inspect_prepared sources separated
  let preparedIndices : Nat × Nat := prepared.denominator.name.state.source.source
  unless preparedIndices = (0, 0) ∧ attempt.sources.1.state.nextIndex = 0 ∧
      attempt.sources.2.state.nextIndex = 0 do
    throw (IO.userError "cached sum changed its starting state or source retry positions")
  let mixedSources := (cached, cached.conj.conj)
  let mixedBall := mixedSources.1.ball.add mixedSources.2.ball
  have mixedSeparated : mixedBall.Separated := by
    change (cached.ball.add cached.conj.conj.ball).Separated
    rewrite [Prepared.Sum.Source.conj_conj_ball]
    apply Enclosure.Ball.add_self_separated
    exact originalSeparated
  let mixed := Prepared.Sum.inspect mixedSources
  let mixedPrepared := Prepared.Sum.fromBalls mixedSources mixedBall rfl mixedSeparated
  have _wholeMixed := Prepared.Sum.inspect_prepared mixedSources mixedSeparated
  let mixedIndices : Nat × Nat := mixedPrepared.denominator.name.state.source.source
  unless mixed.prepared.isSome ∧ mixedIndices = (0, 0) ∧
      mixed.sources.1.ball = cached.ball ∧ mixed.sources.2.ball = cached.ball do
    throw (IO.userError "cached sum replaced a double-conjugate source or starting state")
  let state := Prepared.Sum.pairedState sources
  let actual : Enclosure.Ball.Apart
      ((CoherentNamed.add conjugated.presentation conjugated.presentation).name.process.ball state.source) :=
    (Prepared.Sum.paired_readback sources) ▸ Enclosure.Residual.apartOfCenter ball separated
  let evidence := Process.Apart.Based.possibleApartOfBall
    (CoherentNamed.add conjugated.presentation conjugated.presentation).name.process state.source actual
  let originalDefault := Prepared.ofEvidence state evidence none
  let defaultIndices : Nat × Nat := originalDefault.denominator.name.state.source.source
  unless defaultIndices.1 > 0 ∧ defaultIndices.2 > 0 do
    throw (IO.userError "the comparison control no longer exercises the original starting refinement")
  let opposite := cachedPoint (-point)
  unless cached.ball.Separated ∧ opposite.ball.Separated do
    throw (IO.userError "the cancelling-sum inputs lost their separate cached nonzero margins")
  let cancellation := Prepared.Sum.inspect (cached, opposite)
  unless cancellation.prepared.isNone ∧ cancellation.ball.center = 0 ∧ cancellation.ball.radiusSq = 4 ∧
      cancellation.sources.1.ball.center = point ∧ cancellation.sources.2.ball.center = -point do
    throw (IO.userError "cancelling sum lost its finite inconclusive result or an original input")
  System.IO.println "cached sum: cached states retained; default refinement distinguished; cancellation inconclusive"

/-- Execute cached finite polynomial operations at the same actual Gaussian-rational input owners.

Original atom normalizations retain both input channels and their actual
power/product/suffix caches. Every operation receives its once-prepared cache,
and its actual executable comparison is requested at two distinct nonzero
start pairs. Cancellation retains its original source exponent bank even
though its output is zero. Both literal-channel and purely operational
renaming paths retain their original and target variable owners. The dense
Horner case consumes its retained accumulator spine and once-prepared sparse
coefficient interpretation through the original dense bridge. Conjugation and
double conjugation use a nonreal variable and nonreal coefficients, retaining
their actual successive target channels and interpretation caches.
-/
public def checkCachedComparisons : IO Unit := do
  TestPurelib.Polynomial.GaussianRootCandidates.check
  checkCachedSumPreparation ⟨2, 1⟩
    (by change (2 : Rational) * 1 < normSq (⟨2, 1⟩ : Canonical); decide)
    (by change (2 : Rational) * 1 < normSq (⟨2, -1⟩ : Canonical); decide)
  let two := Coherence.exact (2 : Canonical)
  let three := Coherence.exact (3 : Canonical)
  let bindings : Fin 2 → CoherentNamed := Data.Fin.cases two (fun _ => three)
  let left := Gaussian.Normalized.atom bindings (0 : Fin 2)
  let right := Gaussian.Normalized.atom bindings (1 : Fin 2)
  let negativeCache := left.prepareNeg
  let negative := left.neg (some negativeCache)
  checkRequests "neg" negative (-2)
  let sumCache := left.prepareAdd right
  let sum := left.add right (some sumCache)
  checkRequests "add" sum 5
  let differenceCache := left.prepareSub right
  let difference := left.sub right (some differenceCache)
  checkRequests "sub" difference (-1)
  let productCache := left.prepareMul right
  let product := left.mul right (some productCache)
  checkRequests "mul" product 6
  let cubeCache := left.preparePow 3
  let cube := left.pow 3 (some cubeCache)
  checkRequests "pow" cube 8
  let cancellationCache := cube.prepareSub cube
  let cancellation := cube.sub cube (some cancellationCache)
  let sourceBound := Terms.exponentBound (0 : Fin 2) cube.form.terms
  let outputBound := Terms.exponentBound (0 : Fin 2) cancellationCache.form.terms
  unless cancellation.form.terms.isEmpty ∧ cancellationCache.bounds 0 ≥ sourceBound ∧ sourceBound > outputBound do
    throw (IO.userError "cached polynomial cancellation discarded its actual original source exponent ceiling")
  unless (Monomial.findPower (bindings 0) 3 (cube.denotation.sums.powersAt 0)).isSome ∧
      (Monomial.findPower (bindings 0) 3 (cancellationCache.banks.get 0).val).isSome do
    throw (IO.userError "cached polynomial cancellation lost its actual retained source power bank")
  checkRequests "cancellation" cancellation 0
  let destination : Fin 2 → CoherentNamed := Data.Fin.cases three (fun _ => two)
  let mapping : Fin 2 → Fin 2 := Data.Fin.cases (1 : Fin 2) (fun _ => 0)
  have same : ∀ index, bindings index = destination (mapping index) := by
    intro index
    refine Data.Fin.cases_induction ?_ ?_ index
    · rfl
    · intro _
      rfl
  let equivalent : ∀ index, NamedEquivalent (bindings index).name (destination (mapping index)).name := by
    intro index
    rewrite [same index]
    exact NamedEquivalent.refl _
  let renamedCache := sum.prepareRename destination mapping (some ⟨same⟩)
  let renamed := sum.rename destination mapping equivalent (some renamedCache)
  checkRequests "rename literal channels" renamed 5
  let shifted : Fin 2 → CoherentNamed := fun index => CoherentNamed.add (destination index) (Coherence.exact 0)
  let shiftedEquivalent : ∀ index, NamedEquivalent (bindings index).name (shifted (mapping index)).name :=
    fun index => (equivalent index).trans ((Add.coherentAdd_zero_right (destination (mapping index))).symm)
  let shiftedCache := sum.prepareRename shifted mapping
  let shiftedResult := sum.rename shifted mapping shiftedEquivalent (some shiftedCache)
  checkRequests "rename operational channels" shiftedResult 5
  let densePolynomial : CoefficientPolynomial := ⟨[1, 2, 3]⟩
  let denseBindings : Fin 1 → CoherentNamed := fun _ => two
  let numerical := Horner.retain two (Coherence.exact 0) densePolynomial.coeffs
  let numericalOutput := numerical.output two (Coherence.exact 0) densePolynomial.coeffs
  let denseForm := Sparse.ofDenseAt (0 : Fin 1) densePolynomial
  let denseCache := Terms.Denotation.prepare denseBindings [] denseForm
  let denseNormalized := Gaussian.Normalized.ofDenseAt denseBindings (0 : Fin 1) densePolynomial numerical
    (original := numericalOutput) (NamedEquivalent.refl numericalOutput.name) denseCache
  checkRequests "retained dense Horner" denseNormalized 11
  let complexBindings : Fin 1 → CoherentNamed := fun _ => Coherence.exact (⟨2, 3⟩ : Canonical)
  let complexAtom := Gaussian.Normalized.atom complexBindings (0 : Fin 1)
  let complexCoefficient := Gaussian.Normalized.constant complexBindings (⟨1, 2⟩ : Canonical)
  let complexProductCache := complexCoefficient.prepareMul complexAtom
  let complexProduct := complexCoefficient.mul complexAtom (some complexProductCache)
  let complexOffset := Gaussian.Normalized.constant complexBindings (⟨3, -1⟩ : Canonical)
  let complexSumCache := complexProduct.prepareAdd complexOffset
  let complexSum := complexProduct.add complexOffset (some complexSumCache)
  let conjugatedCache := complexSum.prepareConj
  let conjugated := complexSum.conj conjugatedCache
  checkRequests "conjugated nonreal coefficients and variable" conjugated ⟨-1, -6⟩
  let twiceConjugatedCache := conjugated.prepareConj
  let twiceConjugated := conjugated.conj twiceConjugatedCache
  checkRequests "twice conjugated actual channels" twiceConjugated ⟨-1, 6⟩
  System.IO.println "cached polynomial comparisons: original owners, source banks and actual finite payments checked"
  (← IO.getStdout).flush

/-- Arbitrary original Horner caches retain their whole original numerical output, including process and state. -/
example (input initial : CoherentNamed) (coefficients : List Canonical)
    (cached : Horner.Accumulations input initial coefficients) :
    cached.output input initial coefficients =
      Horner.horner input initial coefficients :=
  cached.output_eq input initial coefficients

/-- A retained Horner bridge preserves the complete actual comparison and its original paid request. -/
example (polynomial : CoefficientPolynomial)
    (input : CoherentNamed) (source : GeometricApproximation)
    (sourceEq : NamedEquivalent input.name source.toApproximation.toNamed)
    (cached : Horner.Accumulations input
      (Coherence.exact 0) polynomial.coeffs)
    (leftStart rightStart : Nat) (target : Rational) (positive : 0 < target) :
    (CoherentEvaluation.evaluate_agrees polynomial input source sourceEq
      (some cached)).compare leftStart rightStart target positive =
    (CoherentEvaluation.evaluate_agrees polynomial input source sourceEq).compare
      leftStart rightStart target positive :=
  congrArg (fun relation => relation.compare leftStart rightStart target positive)
    (CoherentEvaluation.evaluate_agrees_cached_eq_default
      polynomial input source sourceEq cached)

/-- An inverse output is normalized from its actual stored inverse polynomial at the original generator position. -/
example {arity : Nat} (bindings : Fin arity → CoherentNamed) (original : CoherentNamed)
    (input : Gaussian.Normalized bindings original) (inverse : Gaussian.Normalized.Inverse input) :
    inverse.normalizeOutput.form = Sparse.ofDenseAt inverse.index inverse.inversePolynomial :=
  inverse.normalizeOutput_form

/-- A demanded compound guard retains its exact original ordered slot run. -/
example {arity : Nat} (bindings : Fin arity → CoherentNamed) (original : CoherentNamed)
    (input : Gaussian.Normalized bindings original)
    (generators : (index : Fin arity) → Option
      (Algebraic.Sidecar (bindings index))) :
    (input.inverseCheck generators).val = input.inverseRun generators (List.ofFn (fun index : Fin arity => index)) :=
  input.inverseCheck_result generators

/-- Conjugation's actual source preparation retains the whole arbitrary original denotation. -/
example {arity : Nat} (bindings : Fin arity → CoherentNamed) (original : CoherentNamed)
    (input : Gaussian.Normalized bindings original) :
    input.prepareConj.before.denotation = input.denotation :=
  Gaussian.Normalized.prepareConj_before_denotation input

/-- A supplied conjugation construction contributes its identical complete target coefficient and channel caches. -/
example {arity : Nat} (bindings : Fin arity → CoherentNamed) (original : CoherentNamed)
    (input : Gaussian.Normalized bindings original) (cached : Gaussian.Normalized.ConjInputs input) :
    (input.conj cached).denotation = cached.after.denotation :=
  Gaussian.Normalized.conj_denotation input cached

/-- Actual conjugated variable owners retain their original finite positions and explicit construction identities. -/
example {arity : Nat} (bindings : Fin arity → CoherentNamed) (original : CoherentNamed)
    (input : Gaussian.Normalized bindings original) (cached : Gaussian.Normalized.ConjInputs input)
    (index : Fin arity) :
    cached.channels index = CoherentNamed.conj (bindings index) := cached.channels_eq index

/-- The actual conjugation relation pays indices above both actual caller starts. -/
example {arity : Nat} (bindings : Fin arity → CoherentNamed) (original : CoherentNamed)
    (input : Gaussian.Normalized bindings original) (cached : Gaussian.Normalized.ConjInputs input)
    (leftStart rightStart : Nat) (target : Purelib.Data.Rat.Fraction.Rational) (positive : 0 < target) :
    let paid := (input.conj cached).equivalent.compare leftStart rightStart target positive
    leftStart ≤ paid.leftIndex ∧ rightStart ≤ paid.rightIndex := by
  let paid := (input.conj cached).equivalent.compare leftStart rightStart target positive
  exact ⟨paid.left_ge, paid.right_ge⟩

/-- Double conjugation keeps both actual channel owners and supplies their operational relation. -/
example (channel : CoherentNamed) :
    NamedEquivalent (CoherentNamed.conj (CoherentNamed.conj channel)).name channel.name :=
  CoherentNamed.conj_conj channel

end TestPurelib.Polynomial.MultivariateDenotation
