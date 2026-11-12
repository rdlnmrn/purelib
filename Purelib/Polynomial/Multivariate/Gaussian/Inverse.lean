module

import Purelib.Polynomial.Approximation.CoherentEvaluation
import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner
public import Purelib.Polynomial.Multivariate.Gaussian.Dense
import Purelib.Polynomial.Multivariate.Gaussian.Normalization
import Purelib.Polynomial.Multivariate.Gaussian.Denotation
import Purelib.Polynomial.Multivariate.PowerReduction
public import Purelib.Approximation.Gaussian.Provenance.Algebraic
public import Purelib.Polynomial.Multivariate.Gaussian.PowerCoordinates
public import Purelib.Polynomial.Dense.Gaussian.Coprime.Decision
public import Purelib.Polynomial.Approximation.CoherentEvaluation.Division
public import Purelib.Approximation.Gaussian.Division.Prepared.Factor
public import Purelib.Approximation.Gaussian.Division.Prepared.Sum
public import Purelib.Approximation.Gaussian.Geometric.Preparation
import Purelib.Polynomial.Approximation.Evaluation
public import Purelib.Approximation.Gaussian.Division.Prepared.Quotient.Inverse
import Purelib.Polynomial.Dense.Gaussian.Degree
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Gaussian.Field
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Retained inverses in an original polynomial generator

The same original normalization, bounded power coordinates and completed
Euclidean record yield an operational product with one. The numerical
preparation consumes a supplied actual original-channel preparation or the
actual geometric denominator head and, if needed, one retained twice-advanced
observation before its original unit-product fallback. Reciprocal-output preparation consumes the same shared procedure.
This construction computes no composite annihilator or new Sidecar.
-/

public section
namespace Purelib.Polynomial.Multivariate.Gaussian.Normalized

open Purelib.Data.Gaussian.Basic renaming Canonical -> Coefficient
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Approximation.Gaussian.Division (Prepared)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Coprime.Basic (CoprimeCertificate)
open Purelib.Polynomial.Dense.Gaussian.Coprime
open Purelib.Polynomial.Approximation
open Purelib.Polynomial.Approximation.Gaussian.Evaluation

variable {arity : Nat} {bindings : Fin arity → CoherentNamed} {channel : CoherentNamed}

namespace Inverse

/-- Consume one actual initial denominator observation or retain the original factor fallback.

A separated head returns its same stored preparation. Current inconclusivity
pays the original unit-product comparison once and stores its actual factor
observation with the resulting preparation; it asserts no operational zero.
-/
@[expose] def prepare {source : GeometricApproximation} {channel : CoherentNamed}
    {equivalent : NamedEquivalent channel.name source.toApproximation.toNamed}
    {state : Geometric.Preparation.State source}
    (initial : Geometric.Preparation.Observation source channel equivalent state) (inverse : CoherentNamed)
    (product : NamedEquivalent (CoherentNamed.mul channel inverse).name (Coherence.exact 1).name) :
    Option (Prepared.Factor.Observation channel inverse 1) × Prepared channel :=
  match initial.outcome with
  | .prepared _ result _ => (none, result)
  | .inconclusive _ =>
      let observation := Prepared.Factor.observe channel inverse 1 (by decide) product
      (some observation, observation.prepare)

/-- A successful original head preparation bypasses factor comparison and returns that literal stored result. -/
theorem prepare_prepared {source : GeometricApproximation} {channel : CoherentNamed}
    {equivalent : NamedEquivalent channel.name source.toApproximation.toNamed}
    {state : Geometric.Preparation.State source}
    (initial : Geometric.Preparation.Observation source channel equivalent state) (inverse : CoherentNamed)
    (product : NamedEquivalent (CoherentNamed.mul channel inverse).name (Coherence.exact 1).name)
    (separated : Geometric.Preparation.Separated initial.ball) (result : Prepared channel)
    (computed : result = Geometric.Preparation.fromBall source channel equivalent initial.state initial.ball
      initial.readback separated)
    (selected : initial.outcome = .prepared separated result computed) :
    prepare initial inverse product = (none, result) := by
  unfold prepare
  rewrite [selected]
  rfl

/-- An inconclusive original head retains the complete original factor observation and preparation. -/
theorem prepare_inconclusive {source : GeometricApproximation} {channel : CoherentNamed}
    {equivalent : NamedEquivalent channel.name source.toApproximation.toNamed}
    {state : Geometric.Preparation.State source}
    (initial : Geometric.Preparation.Observation source channel equivalent state) (inverse : CoherentNamed)
    (product : NamedEquivalent (CoherentNamed.mul channel inverse).name (Coherence.exact 1).name)
    (failed : ¬ Geometric.Preparation.Separated initial.ball)
    (selected : initial.outcome = .inconclusive failed) :
    prepare initial inverse product =
      (let observation := Prepared.Factor.observe channel inverse 1 (by decide) product
       (some observation, observation.prepare)) := by
  unfold prepare
  rewrite [selected]
  rfl

/-- One original bounded continuation of a failed geometric observation, with exact state and inspection origins. -/
abbrev Followup {source : GeometricApproximation} {observed : CoherentNamed}
    {equivalent : NamedEquivalent observed.name source.toApproximation.toNamed}
    {state : Geometric.Preparation.State source}
    (initial : Geometric.Preparation.Observation source observed equivalent state) :=
  (state : {actual : Geometric.Preparation.State source // actual = initial.state.advance.advance}) ×
    {result : Geometric.Preparation.Observation source observed equivalent state.val //
      result = Geometric.Preparation.inspectAt source observed equivalent state.val}

/-- Try the retained initial head, then two original canonical requests before the same factor fallback.

A failed first sufficient test remains retained. The second observation starts
from the actual twice advanced original state, including its original retry
counter. Failure of both finite tests invokes the unchanged factor observation
once; no failed head is classified as an operational zero. A supplied actual
preparation is consumed before either head or factor request.
-/
@[expose] def prepareAfter {source : GeometricApproximation} {observed : CoherentNamed}
    {equivalent : NamedEquivalent observed.name source.toApproximation.toNamed}
    {state : Geometric.Preparation.State source}
    (initial : Geometric.Preparation.Observation source observed equivalent state) (inverse : CoherentNamed)
    (product : NamedEquivalent (CoherentNamed.mul observed inverse).name (Coherence.exact 1).name)
    (supplied : Option (Prepared observed) := none) :
    Option (Followup initial) × (Option (Prepared.Factor.Observation observed inverse 1) × Prepared observed) :=
  match supplied with
  | some prepared => (none, (none, prepared))
  | none =>
      match initial.outcome with
      | .prepared _ _ _ => (none, prepare initial inverse product)
      | .inconclusive _ =>
          let state := initial.state.advance.advance
          let later := Geometric.Preparation.inspectAt source observed equivalent state
          let result := prepare later inverse product
          (some ⟨⟨state, rfl⟩, ⟨later, rfl⟩⟩, result)

/-- A supplied original-channel preparation is retained literally without a follow-up or factor payment. -/
theorem prepareAfter_supplied {source : GeometricApproximation} {observed : CoherentNamed}
    {equivalent : NamedEquivalent observed.name source.toApproximation.toNamed}
    {state : Geometric.Preparation.State source}
    (initial : Geometric.Preparation.Observation source observed equivalent state) (inverse : CoherentNamed)
    (product : NamedEquivalent (CoherentNamed.mul observed inverse).name (Coherence.exact 1).name)
    (prepared : Prepared observed) :
    prepareAfter initial inverse product (some prepared) = (none, (none, prepared)) := rfl

/-- An absent supplied preparation preserves the entire original two-head/factor computation. -/
theorem prepareAfter_none {source : GeometricApproximation} {observed : CoherentNamed}
    {equivalent : NamedEquivalent observed.name source.toApproximation.toNamed}
    {state : Geometric.Preparation.State source}
    (initial : Geometric.Preparation.Observation source observed equivalent state) (inverse : CoherentNamed)
    (product : NamedEquivalent (CoherentNamed.mul observed inverse).name (Coherence.exact 1).name) :
    prepareAfter initial inverse product none =
      (match initial.outcome with
       | .prepared _ _ _ => (none, prepare initial inverse product)
       | .inconclusive _ =>
           let state := initial.state.advance.advance
           let later := Geometric.Preparation.inspectAt source observed equivalent state
           let result := prepare later inverse product
           (some ⟨⟨state, rfl⟩, ⟨later, rfl⟩⟩, result)) := rfl

/-- A separated initial head retains no later observation and returns its actual stored preparation. -/
theorem prepareAfter_prepared {source : GeometricApproximation} {observed : CoherentNamed}
    {equivalent : NamedEquivalent observed.name source.toApproximation.toNamed}
    {state : Geometric.Preparation.State source}
    (initial : Geometric.Preparation.Observation source observed equivalent state) (inverse : CoherentNamed)
    (product : NamedEquivalent (CoherentNamed.mul observed inverse).name (Coherence.exact 1).name)
    (separated : Geometric.Preparation.Separated initial.ball) (result : Prepared observed)
    (computed : result = Geometric.Preparation.fromBall source observed equivalent initial.state initial.ball
      initial.readback separated)
    (selected : initial.outcome = .prepared separated result computed) :
    prepareAfter initial inverse product = (none, (none, result)) := by
  unfold prepareAfter
  rewrite [selected, prepare_prepared initial inverse product separated result computed selected]
  rfl

/-- Initial inconclusivity retains its exact original follow-up state and shared preparation result. -/
theorem prepareAfter_inconclusive {source : GeometricApproximation} {observed : CoherentNamed}
    {equivalent : NamedEquivalent observed.name source.toApproximation.toNamed}
    {state : Geometric.Preparation.State source}
    (initial : Geometric.Preparation.Observation source observed equivalent state) (inverse : CoherentNamed)
    (product : NamedEquivalent (CoherentNamed.mul observed inverse).name (Coherence.exact 1).name)
    (failed : ¬ Geometric.Preparation.Separated initial.ball)
    (selected : initial.outcome = .inconclusive failed) :
    prepareAfter initial inverse product =
      (let state := initial.state.advance.advance
       let later := Geometric.Preparation.inspectAt source observed equivalent state
       (some ⟨⟨state, rfl⟩, ⟨later, rfl⟩⟩, prepare later inverse product)) := by
  unfold prepareAfter
  rewrite [selected]
  rfl

/-- A retained actual follow-up determines the same complete lower-level preparation without another branch scan. -/
theorem prepareAfter_result {source : GeometricApproximation} {observed : CoherentNamed}
    {equivalent : NamedEquivalent observed.name source.toApproximation.toNamed}
    {state : Geometric.Preparation.State source}
    (initial : Geometric.Preparation.Observation source observed equivalent state) (inverse : CoherentNamed)
    (product : NamedEquivalent (CoherentNamed.mul observed inverse).name (Coherence.exact 1).name)
    (later : Followup initial) (supplied : Option (Prepared observed))
    (found : (prepareAfter initial inverse product supplied).1 = some later) :
    (prepareAfter initial inverse product supplied).2 = prepare later.2.val inverse product := by
  cases supplied with
  | some prepared => cases found
  | none =>
      cases selected : initial.outcome with
      | prepared separated result computed =>
          unfold prepareAfter at found ⊢
          rewrite [selected] at found
          change (none : Option (Followup initial)) = some later at found
          cases found
      | inconclusive failed =>
          unfold prepareAfter at found ⊢
          rewrite [selected] at found ⊢
          let retainedState := initial.state.advance.advance
          let observation := Geometric.Preparation.inspectAt source observed equivalent retainedState
          let retained : Followup initial := ⟨⟨retainedState, rfl⟩, ⟨observation, rfl⟩⟩
          have equal : retained = later := Option.some.inj found
          exact congrArg (fun actual : Followup initial => prepare actual.2.val inverse product) equal

end Inverse

set_option genInjectivity false in
/-- An exact inverse certificate retaining the original normalization and one actual selected generator.

The same bounded entries determine the stored dense polynomial. Its original
Euclidean result, normalized right coefficient, actual product comparison and
geometric observations or fallback factor observation are retained once and
consumed by the output preparation.
-/
structure Inverse (original : Gaussian.Normalized bindings channel) where
  /-- The entire actual original normalization, including all power and suffix caches. -/
  input : Gaussian.Normalized bindings channel
  /-- The retained normalization is the original input owner. -/
  input_eq : input = original
  /-- The actual original bounded generator coordinate. -/
  index : Fin arity
  /-- The original generator Sidecar with its unchanged annihilator and residual sampler. -/
  generator : Algebraic.Sidecar (bindings index)
  /-- The actual computed finite power bound. -/
  degree : Nat
  /-- The bound is computed from these same original surviving terms. -/
  degree_eq : degree = Terms.exponentBound index input.form.terms
  /-- The complete actual coordinate inspection at this original request. -/
  check : Sparse.PowerCheck input.form index degree
  /-- The retained check is the original finite procedure. -/
  check_eq : check = input.form.inspectPowers index degree
  /-- The bounded original coefficients retained by its successful branch. -/
  coordinates : Sparse.PowerCoordinates input.form index degree
  /-- These are the actual same cached coordinates returned by that check. -/
  coordinates_eq : check.originalOutcome = .coordinates coordinates
  /-- The once computed dense polynomial of those same ordered entries. -/
  polynomial : CoefficientPolynomial
  /-- The dense cache is built from the actual original coordinate entries. -/
  polynomial_eq : polynomial = coordinates.dense
  /-- The actual selected-generator powers and missing predecessor powers retained for comparison. -/
  powers : Monomial.PowerPrefix (bindings index) degree
  /-- The same original denotation supplied every pre-existing power to this actual prefix builder. -/
  powers_eq : powers = Monomial.retainPowerPrefix (bindings index) (input.denotation.sums.powersAt index) degree
  /-- The actual original channel compares to this same retained dense evaluation. -/
  equivalent : NamedEquivalent channel.name (Horner.polynomialEval polynomial (bindings index)).name
  /-- The actual geometric denominator source evaluates the same retained dense coefficients and root samples. -/
  source : GeometricApproximation
  /-- The denominator source is the original cached polynomial evaluation at the unchanged generator source. -/
  source_eq : source = Evaluation.evaluate polynomial generator.residual.source
  /-- The original denominator agrees with this same retained geometric sample program. -/
  sourceEquivalent : NamedEquivalent channel.name source.toApproximation.toNamed
  /-- This is the same stored coordinate comparison followed by the original polynomial sample bridge. -/
  sourceEquivalent_eq : HEq sourceEquivalent
    (equivalent.trans (CoherentEvaluation.evaluate_agrees polynomial (bindings index)
      generator.residual.source generator.residual.equivalent))
  /-- The actual once inspected denominator head, including its ball and typed sufficient-test outcome. -/
  initial : Geometric.Preparation.Observation source channel sourceEquivalent
  /-- The head was computed from that same source, channel and relation without another numerical scan. -/
  initial_eq : initial = Geometric.Preparation.inspectInitial source channel sourceEquivalent
  /-- The nonzero constant-GCD certificate retaining the actual original Euclidean record. -/
  coprime : CoprimeCertificate generator.polynomial polynomial
  /-- The scaled original right Bezout coefficient computed once. -/
  inversePolynomial : CoefficientPolynomial
  /-- The inverse coefficient cache consumes this same retained Euclidean result. -/
  inversePolynomial_eq : inversePolynomial = coprime.right
  /-- The actual original Horner coefficient/accumulator execution retained once for the inverse polynomial. -/
  inverseHorner : Horner.Accumulations (bindings index) (Coherence.exact 0) inversePolynomial.coeffs
  /-- This is the actual original finite Horner retention procedure on those same cached coefficients. -/
  inverseHorner_eq : inverseHorner = Horner.retain (bindings index) (Coherence.exact 0) inversePolynomial.coeffs
  /-- The actual numerical inverse-generator evaluation computed once. -/
  inverse : CoherentNamed
  /-- The numerical cache evaluates this same stored inverse polynomial at the unchanged generator. -/
  inverse_eq : inverse = Horner.polynomialEval inversePolynomial (bindings index)
  /-- The numerical inverse is the exact final accumulator of that retained original execution. -/
  inverse_cache_eq : inverse = inverseHorner.output (bindings index) (Coherence.exact 0) inversePolynomial.coeffs
  /-- The operational unit product uses the original channel and this exact inverse cache. -/
  product : NamedEquivalent (CoherentNamed.mul channel inverse).name (Coherence.exact 1).name
  /-- The actual optional original-channel preparation supplied to this demanded inverse guard. -/
  request : Option (Prepared channel)
  /-- The actual twice-advanced observation, present only for an unprepared inconclusive original first head. -/
  followup : Option (Inverse.Followup initial)
  /-- The actual original factor observation exists only when both retained geometric tests were inconclusive. -/
  observation : Option (Prepared.Factor.Observation channel inverse 1)
  /-- The actual supplied preparation or the result of the retained geometric heads and same factor observation. -/
  prepared : Prepared channel
  /-- All stored outputs are the complete result of the same request-aware original preparation procedure. -/
  preparation_eq : (followup, (observation, prepared)) = Inverse.prepareAfter initial inverse product request
  /-- The actual prepared reciprocal output channel, computed once. -/
  output : CoherentNamed
  /-- The output cache is the original numerical quotient using this same retained preparation. -/
  output_eq : output = prepared.quotient (Coherence.exact 1)

constructive_injectivity Inverse

namespace Inverse

/-- Build a retained inverse from one successful original coordinate check and its cached constant-GCD certificate. -/
@[expose] def build (input : Gaussian.Normalized bindings channel) (index : Fin arity)
    (generator : Algebraic.Sidecar (bindings index)) (degree : Nat)
    (degreeEq : degree = Terms.exponentBound index input.form.terms)
    (check : Sparse.PowerCheck input.form index degree)
    (checkEq : check = input.form.inspectPowers index degree)
    (coordinates : Sparse.PowerCoordinates input.form index degree)
    (coordinatesEq : check.originalOutcome = .coordinates coordinates)
    (polynomial : CoefficientPolynomial) (polynomialEq : polynomial = coordinates.dense)
    (coprime : CoprimeCertificate generator.polynomial polynomial)
    (supplied : Option (Prepared channel) := none) : Inverse input := by
  let inversePolynomial := coprime.right
  let inverseHorner := Horner.retain (bindings index) (Coherence.exact 0) inversePolynomial.coeffs
  let inverse := inverseHorner.output (bindings index) (Coherence.exact 0) inversePolynomial.coeffs
  let powers := Monomial.retainPowerPrefix (bindings index) (input.denotation.sums.powersAt index) degree
  have sameDense := coordinates.dense_equivalent bindings generator.residual.source generator.residual.equivalent
    input.denotation powers
  rewrite [← polynomialEq, ← input.denotation_eq] at sameDense
  let equivalent := input.equivalent.trans sameDense
  have constant : coprime.result.gcd = DensePolynomial.constant coprime.unit := coprime.result_gcd_eq_constant
  have inverseEval : ∀ point : Coefficient,
      inversePolynomial.eval point = coprime.unit⁻¹ * coprime.result.right.eval point := by
    intro point
    exact (congrArg (fun value : CoefficientPolynomial => value.eval point) coprime.right_eq).trans
      (DensePolynomial.eval_scale coprime.unit⁻¹ coprime.result.right point)
  let denseProduct := CoherentEvaluation.bezout_inverse_agrees coprime.result coprime.unit constant
    coprime.unit_ne_zero inversePolynomial inverseEval (bindings index) generator.residual.source
    generator.residual.equivalent generator.equation inverse
    (inverseHorner.output_eq (bindings index) (Coherence.exact 0) inversePolynomial.coeffs) (some inverseHorner)
  let product := (Product.Congruence.coherentMul_respects channel
    (Horner.polynomialEval polynomial (bindings index)) inverse inverse equivalent (NamedEquivalent.refl _)).trans
      denseProduct
  let source := Evaluation.evaluate polynomial generator.residual.source
  let sourceEquivalent := equivalent.trans (CoherentEvaluation.evaluate_agrees polynomial
    (bindings index) generator.residual.source generator.residual.equivalent)
  let initial := Geometric.Preparation.inspectInitial source channel sourceEquivalent
  let preparation := Inverse.prepareAfter initial inverse product supplied
  let followup := preparation.1
  let observation := preparation.2.1
  let prepared := preparation.2.2
  let output := prepared.quotient (Coherence.exact 1)
  exact
    { input := input
      input_eq := rfl
      index := index
      generator := generator
      degree := degree
      degree_eq := degreeEq
      check := check
      check_eq := checkEq
      coordinates := coordinates
      coordinates_eq := coordinatesEq
      polynomial := polynomial
      polynomial_eq := polynomialEq
      powers := powers
      powers_eq := rfl
      equivalent := equivalent
      source := source
      source_eq := rfl
      sourceEquivalent := sourceEquivalent
      sourceEquivalent_eq := HEq.rfl
      initial := initial
      initial_eq := rfl
      coprime := coprime
      inversePolynomial := inversePolynomial
      inversePolynomial_eq := rfl
      inverseHorner := inverseHorner
      inverseHorner_eq := rfl
      inverse := inverse
      inverse_eq := inverseHorner.output_eq (bindings index) (Coherence.exact 0) inversePolynomial.coeffs
      inverse_cache_eq := rfl
      product := product
      request := supplied
      followup := followup
      observation := observation
      prepared := prepared
      preparation_eq := rfl
      output := output
      output_eq := rfl }

/-- An absent supplied preparation retains the whole original inverse record and every original cached computation. -/
theorem build_none (input : Gaussian.Normalized bindings channel) (index : Fin arity)
    (generator : Algebraic.Sidecar (bindings index)) (degree : Nat)
    (degreeEq : degree = Terms.exponentBound index input.form.terms)
    (check : Sparse.PowerCheck input.form index degree)
    (checkEq : check = input.form.inspectPowers index degree)
    (coordinates : Sparse.PowerCoordinates input.form index degree)
    (coordinatesEq : check.originalOutcome = .coordinates coordinates)
    (polynomial : CoefficientPolynomial) (polynomialEq : polynomial = coordinates.dense)
    (coprime : CoprimeCertificate generator.polynomial polynomial) :
    build input index generator degree degreeEq check checkEq coordinates coordinatesEq polynomial polynomialEq
      coprime none =
    (by
      let inversePolynomial := coprime.right
      let inverseHorner := Horner.retain (bindings index) (Coherence.exact 0) inversePolynomial.coeffs
      let inverse := inverseHorner.output (bindings index) (Coherence.exact 0) inversePolynomial.coeffs
      let powers := Monomial.retainPowerPrefix (bindings index) (input.denotation.sums.powersAt index) degree
      have sameDense := coordinates.dense_equivalent bindings generator.residual.source generator.residual.equivalent
        input.denotation powers
      rewrite [← polynomialEq, ← input.denotation_eq] at sameDense
      let equivalent := input.equivalent.trans sameDense
      have constant : coprime.result.gcd = DensePolynomial.constant coprime.unit := coprime.result_gcd_eq_constant
      have inverseEval : ∀ point : Coefficient,
          inversePolynomial.eval point = coprime.unit⁻¹ * coprime.result.right.eval point := by
        intro point
        exact (congrArg (fun value : CoefficientPolynomial => value.eval point) coprime.right_eq).trans
          (DensePolynomial.eval_scale coprime.unit⁻¹ coprime.result.right point)
      let denseProduct := CoherentEvaluation.bezout_inverse_agrees coprime.result coprime.unit constant
        coprime.unit_ne_zero inversePolynomial inverseEval (bindings index) generator.residual.source
        generator.residual.equivalent generator.equation inverse
        (inverseHorner.output_eq (bindings index) (Coherence.exact 0) inversePolynomial.coeffs) (some inverseHorner)
      let product := (Product.Congruence.coherentMul_respects channel
        (Horner.polynomialEval polynomial (bindings index)) inverse inverse equivalent (NamedEquivalent.refl _)).trans
          denseProduct
      let source := Evaluation.evaluate polynomial generator.residual.source
      let sourceEquivalent := equivalent.trans (CoherentEvaluation.evaluate_agrees polynomial
        (bindings index) generator.residual.source generator.residual.equivalent)
      let initial := Geometric.Preparation.inspectInitial source channel sourceEquivalent
      let preparation := Inverse.prepareAfter initial inverse product
      let followup := preparation.1
      let observation := preparation.2.1
      let prepared := preparation.2.2
      let output := prepared.quotient (Coherence.exact 1)
      exact
        { input := input
          input_eq := rfl
          index := index
          generator := generator
          degree := degree
          degree_eq := degreeEq
          check := check
          check_eq := checkEq
          coordinates := coordinates
          coordinates_eq := coordinatesEq
          polynomial := polynomial
          polynomial_eq := polynomialEq
          powers := powers
          powers_eq := rfl
          equivalent := equivalent
          source := source
          source_eq := rfl
          sourceEquivalent := sourceEquivalent
          sourceEquivalent_eq := HEq.rfl
          initial := initial
          initial_eq := rfl
          coprime := coprime
          inversePolynomial := inversePolynomial
          inversePolynomial_eq := rfl
          inverseHorner := inverseHorner
          inverseHorner_eq := rfl
          inverse := inverse
          inverse_eq := inverseHorner.output_eq (bindings index) (Coherence.exact 0) inversePolynomial.coeffs
          inverse_cache_eq := rfl
          product := product
          request := none
          followup := followup
          observation := observation
          prepared := prepared
          preparation_eq := rfl
          output := output
          output_eq := rfl }) := by
  rfl

/-- Building an inverse stores the identical supplied preparation request, without changing its owner. -/
theorem build_request (input : Gaussian.Normalized bindings channel) (index : Fin arity)
    (generator : Algebraic.Sidecar (bindings index)) (degree : Nat)
    (degreeEq : degree = Terms.exponentBound index input.form.terms)
    (check : Sparse.PowerCheck input.form index degree)
    (checkEq : check = input.form.inspectPowers index degree)
    (coordinates : Sparse.PowerCoordinates input.form index degree)
    (coordinatesEq : check.originalOutcome = .coordinates coordinates)
    (polynomial : CoefficientPolynomial) (polynomialEq : polynomial = coordinates.dense)
    (coprime : CoprimeCertificate generator.polynomial polynomial) (supplied : Option (Prepared channel)) :
    (build input index generator degree degreeEq check checkEq coordinates coordinatesEq polynomial polynomialEq
      coprime supplied).request = supplied := rfl

/-- The optional actual follow-up is the same shared preparation procedure's first retained output. -/
theorem followup_eq {input : Gaussian.Normalized bindings channel} (certificate : Inverse input) :
    certificate.followup =
      (prepareAfter certificate.initial certificate.inverse certificate.product certificate.request).1 :=
  congrArg Prod.fst certificate.preparation_eq

/-- The optional stored factor observation is read from the same complete two-head preparation result. -/
theorem observation_eq {input : Gaussian.Normalized bindings channel} (certificate : Inverse input) :
    certificate.observation =
      (prepareAfter certificate.initial certificate.inverse certificate.product certificate.request).2.1 :=
  congrArg (fun result => result.2.1) certificate.preparation_eq

/-- The stored preparation consumes the same complete procedure result without another observation or factor payment. -/
theorem prepared_eq {input : Gaussian.Normalized bindings channel} (certificate : Inverse input) :
    certificate.prepared =
      (prepareAfter certificate.initial certificate.inverse certificate.product certificate.request).2.2 :=
  congrArg (fun result => result.2.2) certificate.preparation_eq

/-- A successful actual first head is the literal stored preparation with no follow-up or factor observation. -/
theorem preparation_eq_of_prepared {input : Gaussian.Normalized bindings channel} (certificate : Inverse input)
    (separated : Geometric.Preparation.Separated certificate.initial.ball) (result : Prepared channel)
    (computed : result = Geometric.Preparation.fromBall certificate.source channel certificate.sourceEquivalent
      certificate.initial.state certificate.initial.ball certificate.initial.readback separated)
    (selected : certificate.initial.outcome = .prepared separated result computed)
    (unrequested : certificate.request = none) :
    (certificate.followup, (certificate.observation, certificate.prepared)) = (none, (none, result)) :=
  by
    have actual := certificate.preparation_eq
    rewrite [unrequested] at actual
    exact actual.trans (prepareAfter_prepared certificate.initial certificate.inverse certificate.product
      separated result computed selected)

/-- An inconclusive actual first head retains its exact original continuation and same lower preparation procedure. -/
theorem preparation_eq_of_inconclusive {input : Gaussian.Normalized bindings channel} (certificate : Inverse input)
    (failed : ¬ Geometric.Preparation.Separated certificate.initial.ball)
    (selected : certificate.initial.outcome = .inconclusive failed)
    (unrequested : certificate.request = none) :
    (certificate.followup, (certificate.observation, certificate.prepared)) =
      (let state := certificate.initial.state.advance.advance
       let later := Geometric.Preparation.inspectAt certificate.source channel certificate.sourceEquivalent state
       (some ⟨⟨state, rfl⟩, ⟨later, rfl⟩⟩, prepare later certificate.inverse certificate.product)) :=
  by
    have actual := certificate.preparation_eq
    rewrite [unrequested] at actual
    exact actual.trans
      (prepareAfter_inconclusive certificate.initial certificate.inverse certificate.product failed selected)

/-- A stored actual follow-up supplies the same complete pair through the original lower preparation procedure. -/
theorem preparation_eq_of_followup {input : Gaussian.Normalized bindings channel} (certificate : Inverse input)
    (later : Followup certificate.initial) (retained : certificate.followup = some later) :
    (certificate.observation, certificate.prepared) = prepare later.2.val certificate.inverse certificate.product :=
  (congrArg Prod.snd certificate.preparation_eq).trans
    (prepareAfter_result certificate.initial certificate.inverse certificate.product later certificate.request
      ((congrArg Prod.fst certificate.preparation_eq).symm.trans retained))

/-- A separated actual second head consumes its literal stored preparation and retains no factor observation. -/
theorem preparation_eq_of_followup_prepared {input : Gaussian.Normalized bindings channel}
    (certificate : Inverse input) (later : Followup certificate.initial)
    (retained : certificate.followup = some later)
    (separated : Geometric.Preparation.Separated later.2.val.ball) (result : Prepared channel)
    (computed : result = Geometric.Preparation.fromBall certificate.source channel certificate.sourceEquivalent
      later.2.val.state later.2.val.ball later.2.val.readback separated)
    (selected : later.2.val.outcome = .prepared separated result computed) :
    (certificate.observation, certificate.prepared) = (none, result) :=
  (certificate.preparation_eq_of_followup later retained).trans
    (prepare_prepared later.2.val certificate.inverse certificate.product separated result computed selected)

/-- Failure of both actual geometric heads retains the original factor observation and same paid preparation. -/
theorem preparation_eq_of_followup_inconclusive {input : Gaussian.Normalized bindings channel}
    (certificate : Inverse input) (later : Followup certificate.initial)
    (retained : certificate.followup = some later)
    (failed : ¬ Geometric.Preparation.Separated later.2.val.ball)
    (selected : later.2.val.outcome = .inconclusive failed) :
    (certificate.observation, certificate.prepared) =
      (let observation := Prepared.Factor.observe channel certificate.inverse 1 (by decide) certificate.product
       (some observation, observation.prepare)) :=
  (certificate.preparation_eq_of_followup later retained).trans
    (prepare_inconclusive later.2.val certificate.inverse certificate.product failed selected)

/-- A supplied preparation determines the same retained complete inverse preparation result. -/
theorem preparation_eq_of_supplied {input : Gaussian.Normalized bindings channel} (certificate : Inverse input)
    (prepared : Prepared channel) (supplied : certificate.request = some prepared) :
    (certificate.followup, (certificate.observation, certificate.prepared)) = (none, (none, prepared)) := by
  have actual := certificate.preparation_eq
  rewrite [supplied] at actual
  exact actual.trans (prepareAfter_supplied certificate.initial certificate.inverse certificate.product prepared)

/-- The actual prepared reciprocal compares to this same retained inverse-generator channel. -/
def reciprocal_equivalent {input : Gaussian.Normalized bindings channel} (certificate : Inverse input) :
    NamedEquivalent certificate.output.name certificate.inverse.name := by
  have agreement := certificate.prepared.reciprocal_equivalent_of_product certificate.inverse certificate.product
  rewrite [← certificate.output_eq] at agreement
  exact agreement

/-- Prepare the reciprocal output's exact polynomial normalization from its actual retained inverse execution.

The original reciprocal remains the numerical source. Its existing product
certificate supplies reciprocal agreement, and the output coefficients consume
the same cached inverse polynomial and Horner accumulators. This construction
runs no coordinate inspection, Euclidean algorithm or Sidecar eliminant.
-/
@[expose] def normalizeOutput {input : Gaussian.Normalized bindings channel} (certificate : Inverse input) :
    Gaussian.Normalized bindings certificate.output := by
  let cached := Terms.Denotation.prepare bindings certificate.input.sources
    (Sparse.ofDenseAt certificate.index certificate.inversePolynomial)
  have agreement := certificate.reciprocal_equivalent
  rewrite [certificate.inverse_cache_eq] at agreement
  exact Gaussian.Normalized.ofDenseAt bindings certificate.index certificate.inversePolynomial
    certificate.inverseHorner agreement cached

/-- The reciprocal output normalization reads the exact original stored inverse coefficient polynomial. -/
theorem normalizeOutput_form {input : Gaussian.Normalized bindings channel} (certificate : Inverse input) :
    certificate.normalizeOutput.form = Sparse.ofDenseAt certificate.index certificate.inversePolynomial :=
  Gaussian.Normalized.ofDenseAt_form _ _ _ _ _ _

/-- The original reciprocal product-to-unit relation, retaining the same numerical output and denominator. -/
def reciprocal_product {input : Gaussian.Normalized bindings channel} (certificate : Inverse input) :
    NamedEquivalent (CoherentNamed.mul certificate.output channel).name (Coherence.exact 1).name :=
  (Product.Congruence.coherentMul_respects certificate.output certificate.inverse channel channel
    certificate.reciprocal_equivalent (NamedEquivalent.refl _)).trans
      ((Product.Laws.coherentMul_comm certificate.inverse channel).trans certificate.product)

/-- The actual inverse-polynomial sample program is linked to the original reciprocal output. -/
def reciprocal_source_equivalent {input : Gaussian.Normalized bindings channel} (certificate : Inverse input)
    (source : {actual : GeometricApproximation //
      actual = Evaluation.evaluate certificate.inversePolynomial certificate.generator.residual.source}) :
    NamedEquivalent certificate.output.name source.val.toApproximation.toNamed := by
  have agreement := CoherentEvaluation.evaluate_agrees certificate.inversePolynomial (bindings certificate.index)
    certificate.generator.residual.source certificate.generator.residual.equivalent (some certificate.inverseHorner)
  rewrite [← certificate.inverse_eq] at agreement
  have actual := certificate.reciprocal_equivalent.trans agreement
  rewrite [← source.property] at actual
  exact actual

/-- Reusing the actual inverse Horner cache preserves the complete original reciprocal-source comparison. -/
theorem reciprocal_source_equivalent_eq_default {input : Gaussian.Normalized bindings channel}
    (certificate : Inverse input)
    (source : {actual : GeometricApproximation //
      actual = Evaluation.evaluate certificate.inversePolynomial certificate.generator.residual.source}) :
    certificate.reciprocal_source_equivalent source = (by
      have agreement := CoherentEvaluation.evaluate_agrees certificate.inversePolynomial (bindings certificate.index)
        certificate.generator.residual.source certificate.generator.residual.equivalent
      rewrite [← certificate.inverse_eq] at agreement
      have actual := certificate.reciprocal_equivalent.trans agreement
      rewrite [← source.property] at actual
      exact actual) := by
  unfold reciprocal_source_equivalent
  rewrite [CoherentEvaluation.evaluate_agrees_cached_eq_default]
  rfl

/-- A retained reciprocal request contains its actual source, failed/successful heads and shared preparation outputs. -/
abbrev ReciprocalPreparation {input : Gaussian.Normalized bindings channel} (certificate : Inverse input) :=
  (source : {actual : GeometricApproximation //
    actual = Evaluation.evaluate certificate.inversePolynomial certificate.generator.residual.source}) ×
  (initial : Geometric.Preparation.Observation source.val certificate.output
    (certificate.reciprocal_source_equivalent source)) ×
    {result : Option (Followup initial) ×
      (Option (Prepared.Factor.Observation certificate.output channel 1) × Prepared certificate.output) //
      initial = Geometric.Preparation.inspectInitial source.val certificate.output
        (certificate.reciprocal_source_equivalent source) ∧
      result = prepareAfter initial channel certificate.reciprocal_product}

namespace ReciprocalPreparation

/-- Read the same actual original inverse-polynomial sample source retained by this request. -/
@[expose] def source {input : Gaussian.Normalized bindings channel} {certificate : Inverse input}
    (receipt : ReciprocalPreparation certificate) : GeometricApproximation := receipt.1.val

/-- Read the exact original first observation, including its finite inconclusive outcome when present. -/
@[expose] def initial {input : Gaussian.Normalized bindings channel} {certificate : Inverse input}
    (receipt : ReciprocalPreparation certificate) :
    Geometric.Preparation.Observation receipt.source certificate.output
      (certificate.reciprocal_source_equivalent receipt.1) := receipt.2.1

/-- Read the retained actual follow-up state and observation, without advancing or inspecting again. -/
@[expose] def followup {input : Gaussian.Normalized bindings channel} {certificate : Inverse input}
    (receipt : ReciprocalPreparation certificate) : Option (Followup receipt.initial) := receipt.2.2.val.1

/-- Read the actual original factor fallback, present only when both finite heads were inconclusive. -/
@[expose] def observation {input : Gaussian.Normalized bindings channel} {certificate : Inverse input}
    (receipt : ReciprocalPreparation certificate) :
    Option (Prepared.Factor.Observation certificate.output channel 1) := receipt.2.2.val.2.1

/-- Read the same stored original-output preparation, with no fresh observation or numerical scan. -/
@[expose] def prepared {input : Gaussian.Normalized bindings channel} {certificate : Inverse input}
    (receipt : ReciprocalPreparation certificate) : Prepared certificate.output := receipt.2.2.val.2.2

/-- Read the latest actual cached source observation without requesting another numerical sample.

The complete receipt retains the first failed head and any actual follow-up.
This view selects their stored state and ball, irrespective of separation; a
later sum inspection still checks its own combined sufficient condition.
-/
@[expose] def cachedSource {input : Gaussian.Normalized bindings channel} {certificate : Inverse input}
    (receipt : ReciprocalPreparation certificate) : Prepared.Sum.Source certificate.output :=
  match receipt.followup with
  | none => Prepared.Sum.Source.ofBall (Geometric.Preparation.sampledChannel receipt.source)
      (certificate.reciprocal_source_equivalent receipt.1) receipt.initial.state
      receipt.initial.ball receipt.initial.readback
  | some later => Prepared.Sum.Source.ofBall (Geometric.Preparation.sampledChannel receipt.source)
      (certificate.reciprocal_source_equivalent receipt.1) later.2.val.state
      later.2.val.ball later.2.val.readback

/-- Without a follow-up, the source view consumes the literal retained initial observation. -/
theorem cachedSource_initial {input : Gaussian.Normalized bindings channel} {certificate : Inverse input}
    (receipt : ReciprocalPreparation certificate) (selected : receipt.followup = none) :
    receipt.cachedSource = Prepared.Sum.Source.ofBall (Geometric.Preparation.sampledChannel receipt.source)
      (certificate.reciprocal_source_equivalent receipt.1) receipt.initial.state
      receipt.initial.ball receipt.initial.readback := by
  unfold cachedSource
  rewrite [selected]
  rfl

/-- An actual follow-up supplies its same stored state and complete cached enclosure. -/
theorem cachedSource_followup {input : Gaussian.Normalized bindings channel} {certificate : Inverse input}
    (receipt : ReciprocalPreparation certificate) (later : Followup receipt.initial)
    (selected : receipt.followup = some later) :
    receipt.cachedSource = Prepared.Sum.Source.ofBall (Geometric.Preparation.sampledChannel receipt.source)
      (certificate.reciprocal_source_equivalent receipt.1) later.2.val.state
      later.2.val.ball later.2.val.readback := by
  unfold cachedSource
  rewrite [selected]
  rfl

/-- The receipt retains the complete actual shared two-head/fallback procedure's result. -/
theorem result_eq {input : Gaussian.Normalized bindings channel} {certificate : Inverse input}
    (receipt : ReciprocalPreparation certificate) :
    (receipt.followup, (receipt.observation, receipt.prepared)) =
      prepareAfter receipt.initial channel certificate.reciprocal_product := receipt.2.2.property.2

end ReciprocalPreparation

/-- Compute one demanded reciprocal-output preparation and retain its complete actual observation receipt.

The original inverse is built without this work. A later request evaluates the
same cached inverse polynomial at the original generator source, inspects its
head once and consumes the original bounded follow-up/factor procedure.
-/
@[expose] def prepareReciprocal {input : Gaussian.Normalized bindings channel} (certificate : Inverse input) :
    ReciprocalPreparation certificate :=
  let source := Evaluation.evaluate certificate.inversePolynomial certificate.generator.residual.source
  let retained := (⟨source, rfl⟩ : {actual : GeometricApproximation //
    actual = Evaluation.evaluate certificate.inversePolynomial certificate.generator.residual.source})
  let equivalent := certificate.reciprocal_source_equivalent retained
  let initial := Geometric.Preparation.inspectInitial source certificate.output equivalent
  let result := prepareAfter initial channel certificate.reciprocal_product
  ⟨retained, initial, ⟨result, rfl, rfl⟩⟩

/-- Prepare the actual reciprocal at its unchanged original interface through the retained request procedure. -/
def reciprocal_prepared {input : Gaussian.Normalized bindings channel} (certificate : Inverse input) :
    Prepared certificate.output := certificate.prepareReciprocal.prepared

end Inverse

set_option genInjectivity false in
/-- One original-generator inverse attempt, preserving coordinate and Euclidean inconclusivity distinctly. -/
inductive InverseAttempt (input : Gaussian.Normalized bindings channel) (index : Fin arity)
    (generator : Algebraic.Sidecar (bindings index)) where
  /-- Retain the complete original coordinate check and every unsupported term in its original order. -/
  | unsupported (retained : Algebraic.Sidecar (bindings index)) (retained_eq : retained = generator) (degree : Nat)
      (degree_eq : degree = Terms.exponentBound index input.form.terms)
      (check : Sparse.PowerCheck input.form index degree) (check_eq : check = input.form.inspectPowers index degree)
      (view : Terms.PowerView index degree input.form.terms) (incomplete : ¬ view.Complete)
      (selected : check.originalOutcome = .unresolved view incomplete)
  /-- Retain the same coordinate cache and original nonconstant gcd; this proves no selected-generator zero. -/
  | commonDivisor (retained : Algebraic.Sidecar (bindings index)) (retained_eq : retained = generator) (degree : Nat)
      (degree_eq : degree = Terms.exponentBound index input.form.terms)
      (check : Sparse.PowerCheck input.form index degree) (check_eq : check = input.form.inspectPowers index degree)
      (coordinates : Sparse.PowerCoordinates input.form index degree)
      (coordinates_eq : check.originalOutcome = .coordinates coordinates)
      (polynomial : CoefficientPolynomial) (polynomial_eq : polynomial = coordinates.dense)
      (common : Decision.NonconstantCommonDivisor retained.polynomial polynomial)
  /-- Retain the actual exact unit/product/preparation cache at this original generator. -/
  | ready (certificate : Inverse input) (index_eq : certificate.index = index)
      (generator_eq : (index_eq ▸ certificate.generator) = generator)

constructive_injectivity InverseAttempt

/-- Attempt a same-generator inverse with one original coordinate inspection and one retained Euclidean computation. -/
@[expose] def inverseAt (input : Gaussian.Normalized bindings channel) (index : Fin arity)
    (generator : Algebraic.Sidecar (bindings index)) (supplied : Option (Prepared channel) := none) :
    InverseAttempt input index generator := by
  let degree := Terms.exponentBound index input.form.terms
  let check := input.form.inspectPowers index degree
  match selected : check.originalOutcome with
  | .unresolved view incomplete => exact .unsupported generator rfl degree rfl check rfl view incomplete selected
  | .coordinates coordinates =>
      let polynomial := coordinates.dense
      let result := Dense.Gaussian.GCD.extendedGCD generator.polynomial polynomial
      let outcome := Decision.coprimeOutcome generator.polynomial polynomial
        (Or.inl (Dense.Gaussian.Degree.Global.isZero_false_of_natDegree_pos
          generator.residual.degreePositive)) result rfl
      match outcome with
      | .commonDivisor common =>
          exact .commonDivisor generator rfl degree rfl check rfl coordinates selected polynomial rfl common
      | .coprime coprime =>
          exact .ready
            (Inverse.build input index generator degree rfl check rfl coordinates selected
              polynomial rfl coprime supplied) rfl rfl

set_option genInjectivity false in
/-- One actual original generator slot and its retained finite coordinate/Euclidean inverse attempt. -/
inductive GeneratorAttempt (input : Gaussian.Normalized bindings channel)
    (generators : (index : Fin arity) → Option (Algebraic.Sidecar (bindings index))) (index : Fin arity) where
  /-- The same original occurrence has no retained generator; the exact route remains inconclusive. -/
  | absent (selected : generators index = none)
  /-- Retain the literal original generator and its complete finite attempt at this actual source normalization. -/
  | inspected (generator : Algebraic.Sidecar (bindings index)) (selected : generators index = some generator)
      (attempt : InverseAttempt input index generator)

constructive_injectivity GeneratorAttempt

/-- Inspect one actual original generator slot once at its unchanged finite source index. -/
@[expose] def generatorAttempt (input : Gaussian.Normalized bindings channel)
    (generators : (index : Fin arity) → Option (Algebraic.Sidecar (bindings index))) (index : Fin arity)
    (supplied : Option (Prepared channel) := none) : GeneratorAttempt input generators index :=
  match selected : generators index with
  | none => .absent selected
  | some generator => .inspected generator selected (input.inverseAt index generator supplied)

/-- The original ordered visited slots, complete attempts and optional first successful exact inverse. -/
abbrev InverseRun (input : Gaussian.Normalized bindings channel)
    (generators : (index : Fin arity) → Option (Algebraic.Sidecar (bindings index))) :=
  List ((index : Fin arity) × GeneratorAttempt input generators index) × Option (Inverse input)

/-- Scan original generator occurrences in order and retain every attempt before the first unit certificate.

An absent generator, unsupported coordinates or nonconstant common divisor is
inconclusive and preserves the original attempt. A successful unit stops the
scan; no later occurrence is inspected and no failed attempt proves a pole.
-/
@[expose] def inverseRun (input : Gaussian.Normalized bindings channel)
    (generators : (index : Fin arity) → Option (Algebraic.Sidecar (bindings index)))
    (remaining : List (Fin arity)) (supplied : Option (Prepared channel) := none) : InverseRun input generators :=
  match remaining with
  | [] => ([], none)
  | index :: remaining =>
      let attempt := input.generatorAttempt generators index supplied
      match attempt with
      | .inspected _ _ (.ready result _ _) => ([⟨index, attempt⟩], some result)
      | .absent _ | .inspected _ _ (.unsupported _ _ _ _ _ _ _ _ _)
          | .inspected _ _ (.commonDivisor _ _ _ _ _ _ _ _ _ _ _) =>
          let later := inverseRun input generators remaining supplied
          (⟨index, attempt⟩ :: later.1, later.2)
termination_by structural remaining

/-- The actual preparation request and exact original ordered inverse-run result at the same input and slot owners. -/
abbrev InverseCheck (input : Gaussian.Normalized bindings channel)
    (generators : (index : Fin arity) → Option (Algebraic.Sidecar (bindings index))) :=
  (request : Option (Prepared channel)) ×
    {result : InverseRun input generators //
      result = input.inverseRun generators (List.ofFn (fun index : Fin arity => index)) request}

namespace InverseCheck

/-- Read the actual original-channel preparation request used by this same retained scan. -/
@[expose] def request {input : Gaussian.Normalized bindings channel}
    {generators : (index : Fin arity) → Option (Algebraic.Sidecar (bindings index))}
    (checked : InverseCheck input generators) : Option (Prepared channel) := checked.1

/-- Read the complete original ordered attempts and first successful inverse without another guard. -/
@[expose] def val {input : Gaussian.Normalized bindings channel}
    {generators : (index : Fin arity) → Option (Algebraic.Sidecar (bindings index))}
    (checked : InverseCheck input generators) : InverseRun input generators := checked.2.val

/-- The whole stored run is the original procedure on its own retained actual preparation request. -/
theorem property {input : Gaussian.Normalized bindings channel}
    {generators : (index : Fin arity) → Option (Algebraic.Sidecar (bindings index))}
    (checked : InverseCheck input generators) :
    checked.val = input.inverseRun generators (List.ofFn (fun index : Fin arity => index)) checked.request :=
  checked.2.property

end InverseCheck

/-- Retain one demanded exact inverse guard over its actual original input, ordered slots and supplied preparation. -/
@[expose] def inverseCheck (input : Gaussian.Normalized bindings channel)
    (generators : (index : Fin arity) → Option (Algebraic.Sidecar (bindings index)))
    (supplied : Option (Prepared channel) := none) : InverseCheck input generators :=
  ⟨supplied, ⟨input.inverseRun generators (List.ofFn (fun index : Fin arity => index)) supplied, rfl⟩⟩

/-- A fresh guard stores the identical supplied preparation input, including its actual presentation and relation. -/
theorem inverseCheck_request (input : Gaussian.Normalized bindings channel)
    (generators : (index : Fin arity) → Option (Algebraic.Sidecar (bindings index)))
    (supplied : Option (Prepared channel)) : (input.inverseCheck generators supplied).request = supplied := rfl

/-- The default guard retains the whole original absent-request run and its exact construction equality. -/
theorem inverseCheck_none (input : Gaussian.Normalized bindings channel)
    (generators : (index : Fin arity) → Option (Algebraic.Sidecar (bindings index))) :
    input.inverseCheck generators none =
      ⟨none, ⟨input.inverseRun generators (List.ofFn (fun index : Fin arity => index)) none, rfl⟩⟩ := rfl

/-- An absent supplied preparation retains the original ordered scan branch and its complete actual attempts. -/
theorem inverseRun_cons_none (input : Gaussian.Normalized bindings channel)
    (generators : (index : Fin arity) → Option (Algebraic.Sidecar (bindings index)))
    (index : Fin arity) (remaining : List (Fin arity)) :
    input.inverseRun generators (index :: remaining) none =
      (let attempt := input.generatorAttempt generators index
       match attempt with
       | .inspected _ _ (.ready result _ _) => ([⟨index, attempt⟩], some result)
       | .absent _ | .inspected _ _ (.unsupported _ _ _ _ _ _ _ _ _)
           | .inspected _ _ (.commonDivisor _ _ _ _ _ _ _ _ _ _ _) =>
           let later := input.inverseRun generators remaining
           (⟨index, attempt⟩ :: later.1, later.2)) := rfl

/-- An empty original scan retains no visited occurrences and no inverse result. -/
theorem inverseRun_nil (input : Gaussian.Normalized bindings channel)
    (generators : (index : Fin arity) → Option (Algebraic.Sidecar (bindings index))) :
    input.inverseRun generators [] = ([], none) := rfl

/-- A demanded guard stores its entire actual original ordered run, including every failed finite attempt. -/
theorem inverseCheck_result (input : Gaussian.Normalized bindings channel)
    (generators : (index : Fin arity) → Option (Algebraic.Sidecar (bindings index))) :
    (input.inverseCheck generators).val = input.inverseRun generators (List.ofFn (fun index : Fin arity => index)) :=
  rfl

/-- A successful actual ordered run selects the same whole original Sidecar at its retained bounded index. -/
theorem inverseRun_generator (input : Gaussian.Normalized bindings channel)
    (generators : (index : Fin arity) → Option (Algebraic.Sidecar (bindings index)))
    {supplied : Option (Prepared channel)} :
    (remaining : List (Fin arity)) → (certificate : Inverse input) →
      (input.inverseRun generators remaining supplied).2 = some certificate →
        generators certificate.index = some certificate.generator
  | [], _, impossible => by cases impossible
  | index :: remaining, certificate, found => by
      unfold inverseRun at found
      cases computed : input.generatorAttempt generators index supplied with
      | absent absent =>
          rewrite [computed] at found
          exact inverseRun_generator input generators remaining certificate found
      | inspected generator selected attempt =>
          rewrite [computed] at found
          cases attempt with
          | unsupported _ _ _ _ _ _ _ _ _ =>
              exact inverseRun_generator input generators remaining certificate found
          | commonDivisor _ _ _ _ _ _ _ _ _ _ _ =>
              exact inverseRun_generator input generators remaining certificate found
          | ready retained indexEq generatorEq =>
              change some retained = some certificate at found
              cases Option.some.inj found
              cases indexEq
              exact selected.trans (congrArg some generatorEq.symm)

/-- A retained successful inverse check certifies the identical selected original generator payload
without rerunning it. -/
theorem inverseCheck_generator (input : Gaussian.Normalized bindings channel)
    (generators : (index : Fin arity) → Option (Algebraic.Sidecar (bindings index)))
    (checked : InverseCheck input generators) (certificate : Inverse input)
    (selected : checked.val.2 = some certificate) : generators certificate.index = some certificate.generator := by
  have run := (congrArg (fun result : InverseRun input generators => result.2) checked.property).symm.trans selected
  exact inverseRun_generator input generators (List.ofFn (fun index : Fin arity => index)) certificate run

end Purelib.Polynomial.Multivariate.Gaussian.Normalized
end
