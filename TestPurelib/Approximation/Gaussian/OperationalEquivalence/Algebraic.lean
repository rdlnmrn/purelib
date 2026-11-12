module

import Purelib.Tactic.OperationalEquivalence
import Purelib.Approximation.Gaussian.Provenance.Algebraic.Comparison
import Purelib.Approximation.Gaussian.Provenance.PolynomialRoot
import Purelib.Polynomial.Approximation.Gaussian.Localization.Selection
import Purelib.Polynomial.Multivariate.Gaussian.Inverse
import Purelib.Approximation.Gaussian.Name.Coherent.Conjugation
import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Acquisition
import Purelib.Data.Gaussian.Field

/-! # Operational identities from original general-root, reciprocal and conjugate certificates -/

namespace TestPurelib.Approximation.Gaussian.OperationalEquivalence.Algebraic

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Polynomial.Multivariate
open Purelib.Polynomial.Approximation.Gaussian (Residual)
open Purelib.Polynomial.Approximation.Gaussian.Localization (Preparation)
open Purelib.Polynomial.Approximation.Gaussian.Evaluation
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.RootContinuation
open Purelib.RootIsolation
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Acquisition.Expression
open Purelib.Approximation.Gaussian.Acquisition.Expression.Checked

/-- Every intrinsic Sidecar supplies its original polynomial-zero programme without a displayed coefficient table. -/
private def annihilator {channel : CoherentNamed} (sidecar : Algebraic.Sidecar channel) :
    NamedEquivalent
      (Horner.polynomialEval sidecar.polynomial channel).name
      (CoherentNamed.Coherence.exact 0).name := by
  ccl_equiv [sidecar]

/-- A supplied selected-root owner retains its actual factor equation on the unchanged original numerical channel. -/
private def selectedAnnihilator {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    (residual : Residual polynomial channel) (preparation : Preparation polynomial residual.source)
    (selection : Preparation.Selection preparation) :
    NamedEquivalent
      (Horner.polynomialEval
        (Algebraic.Sidecar.ofRoot (PolynomialRoot.Sidecar.ofSelection residual preparation selection)).polynomial
        channel).name
      (CoherentNamed.Coherence.exact 0).name := by
  ccl_equiv [PolynomialRoot.Sidecar.ofSelection residual preparation selection]

/-- The displayed cubic has a genuine linear term and is not a pure-power polynomial. -/
private def cubic : CoefficientPolynomial := ⟨[1, 0, -1, -1]⟩

/-- The actual retained general cubic equation proves an identity on its unchanged original root channel. -/
private def generalCubic {ambient : CoherentRoot.Box} {track : CoherentRoot.WindingOneTrack cubic ambient}
    (root : CoherentRoot.CertifiedName track) (input : FTA.Positive.Input.PositiveInput cubic) :
    NamedEquivalent (Power.namedPower root.value 3).name
      (CoherentNamed.add root.value (CoherentNamed.Coherence.exact 1)).name := by
  ccl_equiv [PolynomialRoot.Sidecar.ofIsolated root input]

/-- A supplied original atom comparison keeps precedence when the retained general equation selects its binding. -/
private def transportedCubic {ambient : CoherentRoot.Box} {track : CoherentRoot.WindingOneTrack cubic ambient}
    (root : CoherentRoot.CertifiedName track) (input : FTA.Positive.Input.PositiveInput cubic)
    (original : CoherentNamed) (same : NamedEquivalent original.name root.value.name) :
    NamedEquivalent (Power.namedPower original 3).name
      (CoherentNamed.add root.value (CoherentNamed.Coherence.exact 1)).name := by
  ccl_equiv [same, PolynomialRoot.Sidecar.ofIsolated root input]

/-- Two independent original roots use both retained equations without identifying their owners. -/
private def independentCubics {firstAmbient secondAmbient : CoherentRoot.Box}
    {firstTrack : CoherentRoot.WindingOneTrack cubic firstAmbient}
    {secondTrack : CoherentRoot.WindingOneTrack cubic secondAmbient}
    (first : CoherentRoot.CertifiedName firstTrack) (second : CoherentRoot.CertifiedName secondTrack)
    (input : FTA.Positive.Input.PositiveInput cubic) :
    NamedEquivalent (CoherentNamed.add (Power.namedPower first.value 3) (Power.namedPower second.value 3)).name
      (CoherentNamed.add (CoherentNamed.add first.value second.value) (CoherentNamed.Coherence.exact 2)).name := by
  ccl_equiv [PolynomialRoot.Sidecar.ofIsolated first input, PolynomialRoot.Sidecar.ofIsolated second input]

/-- An actual retained inverse proves the original output's unit product without any caller-supplied product law. -/
private def retainedInverse {arity : Nat} {bindings : Fin arity → CoherentNamed} {channel : CoherentNamed}
    {input : Gaussian.Normalized bindings channel} (inverse : Gaussian.Normalized.Inverse input) :
    NamedEquivalent (CoherentNamed.mul inverse.output channel).name (CoherentNamed.Coherence.exact 1).name := by
  ccl_equiv [inverse]

/-- The original prepared quotient view consumes that same retained inverse and its exact output identity. -/
private def preparedInverse {arity : Nat} {bindings : Fin arity → CoherentNamed} {channel : CoherentNamed}
    {input : Gaussian.Normalized bindings channel} (inverse : Gaussian.Normalized.Inverse input) :
    NamedEquivalent
      (CoherentNamed.mul (inverse.prepared.quotient (CoherentNamed.Coherence.exact 1)) channel).name
      (CoherentNamed.Coherence.exact 1).name := by
  ccl_equiv [inverse]

/-- The original complex cubic retains a nonreal constant and its actual conjugate coefficient. -/
private def complexCubic : CoefficientPolynomial := ⟨[1, 0, -1, ⟨-1, -1⟩]⟩

/-- Coefficientwise conjugation of the same root owner proves the conjugated general cubic equation. -/
private def conjugatedCubic {ambient : CoherentRoot.Box} {track : CoherentRoot.WindingOneTrack complexCubic ambient}
    (root : CoherentRoot.CertifiedName track) (input : FTA.Positive.Input.PositiveInput complexCubic) :
    NamedEquivalent (Power.namedPower (CoherentNamed.conj root.value) 3).name
      (CoherentNamed.add (CoherentNamed.conj root.value) (CoherentNamed.Coherence.exact ⟨1, -1⟩)).name := by
  ccl_equiv [PolynomialRoot.Sidecar.ofIsolated root input]

/-- Double conjugation uses the original operational law before exact coefficient normalization. -/
private def doubleConjugation (channel : CoherentNamed) :
    NamedEquivalent (CoherentNamed.conj (CoherentNamed.conj channel)).name channel.name := by
  ccl_equiv

/-- Exact conjugation changes the original imaginary coefficient without assuming its channel is fixed. -/
private def exactConjugation : NamedEquivalent (CoherentNamed.conj (CoherentNamed.Coherence.exact ⟨2, 3⟩)).name
    (CoherentNamed.Coherence.exact ⟨2, -3⟩).name := by
  ccl_equiv

/-- Admitted syntax is consumed by the original checked-result producer, including inverse obstructions. -/
private def admittedResult {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (admitted : Admitted environment expression) : CheckedResult environment expression := by
  ccl_equiv [admitted]

/-- The frontend invokes original completeness at the exact supplied admission tree and original outcome. -/
private theorem admittedResolved {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (admitted : Admitted environment expression) : admitted.run.Resolved := by
  ccl_equiv [admitted]

/-- The original typed checker retains both ordered zero-denominator occurrences in its actual emitted programme. -/
private def orderedResult (environment : Fin 0 → Annotated) : CheckedResult environment
    (.add (.inverse (.base (.rational 0))) (.inverse (.base (.rational 0)))) := by
  let first := Admitted.inverse (Admitted.rational environment 0)
  let later := Admitted.inverse (Admitted.rational environment 0)
  let original := Admitted.add first later
  ccl_equiv [original]

/-- The generated checked result is the complete original producer result, including its ordered first-zero outcome. -/
example (environment : Fin 0 → Annotated) :
    let first := Admitted.inverse (Admitted.rational environment 0)
    let later := Admitted.inverse (Admitted.rational environment 0)
    let original := Admitted.add first later
    orderedResult environment = original.check := rfl

/-- An unresolved original inverse is checked before even a reflexive polynomial target can be normalized. -/
example {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (_admitted : Admitted environment expression) (_channel : CoherentNamed) : True := by
  fail_if_success
    have : NamedEquivalent _channel.name _channel.name := by ccl_equiv [_admitted]
  trivial

/-- Replacing a polynomial by its exact readback retains the complete original Sidecar and its paired caches. -/
example {channel : CoherentNamed} (sidecar : Algebraic.Sidecar channel) (polynomial : CoefficientPolynomial)
    (same : sidecar.polynomial = polynomial) :
    let original : (residual : Residual sidecar.polynomial channel) ×
        Algebraic.Cached sidecar.origin sidecar.polynomial residual := ⟨sidecar.residual, sidecar.cached⟩
    let retained := (congrArg (fun coefficient =>
      (residual : Residual coefficient channel) ×
        Algebraic.Cached sidecar.origin coefficient residual) same).mp original
    ({origin := sidecar.origin, polynomial := polynomial, residual := retained.1, cached := retained.2} :
      Algebraic.Sidecar channel) = sidecar := by
  cases same
  cases sidecar
  rfl

/-- An unrelated scalar cannot be substituted for the original general root by coefficient normalization. -/
example {ambient : CoherentRoot.Box} {track : CoherentRoot.WindingOneTrack cubic ambient}
    (_root : CoherentRoot.CertifiedName track) (_input : FTA.Positive.Input.PositiveInput cubic) : True := by
  fail_if_success
    have : NamedEquivalent _root.value.name (CoherentNamed.Coherence.exact 1).name := by
      ccl_equiv [PolynomialRoot.Sidecar.ofIsolated _root _input]
  trivial

/-- A shared real annihilator alone does not identify independently retained conjugate branches. -/
example {ambient : CoherentRoot.Box} {track : CoherentRoot.WindingOneTrack cubic ambient}
    (_root : CoherentRoot.CertifiedName track) (_input : FTA.Positive.Input.PositiveInput cubic) : True := by
  fail_if_success
    have : NamedEquivalent _root.value.name (CoherentNamed.conj _root.value).name := by
      ccl_equiv [PolynomialRoot.Sidecar.ofIsolated _root _input]
  trivial

/-- General independent intrinsic inputs retain the original runtime classifier without assuming its outcome. -/
private def independentComparison {first second : CoherentNamed}
    (left : Algebraic.Sidecar first) (right : Algebraic.Sidecar second) :
    Algebraic.Comparison first second := by
  ccl_equiv [left, right]

/-- Symbolic independent owners retain a typed classifier without claiming a closed equality decision. -/
example {first second : CoherentNamed} (_left : Algebraic.Sidecar first) (_right : Algebraic.Sidecar second) :
    True := by
  fail_if_success
    have : NamedEquivalent first.name second.name := by
      ccl_equiv [_left, _right]
  trivial

/-- A supplied whole comparison is consumed through its same actual cached outcome. -/
private def retainedComparison {first second : CoherentNamed}
    {left : Algebraic.Sidecar first} {right : Algebraic.Sidecar second}
    (retained : Algebraic.Sidecar.Compared left right) : Algebraic.Comparison first second := by
  ccl_equiv [retained]

/-- The frontend's retained-comparison mode projects the literal supplied outcome rather than rerunning its producer. -/
example {first second : CoherentNamed} {left : Algebraic.Sidecar first} {right : Algebraic.Sidecar second}
    (retained : Algebraic.Sidecar.Compared left right) :
    retainedComparison retained = retained.comparison := rfl

/-- A quantified retained comparison consumes its own outcome after the original additive identity is proved. -/
private def retainedNeutralAddition {channel : CoherentNamed} (sidecar : Algebraic.Sidecar channel)
    (retained : Algebraic.Sidecar.Compared sidecar
      ((Algebraic.Sidecar.ofRational (Rational.Basic.RationalSidecar.exact 0)).add sidecar)) :
    NamedEquivalent channel.name (CoherentNamed.add (CoherentNamed.Coherence.exact 0) channel).name := by
  ccl_equiv [retained]

/-- Completed results use their original full materializations at the explicit comparison boundary. -/
private def finishedComparison {firstArity secondArity : Nat}
    {firstEnvironment : Fin firstArity → Annotated} {secondEnvironment : Fin secondArity → Annotated}
    {firstExpression : Expr firstArity} {secondExpression : Expr secondArity}
    (first : Finished firstEnvironment firstExpression) (second : Finished secondEnvironment secondExpression) :
    Algebraic.Comparison first.materialize.channel second.materialize.channel := by
  ccl_equiv [first, second]

/-- The first exact original scalar owner used by closed comparison reconstruction. -/
private def comparisonOne : Algebraic.Sidecar (CoherentNamed.Coherence.exact 1) :=
  Algebraic.Sidecar.ofRational (Rational.Basic.RationalSidecar.exact 1)

/-- An independently constructed arithmetic channel at the same scalar retains both original operand caches. -/
private def comparisonSum : Algebraic.Sidecar
    (CoherentNamed.add (CoherentNamed.Coherence.exact 0) (CoherentNamed.Coherence.exact 1)) :=
  (Algebraic.Sidecar.ofRational (Rational.Basic.RationalSidecar.exact 0)).add comparisonOne

/-- The same full original comparison programme supplies this actual equal-site constructor. -/
private def equalComparison := comparisonOne.compare comparisonSum

/-- Closed equality reconstruction consumes the original classifier result
without assuming coefficient coincidence. -/
private def closedIndependentEquality :
    NamedEquivalent (CoherentNamed.Coherence.exact 1).name
      (CoherentNamed.add (CoherentNamed.Coherence.exact 0) (CoherentNamed.Coherence.exact 1)).name := by
  ccl_equiv [equalComparison]

/-- The actual original comparison of distinct scalar channels retains its quantitative difference preparation. -/
private def separatedComparison := comparisonOne.compare
  (Algebraic.Sidecar.ofRational (Rational.Basic.RationalSidecar.exact 0))

/-- A negative operational goal consumes the original separation certificate at both unchanged channels. -/
private theorem closedIndependentSeparation :
    ¬ Nonempty (NamedEquivalent (CoherentNamed.Coherence.exact 1).name
      (CoherentNamed.Coherence.exact 0).name) := by
  ccl_equiv [comparisonOne, Algebraic.Sidecar.ofRational (Rational.Basic.RationalSidecar.exact 0)]

/-- A genuinely separated original classifier must not be reconstructed as an equality certificate. -/
example : True := by
  fail_if_success
    have : NamedEquivalent (CoherentNamed.Coherence.exact 1).name (CoherentNamed.Coherence.exact 0).name := by
      ccl_equiv [separatedComparison]
  trivial

/-- The actual equal-site constructor cannot be presented as quantitative separation. -/
example : True := by
  fail_if_success
    have : ¬ Nonempty (NamedEquivalent (CoherentNamed.Coherence.exact 1).name
        (CoherentNamed.add (CoherentNamed.Coherence.exact 0) (CoherentNamed.Coherence.exact 1)).name) := by
      ccl_equiv [equalComparison]
  trivial

/-- Read an original left-add context without identifying its dependent syntax indices. -/
private def leftAddFrame {arity : Nat} {environment : Fin arity → Annotated}
    {input output : Expr arity} (frame : Frame environment input output) : Bool :=
  match frame with
  | .left operation _ _ => match operation with | .add => true | _ => false
  | _ => false

/-- Inspect the original invalidity context for the leftmost reciprocal of an ordered sum. -/
private def firstZeroOnLeft {arity : Nat} {environment : Fin arity → Annotated} :
    {expression : Expr arity} → Invalid environment expression → Bool
  | _, .through frame first => leftAddFrame frame &&
      match first with | .inverse _ _ => true | .through _ _ => false
  | _, .inverse _ _ => false

/-- The actual ordered two-zero programme retains its left occurrence, empty prefix and original zero denominator. -/
example (environment : Fin 0 → Annotated) :
    match (Admitted.add
      (Admitted.inverse (Admitted.rational environment 0))
      (Admitted.inverse (Admitted.rational environment 0))).run with
    | .invalid first => firstZeroOnLeft first = true ∧ first.prefix = [] ∧
        first.denominator.2.1.channel = CoherentNamed.Coherence.exact 0
    | _ => False := by
  exact ⟨rfl, rfl, rfl⟩

/-- A concrete first-zero reciprocal prevents even a reflexive target from bypassing the original checked run. -/
example : True := by
  let environment : Fin 0 → Annotated := fun index => Fin.elim0 index
  let first := Admitted.inverse (Admitted.rational environment 0)
  let later := Admitted.inverse (Admitted.rational environment 0)
  let original := Admitted.add first later
  fail_if_success
    have : NamedEquivalent (CoherentNamed.Coherence.exact 1).name
        (CoherentNamed.Coherence.exact 1).name := by
      ccl_equiv [original]
  trivial

end TestPurelib.Approximation.Gaussian.OperationalEquivalence.Algebraic
