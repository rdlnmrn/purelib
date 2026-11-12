module

import Purelib.Integration.Path.Primitive.Algebraic.Path
import Purelib.Integration.Path.Primitive.Algebraic.Transport
import Purelib.Integration.Program.Gaussian.Exact
import Purelib.Data.List.Membership
import Purelib.Polynomial.Dense.Gaussian.Derivative
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Arithmetic.Mul
import Purelib.Approximation.Gaussian.Division.Prepared.Decision.Laws
import Purelib.Approximation.Gaussian.Provenance.Algebraic.Comparison
import Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic
import Purelib.Data.List.OfFn.Basic
import Purelib.Integration.Algebraic.SquareFactor.NamedTransport
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Constants
meta import Purelib.Integration.Path.Primitive.Algebraic.Transport
meta import Purelib.Integration.Path.Primitive.Algebraic
meta import Purelib.Approximation.Gaussian.Name.Coherent
meta import Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic

/-!
# Checked primitives on original endpoint banks and actual finite cells

The fixed nonempty path uses two exact polynomial integration programs, their
actual lifted cells, retained local derivative residuals and source endpoint
samplers. Other checks distinguish unlike radicands and changed sheet labels.
-/

namespace TestPurelib.Integration.AlgebraicPrimitive

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.List
open Purelib.Data.Rat.Fraction
open Purelib.Integration.Path.Primitive
open Purelib.Integration.Path.Primitive.Algebraic
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Geometry.Path.Gaussian.Lifted.Basic
open Purelib.Riemann.RootContinuation
open Purelib.Topology.Chain
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Provenance

/-- The original constant square parameter two. -/
private def polynomialAt (_chart : Unit) : Coefficients := DensePolynomial.constant 2

/-- The exact spatial primitive polynomial X. -/
private def coordinate : Coefficients := ⟨[1, 0]⟩

/-- Cache both independently selected original root owners once for the endpoint bank. -/
private def roots : Data.Vector RootReading 2 :=
  .cons (SquareRootSidecar.isolated (2 : Canonical) 0)
    (.cons (SquareRootSidecar.isolated (2 : Canonical) 1) .nil)

/-- Each cached original sheet retains its exact original parameter. -/
private theorem roots_parameter (sheet : Fin 2) : (roots sheet).2.parameter = 2 := by
  cases sheet with
  | mk index bound =>
    cases index with
    | zero => exact SquareRootSidecar.isolated_parameter 2 0
    | succ index =>
      cases index with
      | zero => exact SquareRootSidecar.isolated_parameter 2 1
      | succ index => exact False.elim (Nat.not_lt_zero _
          (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ bound)))

/-- Read the same retained original root owner at every endpoint on its selected constant sheet. -/
private def rootAt (_chart : Unit) (point : LiftedPoint 2) : RootReading :=
  roots point.sheet

/-- The scalar coordinate primitive in the original constant chart. -/
private def primitive : Expression (polynomialAt ()) := Expression.scalar coordinate

/-- The scalar unit differential in the original constant chart. -/
private def differential : Expression (polynomialAt ()) := Expression.scalar (DensePolynomial.constant 1)

/-- Execute the primitive checker and retain its actual success certificate. -/
private def checked : Exact differential primitive :=
  let attempt := prepare differential primitive
  match attempt.check with
  | .exact certificate => certificate
  | .realObstructed nonzero => False.elim (Bool.noConfusion
      ((show attempt.comparison.real.isZero = true from by decide +kernel).symm.trans nonzero))
  | .imaginaryObstructed _ nonzero => False.elim (Bool.noConfusion
      ((show attempt.comparison.imaginary.isZero = true from by decide +kernel).symm.trans nonzero))

/-- Retain the exact scalar primitive at one original isolated-root endpoint. -/
private def endpoint (value : Canonical) (sheet : Fin 2) : Endpoint Unit 2 polynomialAt rootAt :=
  Endpoint.retain polynomialAt rootAt () ⟨value, sheet⟩ primitive
    ((roots_parameter sheet).trans
      (DensePolynomial.eval_constant (2 : Canonical) value).symm)
    (Expression.defined_scalar coordinate value)

/-- The original two-point source bank at zero and one on the same selected sheet. -/
private def bank : EndpointBank Unit 2 2 polynomialAt rootAt :=
  .cons (endpoint 0 0) (.cons (endpoint 1 0) .nil)

/-- The exact forward occurrence between the original bank keys. -/
private def forward : OrientedEdge 2 := ⟨0, 1⟩

/-- The exact backward occurrence between the same original bank keys. -/
private def backward : OrientedEdge 2 := forward.reverse

/-- The two actual ordered occurrences forming the source loop. -/
private def occurrences : Data.Vector (OrientedEdge 2) 2 := .cons forward (.cons backward .nil)

/-- The source word is closed at the literal original bank key zero. -/
private theorem loopPath : PathBoundary.PathEndpoints edgeStart edgeFinish
    (List.ofFn fun position => occurrences position) 0 0 := by
  rewrite [Data.List.OfFn.Basic.ofFn_succ, Data.List.OfFn.Basic.ofFn_succ, List.ofFn_zero]
  exact .cons (.cons (.nil _))

example : (boundary bank _ 0 0 loopPath).coefficients 0 = 0 := (boundary bank _ 0 0 loopPath).closed 0

example : (boundary bank _ 0 0 loopPath).reverse.coefficients 1 = 0 :=
  (boundary bank _ 0 0 loopPath).reverse.closed 1

/-- The same scalar primitive has an exact retained sampler at each original bank entry. -/
private def sampling (key : Fin 2) : Endpoint.Sampling (bank key) :=
  (bank key).sampleScalar coordinate (by
    cases key with
    | mk key bound =>
      cases key with
      | zero => rfl
      | succ key =>
        cases key with
        | zero => rfl
        | succ key => exact False.elim (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ bound))))

/-- The original exact cell used by the forward program. -/
private def forwardCell : Cell.Basic.CellModel := Cell.Basic.CellModel.exact 0 1 ⟨[1]⟩

/-- The original constant refinement program integrating the forward cell's actual polynomial. -/
private def forwardProgram := Purelib.Integration.Program.Gaussian.Basic.RefinementProgram.exactPolynomial 0 1 ⟨[1]⟩

/-- The original lifted forward cell retains the actual sheet identity transport. -/
private def forwardLiftCell : LiftedCell (bank 0).point (bank 1).point :=
  ⟨Data.Fin.Bijection.identity 2, rfl⟩

/-- The actual nonempty original lifted forward path. -/
private def forwardLift : LiftedPath 2 (bank 0).point (bank 1).point :=
  .cons forwardLiftCell (.nil (bank 1).point)

/-- The actual cached local primitive derivative and displacement residual for the forward cell. -/
private def forwardComparison : Cell.Primitive.Comparison forwardCell :=
  Cell.Primitive.Comparison.build forwardCell coordinate

/-- Source-owned forward finite models derive the numerical primitive comparison internally. -/
private def forwardModels : PrimitiveEdge.PolynomialModels (bank 0).point (bank 1).point
    (sampling 0).source (sampling 1).source forwardProgram where
  value := fun _ => coordinate
  lifted := fun _ => forwardLift
  follows := fun _ => .cons rfl rfl (.nil _)
  cellComparison := fun _ cell member => by
    change cell ∈ [forwardCell] at member
    have equal : cell = forwardCell := (Membership.mem_singleton.mp member)
    cases equal
    exact forwardComparison
  localStart := by
    intro index cell member
    change cell ∈ [forwardCell] at member
    have equal : cell = forwardCell := Membership.mem_singleton.mp member
    cases equal
    rfl
  localFinish := by
    intro index cell member
    change cell ∈ [forwardCell] at member
    have equal : cell = forwardCell := Membership.mem_singleton.mp member
    cases equal
    rfl
  endpointBound := fun _ => 0
  startError := by
    intro index
    unfold sampling
    rewrite [Endpoint.sampleScalar_source, Approximation.Gaussian.Geometric.GeometricApproximation.exact_sample,
      Data.Gaussian.Basic.sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
    exact Order.Basic.le_refl _
  finishError := by
    intro index
    unfold sampling
    rewrite [Endpoint.sampleScalar_source, Approximation.Gaussian.Geometric.GeometricApproximation.exact_sample,
      Data.Gaussian.Basic.sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
    exact Order.Basic.le_refl _
  localBound := fun _ => 0
  localBound_le := by
    intro index cell member
    change cell ∈ [forwardCell] at member
    have equal : cell = forwardCell := Membership.mem_singleton.mp member
    cases equal
    change forwardComparison.bound ≤ (0 : Data.Rat.Fraction.Rational)
    decide +kernel
  scale := 0
  scale_nonnegative := Order.Basic.le_refl _
  budget_le := by
    intro index
    simp only [Data.Rat.Fraction.Field.mul_zero_direct, Data.Rat.Fraction.Field.zero_add]
    exact Approximation.Rational.Geometric.Basic.quarterRadius_nonneg (Order.Basic.le_refl _) index

/-- The original forward edge admission caches its formal check and actual numerical source construction. -/
private def admittedForward : EdgeAdmission bank forward :=
  EdgeAdmission.build bank forward differential checked rfl (HEq.rfl)
    (sampling 0) (sampling 1) forwardProgram forwardModels

example (startRoot : Algebraic.Sidecar (bank 0).root.1)
    (finishRoot : Algebraic.Sidecar (bank 1).root.1) (index : Nat) :
    (admittedForward.numerical.outputSidecar ((bank 0).sidecar startRoot)
      ((bank 1).sidecar finishRoot)).residual.source.sample index =
    (primitiveDifferenceSidecar ((bank 0).sidecar startRoot)
      ((bank 1).sidecar finishRoot)).residual.source.sample index :=
  (primitiveDifferenceSidecar ((bank 0).sidecar startRoot) ((bank 1).sidecar finishRoot)).transport_sample
    admittedForward.numerical.integral_eq_difference index

example : admittedForward.numerical.program = forwardProgram := by
  exact admittedForward.numerical_program

/-- The original exact-zero root and its square provenance at a constant chart. -/
private def zeroRootAt (_chart : Unit) (_point : LiftedPoint 1) : RootReading :=
  ⟨Coherence.exact 0, SquareRootSidecar.zeroSidecar⟩

/-- A scalar primitive endpoint using the original exact-zero root. -/
private def zeroEndpoint : Endpoint Unit 1 (fun _ => DensePolynomial.constant 0) zeroRootAt :=
  Endpoint.retain (fun _ => DensePolynomial.constant 0) zeroRootAt () ⟨0, 0⟩
    (Expression.scalar coordinate) (DensePolynomial.eval_constant 0 0).symm
    (Expression.defined_scalar coordinate 0)

example : (zeroEndpoint.sidecar
    (Algebraic.Sidecar.ofRational (Rational.Basic.RationalSidecar.exact 0))).scalar?.map
      (fun reading => reading.value) = some 0 := rfl

/-- A different formal primitive at the same original selected zero root. -/
private def zeroGeneratorEndpoint : Endpoint Unit 1 (fun _ => DensePolynomial.constant 0) zeroRootAt :=
  Endpoint.retain (fun _ => DensePolynomial.constant 0) zeroRootAt () ⟨0, 0⟩
    Expression.generator (DensePolynomial.eval_constant 0 0).symm (Expression.defined_generator 0)

/-- The original zero root is related to itself through the unit chart factor. -/
private def zeroGeneratorTransport := Endpoint.prepareTransport
  (fun (_ : Unit) (_ _ : Endpoint Unit 1 (fun _ => DensePolynomial.constant 0) zeroRootAt) => True)
  (fun _ => 1) () zeroGeneratorEndpoint zeroEndpoint trivial (by
    have product := Exact.Arithmetic.exact_mul (1 : Canonical) 0
    rewrite [Basic.mul_zero] at product
    exact product.symm)

/-- The original zero-generator endpoint transported to itself through the unit factor. -/
private def zeroGeneratorSelfTransport := Endpoint.prepareTransport
  (fun (_ : Unit) (_ _ : Endpoint Unit 1 (fun _ => DensePolynomial.constant 0) zeroRootAt) => True)
  (fun _ => 1) () zeroGeneratorEndpoint zeroGeneratorEndpoint trivial (by
    have product := Exact.Arithmetic.exact_mul (1 : Canonical) 0
    rewrite [Basic.mul_zero] at product
    exact product.symm)

/-- The self-transport retains zero real and imaginary coefficient differences. -/
private def zeroGeneratorSelfCertificate : Endpoint.Transport zeroGeneratorSelfTransport :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- The original transport equivalence selects its requested refinement indices. -/
private def checkZeroGeneratorTransportRequest : IO Unit := do
  let target : Rational := 1
  if positive : 0 < target then
    let comparison := zeroGeneratorSelfCertificate.equivalent.compare 0 0 target positive
    unless comparison.leftIndex = 8 ∧ comparison.rightIndex = 9 do
      let actual := s!"({comparison.leftIndex}, {comparison.rightIndex})"
      throw (IO.userError s!"zero-generator self-transport selected {actual} instead of (8, 9)")
  else
    throw (IO.userError "zero-generator transport target is not positive")

#eval checkZeroGeneratorTransportRequest

example : (match zeroGeneratorTransport.check with
  | .imaginaryObstructed _ _ => true
  | _ => false) = true := rfl

example : (match ((zeroGeneratorEndpoint.sidecar
    (Algebraic.Sidecar.ofRational (Rational.Basic.RationalSidecar.exact 0))).compare
      (zeroEndpoint.sidecar (Algebraic.Sidecar.ofRational (Rational.Basic.RationalSidecar.exact 0)))).comparison with
  | .equal _ => true
  | .distinct _ _ => false) = true := by
  have known : NamedEquivalent zeroGeneratorEndpoint.channel.name zeroEndpoint.channel.name := by
    change NamedEquivalent ((Expression.generator (radicand := DensePolynomial.constant 0)).denote
      0 (Coherence.exact 0)).name ((Expression.scalar coordinate).denote 0 (Coherence.exact 0)).name
    apply NamedEquivalent.trans (Expression.denote_generator 0 (Coherence.exact 0))
    have scalar := Expression.denote_scalar (radicand := DensePolynomial.constant 0) coordinate 0 (Coherence.exact 0)
    have value : coordinate.eval 0 = 0 := by decide +kernel
    rewrite [value] at scalar
    exact scalar.symm
  cases found : ((zeroGeneratorEndpoint.sidecar
      (Algebraic.Sidecar.ofRational (Rational.Basic.RationalSidecar.exact 0))).compare
        (zeroEndpoint.sidecar (Algebraic.Sidecar.ofRational (Rational.Basic.RationalSidecar.exact 0)))).comparison with
  | equal equivalent => rfl
  | distinct prepared different => exact (different ⟨known⟩).elim

example : NamedEquivalent admittedForward.numerical.program.output.name
    (primitiveDifference (bank 0).channel (bank 1).channel).name :=
  admittedForward.numerical.integral_eq_difference

/-- The original exact reverse cell uses the same original spatial unit differential. -/
private def backwardCell : Cell.Basic.CellModel := Cell.Basic.CellModel.exact 1 0 ⟨[1]⟩

/-- The original constant refinement program for the reverse oriented cell. -/
private def backwardProgram := Purelib.Integration.Program.Gaussian.Basic.RefinementProgram.exactPolynomial 1 0 ⟨[1]⟩

/-- The reverse lifted cell retains the actual same-sheet endpoint transport. -/
private def backwardLiftCell : LiftedCell (bank 1).point (bank 0).point :=
  ⟨Data.Fin.Bijection.identity 2, rfl⟩

/-- The actual original reverse lifted path. -/
private def backwardLift : LiftedPath 2 (bank 1).point (bank 0).point :=
  .cons backwardLiftCell (.nil (bank 0).point)

/-- The reverse local primitive is one minus the original unit parameter. -/
private def backwardComparison : Cell.Primitive.Comparison backwardCell :=
  Cell.Primitive.Comparison.build backwardCell ⟨[-1, 1]⟩

/-- Source-owned backward finite models derive the numerical primitive comparison internally. -/
private def backwardModels : PrimitiveEdge.PolynomialModels (bank 1).point (bank 0).point
    (sampling 1).source (sampling 0).source backwardProgram where
  value := fun _ => coordinate
  lifted := fun _ => backwardLift
  follows := fun _ => .cons rfl rfl (.nil _)
  cellComparison := fun _ cell member => by
    change cell ∈ [backwardCell] at member
    have equal : cell = backwardCell := (Membership.mem_singleton.mp member)
    cases equal
    exact backwardComparison
  localStart := by
    intro index cell member
    change cell ∈ [backwardCell] at member
    have equal : cell = backwardCell := Membership.mem_singleton.mp member
    cases equal
    change backwardComparison.value.eval 0 = coordinate.eval backwardCell.start
    decide +kernel
  localFinish := by
    intro index cell member
    change cell ∈ [backwardCell] at member
    have equal : cell = backwardCell := Membership.mem_singleton.mp member
    cases equal
    change backwardComparison.value.eval 1 = coordinate.eval backwardCell.finish
    decide +kernel
  endpointBound := fun _ => 0
  startError := by
    intro index
    unfold sampling
    rewrite [Endpoint.sampleScalar_source, Approximation.Gaussian.Geometric.GeometricApproximation.exact_sample,
      Data.Gaussian.Basic.sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
    exact Order.Basic.le_refl _
  finishError := by
    intro index
    unfold sampling
    rewrite [Endpoint.sampleScalar_source, Approximation.Gaussian.Geometric.GeometricApproximation.exact_sample,
      Data.Gaussian.Basic.sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
    exact Order.Basic.le_refl _
  localBound := fun _ => 0
  localBound_le := by
    intro index cell member
    change cell ∈ [backwardCell] at member
    have equal : cell = backwardCell := Membership.mem_singleton.mp member
    cases equal
    change backwardComparison.bound ≤ (0 : Data.Rat.Fraction.Rational)
    decide +kernel
  scale := 0
  scale_nonnegative := Order.Basic.le_refl _
  budget_le := by
    intro index
    simp only [Data.Rat.Fraction.Field.mul_zero_direct, Data.Rat.Fraction.Field.zero_add]
    exact Approximation.Rational.Geometric.Basic.quarterRadius_nonneg (Order.Basic.le_refl _) index

/-- The reverse admission retains the same formal primitive and its own actual source integration program. -/
private def admittedBackward : EdgeAdmission bank backward :=
  EdgeAdmission.build bank backward differential checked rfl (HEq.rfl)
    (sampling 1) (sampling 0) backwardProgram backwardModels

/-- Store both actual source admissions in their original occurrence order. -/
private def admissions : Admissions bank occurrences := .cons admittedForward (.cons admittedBackward .nil)

/-- The actual forward integration program with its original endpoint owners. -/
private def openPath : PrimitivePath (bank 0).channel (bank 1).channel :=
  .cons admittedForward.numerical (.nil (bank 1).channel)

example (startEvidence : Algebraic.Sidecar (bank 0).channel)
    (finishEvidence : Algebraic.Sidecar (bank 1).channel) (index : Nat) :
    (openPath.integralSumSidecar startEvidence finishEvidence).residual.source.sample index =
      (startEvidence.neg.add finishEvidence).residual.source.sample index :=
  (startEvidence.neg.add finishEvidence).transport_sample openPath.integralSum_eq_difference index

/-- The nonempty source loop closes through literal original lifted endpoint ownership. -/
private def closedLoop : ClosedPrimitiveBoundary := Admissions.closed bank occurrences admissions loopPath

example : NamedEquivalent closedLoop.integralSum.name (Coherence.exact 0).name := closedLoop.integralSum_zero

example : closedLoop.integralSumSidecar.scalar?.map (fun reading => reading.value) = some 0 := rfl

example : closedLoop.integralSumSidecar.decide.isPrepared = false := rfl

/-- A bank distinguishes identical base coordinates on different original selected sheets. -/
private def sheetBank : EndpointBank Unit 2 2 polynomialAt rootAt :=
  .cons (endpoint 0 0) (.cons (endpoint 0 1) .nil)

example : (boundary sheetBank [forward] 0 1 (.cons (.nil _))).coefficients 1 = 1 :=
  (boundary sheetBank [forward] 0 1 (.cons (.nil _))).sheetChanging_finish (by decide +kernel)

example : (0 : Fin 2) ≠ 1 :=
  (boundary sheetBank [forward] 0 1 (.cons (.nil _))).sheetChanging_not_closed (by decide +kernel)

namespace Normalization

open Purelib.Polynomial.Dense.Gaussian.Squarefree
open Purelib.Integration.Algebraic.SquareFactor
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Data.Gaussian
open Purelib.Approximation.Gaussian.Arithmetic

attribute [local irreducible] CertifiedSquareRoot.rawRoot

/-- The normalization map `2 = (1/2)^2 * 8`, with its actual finite coefficient certificate. -/
private def reduction : SquareFactor.Basic.Reduction (DensePolynomial.constant (2 : Canonical)) :=
  { squareFactor := DensePolynomial.constant ⟨1 / 2, 0⟩
    radicand := DensePolynomial.constant 8
    squareFactorNonzero := by decide +kernel
    radicandNonzero := by decide +kernel
    squareFactorNormalized := by decide +kernel
    radicandNormalized := by decide +kernel
    squarefree := Constants.constant 8 (by decide +kernel)
    identity := by decide +kernel }

/-- The inverse chart map `8 = 2^2 * 2`, checked in the same original coefficient representation. -/
private def expansion : SquareFactor.Basic.Reduction (DensePolynomial.constant (8 : Canonical)) :=
  { squareFactor := DensePolynomial.constant 2
    radicand := DensePolynomial.constant 2
    squareFactorNonzero := by decide +kernel
    radicandNonzero := by decide +kernel
    squareFactorNormalized := by decide +kernel
    radicandNormalized := by decide +kernel
    squarefree := Constants.constant 2 (by decide +kernel)
    identity := by decide +kernel }

/-- The two actual chart polynomials have different original radicands. -/
private def polynomial : Bool → Coefficients
  | false => DensePolynomial.constant 2
  | true => DensePolynomial.constant 8

/-- Reuse the original isolated root through the actual inverse coordinate-map operation. -/
private def normalizedRoot (point : LiftedPoint 2) : RootReading := by
  let original : (channel : CoherentNamed) × SquareRootSidecar.Sidecar channel := rootAt () point
  let channel := NamedTransport.coordinateName expansion point.coordinate original.1
  have square : NamedEquivalent (CoherentNamed.mul original.1 original.1).name
      (Coherence.exact (expansion.radicand.eval point.coordinate)).name := by
    have parameter : expansion.radicand.eval point.coordinate = (2 : Canonical) :=
      DensePolynomial.eval_constant _ _
    rewrite [parameter]
    have retained := original.2.square
    have parameterEq : original.2.parameter = 2 := roots_parameter point.sheet
    rewrite [parameterEq] at retained
    exact retained
  have transported := NamedTransport.coordinate_square expansion point.coordinate original.1 square
  have originalParameter : (DensePolynomial.constant (8 : Canonical)).eval point.coordinate = 8 :=
    DensePolynomial.eval_constant _ _
  rewrite [originalParameter] at transported
  exact ⟨channel, ⟨8, transported, none⟩⟩

/-- Each endpoint reads its actual original or normalized chart channel without re-isolating the normalized root. -/
private def root : Bool → LiftedPoint 2 → RootReading
  | false, point => rootAt () point
  | true, point => normalizedRoot point

/-- The original scalar primitive retains the same original endpoint and numerical channel. -/
private def source (key : Fin 2) : Endpoint Bool 2 polynomial root :=
  Endpoint.retain polynomial root false (bank key).point (Expression.scalar coordinate)
    ((roots_parameter (bank key).point.sheet).trans
      (DensePolynomial.eval_constant (2 : Canonical) (bank key).point.coordinate).symm)
    (Expression.defined_scalar coordinate (bank key).point.coordinate)

/-- The same scalar primitive in the normalized chart retains its distinct radicand and transported root. -/
private def target (key : Fin 2) : Endpoint Bool 2 polynomial root :=
  Endpoint.retain polynomial root true (bank key).point (Expression.scalar coordinate)
    (by
      change (normalizedRoot (bank key).point).2.parameter = (DensePolynomial.constant (8 : Canonical)).eval _
      unfold normalizedRoot
      exact (DensePolynomial.eval_constant (8 : Canonical) (bank key).point.coordinate).symm)
    (Expression.defined_scalar coordinate (bank key).point.coordinate)

/-- The source presentation preserves the actual endpoint denotation used by both original programs. -/
private theorem source_channel (key : Fin 2) : (source key).channel = (bank key).channel := by
  cases key with
  | mk key bound =>
    cases key with
    | zero => rfl
    | succ key =>
      cases key with
      | zero => rfl
      | succ key => exact False.elim (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ bound)))

/-- The original selected root equals its normalization factor times the same transported root channel. -/
private def normalizedRoot_equivalent (point : LiftedPoint 2) : NamedEquivalent (root false point).1.name
    (CoherentNamed.mul (Coherence.exact (reduction.squareFactor.eval point.coordinate)) (root true point).1).name := by
  let original := (rootAt () point).1
  have associated := Product.Laws.coherentMul_assoc (Coherence.exact ⟨1 / 2, 0⟩) (Coherence.exact 2) original
  have factor := Product.Congruence.coherentMul_respects
    (CoherentNamed.mul (Coherence.exact ⟨1 / 2, 0⟩) (Coherence.exact 2)) (Coherence.exact 1)
    original original (by
      have product := Exact.Arithmetic.exact_mul (⟨1 / 2, 0⟩ : Canonical) 2
      rewrite [show (⟨1 / 2, 0⟩ : Canonical) * 2 = 1 by decide +kernel] at product
      exact product) (NamedEquivalent.refl _)
  have comparison := ((factor.trans (Mul.coherentMul_one_left original)).symm).trans associated
  have scalar : reduction.squareFactor.eval point.coordinate = (⟨1 / 2, 0⟩ : Canonical) :=
    DensePolynomial.eval_constant _ _
  have normalizedChannel : (root true point).1 = CoherentNamed.mul (Coherence.exact 2) original := by
    change NamedTransport.coordinateName expansion point.coordinate original = _
    unfold NamedTransport.coordinateName
    rewrite [show expansion.squareFactor.eval point.coordinate = (2 : Canonical) from
      DensePolynomial.eval_constant _ _]
    rfl
  rewrite [scalar, normalizedChannel]
  exact comparison

/-- The map ownership identifies both actual chart labels, the shared lifted endpoint and the retained map point. -/
private def belongs (owner : SquareFactor.Basic.Reduction (DensePolynomial.constant (2 : Canonical)) × Canonical)
    (left right : Endpoint Bool 2 polynomial root) : Prop :=
  owner.1 = reduction ∧ left.chart = false ∧ right.chart = true ∧
    left.point = right.point ∧ left.point.coordinate = owner.2 ∧ owner.1.squareFactor.eval owner.2 ≠ 0

/-- Compute the actual scalar primitive transport attempt through the original normalization map. -/
private def attempt (key : Fin 2) := Endpoint.prepareTransport belongs
  (fun owner => owner.1.squareFactor.eval owner.2) ⟨reduction, (bank key).point.coordinate⟩ (source key) (target key)
  ⟨rfl, rfl, rfl, rfl, rfl, by
    change (DensePolynomial.constant (⟨1 / 2, 0⟩ : Canonical)).eval (bank key).point.coordinate ≠ 0
    rewrite [DensePolynomial.eval_constant]
    decide +kernel⟩ (normalizedRoot_equivalent (bank key).point)

/-- The actual retained scalar coefficient checks vanish without equating unlike quadratic pairs. -/
private theorem attempt_zero (key : Fin 2) : (attempt key).realDifference = 0 ∧
    (attempt key).imaginaryDifference = 0 := by
  constructor
  · change (source key).denotation.value.re - (target key).denotation.value.re = 0
    rewrite [(source key).denotation.value_eq, (target key).denotation.value_eq]
    change ((Expression.scalar (radicand := polynomial false) coordinate).evaluate
      (bank key).point.coordinate).re - ((Expression.scalar (radicand := polynomial true) coordinate).evaluate
      (bank key).point.coordinate).re = 0
    rewrite [Expression.evaluate_scalar, Expression.evaluate_scalar]
    exact Basic.sub_self _
  · change (source key).denotation.value.im * _ - (target key).denotation.value.im = 0
    rewrite [(source key).denotation.value_eq, (target key).denotation.value_eq]
    change ((Expression.scalar (radicand := polynomial false) coordinate).evaluate
      (bank key).point.coordinate).im * _ - ((Expression.scalar (radicand := polynomial true) coordinate).evaluate
      (bank key).point.coordinate).im = 0
    rewrite [Expression.evaluate_scalar, Expression.evaluate_scalar]
    change (0 : Canonical) * _ - 0 = 0
    rewrite [Basic.zero_mul, Basic.sub_self]
    rfl

/-- Execute the actual explanatory checker and retain its certified chart correspondence. -/
private def checked (key : Fin 2) : Endpoint.Transport (attempt key) :=
  match (attempt key).check with
  | .transported certificate => certificate
  | .realObstructed nonzero => False.elim (nonzero (attempt_zero key).1)
  | .imaginaryObstructed _ nonzero => False.elim (nonzero (attempt_zero key).2)

/-- The original forward edge retains its actual program under the source chart presentation. -/
private def forwardEdge : PrimitiveEdge (source 0).channel (source 1).channel :=
  admittedForward.numerical.changeEndpoints _ _
    (by rewrite [source_channel]; exact NamedEquivalent.refl _)
    (by rewrite [source_channel]; exact NamedEquivalent.refl _)

/-- The original reverse edge uses the normalized chart through the actual checked endpoint maps. -/
private def backwardEdge : PrimitiveEdge (target 1).channel (target 0).channel :=
  admittedBackward.numerical.changeEndpoints _ _
    (by
      have comparison := (checked 1).equivalent
      rewrite [source_channel] at comparison
      exact comparison)
    (by
      have comparison := (checked 0).equivalent
      rewrite [source_channel] at comparison
      exact comparison)

/-- The actual forward and reverse programs are joined at their checked cross-chart endpoint. -/
private def joined : PrimitivePath (source 0).channel (target 0).channel :=
  (checked 1).overlap forwardEdge (.cons backwardEdge (.nil _))

/-- Close the original two-program path using the actual inverse of its initial endpoint transport. -/
private def loop : ClosedPrimitiveBoundary :=
  ⟨(source 0).channel, (target 0).channel, joined, (checked 0).equivalent.symm⟩

/-- The cross-chart path retains both original finite integration programs and its certified endpoint cancellation. -/
private def loop_integral_zero : NamedEquivalent loop.integralSum.name (Coherence.exact 0).name :=
  loop.integralSum_zero

/-- The cross-chart change preserves the actual forward integration program. -/
private theorem forward_program : forwardEdge.program = forwardProgram :=
  admittedForward.numerical_program

/-- The cross-chart change preserves the actual reverse integration program. -/
private theorem backward_program : backwardEdge.program = backwardProgram :=
  admittedBackward.numerical_program

/-- The original formal generator at a retained endpoint on either independently selected sheet. -/
private def generatorSource (sheet : Fin 2) : Endpoint Bool 2 polynomial root :=
  Endpoint.retain polynomial root false ⟨1, sheet⟩ Expression.generator
    ((roots_parameter sheet).trans (DensePolynomial.eval_constant (2 : Canonical) 1).symm)
    (Expression.defined_generator 1)

/-- The normalized formal generator with the actual map's inverse scalar coefficient. -/
private def generatorTarget (sheet : Fin 2) : Endpoint Bool 2 polynomial root :=
  Endpoint.retain polynomial root true ⟨1, sheet⟩
    (Expression.scale (DensePolynomial.constant ⟨1 / 2, 0⟩) Expression.generator)
    (by
      change (normalizedRoot ⟨1, sheet⟩).2.parameter = (DensePolynomial.constant (8 : Canonical)).eval 1
      unfold normalizedRoot
      exact (DensePolynomial.eval_constant (8 : Canonical) 1).symm)
    (Expression.defined_scale _ _ _ (Expression.defined_generator 1))

/-- The nonzero generator coefficient uses the same original normalization map and retained selected roots. -/
private def generatorAttempt (sheet : Fin 2) := Endpoint.prepareTransport belongs
  (fun owner => owner.1.squareFactor.eval owner.2) ⟨reduction, 1⟩ (generatorSource sheet) (generatorTarget sheet)
  ⟨rfl, rfl, rfl, rfl, rfl, by
    change (DensePolynomial.constant (⟨1 / 2, 0⟩ : Canonical)).eval 1 ≠ 0
    rewrite [DensePolynomial.eval_constant]
    decide +kernel⟩ (normalizedRoot_equivalent ⟨1, sheet⟩)

/-- The cached generator coefficients transport through the actual scalar factor on both original sheets. -/
private theorem generator_checks (sheet : Fin 2) : (generatorAttempt sheet).realDifference = 0 ∧
    (generatorAttempt sheet).imaginaryDifference = 0 := by
  have sourceValue := (generatorSource sheet).denotation.value_eq
  change _ = (Expression.generator (radicand := polynomial false)).evaluate 1 at sourceValue
  rewrite [Expression.evaluate_generator] at sourceValue
  have targetValue := (generatorTarget sheet).denotation.value_eq
  change _ = (Expression.scale (DensePolynomial.constant (⟨1 / 2, 0⟩ : Canonical))
    (Expression.generator (radicand := polynomial true))).evaluate 1 at targetValue
  rewrite [Expression.evaluate_scale, Expression.evaluate_generator, DensePolynomial.eval_constant] at targetValue
  constructor
  · change (generatorSource sheet).denotation.value.re - (generatorTarget sheet).denotation.value.re = 0
    rewrite [sourceValue, targetValue]
    change (0 : Canonical) - (⟨1 / 2, 0⟩ : Canonical) * 0 = 0
    rewrite [Basic.mul_zero, Basic.sub_self]
    rfl
  · change (generatorSource sheet).denotation.value.im * _ - (generatorTarget sheet).denotation.value.im = 0
    rewrite [sourceValue, targetValue]
    change (1 : Canonical) * (DensePolynomial.constant (⟨1 / 2, 0⟩ : Canonical)).eval 1 -
      (⟨1 / 2, 0⟩ : Canonical) * 1 = 0
    rewrite [DensePolynomial.eval_constant, Basic.one_mul, Basic.mul_one, Basic.sub_self]
    rfl

/-- Execute the original coefficient checker for the nonzero generator coefficient on either selected sheet. -/
private def generatorChecked (sheet : Fin 2) : Endpoint.Transport (generatorAttempt sheet) :=
  match (generatorAttempt sheet).check with
  | .transported certificate => certificate
  | .realObstructed nonzero => False.elim (nonzero (generator_checks sheet).1)
  | .imaginaryObstructed _ nonzero => False.elim (nonzero (generator_checks sheet).2)

/-- The original generator agrees with its normalized expression using the retained actual root transport. -/
private def generator_equivalent (sheet : Fin 2) :
    NamedEquivalent (generatorSource sheet).channel.name (generatorTarget sheet).channel.name :=
  (generatorChecked sheet).equivalent

end Normalization

end TestPurelib.Integration.AlgebraicPrimitive
