module

public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Homogeneous
public import Purelib.Approximation.Gaussian.Provenance.Algebraic
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Algebraic evidence for original integral fractional rows

Each row retains the actual matrix and original input channel. Its affine
construction uses the original integral coefficients and transports its
evidence through the existing homogeneous row comparison.
-/

public section

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Algebraic

open Purelib.Approximation.Gaussian.Provenance.Algebraic (Sidecar)
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Division
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Data.Gaussian
open Purelib.LinearAlgebra.Matrix.Basic (IntegralMatrix)
open Purelib.Riemann.Integration.LegendreModularMonodromy
  (fractionalRow fractionalDenominator fractionalNumerator fractionalLinear)

variable {tau : CoherentNamed}

/-- An original algebraic input at its unchanged coherent channel. -/
@[expose] def InputSidecar (tau : CoherentNamed) : Type 1 := Sidecar tau

/-- A retained coherent channel of an original integral fractional row. -/
@[expose] def RowChannel : Type 1 := CoherentNamed

/-- Algebraic evidence at a retained original row channel. -/
@[expose] def RowEvidence (channel : RowChannel) : Type 1 := Sidecar channel

/-- The original integral fractional row at its requested matrix and input. -/
@[expose] def rowChannel (tau : CoherentNamed) (matrix : IntegralMatrix) (index : Fin 2) : RowChannel :=
  fractionalRow matrix tau index

/-- Algebraic evidence at one actual integral fractional row. -/
@[expose] def RowSidecar (tau : CoherentNamed) (matrix : IntegralMatrix) (index : Fin 2) : Type 1 :=
  RowEvidence (rowChannel tau matrix index)

/-- Construct row evidence at the supplied actual original channel.

The channel equality ties that exact object to the original matrix row. The
affine evidence uses the original input and signed coefficients, and the
existing row comparison transports it to the retained channel. -/
@[expose, noinline, nospecialize] def rowAt (input : InputSidecar tau)
    (matrix : IntegralMatrix) (index : Fin 2) (channel : RowChannel)
    (same : channel = rowChannel tau matrix index) : RowEvidence channel := by
  let constantName := Coherence.exact (Cast.integralGaussian (matrix index 0))
  let coefficientName := Coherence.exact (Cast.integralGaussian (matrix index 1))
  let productName := CoherentNamed.mul coefficientName tau
  let affineName := CoherentNamed.add constantName productName
  let constant := Sidecar.ofRational
    (RationalSidecar.exact (Cast.integralGaussian (matrix index 0)))
  let coefficient := Sidecar.ofRational
    (RationalSidecar.exact (Cast.integralGaussian (matrix index 1)))
  let product := @Sidecar.mul coefficientName tau coefficient input
  let affine := @Sidecar.add constantName productName constant product
  have comparison : NamedEquivalent channel.name affineName.name := by
    exact same.symm ▸ Homogeneous.fractionalRow_affine matrix tau index
  exact @Sidecar.transport affineName channel affine comparison

/-- Construct evidence for the original matrix row using the retained input and signed coefficients. -/
@[expose, noinline, nospecialize] def row (input : InputSidecar tau)
    (matrix : IntegralMatrix) (index : Fin 2) : RowSidecar tau matrix index :=
  rowAt input matrix index (rowChannel tau matrix index) rfl

section

attribute [local irreducible] InputSidecar RowChannel RowEvidence rowChannel

set_option genInjectivity false in
/-- Both original row sidecars, cached for one retained input and requested matrix. -/
structure Rows (input : InputSidecar tau) (matrix : IntegralMatrix) where
  /-- The complete original algebraic input. -/
  source : InputSidecar tau
  /-- The retained source is the original input. -/
  source_eq : source = input
  /-- The complete original matrix request. -/
  request : IntegralMatrix
  /-- The retained matrix is the original request. -/
  request_eq : request = matrix
  /-- The actual retained denominator row channel. -/
  denominator : RowChannel
  /-- The retained channel is the original requested denominator row. -/
  denominator_eq : denominator = rowChannel tau matrix 0
  /-- The original algebraic evidence indexed by that exact retained channel. -/
  denominatorEvidence : RowEvidence denominator
  /-- The retained evidence is constructed from the original input and request. -/
  denominatorEvidence_eq :
    Eq.ndrec (motive := fun channel : RowChannel => RowEvidence channel)
      denominatorEvidence denominator_eq = row input matrix 0
  /-- The actual retained numerator row channel. -/
  numerator : RowChannel
  /-- The retained channel is the original requested numerator row. -/
  numerator_eq : numerator = rowChannel tau matrix 1
  /-- The original algebraic evidence indexed by that exact retained channel. -/
  numeratorEvidence : RowEvidence numerator
  /-- The retained evidence is constructed from the original input and request. -/
  numeratorEvidence_eq :
    Eq.ndrec (motive := fun channel : RowChannel => RowEvidence channel)
      numeratorEvidence numerator_eq = row input matrix 1

constructive_injectivity Rows

end

/-- Compute and retain both original row constructions once, without dividing. -/
@[expose, noinline, nospecialize] def readRows (input : Sidecar tau)
    (matrix : IntegralMatrix) : Rows input matrix :=
  let denominator := rowChannel tau matrix 0
  let numerator := rowChannel tau matrix 1
  let denominatorEvidence := rowAt input matrix 0 denominator rfl
  let numeratorEvidence := rowAt input matrix 1 numerator rfl
  ⟨input, rfl, matrix, rfl, denominator, rfl, denominatorEvidence, rfl,
    numerator, rfl, numeratorEvidence, rfl⟩

/-- Decide the actual cached denominator, retaining its exact zero or equivalent prepared presentation. -/
@[expose, noinline, nospecialize] def Rows.decide {input : Sidecar tau} {matrix : IntegralMatrix}
    (rows : Rows input matrix) : Prepared.Decision (fractionalDenominator matrix tau) :=
  Eq.ndrec (motive := fun channel => Prepared.Decision channel)
    rows.denominatorEvidence.decide rows.denominator_eq

/-- Reuse a successful decision at the original matrix-indexed denominator. -/
@[expose] def Rows.toPreparation {input : Sidecar tau} {matrix : IntegralMatrix}
    (rows : Rows input matrix) (prepared : Prepared (fractionalDenominator matrix tau))
    (_computed : rows.decide = .prepared prepared) :
    Prepared.DenominatorPreparation (fractionalDenominator matrix tau) :=
  ⟨prepared.denominator, prepared.apart, prepared.equivalent⟩

/-- An actual fractional output and its algebraic evidence at one original preparation. -/
@[expose] def Action (tau : CoherentNamed) (matrix : IntegralMatrix)
    (preparation : Prepared.DenominatorPreparation (fractionalDenominator matrix tau)) : Type 1 :=
  Σ output : { value : CoherentNamed // value = fractionalLinear matrix tau preparation },
    Sidecar output.val

/-- Construct and retain the actual action output using the same cached prepared denominator.

The numerator and reciprocal channels are shared by the retained output and
its sidecar. The reciprocal consumes this exact preparation and denominator
cache, and the returned identity ties the output to the original action. -/
@[expose, noinline, nospecialize] def Rows.outputPrepared {input : Sidecar tau}
    {matrix : IntegralMatrix} (rows : Rows input matrix) (prepared : Prepared (fractionalDenominator matrix tau)) :
    Action tau matrix ⟨prepared.denominator, prepared.apart, prepared.equivalent⟩ := by
  let direct : Prepared rows.denominator :=
    Eq.ndrec (motive := fun channel => Prepared channel) prepared rows.denominator_eq.symm
  let cache := Polynomial.Approximation.Gaussian.Residual.Reciprocal.ofPrepared
    rows.denominatorEvidence.residual direct
  let numerator := rows.numerator
  let reciprocal := direct.quotient (Coherence.exact 1)
  let output := CoherentNamed.mul numerator reciprocal
  let evidence := @Sidecar.mul numerator reciprocal rows.numeratorEvidence
    (rows.denominatorEvidence.reciprocalFromCache cache)
  have quotient_eq : reciprocal = prepared.quotient (Coherence.exact 1) := by
    have reindex {first second : CoherentNamed} (same : first = second)
        (value : Prepared second) (numerator : CoherentNamed) :
        (Eq.ndrec (motive := fun channel => Prepared channel) value same.symm).quotient numerator =
          value.quotient numerator := by
      cases same
      rfl
    exact reindex rows.denominator_eq prepared (Coherence.exact 1)
  have output_eq : output =
      fractionalLinear matrix tau ⟨prepared.denominator, prepared.apart, prepared.equivalent⟩ := by
    change CoherentNamed.mul rows.numerator reciprocal = _
    rewrite [rows.numerator_eq, quotient_eq]
    rfl
  exact ⟨⟨output, output_eq⟩, evidence⟩

/-- Attach cached row evidence to an existing original denominator preparation. -/
@[expose] def Rows.output {input : Sidecar tau} {matrix : IntegralMatrix}
    (rows : Rows input matrix) (preparation : Prepared.DenominatorPreparation (fractionalDenominator matrix tau)) :
    Action tau matrix preparation :=
  rows.outputPrepared ⟨preparation.prepared, preparation.apart, preparation.equivalent⟩

/-- Repackaging a computed preparation retains the complete original action construction. -/
theorem Rows.outputPrepared_eq_output {input : Sidecar tau} {matrix : IntegralMatrix}
    (rows : Rows input matrix) (prepared : Prepared (fractionalDenominator matrix tau))
    (computed : rows.decide = .prepared prepared) :
    rows.outputPrepared prepared = rows.output (rows.toPreparation prepared computed) := by
  cases prepared
  rfl

/-- A successful row cache and its actual action at the same prepared denominator. -/
@[expose] def Head {input : Sidecar tau} {matrix : IntegralMatrix}
    (rows : Rows input matrix) (preparation : Prepared.DenominatorPreparation (fractionalDenominator matrix tau)) :
    Type 1 :=
  Σ source : { value : Rows input matrix // value = rows },
    Σ prepared : { value : Prepared (fractionalDenominator matrix tau) // source.val.decide = .prepared value },
      { action : Action tau matrix preparation // action = source.val.output preparation ∧
        preparation = source.val.toPreparation prepared.val prepared.property }

/-- Read the exact retained original row cache of a successful head. -/
@[expose] def Head.source {input : Sidecar tau} {matrix : IntegralMatrix}
    {rows : Rows input matrix} {preparation : Prepared.DenominatorPreparation (fractionalDenominator matrix tau)}
    (head : Head rows preparation) : Rows input matrix := head.1.val

/-- The successful head retains the same supplied row cache. -/
theorem Head.source_eq {input : Sidecar tau} {matrix : IntegralMatrix}
    {rows : Rows input matrix} {preparation : Prepared.DenominatorPreparation (fractionalDenominator matrix tau)}
    (head : Head rows preparation) : head.source = rows := head.1.property

/-- Read the exact equivalent denominator presentation computed by the retained rows. -/
@[expose] def Head.prepared {input : Sidecar tau} {matrix : IntegralMatrix}
    {rows : Rows input matrix} {preparation : Prepared.DenominatorPreparation (fractionalDenominator matrix tau)}
    (head : Head rows preparation) : Prepared (fractionalDenominator matrix tau) := head.2.1.val

/-- The retained denominator presentation is the actual decision of the same cached rows. -/
theorem Head.decision_eq {input : Sidecar tau} {matrix : IntegralMatrix}
    {rows : Rows input matrix} {preparation : Prepared.DenominatorPreparation (fractionalDenominator matrix tau)}
    (head : Head rows preparation) : head.source.decide = .prepared head.prepared := head.2.1.property

/-- Read the actual retained output and sidecar of a successful head. -/
@[expose] def Head.action {input : Sidecar tau} {matrix : IntegralMatrix}
    {rows : Rows input matrix} {preparation : Prepared.DenominatorPreparation (fractionalDenominator matrix tau)}
    (head : Head rows preparation) : Action tau matrix preparation := head.2.2.val

/-- The retained action uses the same cached rows and original preparation. -/
theorem Head.action_eq {input : Sidecar tau} {matrix : IntegralMatrix}
    {rows : Rows input matrix} {preparation : Prepared.DenominatorPreparation (fractionalDenominator matrix tau)}
    (head : Head rows preparation) : head.action = head.source.output preparation := head.2.2.property.1

/-- The original matrix preparation is the conversion of the same retained decision. -/
theorem Head.preparation_eq {input : Sidecar tau} {matrix : IntegralMatrix}
    {rows : Rows input matrix} {preparation : Prepared.DenominatorPreparation (fractionalDenominator matrix tau)}
    (head : Head rows preparation) :
    preparation = head.source.toPreparation head.prepared head.decision_eq := head.2.2.property.2

/-- A cached original row and the exact zero decision computed for its denominator. -/
@[expose] def Obstruction {input : Sidecar tau} {matrix : IntegralMatrix}
    (rows : Rows input matrix) : Type 1 :=
  Σ source : { value : Rows input matrix // value = rows },
    { zero : Zero.ZeroIdentity (fractionalDenominator matrix tau) // source.val.decide = .excluded zero }

/-- Read the original row cache retained by an exact zero obstruction. -/
@[expose] def Obstruction.source {input : Sidecar tau} {matrix : IntegralMatrix}
    {rows : Rows input matrix} (obstruction : Obstruction rows) : Rows input matrix := obstruction.1.val

/-- The obstruction retains the same original row cache. -/
theorem Obstruction.source_eq {input : Sidecar tau} {matrix : IntegralMatrix}
    {rows : Rows input matrix} (obstruction : Obstruction rows) : obstruction.source = rows :=
  obstruction.1.property

/-- Read the exact original denominator's operational zero identity. -/
@[expose] def Obstruction.zero {input : Sidecar tau} {matrix : IntegralMatrix}
    {rows : Rows input matrix} (obstruction : Obstruction rows) :
    Zero.ZeroIdentity (fractionalDenominator matrix tau) := obstruction.2.val

/-- The zero identity is the actual decision of the retained original rows. -/
theorem Obstruction.decision_eq {input : Sidecar tau} {matrix : IntegralMatrix}
    {rows : Rows input matrix} (obstruction : Obstruction rows) :
    obstruction.source.decide = .excluded obstruction.zero := obstruction.2.property

/-- Execute the original fractional action or report its exact zero denominator.

The successful branch consumes the cached denominator decision and numerator
row, constructs the reciprocal cache once, and indexes the output evidence by
the actual action using the same prepared denominator. -/
@[expose, noinline, nospecialize] def Rows.step {input : Sidecar tau} {matrix : IntegralMatrix}
    (rows : Rows input matrix) :
    Except (Obstruction rows)
      (Σ preparation : Prepared.DenominatorPreparation (fractionalDenominator matrix tau),
        Head rows preparation) := by
  match computed : rows.decide with
  | .excluded zero => exact .error ⟨⟨rows, rfl⟩, ⟨zero, computed⟩⟩
  | .prepared prepared =>
      let preparation := rows.toPreparation prepared computed
      let action := rows.outputPrepared prepared
      exact .ok ⟨preparation, ⟨⟨rows, rfl⟩, ⟨⟨prepared, computed⟩,
        ⟨action, ⟨rows.outputPrepared_eq_output prepared computed, rfl⟩⟩⟩⟩⟩

end Purelib.Approximation.Gaussian.FractionalAction.Integral.Algebraic

end
