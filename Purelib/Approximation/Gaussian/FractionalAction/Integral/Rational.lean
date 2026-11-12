module

public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Homogeneous
public import Purelib.Approximation.Gaussian.Provenance.Rational.Division
public import Purelib.Approximation.Gaussian.Division.Prepared.Rational
import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Riemann.Integration.LegendreModularMonodromy
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Exact rational readings of original integral fractional actions

Both actual matrix rows retain their original input and exact coefficient
readings. A successful denominator check prepares that same row, computes
the actual numerical action and propagates its exact rational reading.
-/

public section

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Rational

open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Division
open Purelib.Data.Gaussian
open Purelib.LinearAlgebra.Matrix.Basic (IntegralMatrix)
open Purelib.Riemann.Integration.LegendreModularMonodromy
  (fractionalRow fractionalDenominator fractionalNumerator fractionalLinear)

variable {tau : CoherentNamed}

/-- Read an original matrix row using the actual retained rational input and integer coefficients. -/
@[noinline, nospecialize] def row (input : RationalSidecar tau) (matrix : IntegralMatrix) (index : Fin 2) :
    RationalSidecar (fractionalRow matrix tau index) :=
  let constant := RationalSidecar.exact (Cast.integralGaussian (matrix index 0))
  let coefficient := RationalSidecar.exact (Cast.integralGaussian (matrix index 1))
  let affine := constant.add (coefficient.mul input)
  ⟨affine.value, NamedEquivalent.trans (Homogeneous.fractionalRow_affine matrix tau index) affine.equivalent⟩

/-- The row's exact reading is computed from the same retained input and original signed coefficients. -/
theorem row_value (input : RationalSidecar tau) (matrix : IntegralMatrix) (index : Fin 2) :
    (row input matrix index).value = Cast.integralGaussian (matrix index 0) +
      Cast.integralGaussian (matrix index 1) * input.value :=
  (Eq.refl _).trans (Eq.refl _)

set_option genInjectivity false in
/-- Both original matrix rows and exact readings, retaining the complete original input and request. -/
structure Rows (input : RationalSidecar tau) (matrix : IntegralMatrix) where
  /-- The exact original input sidecar. -/
  source : RationalSidecar tau
  /-- The retained source is the original input. -/
  source_eq : source = input
  /-- The entire original requested matrix. -/
  request : IntegralMatrix
  /-- The retained request is the original matrix. -/
  request_eq : request = matrix
  /-- The actual original denominator channel. -/
  denominator : CoherentNamed
  /-- The cache is the original matrix's first row. -/
  denominator_eq : denominator = fractionalDenominator matrix tau
  /-- The exact reading at this same actual denominator. -/
  denominatorReading : RationalSidecar denominator
  /-- The actual original numerator channel. -/
  numerator : CoherentNamed
  /-- The cache is the original matrix's second row. -/
  numerator_eq : numerator = fractionalNumerator matrix tau
  /-- The exact reading at this same actual numerator. -/
  numeratorReading : RationalSidecar numerator

constructive_injectivity Rows

/-- Cache both actual matrix rows and their exact readings once, without performing any division. -/
@[noinline, nospecialize] def readRows (input : RationalSidecar tau) (matrix : IntegralMatrix) : Rows input matrix :=
  let denominator := fractionalDenominator matrix tau
  let numerator := fractionalNumerator matrix tau
  ⟨input, rfl, matrix, rfl, denominator, rfl, row input matrix 0, numerator, rfl, row input matrix 1⟩

set_option genInjectivity false in
/-- An actual prepared fractional step with its exact original rows, productive output and retained rational reading. -/
structure Ready {input : RationalSidecar tau} {matrix : IntegralMatrix} (rows : Rows input matrix) where
  /-- The same cached original rows used by this action. -/
  source : Rows input matrix
  /-- The retained rows are the original supplied cache. -/
  source_eq : source = rows
  /-- The exact denominator reading has passed its nonzero check. -/
  nonzero : rows.denominatorReading.value ≠ 0
  /-- The actual prepared presentation of that same denominator. -/
  preparation : Prepared rows.denominator
  /-- Preparation consumes this exact original denominator reading and condition. -/
  preparation_eq : preparation = rows.denominatorReading.prepare nonzero
  /-- The actual productive multiplication by the retained reciprocal. -/
  output : CoherentNamed
  /-- The numerical output uses the cached original numerator and supplied preparation. -/
  output_eq : output = CoherentNamed.mul rows.numerator (preparation.quotient (Coherence.exact 1))
  /-- Exact provenance at this same actual numerical output. -/
  reading : RationalSidecar output
  /-- The output's exact value uses both original cached row readings. -/
  value_eq : reading.value = rows.numeratorReading.value / rows.denominatorReading.value

constructive_injectivity Ready

/-- Execute one nonzero checked row cache and retain its actual output and exact rational evidence. -/
@[noinline, nospecialize] def Rows.prepare {input : RationalSidecar tau} {matrix : IntegralMatrix}
    (rows : Rows input matrix) (nonzero : rows.denominatorReading.value ≠ 0) : Ready rows :=
  let preparation := rows.denominatorReading.prepare nonzero
  let output := CoherentNamed.mul rows.numerator (preparation.quotient (Coherence.exact 1))
  let reading := rows.numeratorReading.divide rows.denominatorReading preparation nonzero
  ⟨rows, rfl, nonzero, preparation, rfl, output, rfl, reading,
    rows.numeratorReading.divide_value rows.denominatorReading preparation nonzero⟩

/-- Read the retained denominator preparation at the exact original matrix row. -/
@[noinline, nospecialize] def Ready.toPreparation {input : RationalSidecar tau} {matrix : IntegralMatrix}
    {rows : Rows input matrix} (ready : Ready rows) :
    Prepared.DenominatorPreparation (fractionalDenominator matrix tau) :=
  rows.denominator_eq ▸
    (⟨ready.preparation.denominator, ready.preparation.apart, ready.preparation.equivalent⟩ :
      Prepared.DenominatorPreparation rows.denominator)

/-- The cached numerical output is the original fractional action through its same retained preparation. -/
theorem Ready.output_spec {input : RationalSidecar tau} {matrix : IntegralMatrix}
    {rows : Rows input matrix} (ready : Ready rows) :
    ready.output = fractionalLinear matrix tau ready.toPreparation := by
  rcases rows with ⟨source, source_eq, request, request_eq, denominator, denominator_eq,
    denominatorReading, numerator, numerator_eq, numeratorReading⟩
  cases denominator_eq
  cases numerator_eq
  rcases ready with ⟨sourceRows, sourceRows_eq, nonzero, preparation, preparation_eq,
    output, output_eq, reading, value_eq⟩
  exact output_eq

end Purelib.Approximation.Gaussian.FractionalAction.Integral.Rational

end
