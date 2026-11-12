module

public import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
public import Purelib.Curves.Legendre.Periods.Fibre
public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform
import Purelib.Algebra.Quadratic.Pair.Polynomial.Gaussian.Comparison
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.State.Comparison
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Polynomial.Ascending.Gaussian.Evaluation

/-! # Original six-form observations on independently retained frames

Only scalar parameter and point equality identify the coefficient
specification. Both observations keep their actual curve, lifted cell,
polynomial, selected root, denotation, state and numerical allowance.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Specification.Table

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Expression)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets (UniformObservation)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Polynomial.Ascending.Gaussian

/-- Equal scalar indices compare the original cached table denotations at their actual compared generators. -/
private def denotationsEquivalent
    {firstParameter lastParameter firstPoint lastPoint : Canonical}
    {firstGenerator lastGenerator : CoherentNamed} (channel : Fin 6)
    (first : Expression.Denotation (forms firstParameter channel).coefficient firstPoint firstGenerator)
    (last : Expression.Denotation (forms lastParameter channel).coefficient lastPoint lastGenerator)
    (parameters : firstParameter = lastParameter) (points : firstPoint = lastPoint)
    (roots : NamedEquivalent firstGenerator.name lastGenerator.name) :
    NamedEquivalent first.channel.name last.channel.name := by
  cases parameters
  cases points
  exact first.equivalent last roots

/-- Actual original observations of one six-form entry compare across independent nominal curve owners.

The scalar parameter, physical point and signed root comparisons identify
only their retained coefficient channels. The original candidate-error
certificates pay the two actual polynomial readings; no curve or Frame
record is equated, and neither observation is rebuilt or restaged.
-/
theorem observation_difference_le
    {firstParameter lastParameter : Canonical}
    {firstFrame : Paths.Frame firstParameter} {lastFrame : Paths.Frame lastParameter}
    {firstStart firstFinish lastStart lastFinish : LiftedPoint 2}
    {firstLift : LiftedCell firstStart firstFinish} {lastLift : LiftedCell lastStart lastFinish}
    {firstCell lastCell : CellModel} {firstInput lastInput : Rational} (channel : Fin 6)
    (first : UniformObservation (Fibre.frameCurve firstFrame) (forms firstParameter channel)
      firstLift firstCell firstInput)
    (last : UniformObservation (Fibre.frameCurve lastFrame) (forms lastParameter channel)
      lastLift lastCell lastInput)
    (parameters : firstParameter = lastParameter) (points : first.algebraic.point = last.algebraic.point)
    (roots : NamedEquivalent first.algebraic.sheetValue.value.name last.algebraic.sheetValue.value.name)
    (positive : 0 < firstCell.localAllowance + lastCell.localAllowance) :
    Norm.Basic.normSq (Evaluation.eval firstCell.polynomial ⟨firstInput, 0⟩ -
      Evaluation.eval lastCell.polynomial ⟨lastInput, 0⟩) ≤
        8 * (firstCell.localAllowance + lastCell.localAllowance) := by
  let equivalent := denotationsEquivalent channel first.algebraic.interpretation last.algebraic.interpretation
    parameters points roots
  exact Approximation.Gaussian.Name.Coherent.State.CoefficientState.reference_difference_le
    ⟨first.algebraic.interpretation.channel, first.algebraic.readingState⟩
    ⟨last.algebraic.interpretation.channel, last.algebraic.readingState⟩
    (Evaluation.eval firstCell.polynomial ⟨firstInput, 0⟩)
    (Evaluation.eval lastCell.polynomial ⟨lastInput, 0⟩) firstCell.localAllowance lastCell.localAllowance
    (fun _ possible => first.candidate_error_le possible) (fun _ possible => last.candidate_error_le possible)
    equivalent positive

end Purelib.Curves.Legendre.Periods.Jets.Specification.Table

end
