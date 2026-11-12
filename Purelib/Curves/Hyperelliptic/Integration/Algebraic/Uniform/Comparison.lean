module

public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform
import Purelib.Algebra.Quadratic.Pair.Polynomial.Gaussian
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent.Based
import Purelib.Approximation.Gaussian.Name.Coherent.State.Comparison
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Purelib.Integration.Polynomial.Gaussian.Cell.Primitive
import Purelib.Tactic.Ring

/-! # Same-sheet comparison of original uniformly observed polynomial cells

Both actual reading states and their independent local allowances are retained.
Operational comparison of their based coefficient channels pays the difference
of the original polynomial readings. No polynomial, root owner, observation or
source request is reconstructed, and no exact root value is selected.
-/

namespace Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Expression)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Integration.Polynomial.Gaussian

variable {genus : Nat} {curve : HyperellipticCurve genus}
variable {differential : OddPowerDifferential curve.polynomial}
variable {firstStart firstFinish lastStart lastFinish : LiftedPoint 2}
variable {firstLift : LiftedCell firstStart firstFinish} {lastLift : LiftedCell lastStart lastFinish}
variable {firstCell lastCell : CellModel} {firstParameter lastParameter : Fraction.Rational}

namespace UniformObservation

/-- Equal original coordinates and compared original generators identify the two retained coefficient channels. -/
def interpretationEquivalent
    (first : UniformObservation curve differential firstLift firstCell firstParameter)
    (last : UniformObservation curve differential lastLift lastCell lastParameter)
    (point_eq : first.algebraic.point = last.algebraic.point)
    (roots : NamedEquivalent first.algebraic.sheetValue.value.name last.algebraic.sheetValue.value.name) :
    NamedEquivalent first.algebraic.interpretation.channel.name last.algebraic.interpretation.channel.name := by
  let transported := first.algebraic.interpretation.transport last.algebraic.sheetValue.value roots.symm
  have same : transported.channel = last.algebraic.interpretation.channel :=
    transported.channel_readback.trans
      ((congrArg (fun point => differential.coefficient.denote point last.algebraic.sheetValue.value) point_eq).trans
        last.algebraic.interpretation.channel_readback.symm)
  have equivalent := first.algebraic.interpretation.transport_equivalent last.algebraic.sheetValue.value roots.symm
  rewrite [same] at equivalent
  exact equivalent.symm

/-- Actual old coefficient states and their paid candidate bounds control the two original polynomial readings. -/
theorem polynomial_difference_le_of_interpretations
    (first : UniformObservation curve differential firstLift firstCell firstParameter)
    (last : UniformObservation curve differential lastLift lastCell lastParameter)
    (equivalent : NamedEquivalent first.algebraic.interpretation.channel.name
      last.algebraic.interpretation.channel.name)
    (positive : 0 < firstCell.localAllowance + lastCell.localAllowance) :
    Norm.Basic.normSq (Evaluation.eval firstCell.polynomial ⟨firstParameter, 0⟩ -
      Evaluation.eval lastCell.polynomial ⟨lastParameter, 0⟩) ≤
      8 * (firstCell.localAllowance + lastCell.localAllowance) := by
  exact Name.Coherent.State.CoefficientState.reference_difference_le
    ⟨first.algebraic.interpretation.channel, first.algebraic.readingState⟩
    ⟨last.algebraic.interpretation.channel, last.algebraic.readingState⟩
    (Evaluation.eval firstCell.polynomial ⟨firstParameter, 0⟩)
    (Evaluation.eval lastCell.polynomial ⟨lastParameter, 0⟩) firstCell.localAllowance lastCell.localAllowance
    (fun _ possible => first.candidate_error_le possible) (fun _ possible => last.candidate_error_le possible)
    equivalent positive

/-- Two actual same-point, same-sheet observations bound their original polynomial difference by both paid allowances.

The two observations and reading states remain independent. Their retained
root-name relation derives coefficient-channel agreement; its based finite
comparison supplies actual later candidates that stay possible at those old
states. The universal paid candidate bounds, rather than substituted scalar
witnesses, then control the original polynomial readings.
-/
public theorem polynomial_difference_le
    (first : UniformObservation curve differential firstLift firstCell firstParameter)
    (last : UniformObservation curve differential lastLift lastCell lastParameter)
    (point_eq : first.algebraic.point = last.algebraic.point)
    (roots : NamedEquivalent first.algebraic.sheetValue.value.name last.algebraic.sheetValue.value.name)
    (positive : 0 < firstCell.localAllowance + lastCell.localAllowance) :
    Norm.Basic.normSq (Evaluation.eval firstCell.polynomial ⟨firstParameter, 0⟩ -
      Evaluation.eval lastCell.polynomial ⟨lastParameter, 0⟩) ≤
      8 * (firstCell.localAllowance + lastCell.localAllowance) :=
  polynomial_difference_le_of_interpretations first last (interpretationEquivalent first last point_eq roots) positive

/-- Exact original cell endpoints identify two retained observation points at the same local parameter. -/
theorem point_eq_of_endpoints
    (first : UniformObservation curve differential firstLift firstCell firstParameter)
    (last : UniformObservation curve differential lastLift lastCell firstParameter)
    (start_eq : firstCell.start = lastCell.start) (finish_eq : firstCell.finish = lastCell.finish) :
    first.algebraic.point = last.algebraic.point := by
  have displacement_eq : firstCell.displacement = lastCell.displacement := by
    change firstCell.finish - firstCell.start = lastCell.finish - lastCell.start
    rewrite [start_eq, finish_eq]
    rfl
  have observations : firstCell.observationPoint first.observation =
      lastCell.observationPoint last.observation := by
    unfold CellModel.observationPoint
    rewrite [first.parameter_eq, last.parameter_eq, start_eq, displacement_eq]
    rfl
  exact first.algebraic.point_eq.trans (observations.trans last.algebraic.point_eq.symm)

end UniformObservation

namespace UniformCellCertificate

/-- Same-sheet uniformly observed cells with identical original endpoints have quantitatively close integral samples.

The root relation concerns both actual query owners at every unit parameter.
Each query retains its independent original observation and old reading
state. Their paid allowances first control the original polynomial difference;
the existing finite primitive comparison then controls the two actual cell
integrals without changing either polynomial or integral sample.
-/
public theorem integral_difference_le
    (first : UniformCellCertificate curve differential firstLift firstCell)
    (last : UniformCellCertificate curve differential lastLift lastCell)
    (start_eq : firstCell.start = lastCell.start) (finish_eq : firstCell.finish = lastCell.finish)
    (roots : ∀ (parameter : Fraction.Rational) (lower : 0 ≤ parameter) (upper : parameter ≤ 1),
      NamedEquivalent (first.query parameter lower upper).algebraic.sheetValue.value.name
        (last.query parameter lower upper).algebraic.sheetValue.value.name)
    (positive : 0 < firstCell.localAllowance + lastCell.localAllowance) :
    Norm.Basic.normSq (firstCell.integralSample - lastCell.integralSample) ≤
      16 * (firstCell.localAllowance + lastCell.localAllowance) * Norm.Basic.normSq firstCell.displacement := by
  have bounded := Cell.Primitive.integral_difference_le firstCell lastCell start_eq finish_eq
    (8 * (firstCell.localAllowance + lastCell.localAllowance)) (by
      intro parameter inside
      let firstQuery := first.query parameter inside.1 inside.2
      let lastQuery := last.query parameter inside.1 inside.2
      exact firstQuery.polynomial_difference_le lastQuery
        (UniformObservation.point_eq_of_endpoints firstQuery lastQuery start_eq finish_eq)
        (roots parameter inside.1 inside.2) positive)
  exact bounded.trans_eq (by ring1)

end UniformCellCertificate

end Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets
