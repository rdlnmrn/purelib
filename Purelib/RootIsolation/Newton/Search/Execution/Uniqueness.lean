module

public import Purelib.RootIsolation.Newton.Search.Execution
public import Purelib.RootIsolation.Refinement.Basic
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.State.Raw
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction

/-! Exact rounded checks determine the retained numerical search history.
The original remaining proposal count also bounds the runtime history length. -/

public section

namespace Purelib.RootIsolation.Newton.Search.Trace.DataExecution

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.RootIsolation

variable {polynomial : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {degreeBound : Nat}
    {elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate polynomial degreeBound}
    {current : State.Raw.RawWindingState polynomial ambient} {epsilon : Fraction.Rational}
    {clearances : Clearance.Box.Line.Elimination.Provider.AxisClearances elimination}

/-- The original remaining proposal budget bounds the actual retained attempt list. -/
theorem length_le {remaining bits : Nat} {proposal : Basic.Canonical}
    {steps : List (Attempted current epsilon)} {result : Option (Refinement current epsilon)}
    (execution : DataExecution elimination current epsilon clearances remaining bits proposal steps result) :
    steps.length ≤ remaining := by
  induction execution with
  | exhausted => exact Nat.le_refl 0
  | accepted => exact Nat.succ_le_succ (Nat.zero_le _)
  | stationary => exact Nat.succ_le_succ (Nat.zero_le _)
  | exhaustedAfter => exact Nat.le_refl 1
  | rejected _ _ _ _ _ _ _ induction => exact Nat.succ_le_succ induction

/-- Two certified executions from the same cursor retain exactly the same numerical attempts.

Rounded centers, acceptance checks, derivatives and Newton updates determine
each branch. The conclusion compares the retained list itself, including its
original precisions, proposals, accepted owner and every continuation value. -/
theorem steps_unique {remaining bits : Nat} {proposal : Basic.Canonical}
    {stepsLeft stepsRight : List (Attempted current epsilon)}
    {resultLeft resultRight : Option (Refinement current epsilon)}
    (left : DataExecution elimination current epsilon clearances remaining bits proposal stepsLeft resultLeft)
    (right : DataExecution elimination current epsilon clearances remaining bits proposal stepsRight resultRight) :
    stepsLeft = stepsRight := by
  induction left generalizing stepsRight resultRight with
  | exhausted => cases right; rfl
  | @accepted remaining bits proposal center value rounded checked =>
    cases right with
    | @accepted _ _ _ centerRight valueRight roundedRight checkedRight =>
      have centerEq := roundedRight.trans rounded.symm
      clear roundedRight
      subst centerRight
      have valueEq := Option.some.inj (checkedRight.symm.trans checked)
      subst valueRight
      rfl
    | @stationary _ _ _ centerRight _ roundedRight checkedRight _ _ =>
      have centerEq := roundedRight.trans rounded.symm
      clear roundedRight
      subst centerRight
      cases checkedRight.symm.trans checked
    | @rejected _ _ _ centerRight _ _ _ _ _ roundedRight checkedRight _ _ _ _ =>
      have centerEq := roundedRight.trans rounded.symm
      clear roundedRight
      subst centerRight
      cases checkedRight.symm.trans checked
    | @exhaustedAfter _ _ centerRight _ roundedRight checkedRight _ _ =>
      have centerEq := roundedRight.trans rounded.symm
      clear roundedRight
      subst centerRight
      cases checkedRight.symm.trans checked
  | @stationary remaining bits proposal center derivative rounded checked derivativeEq zero =>
    cases right with
    | @accepted _ _ _ centerRight _ roundedRight checkedRight =>
      have centerEq := roundedRight.trans rounded.symm
      clear roundedRight
      subst centerRight
      cases checkedRight.symm.trans checked
    | @stationary _ _ _ centerRight derivativeRight roundedRight _ derivativeRightEq _ =>
      have centerEq := roundedRight.trans rounded.symm
      clear roundedRight
      subst centerRight
      have derivativeSame := derivativeRightEq.trans derivativeEq.symm
      cases derivativeSame
      rfl
    | @rejected _ _ _ centerRight derivativeRight _ _ _ _ roundedRight _ derivativeRightEq nonzero _ _ =>
      have centerEq := roundedRight.trans rounded.symm
      clear roundedRight
      subst centerRight
      have derivativeSame := derivativeRightEq.trans derivativeEq.symm
      exact False.elim (nonzero (derivativeSame.trans zero))
    | @exhaustedAfter _ _ centerRight derivativeRight roundedRight _ derivativeRightEq nonzero =>
      have centerEq := roundedRight.trans rounded.symm
      clear roundedRight
      subst centerRight
      have derivativeSame := derivativeRightEq.trans derivativeEq.symm
      exact False.elim (nonzero (derivativeSame.trans zero))
  | @exhaustedAfter bits proposal center derivative rounded checked derivativeEq nonzero =>
    cases right with
    | @accepted _ _ _ centerRight _ roundedRight checkedRight =>
      have centerEq := roundedRight.trans rounded.symm
      clear roundedRight
      subst centerRight
      cases checkedRight.symm.trans checked
    | @stationary _ _ _ centerRight derivativeRight roundedRight _ derivativeRightEq zero =>
      have centerEq := roundedRight.trans rounded.symm
      clear roundedRight
      subst centerRight
      have derivativeSame := derivativeRightEq.trans derivativeEq.symm
      exact False.elim (nonzero (derivativeSame.symm.trans zero))
    | @exhaustedAfter _ _ centerRight derivativeRight roundedRight _ derivativeRightEq _ =>
      have centerEq := roundedRight.trans rounded.symm
      clear roundedRight
      subst centerRight
      have derivativeSame := derivativeRightEq.trans derivativeEq.symm
      cases derivativeSame
      rfl
    | rejected remainingPositive _ _ _ _ _ _ =>
      exact False.elim (Nat.not_lt_zero _ remainingPositive)
  | @rejected remaining bits proposal center derivative next steps result remainingPositive rounded checked
      derivativeEq nonzero
      nextEq tail induction =>
    cases right with
    | @accepted _ _ _ centerRight _ roundedRight checkedRight =>
      have centerEq := roundedRight.trans rounded.symm
      clear roundedRight
      subst centerRight
      cases checkedRight.symm.trans checked
    | @stationary _ _ _ centerRight derivativeRight roundedRight _ derivativeRightEq zero =>
      have centerEq := roundedRight.trans rounded.symm
      clear roundedRight
      subst centerRight
      have derivativeSame := derivativeRightEq.trans derivativeEq.symm
      exact False.elim (nonzero (derivativeSame.symm.trans zero))
    | exhaustedAfter => exact False.elim (Nat.not_lt_zero _ remainingPositive)
    | @rejected _ _ _ centerRight derivativeRight nextRight stepsRight resultRight _ roundedRight _ derivativeRightEq _
        nextRightEq tailRight =>
      have centerEq := roundedRight.trans rounded.symm
      clear roundedRight
      subst centerRight
      have derivativeSame := derivativeRightEq.trans derivativeEq.symm
      clear derivativeRightEq
      subst derivativeRight
      have nextSame := nextRightEq.trans nextEq.symm
      clear nextRightEq
      subst nextRight
      have tailSame := induction tailRight
      cases tailSame
      rfl

end Purelib.RootIsolation.Newton.Search.Trace.DataExecution
