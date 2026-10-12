module

import Purelib.Approximation.Gaussian.Name.Coherent.State
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.List.Proximity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.Tactic.Ring
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial

/-!
# Ordered channels and allowances in retained coherent coefficient tables

The original finite state lists retain their actual channels and strict
allowance targets. Ordered channel equalities preserve count and compose;
shared channel coherence bounds the same retained current coefficient values.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable

/-- Every entry of one finite coefficient table has allowance below the same
displayed target.

Each retained coefficient state contributes its strict allowance inequality.
The recursive certificate uses the same rational target at every original
coefficient position. -/
@[expose] public def AllowancesLt : List Name.Coherent.State.CoefficientState → Fraction.Rational → Prop
  | [], _ => True
  | entry :: remaining, target =>
      entry.allowance < target ∧
        Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.AllowancesLt remaining target

/-- Increase the common strict allowance target while preserving every coefficient bound.

Each retained head allowance remains strictly below the larger target by
scalar transitivity. Structural recursion retains every original tail state. -/
public theorem AllowancesLt.mono : ∀ {entries : List Name.Coherent.State.CoefficientState}
    {small large : Fraction.Rational}, CoefficientTable.AllowancesLt entries small → small ≤ large →
      CoefficientTable.AllowancesLt entries large
  | [], _small, _large, _bounded, _order => trivial
  | _entry :: _remaining, _small, _large, bounded, order =>
      ⟨bounded.1.trans_le order,
        Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.AllowancesLt.mono bounded.2
        order⟩

set_option backward.match.sparseCases false in
/-- Two readings have the same ordered progressive coefficient channels.
Only their dependent finite process states may differ.

Equally shaped lists pair their original channels in order, with an exact
channel equality at each position. Only the retained states on those channels
may differ; mismatched shapes fail. -/
@[expose] public def SameChannels : List Name.Coherent.State.CoefficientState → List
  Name.Coherent.State.CoefficientState → Prop
  | [], [] => True
  | left :: leftTail, right :: rightTail =>
      left.channel = right.channel ∧
        Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.SameChannels leftTail rightTail
  | _, _ => False

set_option backward.match.sparseCases false in
/-- Two finite readings of the same coefficient channels are close entrywise.

If both lists have allowances below the common target, each value difference has quadrance at most eight times that
target. -/
private theorem coefficientsClose_of_sameChannels :
    ∀ {left right : List Name.Coherent.State.CoefficientState} {target : Fraction.Rational},
      CoefficientTable.SameChannels left right → CoefficientTable.AllowancesLt left target →
        CoefficientTable.AllowancesLt right target →
          Gaussian.List.Proximity.CoefficientsClose
            (left.map Name.Coherent.State.CoefficientState.value)
            (right.map Name.Coherent.State.CoefficientState.value) (8 * target)
  | [], [], target, _same, _leftSmall, _rightSmall => trivial
  | [], _ :: _, target, same, _leftSmall, _rightSmall => by
      exact same.elim
  | _ :: _, [], target, same, _leftSmall, _rightSmall => by
      exact same.elim
  | ⟨leftChannel, leftState⟩ :: leftTail,
      ⟨rightChannel, rightState⟩ :: rightTail, target, same,
      leftSmall, rightSmall => by
      simp only [CoefficientTable.SameChannels, CoefficientTable.AllowancesLt] at same leftSmall rightSmall
      rcases same with ⟨channelEqual, tailSame⟩
      subst rightChannel
      dsimp only [List.map_cons, Gaussian.List.Proximity.CoefficientsClose]
      constructor
      · have close := leftChannel.coherent.possible_close
          (leftChannel.name.process.witness leftState).property
          (leftChannel.name.process.witness rightState).property
        exact (calc
          Data.Gaussian.Norm.Basic.normSq
              ((leftChannel.name.process.witness leftState).val -
                (leftChannel.name.process.witness rightState).val) ≤
              4 * (leftChannel.coherent.allowance leftState +
                leftChannel.coherent.allowance rightState) := close
          _ < 4 * (target + target) :=
            Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
              (by decide)
              (Fraction.Order.Arithmetic.add_lt_add_direct
                leftSmall.1 rightSmall.1)
          _ = 8 * target := by ring1).le
      · exact
          coefficientsClose_of_sameChannels
          tailSame
          leftSmall.2 rightSmall.2

set_option backward.match.sparseCases false in
/-- Lists with the same ordered coefficient channels have equal lengths.

Both empty lists have zero length, and each paired head contributes one
entry on either side. Mismatched shapes are excluded by the original
channel certificate. -/
public theorem sameChannels_length : ∀ {left right : List Name.Coherent.State.CoefficientState},
    CoefficientTable.SameChannels left right → left.length = right.length
  | [], [], _same => rfl
  | [], _ :: _, same => by exact same.elim
  | _ :: _, [], same => by exact same.elim
  | _left :: leftTail, _right :: rightTail, same => by
      exact congrArg Nat.succ
        (Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.sameChannels_length same.2)

/-- Tables with the same ordered coefficient channels have equal degree.

The table degree is its retained coefficient-state list length.
The original ordered channel certificate therefore identifies the two
displayed finite degree counts. -/
public theorem degree_eq_of_sameChannels
    {left right : CoefficientTable}
    (same : CoefficientTable.SameChannels left.entries right.entries) :
    left.degree = right.degree :=
  CoefficientTable.sameChannels_length same

/-- A coefficient-state list has the same channels as itself.

Each retained head channel has its original reflexive equality.
Structural recursion preserves the complete unchanged tail list. -/
public theorem sameChannels_refl : ∀ entries : List Name.Coherent.State.CoefficientState,
    CoefficientTable.SameChannels entries entries
  | [] => trivial
  | _ :: remaining => ⟨rfl,
    Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.sameChannels_refl remaining⟩

set_option backward.match.sparseCases false in
/-- Equality of ordered coefficient channels is transitive.

At each retained position the two supplied channel equalities compose.
Their common list shapes preserve the same paired tails; mismatched
intermediate or final shapes contradict an original certificate. -/
public theorem sameChannels_trans : ∀ {first second third :
    List Name.Coherent.State.CoefficientState}, CoefficientTable.SameChannels first second →
      CoefficientTable.SameChannels second third → CoefficientTable.SameChannels first third
  | [], [], [], _firstSecond, _secondThird => trivial
  | [], [], _ :: _, _firstSecond, secondThird => by
      exact secondThird.elim
  | [], _ :: _, _, firstSecond, _secondThird => by
      exact firstSecond.elim
  | _ :: _, [], _, firstSecond, _secondThird => by
      exact firstSecond.elim
  | _ :: _, _ :: _, [], _firstSecond, secondThird => by
      exact secondThird.elim
  | first :: firstTail, second :: secondTail, third :: thirdTail,
      firstSecond, secondThird =>
      ⟨firstSecond.1.trans secondThird.1,
        Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.sameChannels_trans
          firstSecond.2 secondThird.2⟩

/-- Accurate readings of the same ordered coefficient channels are close entrywise.

Both retained state lists have allowances below the same supplied target.
Their original shared channel coherence bounds each displayed value difference
by eight times that target while preserving coefficient order. -/
public theorem values_close_of_sameChannels
    {left right : CoefficientTable} {target : Fraction.Rational}
    (same : CoefficientTable.SameChannels left.entries right.entries)
    (leftSmall : CoefficientTable.AllowancesLt left.entries target)
    (rightSmall : CoefficientTable.AllowancesLt right.entries target) :
    Gaussian.List.Proximity.CoefficientsClose left.values right.values (8 * target) := by
  exact CoefficientTable.coefficientsClose_of_sameChannels same leftSmall rightSmall

end Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable
