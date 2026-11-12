module
import Purelib.Algebra.Group.Basic
import Purelib.Data.List.Filter

import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Encoding.Block.Matrix
import Purelib.Data.CCL.Encoding.Block.Semantics
import Purelib.Data.CCL.Encoding.Parser.Constraint
import Purelib.Data.CCL.Encoding.Parser.Semantics.Basic
import Purelib.Data.CCL.Encoding.Parser.Semantics.Normalization
public import Purelib.Data.CCL.Encoding.Parser.Semantics.Prefix
import Purelib.Data.CCL.Encoding.Parser.Semantics.State
import Purelib.Data.CCL.Encoding.Parser.Semantics.Transition
import Purelib.Data.CCL.Encoding.Parser.State
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Code
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Field
import Purelib.Data.List.BinaryPrefix.Decision
import Purelib.Geometry.Projective.Homography.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Constants.Inverse
import Purelib.Data.CCL.Encoding.Parser.Syntax
import Purelib.Data.Rat.Fraction.Order.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Constructive one-bit raw-parser semantics

This module reduces semantic possibility of one more raw CCL bit to an
explicit predicate at the current affine tail.  The only nontrivial case is
the third sector bit: completing that bit subtracts the selected sector
representative and changes to a reciprocal coordinate.  All decisions and
inverse calculations below are finite and rational.
-/

public section

namespace Purelib.Data.CCL.Encoding.Parser.Next

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
/-- Require the next parser bit to be admissible at the exact retained current tail.

A completed sector requires its full block conditions and a nonzero normalized residual. Every other phase requires the
stepped state's exact history and active conditions at the unchanged tail. -/
@[expose] def CanAdvanceAt (state : State) (bit : Bool)
  (before : Basic.Canonical) : Prop :=
  match state.phase with
  | .initial => (State.step state bit).Holds before
  | .highUnary _ => (State.step state bit).Holds before
  | .lowUnary _ => (State.step state bit).Holds before
  | .loopUnary _ => (State.step state bit).Holds before
  | .sector kind exponent bits =>
      match bits with
      | .zero => (State.step state bit).Holds before
      | .one _ => (State.step state bit).Holds before
      | .two first second =>
          let sector := Sector.Code.sectorOfBits first second bit
          Semantics.Basic.fullBlockHolds kind exponent sector before ∧
            Semantics.Basic.normalizedValue kind exponent before - sector.rep ≠ 0

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Gaussian in
/-- Decide the exact local next-bit condition from the retained parser state and Gaussian tail. -/
instance canAdvanceAtDecidable
    (state : State) (bit : Bool) (before : Basic.Canonical) :
    Decidable (CanAdvanceAt state bit before) := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      exact decidable_of_iff
        ((State.step ⟨.initial, matrix, history⟩ bit).holdsBool before = true)
        (State.holdsBool_eq_true _ before)
  | highUnary count =>
      exact decidable_of_iff
        ((State.step ⟨.highUnary count, matrix, history⟩ bit).holdsBool before = true)
        (State.holdsBool_eq_true _ before)
  | lowUnary count =>
      exact decidable_of_iff
        ((State.step ⟨.lowUnary count, matrix, history⟩ bit).holdsBool before = true)
        (State.holdsBool_eq_true _ before)
  | loopUnary count =>
      exact decidable_of_iff
        ((State.step ⟨.loopUnary count, matrix, history⟩ bit).holdsBool before = true)
        (State.holdsBool_eq_true _ before)
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          exact decidable_of_iff
            ((State.step ⟨.sector kind exponent .zero, matrix, history⟩ bit).holdsBool before = true)
            (State.holdsBool_eq_true _ before)
      | one first =>
          exact decidable_of_iff
            ((State.step ⟨.sector kind exponent (.one first), matrix, history⟩ bit).holdsBool before = true)
            (State.holdsBool_eq_true _ before)
      | two first second =>
          dsimp only [CanAdvanceAt]
          infer_instance

section

open Purelib.Data.Gaussian

/-- Decide an original next-bit condition using its retained valid history.

Unary and unfinished-sector steps preserve that exact history, so only their
new active condition needs evaluation. Completing a sector checks the original
full-block and nonzero-residual conditions. The returned decision certifies
the same complete predicate as the unrestricted decision above.
-/
@[expose] def decideAdvance (state : State) (before : Basic.Canonical)
    (holds : state.Holds before) (bit : Bool) : Decidable (CanAdvanceAt state bit before) := by
  let unchangedHistoryDecidable (earlier next : State) (before : Basic.Canonical)
      (history : ∀ constraint ∈ earlier.history, constraint.Holds before)
      (same : next.history = earlier.history) : Decidable (next.Holds before) :=
    match Semantics.Basic.activeHoldsDecidable next.phase before with
    | .isTrue active => .isTrue ⟨fun constraint member => history constraint (same ▸ member), active⟩
    | .isFalse missing => .isFalse (fun accepted => missing accepted.2)
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      cases bit <;> exact unchangedHistoryDecidable _ _ before holds.1 rfl
  | highUnary count =>
      cases bit <;> exact unchangedHistoryDecidable _ _ before holds.1 rfl
  | lowUnary count =>
      cases bit <;> exact unchangedHistoryDecidable _ _ before holds.1 rfl
  | loopUnary count =>
      cases bit <;> exact unchangedHistoryDecidable _ _ before holds.1 rfl
  | sector kind exponent bits =>
      cases bits with
      | zero => exact unchangedHistoryDecidable _ _ before holds.1 rfl
      | one first => exact unchangedHistoryDecidable _ _ before holds.1 rfl
      | two first second =>
          dsimp only [CanAdvanceAt]
          infer_instance

end

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Data.Rat in
/-- At a fixed retained parser state and tail, false and true cannot both satisfy the local advance condition. -/
theorem not_canAdvanceAt_false_and_true
    (state : State) (before : Basic.Canonical) :
    ¬(CanAdvanceAt state false before ∧
      CanAdvanceAt state true before) := by
  rintro ⟨falseHolds, trueHolds⟩
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      have low := falseHolds.2
      have high := trueHolds.2
      change Basic.Canonical.normSq before < 2 at low
      change (2 : Fraction.Rational) ^ 1 ≤ Basic.Canonical.normSq before at high
      rw [pow_one] at high
      exact (not_lt_of_ge high) low
  | highUnary count =>
      have upper := falseHolds.2.1.2
      have lower := trueHolds.2
      exact (not_lt_of_ge lower) upper
  | lowUnary count =>
      have lower := falseHolds.2.1.1
      have upper := trueHolds.2
      exact (not_lt_of_ge lower) upper
  | loopUnary count =>
      have upper := falseHolds.2.1.2
      have lower := trueHolds.2
      exact (not_lt_of_ge upper) lower
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          rcases falseHolds.2 with
            ⟨_, falseSector, falseMember, falseSectorHolds⟩
          rcases trueHolds.2 with
            ⟨_, trueSector, trueMember, trueSectorHolds⟩
          have sectorEqual := Sector.holds_unique falseSectorHolds
            trueSectorHolds
          subst trueSector
          have falsePrefix : BinaryPrefix.Decision.isWordPrefix [false] falseSector.code = true :=
            (Filter.mem_filter.mp falseMember).2
          have truePrefix : BinaryPrefix.Decision.isWordPrefix [true] falseSector.code = true :=
            (Filter.mem_filter.mp trueMember).2
          cases falseSector <;> first | exact Bool.noConfusion falsePrefix | exact Bool.noConfusion truePrefix
      | one first =>
          rcases falseHolds.2 with
            ⟨_, falseSector, falseMember, falseSectorHolds⟩
          rcases trueHolds.2 with
            ⟨_, trueSector, trueMember, trueSectorHolds⟩
          have sectorEqual := Sector.holds_unique falseSectorHolds
            trueSectorHolds
          subst trueSector
          have falsePrefix :
              BinaryPrefix.Decision.isWordPrefix [first, false] falseSector.code = true :=
            (Filter.mem_filter.mp falseMember).2
          have truePrefix :
              BinaryPrefix.Decision.isWordPrefix [first, true] falseSector.code = true :=
            (Filter.mem_filter.mp trueMember).2
          cases first <;> cases falseSector <;>
            first
            | exact Bool.noConfusion falsePrefix
            | exact Bool.noConfusion truePrefix
      | two first second =>
          have sectorEqual := Sector.holds_unique falseHolds.1.2
            trueHolds.1.2
          cases first <;> cases second <;> cases sectorEqual

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Gaussian in
/-- Two locally admissible next bits at the same retained state and tail are equal. -/
theorem canAdvanceAt_unique
    {state : State} {before : Basic.Canonical} {left right : Bool}
    (leftHolds : CanAdvanceAt state left before)
    (rightHolds : CanAdvanceAt state right before) :
    left = right := by
  cases left <;> cases right
  · rfl
  · exact (not_canAdvanceAt_false_and_true state before
      ⟨leftHolds, rightHolds⟩).elim
  · exact (not_canAdvanceAt_false_and_true state before
      ⟨rightHolds, leftHolds⟩).elim
  · rfl

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- A nonsingular represented state admits a next bit exactly when its local condition holds at the retained current
tail.

The reverse direction constructs the exact inverse residual when a sector completes. Other phases preserve the same
tail, while both directions retain the original state's representation and history constraints. -/
theorem canStep_iff_canAdvanceAt
    (state : State) (input before : Basic.Canonical)
    (determinantNonzero :
      Matrix2.Matrix2.determinant state.matrix ≠ 0)
    (beforeRepresents : Semantics.State.Represents state input before)
    (bit : Bool) :
    Semantics.Prefix.CanStep state input bit ↔ CanAdvanceAt state bit before := by
  constructor
  · rintro ⟨after, afterRepresents⟩
    have previousRepresents := Semantics.Transition.step_represents_previous state bit input after
      afterRepresents
    have previousEqual := Semantics.State.Represents.tail_unique determinantNonzero
      beforeRepresents previousRepresents
    rcases state with ⟨phase, matrix, history⟩
    cases phase with
    | initial =>
        simp only [Semantics.Transition.previousTail, -eq_self, -iff_self] at previousEqual
        subst before
        simpa [CanAdvanceAt] using afterRepresents.2.2
    | highUnary count =>
        simp only [Semantics.Transition.previousTail, -eq_self, -iff_self] at previousEqual
        subst before
        simpa [CanAdvanceAt] using afterRepresents.2.2
    | lowUnary count =>
        simp only [Semantics.Transition.previousTail, -eq_self, -iff_self] at previousEqual
        subst before
        simpa [CanAdvanceAt] using afterRepresents.2.2
    | loopUnary count =>
        simp only [Semantics.Transition.previousTail, -eq_self, -iff_self] at previousEqual
        subst before
        simpa [CanAdvanceAt] using afterRepresents.2.2
    | sector kind exponent bits =>
        cases bits with
        | zero =>
            simp only [Semantics.Transition.previousTail, -eq_self, -iff_self] at previousEqual
            subst before
            simpa [CanAdvanceAt] using afterRepresents.2.2
        | one first =>
            simp only [Semantics.Transition.previousTail, -eq_self, -iff_self] at previousEqual
            subst before
            simpa [CanAdvanceAt] using afterRepresents.2.2
        | two first second =>
            let sector := Sector.Code.sectorOfBits first second bit
            let block := Block.Matrix.blockMatrix kind exponent sector
            have newest :
                (Constraint.mk block kind exponent sector).Holds after := by
              apply afterRepresents.2.2.1
              change Constraint.mk block kind exponent sector ∈
                Constraint.mk block kind exponent sector ::
                  history.map (fun item => item.precompose block)
              exact List.mem_cons_self
            have previousEqual' :
                before = Homography.Basic.homographic block after := by
              simpa [Semantics.Transition.previousTail, sector, block] using previousEqual
            have full : Semantics.Basic.fullBlockHolds kind exponent sector before := by
              rw [previousEqual']
              exact newest.2
            have residual :
                Semantics.Basic.normalizedValue kind exponent before - sector.rep ≠ 0 := by
              intro residualZero
              have terminal :
                  Semantics.Basic.normalizedValue kind exponent before = sector.rep :=
                Basic.gaussian_eq_of_sub_eq_zero residualZero
              have normalizedTail := Block.Semantics.normalizedValue_block_homographic
                kind exponent sector after (by
                  simpa only [block, -eq_self, -iff_self] using newest.1)
              have terminalEquation :
                  sector.rep = sector.rep + (Basic.Canonical.gamma * after)⁻¹ := by
                calc
                  sector.rep = Semantics.Basic.normalizedValue kind exponent before :=
                    terminal.symm
                  _ = Semantics.Basic.normalizedValue kind exponent
                      (Homography.Basic.homographic block after) := congrArg
                        (Semantics.Basic.normalizedValue kind exponent) previousEqual'
                  _ = sector.rep + (Basic.Canonical.gamma * after)⁻¹ := by
                    simpa only [block, -eq_self, -iff_self] using normalizedTail
              have inverseZero : (Basic.Canonical.gamma * after)⁻¹ = 0 := by
                apply Basic.ext
                · have realEquation := congrArg
                      Basic.re terminalEquation
                  change sector.rep.re =
                    sector.rep.re + (Basic.Canonical.gamma * after)⁻¹.re at realEquation
                  have cancelled : (0 : Fraction.Rational) = (Basic.Canonical.gamma * after)⁻¹.re :=
                    calc
                      0 = (sector.rep.re + 0) - sector.rep.re :=
                        (Algebra.Group.add_sub_cancel_left _ _).symm
                      _ = (sector.rep.re + (Basic.Canonical.gamma * after)⁻¹.re) - sector.rep.re :=
                        congrArg (fun value => value - sector.rep.re)
                          ((AddZeroClass.add_zero sector.rep.re).trans realEquation)
                      _ = (Basic.Canonical.gamma * after)⁻¹.re :=
                        Algebra.Group.add_sub_cancel_left _ _
                  exact cancelled.symm
                · have imaginaryEquation := congrArg
                      Basic.im terminalEquation
                  change sector.rep.im =
                    sector.rep.im + (Basic.Canonical.gamma * after)⁻¹.im at imaginaryEquation
                  have cancelled : (0 : Fraction.Rational) = (Basic.Canonical.gamma * after)⁻¹.im :=
                    calc
                      0 = (sector.rep.im + 0) - sector.rep.im :=
                        (Algebra.Group.add_sub_cancel_left _ _).symm
                      _ = (sector.rep.im + (Basic.Canonical.gamma * after)⁻¹.im) - sector.rep.im :=
                        congrArg (fun value => value - sector.rep.im)
                          ((AddZeroClass.add_zero sector.rep.im).trans imaginaryEquation)
                      _ = (Basic.Canonical.gamma * after)⁻¹.im :=
                        Algebra.Group.add_sub_cancel_left _ _
                  exact cancelled.symm
              have afterNonzero := Block.Semantics.tail_ne_of_block_denominator kind exponent
                sector after (by simpa only [block, -eq_self, -iff_self] using newest.1)
              exact (Field.inv_ne_zero_direct
                (Field.mul_ne_zero_direct Constants.Inverse.gamma_ne afterNonzero)) inverseZero
            exact ⟨full, residual⟩
  · intro advance
    rcases state with ⟨phase, matrix, history⟩
    cases phase with
    | initial =>
        refine ⟨before, ?_⟩
        apply Semantics.Transition.step_represents_next
          ⟨.initial, matrix, history⟩ bit input before
        · simpa [Semantics.Transition.previousTail] using beforeRepresents
        · simpa [CanAdvanceAt] using advance
    | highUnary count =>
        refine ⟨before, ?_⟩
        apply Semantics.Transition.step_represents_next
          ⟨.highUnary count, matrix, history⟩ bit input before
        · simpa [Semantics.Transition.previousTail] using beforeRepresents
        · simpa [CanAdvanceAt] using advance
    | lowUnary count =>
        refine ⟨before, ?_⟩
        apply Semantics.Transition.step_represents_next
          ⟨.lowUnary count, matrix, history⟩ bit input before
        · simpa [Semantics.Transition.previousTail] using beforeRepresents
        · simpa [CanAdvanceAt] using advance
    | loopUnary count =>
        refine ⟨before, ?_⟩
        apply Semantics.Transition.step_represents_next
          ⟨.loopUnary count, matrix, history⟩ bit input before
        · simpa [Semantics.Transition.previousTail] using beforeRepresents
        · simpa [CanAdvanceAt] using advance
    | sector kind exponent bits =>
        cases bits with
        | zero =>
            refine ⟨before, ?_⟩
            apply Semantics.Transition.step_represents_next
              ⟨.sector kind exponent .zero, matrix, history⟩ bit input before
            · simpa [Semantics.Transition.previousTail] using beforeRepresents
            · simpa [CanAdvanceAt] using advance
        | one first =>
            refine ⟨before, ?_⟩
            apply Semantics.Transition.step_represents_next
              ⟨.sector kind exponent (.one first), matrix, history⟩ bit input
                before
            · simpa [Semantics.Transition.previousTail] using beforeRepresents
            · simpa [CanAdvanceAt] using advance
        | two first second =>
            let sector := Sector.Code.sectorOfBits first second bit
            let tail :=
              (Basic.Canonical.gamma * (Semantics.Basic.normalizedValue kind exponent before - sector.rep))⁻¹
            rcases advance with ⟨full, residual⟩
            refine ⟨tail, ?_⟩
            have completed := Semantics.Transition.completeSector_represents_next
              ⟨.sector kind exponent (.two first second), matrix, history⟩
              kind exponent first second bit input before tail rfl
              beforeRepresents
              (by
                  simpa only [tail, sector, -eq_self, -iff_self]
                    using Block.Semantics.block_homographic_inverse kind exponent sector before residual)
              (by
                  simpa only [tail, sector, -eq_self, -iff_self]
                    using Block.Semantics.block_inverse_denominator_ne kind exponent sector before residual)
              (by simpa only [sector, -eq_self, -iff_self] using full)
              (by
                have loopActive := Semantics.Normalization.inverse_selected_loop_active kind exponent
                  sector before full residual
                simpa only [tail, sector, -eq_self, -iff_self] using loopActive)
            simpa only [Semantics.Transition.step_eq_completeSector
              ⟨.sector kind exponent (.two first second), matrix, history⟩
              kind exponent first second bit rfl, -eq_self, -iff_self] using completed

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Gaussian in
set_option genInjectivity false in
/-- Retain either impossibility of both next bits or one possible next bit with its uniqueness proof.

The certificate belongs to the supplied parser state and original Gaussian input. Terminality excludes each Boolean
extension; success retains the actual bit and its existential tail representation. -/
inductive LocalDecision (state : State) (input :
  Basic.Canonical) where
  /-- Certify that neither Boolean next bit can represent the original input from this state. -/ | terminal (none : ∀
    bit, ¬Semantics.Prefix.CanStep state input bit)
  /-- Retain the actual next bit, its possible representation and uniqueness among all Boolean extensions. -/ | next
    (bit : Bool) (possible : Semantics.Prefix.CanStep state input bit)
      (unique : ∀ other, Semantics.Prefix.CanStep state input other → other = bit)

constructive_injectivity LocalDecision

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Gaussian in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Decide the next bit or terminality of a nonsingular parser state at its retained represented tail.

Test the exact false advance condition first, then true. Return the original next-bit witness with uniqueness, or retain
both failed tests as a proof that no Boolean extension represents the input.
Reuse the represented state's certified history instead of rechecking its
unchanged constraints at every unary or unfinished-sector bit.
-/
@[expose] def decideLocal
    (state : State) (input before : Basic.Canonical)
    (determinantNonzero :
      Matrix2.Matrix2.determinant state.matrix ≠ 0)
    (beforeRepresents : Semantics.State.Represents state input before) :
    LocalDecision state input := by
  letI : Decidable (CanAdvanceAt state false before) :=
    decideAdvance state before beforeRepresents.2.2 false
  by_cases falseAdvance : CanAdvanceAt state false before
  · have falsePossible : Semantics.Prefix.CanStep state input false :=
      (canStep_iff_canAdvanceAt state input before determinantNonzero
        beforeRepresents false).2 falseAdvance
    exact .next false falsePossible (by
      intro other otherPossible
      exact Semantics.Prefix.canStep_unique determinantNonzero otherPossible falsePossible)
  · letI : Decidable (CanAdvanceAt state true before) :=
      decideAdvance state before beforeRepresents.2.2 true
    by_cases trueAdvance : CanAdvanceAt state true before
    · have truePossible : Semantics.Prefix.CanStep state input true :=
        (canStep_iff_canAdvanceAt state input before determinantNonzero
          beforeRepresents true).2 trueAdvance
      exact .next true truePossible (by
        intro other otherPossible
        exact Semantics.Prefix.canStep_unique determinantNonzero otherPossible truePossible)
    · exact .terminal (by
        intro bit possible
        cases bit
        · exact falseAdvance
            ((canStep_iff_canAdvanceAt state input before determinantNonzero
              beforeRepresents false).1 possible)
        · exact trueAdvance
            ((canStep_iff_canAdvanceAt state input before determinantNonzero
              beforeRepresents true).1 possible))

end Purelib.Data.CCL.Encoding.Parser.Next

end
