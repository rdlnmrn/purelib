module
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Data.CCL.Encoding.Block.Matrix
import Purelib.Data.CCL.Encoding.Parser.Constraint
import Purelib.Data.CCL.Encoding.Parser.Semantics.Basic
public import Purelib.Data.CCL.Encoding.Parser.Semantics.State
import Purelib.Data.CCL.Encoding.Parser.State
import Purelib.Data.CCL.Encoding.Parser.Syntax
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Code
import Purelib.Data.List.Map
import Purelib.Data.Rat.Dyadic
import Purelib.Geometry.Projective.Homography.Basic
import Purelib.Geometry.Projective.Homography.Composition
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Data.Gaussian.Norm.Basic
import Mathlib.Order.Basic

/-!
# Affine semantics of constructive raw-parser states

Parser constraints are evaluated on the current affine tail.  These finite
algebraic lemmas prove that decoder homographies compose in parser order and
that completing a raw block preserves the represented original input.
-/

public section

namespace Purelib.Data.CCL.Encoding.Parser.Semantics.Transition

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Geometry.Projective in
/-- Completed-sector constraints imply the old state constraints at the exact newly emitted block homography image. -/
theorem completeSector_holds_previous
    (state : State) (kind : Parser.Syntax.BlockKind) (exponent : Nat)
    (first second third : Bool) (tail : Basic.Canonical)
    (phase : state.phase = .sector kind exponent (.two first second))
    (holds :
      (Parser.State.completeSector state kind exponent first second third).Holds tail) :
    state.Holds
      (Homography.Basic.homographic
        (Block.Matrix.blockMatrix kind exponent (Sector.Code.sectorOfBits first second third)) tail) := by
  let sector := Sector.Code.sectorOfBits first second third
  let block := Block.Matrix.blockMatrix kind exponent sector
  have newest : (Constraint.mk block kind exponent sector).Holds tail := by
    apply holds.1
    change Constraint.mk block kind exponent sector ∈
      Constraint.mk block kind exponent sector ::
        state.history.map (fun item => item.precompose block)
    exact List.mem_cons_self
  have blockDenominator : Homography.Basic.denominator block tail ≠ 0 := newest.1
  have full :
      Parser.Semantics.Basic.fullBlockHolds kind exponent sector (Homography.Basic.homographic block tail) := newest.2
  constructor
  · intro constraint member
    have mapped : (constraint.precompose block).Holds tail := by
      apply holds.1
      change constraint.precompose block ∈
        (Constraint.mk block kind exponent sector) ::
          state.history.map (fun item => item.precompose block)
      exact List.mem_cons_of_mem _
        (Map.mem_map.mpr ⟨constraint, member, rfl⟩)
    exact (Parser.Constraint.constraint_precompose_iff constraint block tail
      blockDenominator).1 mapped
  · rw [phase]
    exact ⟨full.1, sector,
      Sector.Code.sectorOfBits_mem_two_candidates first second third, full.2⟩

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Projective in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- A completed-sector representation pulls back to the original state through that exact block homography. -/
theorem completeSector_represents_previous
    (state : State) (kind : Parser.Syntax.BlockKind) (exponent : Nat)
    (first second third : Bool) (input tail : Basic.Canonical)
    (phase : state.phase = .sector kind exponent (.two first second))
    (represents : Parser.Semantics.State.Represents
      (Parser.State.completeSector state kind exponent first second third) input tail) :
    Parser.Semantics.State.Represents state input
      (Homography.Basic.homographic
        (Block.Matrix.blockMatrix kind exponent (Sector.Code.sectorOfBits first second third)) tail) := by
  let sector := Sector.Code.sectorOfBits first second third
  let block := Block.Matrix.blockMatrix kind exponent sector
  have newest : (Constraint.mk block kind exponent sector).Holds tail := by
    apply represents.2.2.1
    change Constraint.mk block kind exponent sector ∈
      Constraint.mk block kind exponent sector ::
        state.history.map (fun item => item.precompose block)
    exact List.mem_cons_self
  have blockDenominator : Homography.Basic.denominator block tail ≠ 0 := newest.1
  have productDenominator :
      Homography.Basic.denominator (Matrix2.mul state.matrix block) tail ≠ 0 := by
    simpa [Parser.State.completeSector, sector, block] using represents.1
  have oldDenominator :
      Homography.Basic.denominator state.matrix (Homography.Basic.homographic block tail) ≠ 0 :=
    (Homography.Composition.denominator_mul_ne_iff state.matrix block tail
      blockDenominator).1 productDenominator
  refine ⟨oldDenominator, ?_, ?_⟩
  · calc
      input = Homography.Basic.homographic (Matrix2.mul state.matrix block) tail := by
        simpa [Parser.State.completeSector, sector, block] using represents.2.1
      _ = Homography.Basic.homographic state.matrix (Homography.Basic.homographic block tail) :=
        Homography.Composition.homographic_mul state.matrix block tail blockDenominator oldDenominator
  · exact completeSector_holds_previous state kind exponent first second third
      tail phase represents.2.2

open Purelib.Data.CCL.Encoding in
/-- Reading the third retained sector bit performs exactly the completeSector update. -/
theorem step_eq_completeSector
    (state : State) (kind : Parser.Syntax.BlockKind) (exponent : Nat)
    (first second third : Bool)
    (phase : state.phase = .sector kind exponent (.two first second)) :
    Parser.State.step state third =
      Parser.State.completeSector state kind exponent first second third := by
  rcases state with ⟨statePhase, matrix, history⟩
  simp only at phase
  subst statePhase
  rfl

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Projective in
/-- Recover the tail before a retained parser step.

When the bit completes a sector, apply its exact completed-block homography to the new tail. In every other phase,
return the same tail without changing its representation. -/
@[expose] def previousTail (state : State)
  (bit : Bool) (tail : Basic.Canonical) : Basic.Canonical :=
  match state.phase with
  | .initial => tail
  | .highUnary _ => tail
  | .lowUnary _ => tail
  | .loopUnary _ => tail
  | .sector kind exponent bits =>
      match bits with
      | .zero => tail
      | .one _ => tail
      | .two first second =>
          Homography.Basic.homographic
            (Block.Matrix.blockMatrix kind exponent (Sector.Code.sectorOfBits first second bit)) tail

section
open Purelib.Data.CCL.Encoding
open Purelib.Data.Gaussian
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2
/-- Replace only the parser phase in a retained representation using the supplied old active-phase witness. -/
theorem represents_with_previous_phase
    (oldPhase newPhase : Parser.Syntax.Phase) (matrix : LinearAlgebra.Coordinates2.Matrix.GaussianMatrix)
    (history : List Constraint) (input tail : Basic.Canonical)
    (represents : Parser.Semantics.State.Represents ⟨newPhase, matrix, history⟩ input tail)
    (active : Parser.Semantics.Basic.activeHolds oldPhase tail) :
    Parser.Semantics.State.Represents ⟨oldPhase, matrix, history⟩ input tail :=
  ⟨represents.1, represents.2.1, represents.2.2.1, active⟩

/-- Undo an initial bit while preserving the exact represented input, tail, matrix and history. -/
theorem step_represents_previous_initial
    (matrix : LinearAlgebra.Coordinates2.Matrix.GaussianMatrix) (history : List Constraint)
      (bit : Bool)
    (input tail : Basic.Canonical)
    (represents : Parser.Semantics.State.Represents
      (Parser.State.step ⟨Parser.Syntax.Phase.initial, matrix, history⟩ bit) input tail) :
    Parser.Semantics.State.Represents ⟨Parser.Syntax.Phase.initial, matrix, history⟩ input tail := by
  cases bit with
  | false =>
      have after : Parser.Semantics.State.Represents
          ⟨Parser.Syntax.Phase.lowUnary 0, matrix, history⟩ input tail := by
        exact represents
      exact represents_with_previous_phase .initial (.lowUnary 0) matrix
        history input tail after True.intro
  | true =>
      have after : Parser.Semantics.State.Represents
          ⟨Parser.Syntax.Phase.highUnary 1, matrix, history⟩ input tail := by
        exact represents
      exact represents_with_previous_phase .initial (.highUnary 1) matrix
        history input tail after True.intro

end

section
open Purelib.Data.CCL.Encoding
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2
/-- Undo a high-unary bit using the retained power-of-two lower bound at the unchanged tail. -/
theorem step_represents_previous_highUnary
    (count : Nat) (matrix : LinearAlgebra.Coordinates2.Matrix.GaussianMatrix)
      (history : List Constraint)
      (bit : Bool)
    (input tail : Basic.Canonical)
    (represents : Parser.Semantics.State.Represents
      (Parser.State.step ⟨Parser.Syntax.Phase.highUnary count, matrix, history⟩ bit) input tail) :
    Parser.Semantics.State.Represents ⟨Parser.Syntax.Phase.highUnary count, matrix, history⟩ input tail := by
  cases bit with
  | false =>
      have after : Parser.Semantics.State.Represents
          ⟨Parser.Syntax.Phase.sector .initialHigh count .zero,
            matrix, history⟩ input tail := by
        exact represents
      have active : Parser.Semantics.Basic.activeHolds (.highUnary count) tail :=
        after.2.2.2.1.1
      exact represents_with_previous_phase (.highUnary count)
        (.sector .initialHigh count .zero) matrix history input tail after active
  | true =>
      have after : Parser.Semantics.State.Represents
          ⟨Parser.Syntax.Phase.highUnary (count + 1), matrix, history⟩ input tail := by
        exact represents
      have active : Parser.Semantics.Basic.activeHolds (.highUnary count) tail :=
        (Dyadic.two_pow_le_succ count).trans after.2.2.2
      exact represents_with_previous_phase (.highUnary count)
        (.highUnary (count + 1)) matrix history input tail after active

/-- Undo a low-unary bit using its exact retained radial or successor upper bound at the unchanged tail. -/
theorem step_represents_previous_lowUnary
    (count : Nat) (matrix : LinearAlgebra.Coordinates2.Matrix.GaussianMatrix)
      (history : List Constraint)
      (bit : Bool)
    (input tail : Basic.Canonical)
    (represents : Parser.Semantics.State.Represents
      (Parser.State.step ⟨Parser.Syntax.Phase.lowUnary count, matrix, history⟩ bit) input tail) :
    Parser.Semantics.State.Represents ⟨Parser.Syntax.Phase.lowUnary count, matrix, history⟩ input tail := by
  cases bit with
  | false =>
      have after : Parser.Semantics.State.Represents
          ⟨Parser.Syntax.Phase.sector .initialLow count .zero,
            matrix, history⟩ input tail := by
        exact represents
      cases count with
      | zero =>
          have active : Parser.Semantics.Basic.activeHolds (.lowUnary 0) tail := by
            simpa only [Parser.Semantics.Basic.activeHolds, Norm.Basic.normSq_eq_canonical, pow_zero,
              Fraction.Field.one_mul, -eq_self, -iff_self] using after.2.2.2.1.2
          exact represents_with_previous_phase (.lowUnary 0)
            (.sector .initialLow 0 .zero) matrix history input tail after active
      | succ count =>
          have active : Parser.Semantics.Basic.activeHolds (.lowUnary (count + 1)) tail :=
            Dyadic.lower_low_active_of_radial_upper count tail after.2.2.2.1.2
          exact represents_with_previous_phase (.lowUnary (count + 1))
            (.sector .initialLow (count + 1) .zero) matrix history input tail
            after active
  | true =>
      have after : Parser.Semantics.State.Represents
          ⟨Parser.Syntax.Phase.lowUnary (count + 1), matrix, history⟩ input tail := by
        exact represents
      cases count with
      | zero =>
          have active : Parser.Semantics.Basic.activeHolds (.lowUnary 0) tail := by
            have newer : Gaussian.Norm.Basic.normSq tail < 1 := by
              simpa only [Parser.Semantics.Basic.activeHolds, Norm.Basic.normSq_eq_canonical, pow_zero,
                Fraction.Field.one_mul, -eq_self, -iff_self] using after.2.2.2
            simpa only [Parser.Semantics.Basic.activeHolds, Norm.Basic.normSq_eq_canonical, pow_zero,
              Fraction.Field.one_mul, -eq_self, -iff_self] using newer.trans (by decide : (1 : Fraction.Rational) < 2)
          exact represents_with_previous_phase (.lowUnary 0) (.lowUnary 1)
            matrix history input tail after active
      | succ count =>
          have active : Parser.Semantics.Basic.activeHolds (.lowUnary (count + 1)) tail :=
            Dyadic.lower_low_active_of_next count tail after.2.2.2
          exact represents_with_previous_phase (.lowUnary (count + 1))
            (.lowUnary (count + 2)) matrix history input tail after active

/-- Undo a loop-unary bit using the retained strict power-of-two lower bound at the unchanged tail. -/
theorem step_represents_previous_loopUnary
    (count : Nat) (matrix : LinearAlgebra.Coordinates2.Matrix.GaussianMatrix)
      (history : List Constraint)
      (bit : Bool)
    (input tail : Basic.Canonical)
    (represents : Parser.Semantics.State.Represents
      (Parser.State.step ⟨Parser.Syntax.Phase.loopUnary count, matrix, history⟩ bit) input tail) :
    Parser.Semantics.State.Represents ⟨Parser.Syntax.Phase.loopUnary count, matrix, history⟩ input tail := by
  cases bit with
  | false =>
      have after : Parser.Semantics.State.Represents
          ⟨Parser.Syntax.Phase.sector .loop count .zero, matrix, history⟩ input tail := by
        exact represents
      have active : Parser.Semantics.Basic.activeHolds (.loopUnary count) tail :=
        after.2.2.2.1.1
      exact represents_with_previous_phase (.loopUnary count)
        (.sector .loop count .zero) matrix history input tail after active
  | true =>
      have after : Parser.Semantics.State.Represents
          ⟨Parser.Syntax.Phase.loopUnary (count + 1), matrix, history⟩ input tail := by
        exact represents
      have active : Parser.Semantics.Basic.activeHolds (.loopUnary count) tail :=
        (Dyadic.two_pow_le_succ count).trans_lt after.2.2.2
      exact represents_with_previous_phase (.loopUnary count)
        (.loopUnary (count + 1)) matrix history input tail after active

end

section
open Purelib.Data.CCL.Encoding
open Purelib.Data.ComplexContinuedFraction.Encoding
open Purelib.Data.Gaussian
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2
/-- Undo the first sector bit by retaining its sector witness in the original zero-bit candidate list. -/
theorem step_represents_previous_sector_zero
    (kind : Parser.Syntax.BlockKind) (exponent : Nat) (matrix : LinearAlgebra.Coordinates2.Matrix.GaussianMatrix)
    (history : List Constraint) (bit : Bool) (input tail : Basic.Canonical)
    (represents : Parser.Semantics.State.Represents
      (Parser.State.step ⟨Parser.Syntax.Phase.sector kind exponent .zero, matrix, history⟩ bit)
        input tail) :
    Parser.Semantics.State.Represents ⟨Parser.Syntax.Phase.sector kind exponent .zero, matrix, history⟩
      input tail := by
  have after : Parser.Semantics.State.Represents
      ⟨Parser.Syntax.Phase.sector kind exponent (.one bit),
        matrix, history⟩ input tail := by
    exact represents
  rcases after.2.2.2 with ⟨radial, sector, member, sectorHolds⟩
  have oldMember : sector ∈ Sector.Code.sectorCandidates .zero :=
    Sector.Code.sectorCandidates_mono rfl member
  have active : Parser.Semantics.Basic.activeHolds (.sector kind exponent .zero) tail :=
    ⟨radial, sector, oldMember, sectorHolds⟩
  exact represents_with_previous_phase (.sector kind exponent .zero)
    (.sector kind exponent (.one bit)) matrix history input tail after active

/-- Undo the second sector bit by retaining its sector witness in the original one-bit candidate list. -/
theorem step_represents_previous_sector_one
    (kind : Parser.Syntax.BlockKind) (exponent : Nat) (first : Bool) (matrix :
      LinearAlgebra.Coordinates2.Matrix.GaussianMatrix)
    (history : List Constraint) (bit : Bool) (input tail : Basic.Canonical)
    (represents : Parser.Semantics.State.Represents
      (Parser.State.step ⟨Parser.Syntax.Phase.sector kind exponent (.one first), matrix, history⟩ bit)
        input tail) :
    Parser.Semantics.State.Represents ⟨Parser.Syntax.Phase.sector kind exponent (.one first), matrix, history⟩
      input tail := by
  have after : Parser.Semantics.State.Represents
      ⟨Parser.Syntax.Phase.sector kind exponent (.two first bit),
        matrix, history⟩ input tail := by
    exact represents
  rcases after.2.2.2 with ⟨radial, sector, member, sectorHolds⟩
  have oldMember : sector ∈ Sector.Code.sectorCandidates (.one first) :=
    Sector.Code.sectorCandidates_mono (by cases first <;> rfl) member
  have active : Parser.Semantics.Basic.activeHolds
      (.sector kind exponent (.one first)) tail :=
    ⟨radial, sector, oldMember, sectorHolds⟩
  exact represents_with_previous_phase (.sector kind exponent (.one first))
    (.sector kind exponent (.two first bit)) matrix history input tail
    after active

end

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Gaussian in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Undo the third sector bit by applying the exact completed-block homography to the retained new tail. -/
theorem step_represents_previous_sector_two
    (kind : Parser.Syntax.BlockKind) (exponent : Nat) (first second : Bool) (matrix :
      LinearAlgebra.Coordinates2.Matrix.GaussianMatrix)
    (history : List Constraint) (bit : Bool) (input tail : Basic.Canonical)
    (represents : Parser.Semantics.State.Represents
      (Parser.State.step ⟨Parser.Syntax.Phase.sector kind exponent (.two first second), matrix, history⟩
        bit) input tail) :
    Parser.Semantics.State.Represents ⟨Parser.Syntax.Phase.sector kind exponent (.two first second), matrix, history⟩
      input (previousTail
        ⟨Parser.Syntax.Phase.sector kind exponent (.two first second), matrix, history⟩
        bit tail) := by
  simpa [previousTail, Parser.State.step] using
    completeSector_represents_previous
      ⟨Parser.Syntax.Phase.sector kind exponent (.two first second), matrix, history⟩
      kind exponent first second bit input tail rfl represents

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Undo any sector-reading step with the exact previous tail and original candidate constraints. -/
theorem step_represents_previous_sector
    (kind : Parser.Syntax.BlockKind) (exponent : Nat) (bits : Sector.Code.SectorBits)
    (matrix : LinearAlgebra.Coordinates2.Matrix.GaussianMatrix) (history : List Constraint)
      (bit : Bool)
    (input tail : Basic.Canonical)
    (represents : Parser.Semantics.State.Represents
      (Parser.State.step ⟨Parser.Syntax.Phase.sector kind exponent bits, matrix, history⟩ bit)
        input tail) :
    Parser.Semantics.State.Represents ⟨Parser.Syntax.Phase.sector kind exponent bits, matrix, history⟩ input
      (previousTail ⟨Parser.Syntax.Phase.sector kind exponent bits, matrix, history⟩
        bit tail) := by
  cases bits with
  | zero =>
      have after : Parser.Semantics.State.Represents
          ⟨Parser.Syntax.Phase.sector kind exponent (.one bit),
            matrix, history⟩ input tail := by
        exact represents
      rcases after.2.2.2 with ⟨radial, sector, member, sectorHolds⟩
      have oldMember : sector ∈ Sector.Code.sectorCandidates .zero :=
        Sector.Code.sectorCandidates_mono rfl member
      have active : Parser.Semantics.Basic.activeHolds (.sector kind exponent .zero) tail :=
        ⟨radial, sector, oldMember, sectorHolds⟩
      simpa [previousTail] using
        represents_with_previous_phase (.sector kind exponent .zero)
          (.sector kind exponent (.one bit)) matrix history input tail
          after active
  | one first =>
      have after : Parser.Semantics.State.Represents
          ⟨Parser.Syntax.Phase.sector kind exponent (.two first bit),
            matrix, history⟩ input tail := by
        exact represents
      rcases after.2.2.2 with ⟨radial, sector, member, sectorHolds⟩
      have oldMember : sector ∈ Sector.Code.sectorCandidates (.one first) :=
        Sector.Code.sectorCandidates_mono (by cases first <;> rfl) member
      have active : Parser.Semantics.Basic.activeHolds
          (.sector kind exponent (.one first)) tail :=
        ⟨radial, sector, oldMember, sectorHolds⟩
      simpa [previousTail] using
        represents_with_previous_phase (.sector kind exponent (.one first))
          (.sector kind exponent (.two first bit)) matrix history input tail
          after active
  | two first second =>
      simpa [previousTail, Parser.State.step] using
        completeSector_represents_previous
          ⟨Parser.Syntax.Phase.sector kind exponent (.two first second), matrix, history⟩
          kind exponent first second bit input tail rfl represents

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Gaussian in
/-- Every retained next-state representation gives an old-state representation at its exact previousTail. -/
theorem step_represents_previous
    (state : State) (bit : Bool) (input tail : Basic.Canonical)
    (represents : Parser.Semantics.State.Represents (Parser.State.step state bit) input tail) :
    Parser.Semantics.State.Represents state input (previousTail state bit tail) := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      simpa [previousTail] using
        step_represents_previous_initial matrix history bit input tail
          represents
  | highUnary count =>
      simpa [previousTail] using
        step_represents_previous_highUnary count matrix history bit input tail
          represents
  | lowUnary count =>
      simpa [previousTail] using
        step_represents_previous_lowUnary count matrix history bit input tail
          represents
  | loopUnary count =>
      simpa [previousTail] using
        step_represents_previous_loopUnary count matrix history bit input tail
          represents
  | sector kind exponent bits =>
      exact step_represents_previous_sector kind exponent bits matrix history
        bit input tail represents

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Projective in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Advance a retained representation when the exact next state holds at the supplied new tail.

The old representation uses this step's previousTail. On sector completion the newest retained constraint supplies the
block denominator, allowing exact homography composition with the unchanged input. -/
theorem step_represents_next
    (state : State) (bit : Bool) (input tail : Basic.Canonical)
    (before : Parser.Semantics.State.Represents state input (previousTail state bit tail))
    (afterHolds : (Parser.State.step state bit).Holds tail) :
    Parser.Semantics.State.Represents (Parser.State.step state bit) input tail := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial | highUnary | lowUnary | loopUnary =>
      simp only [previousTail, -eq_self, -iff_self] at before
      refine ⟨?_, ?_, afterHolds⟩
      · cases bit <;> exact before.1
      · cases bit <;> exact before.2.1
  | sector kind exponent bits =>
      cases bits with
      | zero | one =>
          simp only [previousTail, -eq_self, -iff_self] at before
          refine ⟨?_, ?_, afterHolds⟩
          · cases bit <;> exact before.1
          · cases bit <;> exact before.2.1
      | two first second =>
          let sector := Sector.Code.sectorOfBits first second bit
          let block := Block.Matrix.blockMatrix kind exponent sector
          have newest : (Constraint.mk block kind exponent sector).Holds tail := by
            apply afterHolds.1
            change Constraint.mk block kind exponent sector ∈
              Constraint.mk block kind exponent sector ::
                history.map (fun item => item.precompose block)
            exact List.mem_cons_self
          have blockDenominator : Homography.Basic.denominator block tail ≠ 0 := newest.1
          have productDenominator :
              Homography.Basic.denominator (Matrix2.mul matrix block) tail ≠ 0 :=
            (Homography.Composition.denominator_mul_ne_iff matrix block tail blockDenominator).2
              before.1
          refine ⟨?_, ?_, afterHolds⟩
          · simpa [Parser.State.step, Parser.State.completeSector, sector, block] using productDenominator
          · calc
              input = Homography.Basic.homographic matrix (Homography.Basic.homographic block tail) := before.2.1
              _ = Homography.Basic.homographic (Matrix2.mul matrix block) tail :=
                (Homography.Composition.homographic_mul matrix block tail blockDenominator
                  before.1).symm
              _ = Homography.Basic.homographic
                  (Parser.State.step ⟨Parser.Syntax.Phase.sector kind exponent (.two first second),
                    matrix, history⟩ bit).matrix tail := by
                rfl

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Geometry.Projective in
/-- Complete a sector while retaining the original input representation and exact new tail.

The supplied block image equals the previous tail and has nonzero denominator. Preserve the full-block witness and
initial loop condition, prepend that exact constraint, and transport every original history constraint through the same
block. -/
theorem completeSector_represents_next
    (state : State) (kind : Parser.Syntax.BlockKind) (exponent : Nat)
    (first second third : Bool) (input before tail : Basic.Canonical)
    (phase : state.phase = .sector kind exponent (.two first second))
    (beforeRepresents : Parser.Semantics.State.Represents state input before)
    (beforeEq : Homography.Basic.homographic
      (Block.Matrix.blockMatrix kind exponent (Sector.Code.sectorOfBits first second third)) tail =
        before)
    (blockDenominator : Homography.Basic.denominator
      (Block.Matrix.blockMatrix kind exponent (Sector.Code.sectorOfBits first second third)) tail ≠ 0)
    (fullBlock : Parser.Semantics.Basic.fullBlockHolds kind exponent
      (Sector.Code.sectorOfBits first second third) before)
    (loopActive : Parser.Semantics.Basic.activeHolds (.loopUnary 0) tail) :
    Parser.Semantics.State.Represents (Parser.State.completeSector state kind exponent first second third)
      input tail := by
  let sector := Sector.Code.sectorOfBits first second third
  let block := Block.Matrix.blockMatrix kind exponent sector
  have afterHolds :
      (Parser.State.completeSector state kind exponent first second third).Holds tail := by
    constructor
    · intro constraint member
      change constraint ∈
        (Constraint.mk block kind exponent sector) ::
          state.history.map (fun item => item.precompose block) at member
      rcases Purelib.Data.List.Membership.mem_cons.mp member with newest | older
      · subst constraint
        refine ⟨blockDenominator, ?_⟩
        rw [beforeEq]
        exact fullBlock
      · rcases Map.mem_map.mp older with ⟨old, oldMember, rfl⟩
        apply (Parser.Constraint.constraint_precompose_iff old block tail blockDenominator).2
        rw [beforeEq]
        exact beforeRepresents.2.2.1 old oldMember
    · exact loopActive
  rw [← step_eq_completeSector state kind exponent first second third phase]
  apply step_represents_next state third input tail
  · simpa [previousTail, phase, sector, block, beforeEq] using beforeRepresents
  · simpa [step_eq_completeSector state kind exponent first second third phase]
      using afterHolds
end Purelib.Data.CCL.Encoding.Parser.Semantics.Transition

end
