module
import Purelib.Data.CCL.Encoding.Block.Homogeneous
import Purelib.Data.CCL.Encoding.Parser.Matrix.Chunks
import Purelib.Data.CCL.Encoding.Parser.Semantics.Basic
import Purelib.Data.CCL.Encoding.Parser.Syntax
import Purelib.Data.CCL.Transducer.Emission.Initial
import Purelib.Data.CCL.Transducer.Emission.Initial.Preparation
import Purelib.Data.CCL.Transducer.Emission.Low.Preparation
public import Purelib.Data.CCL.Transducer.Emission.Semantics.Basic
public import Purelib.Data.CCL.Transducer.Emission.Step
import Purelib.Data.CCL.Transducer.Mode.Basic
import Purelib.Data.CCL.Transducer.Mode.Semantics
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Power
import Purelib.Data.Gaussian.Power.Gamma
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.Approximation.Gaussian.Process.Gamma.Downscale
import Purelib.Approximation.Gaussian.Process.Gamma.Upscale
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Enclosure.Sector.Large
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.CCL.Transducer.Emission.Initial.Budget
import Purelib.Data.CCL.Encoding.Padding.Residual
import Purelib.Approximation.Gaussian.Enclosure.Sector.Safe
import Purelib.Data.List.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Constants
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.CCL.Transducer.Emission.Basic
import Purelib.Approximation.Gaussian.Enclosure.Sector.Decision
import Purelib.Approximation.Gaussian.Process.Normalization.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Norm.Basic

section
@[expose] public section

/-!
# Exact projective semantics of progressive arithmetic cursors

The raw `Machine` remains the original bit-only cursor.  This module adds a
separate proof wrapper relating its quantitative mode to the ordinary raw
parser matrix.  In particular, residual modes are interpreted homogeneously
as `[1 : γr]`; this is an affine inverse tail when `r ≠ 0` and is exactly
`ω` when `r = 0`.  No equality decision on a completed value is needed.
-/

namespace Purelib.Data.CCL.Transducer.Emission.Semantics.Initial

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Projective in
/-- The initial emission preserves the exact projective parser representation of every possible next tail.

The three decision branches retain their original downscaled, residual or upscaled source witnesses. Their exact matrix
chunk identities and normalization equations recover the same old parser image. -/
theorem initialStep_exact (current :
  Mode.Basic.InitialState) :
    Emission.Semantics.Basic.ExactEmission (.initial current) (Emission.Step.step (.initial current)) := by
  change Emission.Semantics.Basic.ExactEmission (.initial current) (Emission.Initial.initialStep current)
  generalize hStep : Emission.Initial.initialStep current = emission
  unfold Emission.Semantics.Basic.ExactEmission
  intro parser _determinant phase tail possible
  unfold Emission.Initial.initialStep at hStep
  simp only at hStep
  split at hStep
  · split at hStep
    · cases hStep
      simp only [Mode.Semantics.SemanticMode.possible] at possible
      rcases Process.Gamma.Downscale.unaryScaled_candidate_semantics current.process
          (Emission.Initial.Preparation.initialRefinedState current.process current.state) possible with
        ⟨sourceValue, sourcePossible, tailEqual⟩
      have previousPossible :
          current.process.Possible current.state sourceValue :=
        current.process.refine_persists current.state _ _ sourcePossible
      refine ⟨sourceValue, previousPossible, ?_⟩
      rw [Parser.Matrix.Chunks.fold_initial_high_matrix parser phase]
      simp only [Mode.Semantics.SemanticMode.parserTail]
      rw [tailEqual, Power.Gamma.regularUnary_value]
      simp only [Power.natPow_zero,
        Basic.one_mul]
      exact Line.Proj.Equivalent.refl _
    · rename_i sector certificate decisionEqual
      cases hStep
      simp only [Mode.Semantics.SemanticMode.possible] at possible
      rcases possible with
        ⟨sourceValue, sourcePossible, residualEqual⟩
      have previousPossible :
          current.process.Possible current.state sourceValue :=
        current.process.refine_persists current.state _ _ sourcePossible
      refine ⟨sourceValue, previousPossible, ?_⟩
      have blockExact :=
        Block.Homogeneous.blockHomogeneous_exact
          Parser.Syntax.BlockKind.initialLow 0 sector sourceValue
      rw [Parser.Matrix.Chunks.fold_initial_low_sector_matrix parser phase sector,
        Line.Matrix.act_mul]
      apply Line.Matrix.act_respects_equivalent
      simp only [Mode.Semantics.SemanticMode.parserTail]
      rw [residualEqual]
      simpa only [Parser.Semantics.Basic.normalizedValue, Power.natPow_zero,
        Basic.one_mul] using blockExact
  · cases hStep
    simp only [Mode.Semantics.SemanticMode.possible] at possible
    rcases Process.Gamma.Upscale.upscaled_candidate_semantics current.process
        (Emission.Initial.Preparation.initialRefinedState current.process current.state) 1 possible with
      ⟨sourceValue, sourcePossible, tailEqual⟩
    have previousPossible :
        current.process.Possible current.state sourceValue :=
      current.process.refine_persists current.state _ _ sourcePossible
    refine ⟨sourceValue, previousPossible, ?_⟩
    rw [Parser.Matrix.Chunks.fold_initial_low_entry_matrix parser phase]
    simp only [Mode.Semantics.SemanticMode.parserTail]
    rw [tailEqual, Emission.Low.Preparation.nextLowState_count]
    have unaryIdentity := Power.Gamma.lowUnary_value 0 sourceValue
    simp only [Power.natPow_succ, Power.natPow_zero,
      Basic.one_mul] at unaryIdentity ⊢
    rw [unaryIdentity]
    simp only [Field.inv_eq,
      Field.inv_one_direct,
      Basic.one_mul]
    exact Line.Proj.Equivalent.refl
      (Line.Matrix.act parser.matrix (Line.Proj.affine sourceValue))

end Purelib.Data.CCL.Transducer.Emission.Semantics.Initial

end
