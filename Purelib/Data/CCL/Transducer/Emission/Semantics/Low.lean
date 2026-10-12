module
import Purelib.Data.CCL.Encoding.Block.Homogeneous
import Purelib.Data.CCL.Encoding.Parser.Matrix.Chunks
import Purelib.Data.CCL.Encoding.Parser.Semantics.Basic
import Purelib.Data.CCL.Encoding.Parser.Syntax
import Purelib.Data.CCL.Transducer.Emission.Initial.Preparation
import Purelib.Data.CCL.Transducer.Emission.Low
import Purelib.Data.CCL.Transducer.Emission.Low.Preparation
public import Purelib.Data.CCL.Transducer.Emission.Semantics.Basic
public import Purelib.Data.CCL.Transducer.Emission.Step
import Purelib.Data.CCL.Transducer.Mode.Basic
import Purelib.Data.CCL.Transducer.Mode.Semantics
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Power
import Purelib.Data.Gaussian.Power.Gamma
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.Approximation.Gaussian.Process.Gamma.Upscale
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.CCL.Transducer.Emission.Initial.Budget
import Purelib.Data.CCL.Encoding.Padding.Residual
import Purelib.Data.List.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.CCL.Transducer.Emission.Basic
import Purelib.Data.Gaussian.Field
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

namespace Purelib.Data.CCL.Transducer.Emission.Semantics.Low

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Projective in
/-- The low-state emission preserves the exact projective parser representation of every possible next tail.

Sector completion uses the same selected sector, residual source and reciprocal gamma normalization. Unary emission uses
the retained upscaled source and successor-count identity without changing the parser matrix. -/
theorem lowStep_exact (current : Mode.Basic.LowState) :
    Emission.Semantics.Basic.ExactEmission (.low current) (Emission.Step.step (.low current)) := by
  change Emission.Semantics.Basic.ExactEmission (.low current) (Emission.Low.lowStep current)
  generalize hStep : Emission.Low.lowStep current = emission
  unfold Emission.Semantics.Basic.ExactEmission
  intro parser _determinant phase tail possible
  unfold Emission.Low.lowStep at hStep
  simp only at hStep
  split at hStep
  · cases hStep
    simp only [Mode.Semantics.SemanticMode.possible] at possible
    rcases possible with
      ⟨sourceValue, sourcePossible, residualEqual⟩
    have previousPossible :
        current.process.Possible current.state sourceValue :=
      current.process.refine_persists current.state _ _ sourcePossible
    refine ⟨sourceValue, previousPossible, ?_⟩
    let rawValue := (Power.natPow Basic.Canonical.gamma current.count)⁻¹ * sourceValue
    have normalizedIdentity :
        Parser.Semantics.Basic.normalizedValue .initialLow
          current.count rawValue = sourceValue :=
      Parser.Semantics.Basic.lowNormalized_unscaled current.count sourceValue
    have blockExact :=
      Block.Homogeneous.blockHomogeneous_exact
        Parser.Syntax.BlockKind.initialLow current.count
          (Data.ComplexContinuedFraction.Encoding.Sector.select
            (current.process.ball
              (Emission.Initial.Preparation.initialRefinedState current.process current.state)).center)
          rawValue
    rw [Parser.Matrix.Chunks.fold_low_sector_matrix parser current.count phase
      (Data.ComplexContinuedFraction.Encoding.Sector.select
        (current.process.ball
          (Emission.Initial.Preparation.initialRefinedState current.process current.state)).center),
      Line.Matrix.act_mul]
    apply Line.Matrix.act_respects_equivalent
    simp only [Mode.Semantics.SemanticMode.parserTail]
    rw [residualEqual]
    rw [normalizedIdentity] at blockExact
    exact blockExact
  · cases hStep
    simp only [Mode.Semantics.SemanticMode.possible] at possible
    rcases Process.Gamma.Upscale.upscaled_candidate_semantics current.process
        (Emission.Initial.Preparation.initialRefinedState current.process current.state) 1 possible with
      ⟨sourceValue, sourcePossible, tailEqual⟩
    have previousPossible :
        current.process.Possible current.state sourceValue :=
      current.process.refine_persists current.state _ _ sourcePossible
    refine ⟨sourceValue, previousPossible, ?_⟩
    rw [Parser.Matrix.Chunks.fold_low_unary_matrix parser current.count phase]
    simp only [Mode.Semantics.SemanticMode.parserTail]
    rw [tailEqual, Emission.Low.Preparation.nextLowState_count]
    have unaryIdentity := Power.Gamma.lowUnary_value current.count sourceValue
    simp only [Power.natPow_succ, Power.natPow_zero,
      Basic.one_mul] at unaryIdentity ⊢
    rw [unaryIdentity]
    exact Line.Proj.Equivalent.refl _

end Purelib.Data.CCL.Transducer.Emission.Semantics.Low

end
