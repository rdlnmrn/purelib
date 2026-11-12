module
import Purelib.Approximation.Gaussian.Process.Route
import Purelib.Approximation.Gaussian.Process.Observation
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

open Purelib.Data.CCL.Transducer.Mode.Semantics

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

open Purelib.Approximation.Gaussian
open Purelib.Data.CCL.Encoding
open Purelib.Data.CCL.Transducer
open Purelib.Data.Gaussian
open Purelib.Geometry.Projective
/-- Every retained sound initial selection preserves the original exact projective cursor. -/
private theorem selection_exact (current : Mode.Basic.InitialState) (base : current.process.State)
    (observation : Process.Observation current.process base)
    (accurate : (current.process.ball base).radiusSq < Initial.Budget.initialRadiusSq)
    (selected : Initial.Selection observation.ball)
    (persists : ∀ {value}, current.process.Possible base value → current.process.Possible current.state value) :
    Basic.ExactEmission (.initial current) (selected.emission current base observation accurate) := by
  intro parser _determinant phase tail possible
  cases selected with
  | low small =>
      dsimp only [Initial.Selection.emission, SemanticMode.possible] at possible
      rcases Process.Gamma.Upscale.upscaled_candidate_semantics current.process base 1 possible with
        ⟨sourceValue, sourcePossible, tailEqual⟩
      refine ⟨sourceValue, persists sourcePossible, ?_⟩
      dsimp only [Initial.Selection.emission]
      rw [Parser.Matrix.Chunks.fold_initial_low_entry_matrix parser phase]
      simp only [SemanticMode.parserTail]
      rw [tailEqual, Low.Preparation.nextLowState_count]
      have unaryIdentity := Power.Gamma.lowUnary_value 0 sourceValue
      simp only [Power.natPow_succ, Power.natPow_zero, Basic.one_mul] at unaryIdentity ⊢
      rw [unaryIdentity]
      simp only [Field.inv_eq, Field.inv_one_direct, Basic.one_mul]
      exact Line.Proj.Equivalent.refl
        (Line.Matrix.act parser.matrix (Line.Proj.affine sourceValue))
  | high decision =>
      cases decision with
      | unary certificate =>
          dsimp only [Initial.Selection.emission, SemanticMode.possible] at possible
          rcases Process.Gamma.Downscale.unaryScaled_candidate_semantics current.process base possible with
            ⟨sourceValue, sourcePossible, tailEqual⟩
          refine ⟨sourceValue, persists sourcePossible, ?_⟩
          dsimp only [Initial.Selection.emission]
          rw [Parser.Matrix.Chunks.fold_initial_high_matrix parser phase]
          simp only [SemanticMode.parserTail]
          rw [tailEqual, Power.Gamma.regularUnary_value]
          simp only [Power.natPow_zero, Basic.one_mul]
          exact Line.Proj.Equivalent.refl _
      | sector sector certificate =>
          dsimp only [Initial.Selection.emission, SemanticMode.possible] at possible
          rcases possible with ⟨sourceValue, sourcePossible, residualEqual⟩
          refine ⟨sourceValue, persists sourcePossible, ?_⟩
          have blockExact := Block.Homogeneous.blockHomogeneous_exact
            Parser.Syntax.BlockKind.initialLow 0 sector sourceValue
          dsimp only [Initial.Selection.emission]
          rw [Parser.Matrix.Chunks.fold_initial_low_sector_matrix parser phase sector, Line.Matrix.act_mul]
          apply Line.Matrix.act_respects_equivalent
          simp only [SemanticMode.parserTail]
          rw [residualEqual]
          simpa only [Parser.Semantics.Basic.normalizedValue, Power.natPow_zero, Basic.one_mul] using blockExact

/-- The initial emission preserves the exact projective parser representation of every possible next tail.

Its original actual refinement supplies one retained observation and sound
selection. The three original chart constructions preserve their same source
witnesses and original exact matrix chunk identities.
-/
theorem initialStep_exact (current : Mode.Basic.InitialState) :
    Basic.ExactEmission (.initial current) (Step.step (.initial current)) := by
  let route : Process.Route current.process current.process := .input
  let receipt := route.refine current.state Initial.Budget.initialRadiusSq Initial.Budget.initialRadiusSq_pos
  have accurate : (current.process.ball receipt.state).radiusSq < Initial.Budget.initialRadiusSq :=
    receipt.stateEq.symm ▸ current.process.accurate current.state
      Initial.Budget.initialRadiusSq Initial.Budget.initialRadiusSq_pos
  have fine := receipt.observation.ballEq.symm ▸ accurate
  let selected := Initial.Selection.decide receipt.observation.ball
    (fine.trans Initial.Budget.initialRadiusSq_lt_uniform)
  change Basic.ExactEmission (.initial current) (selected.emission current receipt.state receipt.observation accurate)
  apply selection_exact current receipt.state receipt.observation accurate selected
  intro value possible
  exact current.process.refine_persists current.state Initial.Budget.initialRadiusSq
    Initial.Budget.initialRadiusSq_pos (receipt.stateEq ▸ possible)

end Purelib.Data.CCL.Transducer.Emission.Semantics.Initial

end
