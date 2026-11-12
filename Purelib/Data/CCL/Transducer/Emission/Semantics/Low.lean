module
import Purelib.Approximation.Gaussian.Process.Route
import Purelib.Approximation.Gaussian.Process.Observation
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

/-!
# Exact semantics of retained low-state emissions

A retained low-state selection preserves the original possible source tails
and the same exact parser matrix chunk, using its cached source observation.
-/

public section

namespace Purelib.Data.CCL.Transducer.Emission.Semantics.Low

open Purelib.Approximation.Gaussian
open Purelib.Data.CCL.Encoding
open Purelib.Data.CCL.Transducer
open Purelib.Data.Gaussian
open Purelib.Geometry.Projective
open Mode.Semantics

/-- Every retained sound low-state selection preserves the original exact projective cursor. -/
private theorem selection_exact (current : Mode.Basic.LowState) (base : current.process.State)
    (observation : Process.Observation current.process base)
    (accurate : (current.process.ball base).radiusSq < Initial.Budget.initialRadiusSq)
    (selected : Low.Selection observation.ball)
    (persists : ∀ {value}, current.process.Possible base value → current.process.Possible current.state value) :
    Basic.ExactEmission (.low current) (selected.emission current base observation accurate) := by
  intro parser _determinant phase tail possible
  cases selected with
  | low small =>
      dsimp only [Low.Selection.emission, SemanticMode.possible] at possible
      rcases Process.Gamma.Upscale.upscaled_candidate_semantics current.process base 1 possible with
        ⟨sourceValue, sourcePossible, tailEqual⟩
      refine ⟨sourceValue, persists sourcePossible, ?_⟩
      dsimp only [Low.Selection.emission]
      rw [Parser.Matrix.Chunks.fold_low_unary_matrix parser current.count phase]
      simp only [SemanticMode.parserTail]
      rw [tailEqual, Low.Preparation.nextLowState_count]
      have unaryIdentity := Power.Gamma.lowUnary_value current.count sourceValue
      simp only [Power.natPow_succ, Power.natPow_zero, Basic.one_mul] at unaryIdentity ⊢
      rw [unaryIdentity]
      exact Line.Proj.Equivalent.refl _
  | sector chosen certificate =>
      dsimp only [Low.Selection.emission, SemanticMode.possible] at possible
      rcases possible with ⟨sourceValue, sourcePossible, residualEqual⟩
      refine ⟨sourceValue, persists sourcePossible, ?_⟩
      let rawValue := (Power.natPow Basic.Canonical.gamma current.count)⁻¹ * sourceValue
      have normalizedIdentity :
          Parser.Semantics.Basic.normalizedValue .initialLow current.count rawValue = sourceValue :=
        Parser.Semantics.Basic.lowNormalized_unscaled current.count sourceValue
      have blockExact := Block.Homogeneous.blockHomogeneous_exact
        Parser.Syntax.BlockKind.initialLow current.count chosen rawValue
      dsimp only [Low.Selection.emission]
      rw [Parser.Matrix.Chunks.fold_low_sector_matrix parser current.count phase chosen, Line.Matrix.act_mul]
      apply Line.Matrix.act_respects_equivalent
      simp only [SemanticMode.parserTail]
      rw [residualEqual]
      rw [normalizedIdentity] at blockExact
      exact blockExact

/-- The original low-state emission preserves every possible next tail's exact projective parser image.

The same actual refinement supplies the cached branch and source observation.
Both the unary chart and the selected-sector chart retain the original source
witness and its original matrix chunk identity.
-/
theorem lowStep_exact (current : Mode.Basic.LowState) :
    Basic.ExactEmission (.low current) (Step.step (.low current)) := by
  let route : Process.Route current.process current.process := .input
  let receipt := route.refine current.state Initial.Budget.initialRadiusSq Initial.Budget.initialRadiusSq_pos
  have accurate : (current.process.ball receipt.state).radiusSq < Initial.Budget.initialRadiusSq :=
    receipt.stateEq.symm ▸ current.process.accurate current.state
      Initial.Budget.initialRadiusSq Initial.Budget.initialRadiusSq_pos
  have upper : Norm.Basic.normSq (current.process.ball receipt.state).center < 13 / 6 :=
    receipt.stateEq.symm ▸ Low.Preparation.low_center_lt_extended_upper current
  have fine := receipt.observation.ballEq.symm ▸ accurate
  have cachedUpper := receipt.observation.ballEq.symm ▸ upper
  let selected := Low.Selection.decide receipt.observation.ball cachedUpper
    (fine.trans Initial.Budget.initialRadiusSq_lt_uniform)
  change Basic.ExactEmission (.low current) (selected.emission current receipt.state receipt.observation accurate)
  apply selection_exact current receipt.state receipt.observation accurate selected
  intro value possible
  exact current.process.refine_persists current.state Initial.Budget.initialRadiusSq
    Initial.Budget.initialRadiusSq_pos (receipt.stateEq ▸ possible)

end Purelib.Data.CCL.Transducer.Emission.Semantics.Low
