module
import Purelib.Data.CCL.Encoding.Block.Homogeneous
import Purelib.Data.CCL.Encoding.Parser.Semantics.Basic
public import Purelib.Data.CCL.Transducer.Emission.Loop
public import Purelib.Data.CCL.Transducer.Emission.Semantics.Basic
import Purelib.Data.CCL.Transducer.Mode.Basic
import Purelib.Data.CCL.Transducer.Mode.Parser
import Purelib.Data.CCL.Transducer.Mode.Semantics
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Power
import Purelib.Data.Gaussian.Power.Gamma
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.Approximation.Gaussian.Process.Gamma.Downscale
import Purelib.Approximation.Gaussian.Enclosure.Sector.Decision
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Approximation.Gaussian.Enclosure.Sector.Safe
import Purelib.Approximation.Gaussian.Enclosure.Sector.Large
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Approximation.Gaussian.Process.Normalization.Decision
import Purelib.Data.Gaussian.Basic

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

namespace Purelib.Data.CCL.Transducer.Emission.Semantics.Loop

/-! ## Exact controller transitions -/

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Projective in
/-- Every retained loop emission preserves the exact projective parser representation.

Unary scaling pulls the next possible value back to the same refined source and leaves the parser matrix unchanged.
Sector emission composes its exact block matrix and residual identity with the original parser action. -/
theorem loopStep_exact (current : Mode.Basic.LoopState) :
    Emission.Semantics.Basic.ExactEmission (.loop current) (Emission.Loop.loopStep current) := by
  unfold Emission.Semantics.Basic.ExactEmission
  intro parser _determinant phase
  unfold Emission.Loop.loopStep
  split
  · intro tail possible
    simp only [Mode.Semantics.SemanticMode.possible] at possible
    rcases Process.Gamma.Downscale.unaryScaled_candidate_semantics current.process
        (current.domain.refinedState current.state) possible with
      ⟨sourceValue, sourcePossible, tailEqual⟩
    have previousPossible :
        current.process.Possible current.state sourceValue :=
      current.process.refine_persists current.state _ _ sourcePossible
    refine ⟨sourceValue, previousPossible, ?_⟩
    rw [Mode.Parser.fold_regular_unary_matrix parser current.kind current.count phase]
    simp only [Mode.Semantics.SemanticMode.parserTail]
    rw [tailEqual, Power.Gamma.regularUnary_value]
    exact Line.Proj.Equivalent.refl _
  · rename_i sector certificate decisionEqual
    intro residual possible
    simp only [Mode.Semantics.SemanticMode.possible] at possible
    rcases possible with
      ⟨sourceValue, sourcePossible, residualEqual⟩
    have previousPossible :
        current.process.Possible current.state sourceValue :=
      current.process.refine_persists current.state _ _ sourcePossible
    refine ⟨sourceValue, previousPossible, ?_⟩
    let rawValue := Power.natPow Basic.Canonical.gamma current.count * sourceValue
    have normalizedIdentity :
        Parser.Semantics.Basic.normalizedValue
          (Mode.Parser.regularBlockKind current.kind) current.count rawValue =
            sourceValue :=
      Mode.Parser.regularNormalized_scaled current.kind current.count sourceValue
    have blockExact :=
      Block.Homogeneous.blockHomogeneous_exact
        (Mode.Parser.regularBlockKind current.kind) current.count sector rawValue
    rw [Mode.Parser.fold_regular_sector_matrix parser current.kind current.count phase
      sector, Line.Matrix.act_mul]
    apply Line.Matrix.act_respects_equivalent
    simp only [Mode.Semantics.SemanticMode.parserTail]
    rw [residualEqual]
    rw [normalizedIdentity] at blockExact
    exact blockExact

end Purelib.Data.CCL.Transducer.Emission.Semantics.Loop

end
