module
import Purelib.Approximation.Gaussian.Enclosure.Sector.Safe
import Purelib.Approximation.Gaussian.Process.Sector.Residual
import Purelib.Data.CCL.Encoding.Block.Matrix
public import Purelib.Data.CCL.Encoding.Block.ParserCorrespondence
import Purelib.Data.CCL.Encoding.Block.SafeReconstruction
import Purelib.Data.CCL.Encoding.Parser.Semantics.Basic
public import Purelib.Data.CCL.Transducer.Contraction.Transition
public import Purelib.Data.CCL.Transducer.Emission.Loop
import Purelib.Data.CCL.Transducer.Mode.Basic
import Purelib.Data.CCL.Transducer.Mode.Bounds
public import Purelib.Data.CCL.Transducer.Mode.Parser
import Purelib.Data.CCL.Transducer.Mode.Semantics
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Power
import Purelib.Data.Gaussian.Power.Gamma
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.Geometry.Projective.SectorBlock.Safe.Tail
import Purelib.Geometry.Rational.Sector.Eight.Safe

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Process.Gamma.Downscale
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Enclosure.Sector.Large
import Purelib.Approximation.Gaussian.Enclosure.Sector.Decision
import Purelib.Data.Gaussian.Field
import Purelib.Data.CCL.Transducer.Emission.Basic
import Purelib.Approximation.Gaussian.Process.Normalization.Decision
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Approximation.Gaussian.Process.Basic

section
@[expose] public section

/-!
# Optional contraction accounting for progressive arithmetic cursors

The canonical encoder, raw parser, and progressive `List Bool` cursor do not
carry an error symbol.  This module is a separate proof sidecar.  It packages
neutral chart changes and normalized sector emissions into finite traces of
projectively coherent redundant blocks, then combines their dyadic
contraction with the explicit coefficient of any already committed decoder
prefix.
-/

namespace Purelib.Data.CCL.Transducer.Contraction.Loop

/-! ## The actual normalized-loop sector transition -/

section
open Purelib.Data.CCL.Encoding
open Purelib.Data.CCL.Transducer
open Purelib.Data.ComplexContinuedFraction.Encoding
/-- Retain the redundant block determined by the exact loop kind, count and selected sector. -/
def loopSectorBlock (current : Mode.Basic.LoopState)
    (sector : Data.ComplexContinuedFraction.Encoding.Sector) : Data.CCL.Encoding.Block.Redundant :=
  Block.ParserCorrespondence.redundantBlock
    (Mode.Parser.regularBlockKind current.kind) current.count sector

/-- The retained loop-sector block matrix is exactly the regular block matrix at that kind and count. -/
@[simp] theorem loopSectorBlock_matrix (current :
  Mode.Basic.LoopState)
    (sector : Data.ComplexContinuedFraction.Encoding.Sector) :
    (loopSectorBlock current sector).matrix =
      Block.Matrix.blockMatrix
        (Mode.Parser.regularBlockKind current.kind) current.count sector :=
  Block.ParserCorrespondence.redundantBlock_matrix
    (Mode.Parser.regularBlockKind current.kind) current.count sector

end

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Projective in
open Purelib.Geometry.Rational in
/-- The exact safe-sector residual construction contracts through its retained loop-sector block.

Recover the previous possible source from the same residual process and base state. The retained domain lower bound and
sector certificate give a safe block tail whose projective residual is the exact next parser tail. -/
theorem loopSector_contractingTransition
    (current : Mode.Basic.LoopState) (sector : Data.ComplexContinuedFraction.Encoding.Sector)
    (certificate : Enclosure.Sector.Safe.SafeBall sector
      (current.process.ball
        (current.domain.refinedState current.state))) :
    Contraction.Transition.ContractingTransition (.loop current)
      (.residual (Emission.Loop.loopSectorResidualState current sector certificate))
      (loopSectorBlock current sector) := by
  intro residual possible
  change (Process.Sector.Residual.residualProcess current.process
      (current.domain.refinedState current.state) sector).Possible
    (Process.Sector.Residual.residualInitial current.process
      (current.domain.refinedState current.state) sector) residual at possible
  rcases possible with ⟨sourceValue, sourcePossible, residualEqual⟩
  have previousPossible :
      current.process.Possible current.state sourceValue :=
    current.process.refine_persists current.state _ _ sourcePossible
  let rawValue := Power.natPow Basic.Canonical.gamma current.count * sourceValue
  have normalizedIdentity :
      Parser.Semantics.Basic.normalizedValue
          (Mode.Parser.regularBlockKind current.kind) current.count rawValue =
        sourceValue :=
    Mode.Parser.regularNormalized_scaled current.kind current.count sourceValue
  have sourceNorm : 1 ≤ Data.Gaussian.Norm.Basic.normSq sourceValue :=
    Mode.Bounds.loop_candidate_norm_lower current
      (current.domain.refinedState current.state) sourcePossible
  have sourceSafe : Geometry.Rational.Sector.Eight.Safe sector sourceValue :=
    Enclosure.Sector.Safe.safe_of_contains certificate
      (current.process.possible_inside sourcePossible)
  have rawNorm :
      1 ≤ Data.Gaussian.Norm.Basic.normSq (Parser.Semantics.Basic.normalizedValue
        (Mode.Parser.regularBlockKind current.kind) current.count rawValue) := by
    rw [normalizedIdentity]
    exact sourceNorm
  have rawSafe : Geometry.Rational.Sector.Eight.Safe sector
      (Parser.Semantics.Basic.normalizedValue
        (Mode.Parser.regularBlockKind current.kind) current.count rawValue) := by
    rw [normalizedIdentity]
    exact sourceSafe
  let blockTail :=
    Block.SafeReconstruction.safeBlockTail
      (Mode.Parser.regularBlockKind current.kind) current.count sector rawValue
        rawNorm rawSafe
  refine ⟨sourceValue, previousPossible, blockTail, ?_, ?_⟩
  · change (Line.Proj.affine rawValue).Equivalent
      (Line.Matrix.act (loopSectorBlock current sector).matrix blockTail.point)
    rw [loopSectorBlock_matrix]
    exact
      (Block.SafeReconstruction.safeBlockTail_exact
        (Mode.Parser.regularBlockKind current.kind) current.count sector rawValue
          rawNorm rawSafe).symm
  · change blockTail.point.Equivalent ⟨1, Basic.Canonical.gamma * residual⟩
    rw [residualEqual, ← normalizedIdentity]
    exact
      Geometry.Projective.SectorBlock.Safe.Tail.ofSafe_point_equivalent_homogeneous sector
          (Parser.Semantics.Basic.normalizedValue
            (Mode.Parser.regularBlockKind current.kind) current.count rawValue)
          rawNorm rawSafe

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Projective in
/-- Every loop emission is neutral for unary scaling or contracts through its exact selected sector block. -/
theorem loopStep_accounted (current : Mode.Basic.LoopState) :
    Contraction.Transition.AccountedStep (.loop current) (Emission.Loop.loopStep current).next := by
  unfold Contraction.Transition.AccountedStep Emission.Loop.loopStep
  split
  · apply Or.inl
    intro tail possible
    simp only [Mode.Semantics.SemanticMode.possible] at possible
    rcases Process.Gamma.Downscale.unaryScaled_candidate_semantics current.process
        (current.domain.refinedState current.state) possible with
      ⟨sourceValue, sourcePossible, tailEqual⟩
    have previousPossible :
        current.process.Possible current.state sourceValue :=
      current.process.refine_persists current.state _ _ sourcePossible
    refine ⟨sourceValue, previousPossible, ?_⟩
    simp only [Mode.Semantics.SemanticMode.parserTail]
    rw [tailEqual, Power.Gamma.regularUnary_value]
    exact Line.Proj.Equivalent.refl _
  · rename_i sector certificate selected
    apply Or.inr
    exact ⟨loopSectorBlock current sector,
      loopSector_contractingTransition current sector certificate⟩

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.ComplexContinuedFraction.Encoding in
/-- A retained sector decision makes the loop emission's next mode its exact certified residual state. -/
theorem loopStep_next_of_sector
    (current : Mode.Basic.LoopState) (sector : Data.ComplexContinuedFraction.Encoding.Sector)
    (certificate : Enclosure.Sector.Safe.SafeBall sector
      (current.process.ball
        (current.domain.refinedState current.state)))
    (selected : current.domain.decide current.state =
      .sector sector certificate) :
    (Emission.Loop.loopStep current).next =
      .residual (Emission.Loop.loopSectorResidualState current sector certificate) := by
  unfold Emission.Loop.loopStep
  rw [selected]

end Purelib.Data.CCL.Transducer.Contraction.Loop

end
