module

import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Refinement.Comparison
import Purelib.Algebra.Quadratic.Pair.Polynomial
public import Purelib.Integration.Program.Gaussian.Sequential
public import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Certified finite integral programs for original waist spans -/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Refinement

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Integration.Program.Gaussian
open Purelib.Approximation.Rational

open Purelib.Algebra.Quadratic (Pair)

variable {radicand : Pair.Polynomial.Coefficients}

variable {site : Fin 2} {parameter : Canonical} {differential : OddPowerDifferential radicand}
variable {data : Bounds.Data site parameter differential} {simple : differential.denominatorPairs = 0}
variable {quarter : UnitCircuitQuarter} {regular : parameter ≠ criticalValue site}
variable {bound : normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)}
variable {accuracy : Fraction.Rational}

namespace Piece

open Purelib.Data.Rat.Fraction.Order

/-- Construct a whole original waist-quarter piece from its intrinsic patch data and positive residual request.

The original signed cubic lift is cached once at chart time zero. Its retained
seed window supplies the sign certificate internally, and the residual sampler
prepares the actual original differential cell on the closed unit chart span.
-/
@[expose] def ofQuarter (data : Bounds.Data site parameter differential)
    (simple : differential.denominatorPairs = 0) (quarter : UnitCircuitQuarter)
    (regular : parameter ≠ criticalValue site)
    (bound : normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational))
    (accuracy : Fraction.Rational) (positive : 0 < accuracy) :
    Piece data simple quarter regular bound accuracy := by
  let span : Interval.Bounds := ⟨0, 1, by decide +kernel⟩
  let lift := Waist.lift site parameter (direction quarter span.lower) regular bound
  have signed : lift.unitOwner.track.initial.box.Refines (UnitRoot.box site) := by
    rewrite [lift.unitOwner_eq, UnitRoot.owner_initial_box]
    exact Geometry.Rational.Box.refines_refl _
  let cell := Cell.build (span := span) data simple lift signed accuracy positive
  exact ofCell cell

/-- The constructed whole-quarter piece retains the exact closed unit chart interval. -/
theorem ofQuarter_span (data : Bounds.Data site parameter differential)
    (simple : differential.denominatorPairs = 0) (quarter : UnitCircuitQuarter)
    (regular : parameter ≠ criticalValue site)
    (bound : normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational))
    (accuracy : Fraction.Rational) (positive : 0 < accuracy) :
    (ofQuarter data simple quarter regular bound accuracy positive).span = ⟨0, 1, by decide +kernel⟩ := rfl

/-- Construct each finite layer from the original piece, retaining every computed split before reading its children. -/
@[expose] def layerAt (initial : Piece data simple quarter regular bound accuracy) : (depth : Nat) → Layer initial depth
  | 0 => Layer.ofPiece initial
  | depth + 1 =>
      let parent := layerAt initial depth
      let steps := Steps.build parent.pieces
      parent.next steps

/-- Construct the existing sequential refinement interface with internally proved consecutive sample bounds. -/
@[expose] def sequential (initial : Piece data simple quarter regular bound accuracy) :
    Sequential.SequentialCompatibleConstantRefinementProgram :=
  { model depth := (initial.layerAt depth).model
    steps depth :=
      let parent := initial.layerAt depth
      let steps := Steps.build parent.pieces
      parent.compatible steps
    stepScale := 4 * initial.span.width ^ 2 * initial.cell.allowance
    stepScale_nonneg :=
      Arithmetic.mul_nonneg_direct
        (Arithmetic.mul_nonneg_direct (by decide +kernel)
          (Arithmetic.sq_nonneg_direct _)) initial.cell.allowance_nonnegative
    initialAllowance_le := by
      have bound := (Layer.ofPiece initial).aggregateAllowance_le
      rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero, Fraction.Field.mul_one_direct] at bound
      have scaleNonnegative := Arithmetic.mul_nonneg_direct
        (Arithmetic.sq_nonneg_direct initial.span.width) initial.cell.allowance_nonnegative
      have scaled := Arithmetic.mul_le_mul_of_nonneg_right_direct
        (show (1 : Fraction.Rational) ≤ 16 by decide +kernel) scaleNonnegative
      rewrite [Fraction.Field.one_mul] at scaled
      apply bound.trans
      apply scaled.trans_eq
      ring1
    comparisonAllowance_le depth :=
      (initial.layerAt depth).comparisonAllowance_le (Steps.build (initial.layerAt depth).pieces) }

/-- The original retained waist piece produces an actual certified Gaussian integral refinement program. -/
@[expose] def program (initial : Piece data simple quarter regular bound accuracy) : Basic.RefinementProgram :=
  initial.sequential.toRefinementProgram

/-- Read the exact original layer model from the same constructed integral program. -/
theorem model_eq (initial : Piece data simple quarter regular bound accuracy) (depth : Nat) :
    (initial.program.model depth) = (initial.layerAt depth).model := rfl

/-- The actual finite waist integral has sixteen times the original squared-width-times-allowance error scale. -/
theorem errorScale_eq (initial : Piece data simple quarter regular bound accuracy) :
    initial.program.errorScale = 16 * initial.span.width ^ 2 * initial.cell.allowance := by
  change 4 * (4 * initial.span.width ^ 2 * initial.cell.allowance) = _
  ring1

/-- Actual later waist samples meet the earlier finite quarter-radius bound. -/
theorem later_close (initial : Piece data simple quarter regular bound accuracy)
    {earlier later : Nat} (order : earlier ≤ later) :
    normSq ((initial.layerAt later).model.integralSample - (initial.layerAt earlier).model.integralSample) ≤
      Geometric.Basic.quarterRadius (16 * initial.span.width ^ 2 * initial.cell.allowance) earlier := by
  have bounded := initial.program.later_close order
  rewrite [initial.model_eq, initial.model_eq, initial.errorScale_eq] at bounded
  rewrite [Purelib.Data.Gaussian.Norm.Basic.normSq_eq_canonical]
  exact bounded

/-- Cache each requested original layer model with its actual integral sample and certified allowance. -/
@[expose] def cached (initial : Piece data simple quarter regular bound accuracy) : Cached.Basic.CachedProgram :=
  initial.program.certifiedView.program

/-- The cached sample is the actual finite integral sample of the same original layer. -/
theorem cached_sample (initial : Piece data simple quarter regular bound accuracy) (depth : Nat) :
    (initial.cached.stage depth).sample = (initial.layerAt depth).model.integralSample := rfl

/-- The internally selected finite refinement meets the supplied positive allowance request. -/
theorem requested_allowance (initial : Piece data simple quarter regular bound accuracy) (current : Nat)
    (target : Fraction.Rational) (positive : 0 < target) :
    (initial.cached.stage (initial.cached.approximation.refineIndex current target positive)).allowance < target :=
  initial.cached.requested_allowance current target positive

end Piece

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Refinement
