module
import Purelib.Data.List.Membership
import Purelib.Integration.Program.Gaussian.Cached.Basic
public import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.DyadicCount
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.Gaussian.Power
public import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Constant
public import Purelib.Integration.Polynomial.Gaussian.Path.Basic
public import Purelib.Integration.Polynomial.Gaussian.Path.Constant

import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Init.Data.List.Lemmas
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Integration.Polynomial.Gaussian

open Purelib

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Integration.Polynomial.Gaussian.Cell.Basic

open Purelib.Integration.Polynomial.Gaussian.Path.Basic

open Purelib.Integration.Polynomial.Gaussian.Path.Basic.PathModel

@[expose] public section

/-!
# Finite samples on the actual reciprocal of a prepared affine path

Inversion acts on every point of the original segment. Its endpoint chord
does not replace that rational path. The transformed first-order coefficient
and the actual reciprocal endpoint displacement differ from the original
constant-cell sample by an explicit second-order term. Uniform finite meshes
pay that error with a decaying bound including the full squared cell count.
-/

open Purelib.Data

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPathSamples

open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

/-- Exact Gaussian rational reciprocal coordinates and sample values. -/
abbrev Gaussian := Data.Gaussian.Basic.Canonical
/-- Exact rational refinement parameters and error bounds. -/
abbrev Coordinate := Fraction.Rational

/-- The rational image of the original parametrized segment, not its chord. -/
def point (cell : Cell.Basic.CellModel) (parameter :
  Coordinate) : Gaussian :=
  (cell.start + Scale.scale parameter cell.displacement)⁻¹

/-- The reciprocal parametrized segment starts at the inverse of its original starting point. -/
theorem point_zero (cell : Cell.Basic.CellModel) : point
  cell 0 = cell.start⁻¹ := by
  apply congrArg Inv.inv
  apply Data.Gaussian.Basic.ext <;>
    simp only [Scale.scale_re, Scale.scale_im, Basic.add_re, Basic.add_im] <;> ring1

/-- The reciprocal parametrized segment ends at the inverse of its original finishing point. -/
theorem point_one (cell : Cell.Basic.CellModel) : point
  cell 1 = cell.finish⁻¹ := by
  apply congrArg Inv.inv
  apply Data.Gaussian.Basic.ext <;>
    simp only [Scale.scale_re, Scale.scale_im, CellModel.displacement,
      Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im] <;> ring1

set_option genInjectivity false in
/-- Endpoint sample data. Nonvanishing between endpoints is a separate path obligation, discharged for the fixed
exterior by `parent_point_nonzero` in `PreparedExteriorReciprocal`; it does not follow from these two checks. -/
structure Cell (source : Cell.Basic.CellModel) where
  /-- The original source cell constant-coefficient certificate. -/ constant : source.ConstantCertificate
  /-- The original source starting point is nonzero. -/ startNonzero : source.start ≠ 0
  /-- The original source finishing point is nonzero. -/ finishNonzero : source.finish ≠ 0
  /-- The cached reciprocal starting point. -/ start :
    Gaussian
  /-- The cached start is exactly the inverse of the original source start. -/ start_eq : start = source.start⁻¹
  /-- The cached reciprocal finishing point. -/ finish :
    Gaussian
  /-- The cached finish is exactly the inverse of the original source finish. -/ finish_eq : finish = source.finish⁻¹
  /-- The cached coefficient transformed by the reciprocal differential rule. -/ coefficient :
    Gaussian
  /-- The cached coefficient is minus the original start squared times the retained source coefficient. -/
    coefficient_eq : coefficient = -(source.start ^ 2 * constant.coefficient)
  /-- The cached reciprocal endpoint-displacement sample. -/ sample :
    Gaussian
  /-- The cached sample equals its retained reciprocal displacement times transformed coefficient. -/ sample_eq : sample
    = (finish - start) * coefficient

constructive_injectivity Cell

namespace Cell

variable {source : CellModel}

/-- Cache the reciprocal endpoints, transformed coefficient and sample from one original constant cell and its endpoint
nonvanishing proofs. -/
def build (constant : source.ConstantCertificate) (first : source.start ≠ 0) (last : source.finish ≠ 0) :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPathSamples.Cell source :=
  let start := source.start⁻¹
  let finish := source.finish⁻¹
  let coefficient := -(source.start ^ 2 * constant.coefficient)
  ⟨constant, first, last, start, rfl, finish, rfl, coefficient, rfl, (finish - start) * coefficient, rfl⟩

/-- In particular, the stored coefficient is the negative reversed hyperelliptic basis coefficient under the existing
root-coordinate map. -/
theorem coefficient_transport (reading : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPathSamples.Cell source)
  {genus : Nat}
    (differential : Differentials.Basic.Differential genus) (root :
      Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPathSamples.Gaussian) (rootNonzero : root ≠ 0)
    (original : reading.constant.coefficient = HyperellipticReciprocal.coefficient differential source.start root) :
    reading.coefficient = -HyperellipticReciprocal.coefficient (HyperellipticReciprocal.reversedDifferential
      differential)
      reading.start (HyperellipticReciprocal.rootCoordinate genus reading.start root) := by
  rw [reading.coefficient_eq, original, reading.start_eq]
  exact (HyperellipticReciprocal.coefficient_transport differential source.start root reading.startNonzero
    rootNonzero).symm

/-- The error is not silently declared zero: the reciprocal endpoint displacement differs from the derivative times the
affine displacement. -/
theorem error_identity (reading : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPathSamples.Cell source) :
    source.integralSample - reading.sample = reading.constant.coefficient * source.displacement ^ 2 / source.finish :=
      by
  rw [Cell.Basic.CellModel.integralSample_constant source reading.constant.coefficient reading.constant.polynomial_eq,
    reading.sample_eq, reading.start_eq, reading.finish_eq, reading.coefficient_eq]
  apply Data.Gaussian.Field.mul_right_cancel_of_ne reading.finishNonzero
  rw [Algebra.Field.ExplicitField.div_mul_cancel _ reading.finishNonzero]
  change ((source.finish - source.start) * reading.constant.coefficient -
    (source.finish⁻¹ - source.start⁻¹) * -(source.start ^ 2 * reading.constant.coefficient)) * source.finish = _
  calc
    _ = reading.constant.coefficient * ((source.finish - source.start) * source.finish +
        source.start ^ 2 * (source.finish * source.finish⁻¹) -
        source.start * (source.start * source.start⁻¹) * source.finish) := by ring1
    _ = _ := by
      rw [Algebra.Field.ExplicitField.mul_inv_cancel source.finish reading.finishNonzero,
        Algebra.Field.ExplicitField.mul_inv_cancel source.start reading.startNonzero]
      dsimp only [CellModel.displacement]
      ring1

/-- The reciprocal sample discrepancy squared norm is the exact coefficient and displacement expression divided by the
original finish norm. -/
theorem error_norm (reading : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPathSamples.Cell source) :
    Data.Gaussian.Norm.Basic.normSq (source.integralSample - reading.sample) =
      Data.Gaussian.Norm.Basic.normSq reading.constant.coefficient * Data.Gaussian.Norm.Basic.normSq
        source.displacement ^ 2 / Data.Gaussian.Norm.Basic.normSq source.finish := by
  rw [reading.error_identity, Data.Gaussian.Field.normSq_div _ _ reading.finishNonzero,
    Data.Gaussian.Norm.Basic.normSq_mul, Power.normSq_pow]
  rfl

/-- Coefficient and nonzero-endpoint bounds control the reciprocal sample discrepancy by the squared source movement. -/
theorem error_bound (reading : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPathSamples.Cell source) {density lower
  : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPathSamples.Coordinate} (lowerPositive : 0 < lower)
    (coefficientBound : Data.Gaussian.Norm.Basic.normSq reading.constant.coefficient ≤ density) (finishBound :
      lower ≤ Data.Gaussian.Norm.Basic.normSq source.finish) :
    Data.Gaussian.Norm.Basic.normSq (source.integralSample - reading.sample) ≤ (density / lower) *
      Data.Gaussian.Norm.Basic.normSq source.displacement ^ 2 := by
  rw [reading.error_norm]
  have densityNonnegative := (Data.Gaussian.Norm.Basic.normSq_nonneg _).trans coefficientBound
  have denominatorPositive := lowerPositive.trans_le finishBound
  have divisionNonnegative := Fraction.Order.Field.div_nonneg_direct densityNonnegative lowerPositive.le
  have paid : density ≤ (density / lower) * Data.Gaussian.Norm.Basic.normSq source.finish := by
    calc
      _ = (density / lower) * lower := (Fraction.Field.div_mul_cancel_of_ne _ _ lowerPositive.ne').symm
      _ ≤ _ := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct finishBound divisionNonnegative
  apply (Fraction.Order.Field.div_le_iff_pos denominatorPositive).mpr
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (coefficientBound.trans paid)
    (Fraction.Order.Arithmetic.sq_nonneg_direct _)).trans_eq (by ring1)

end Cell

set_option genInjectivity false in
/-- One occurrence per actual source cell. All reciprocal values and coefficients are cached in the retained spine. -/
inductive Cells : List Cell.Basic.CellModel → Type
  /-- The empty source cell list has no reciprocal sample data. -/ | nil :
    Cells []
  /-- Retain the reciprocal sample for the original head cell and the exact retained tail. -/ | cons {source :
    Cell.Basic.CellModel} {remaining : List Cell.Basic.CellModel} (head :
    Cell source) (tail :
    Cells remaining) :
    Cells (source :: remaining)

constructive_injectivity Cells

namespace Cells

/-- Construct the retained reciprocal sample spine from the original constant-cell certificates and endpoint
nonvanishing evidence. -/
def build : ∀ {sources : List Cell.Basic.CellModel}, PathModel.ConstantCells sources →
    (∀ source ∈ sources, source.start ≠ 0 ∧ source.finish ≠ 0) →
      Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPathSamples.Cells sources
  | _, .nil, _ => .nil
  | _, .cons constant tail, nonzero =>
      .cons (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPathSamples.Cell.build constant (nonzero _
        (List.mem_cons_self ..)).1 (nonzero _ (List.mem_cons_self ..)).2)
        (build tail (fun source member =>
          nonzero source (List.mem_cons_of_mem _ member)))

/-- Read the cached reciprocal samples in the original source-cell order. -/
def values : {sources : List Cell.Basic.CellModel} → Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPathSamples.Cells
  sources → List Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPathSamples.Gaussian
  | _, .nil => []
  | _, .cons head tail => head.sample :: tail.values

/-- Compute each original source sample minus its corresponding retained reciprocal sample. -/
def errors : {sources : List Cell.Basic.CellModel} → Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPathSamples.Cells
  sources → List Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPathSamples.Gaussian
  | _, .nil => []
  | source :: _, .cons head tail => (source.integralSample - head.sample) :: tail.errors

/-- There is one retained discrepancy for each original source cell. -/
theorem errors_length {sources : List Cell.Basic.CellModel} (cells :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPathSamples.Cells sources) : cells.errors.length = sources.length :=
  by
  induction cells with
  | nil => rfl
  | cons head tail ih => exact congrArg Nat.succ ih

/-- The finite discrepancy sum equals the original path sample minus the retained reciprocal sample sum. -/
theorem errors_sum {sources : List Cell.Basic.CellModel} (cells :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPathSamples.Cells sources) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum cells.errors = (PathModel.mk sources).integralSample -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum cells.values := by
  induction cells with
  | nil => change (0 : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPathSamples.Gaussian) = 0 - 0; ring1
  | @cons source remaining head tail ih =>
      change _ + Data.Gaussian.Norm.Sum.Basic.gaussianSum tail.errors = _
      rw [ih]
      change (source.integralSample - head.sample) + ((PathModel.mk remaining).integralSample -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum tail.values) =
        (source.integralSample + (PathModel.mk remaining).integralSample) - (head.sample +
          Data.Gaussian.Norm.Sum.Basic.gaussianSum tail.values)
      ring1

/-- Every original constant coefficient in the retained cell spine satisfies the same squared-norm bound. -/
def CoefficientsBounded {sources : List Cell.Basic.CellModel} (cells :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPathSamples.Cells sources) (density :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPathSamples.Coordinate) : Prop :=
  match cells with
  | .nil => True
  | .cons head tail => Data.Gaussian.Norm.Basic.normSq head.constant.coefficient ≤ density ∧
    tail.CoefficientsBounded density

/-- Uniform coefficient, endpoint and movement bounds control every discrepancy in the original finite cell list. -/
theorem errors_bounded {sources : List Cell.Basic.CellModel} (cells :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPathSamples.Cells sources) {density lower movement :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPathSamples.Coordinate}
    (lowerPositive : 0 < lower) (coefficients : cells.CoefficientsBounded density)
    (finishes : ∀ source ∈ sources, lower ≤ Data.Gaussian.Norm.Basic.normSq source.finish)
    (movements : ∀ source ∈ sources, Data.Gaussian.Norm.Basic.normSq source.displacement ≤ movement) :
    ∀ error ∈ cells.errors, Data.Gaussian.Norm.Basic.normSq error ≤ (density / lower) * movement ^ 2 := by
  induction cells with
  | nil => intro error member; cases member
  | @cons source remaining head tail ih =>
      intro error member
      rcases List.Membership.mem_cons.mp member with rfl | member
      · have bound := head.error_bound lowerPositive coefficients.1 (finishes source (List.mem_cons_self ..))
        have square := Fraction.Order.Arithmetic.pow_le_pow_direct (Data.Gaussian.Norm.Basic.normSq_nonneg
          source.displacement)
          (movements source (List.mem_cons_self ..)) 2
        exact bound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct square
          (Fraction.Order.Field.div_nonneg_direct ((Data.Gaussian.Norm.Basic.normSq_nonneg _).trans coefficients.1)
            lowerPositive.le))
      · exact ih coefficients.2 (fun other inTail => finishes other (List.mem_cons_of_mem _ inTail))
          (fun other inTail => movements other (List.mem_cons_of_mem _ inTail)) error member

/-- On a uniform dyadic source side, the complete sample discrepancy decays like its squared step size. No
identification of the inverted arc and its chord, and no infinite limiting argument, is used. -/
theorem dyadic_error_bound {sources : List Cell.Basic.CellModel} (cells :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPathSamples.Cells sources) {density lower movement :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPathSamples.Coordinate}
    (depth : Nat) (count : sources.length = 2 ^ depth) (lowerPositive : 0 < lower)
    (coefficients : cells.CoefficientsBounded density) (finishes : ∀ source ∈ sources, lower ≤
      Data.Gaussian.Norm.Basic.normSq source.finish)
    (movements : ∀ source ∈ sources, Data.Gaussian.Norm.Basic.normSq source.displacement ≤
      Geometric.Basic.quarterRadius movement depth) :
    Data.Gaussian.Norm.Basic.normSq ((PathModel.mk sources).integralSample -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum cells.values) ≤
      (density / lower) * movement * Geometric.Basic.quarterRadius movement depth := by
  rw [← cells.errors_sum]
  have estimate := Data.Gaussian.Norm.Sum.Bounds.normSq_sum_le cells.errors _
    (cells.errors_bounded lowerPositive coefficients finishes movements)
  rw [cells.errors_length, count] at estimate
  apply estimate.trans_eq
  calc
    _ = (density / lower) * Geometric.Basic.quarterRadius movement depth *
        (((2 ^ depth : Nat) : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPathSamples.Coordinate) * (((2 ^ depth :
          Nat) : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPathSamples.Coordinate) *
          Geometric.Basic.quarterRadius movement depth)) := by ring1
    _ = _ := by rw [DyadicCount.dyadic_count_cancel]; ring1

end Cells
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPathSamples
