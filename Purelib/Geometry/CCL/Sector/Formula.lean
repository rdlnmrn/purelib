module
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Rat.SignTest
import Purelib.Geometry.Projective.Hermitian.Atom
public import Purelib.Geometry.Projective.Hermitian.Comparison
public import Purelib.Geometry.Projective.Hermitian.Formula.Basic
import Purelib.Geometry.Projective.Homography.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Projective.Hermitian.Basic

public section

open Purelib

open Purelib.Data.ComplexContinuedFraction.Encoding

open Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic

open Purelib.Data.Rat.SignTest

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Hermitian

open Purelib.Geometry.Projective.Hermitian.Formula

open Purelib.LinearAlgebra.Coordinates2.Matrix

/-!
# Finite Hermitian formulas for raw CCL parser states

Every predicate in an arbitrary finite raw-parser state is compiled into a
finite Boolean formula whose atoms are signs of four-coefficient rational
Hermitian forms.  Unfinished sector prefixes use the direct finite
disjunction of their `8/4/2` candidate rows.  This keeps the implementation
small while preserving the exact weak/strict boundary convention.
-/

namespace Purelib.Geometry.CCL.Sector

/-- Exact finite formula for one sector row through a homography. -/
@[expose] def sectorFormula (sector : Data.ComplexContinuedFraction.Encoding.Sector)
  (matrix :
  GaussianMatrix) : Formula.BoundaryFormula :=
  match sector with
  | .east =>
      .and (.atom ⟨Hermitian.realComparisonForm matrix (1 / 2), .nonnegative⟩)
        (.and (.atom ⟨Hermitian.imagComparisonForm matrix (-1 / 2), .positive⟩)
          (.atom ⟨Hermitian.imagComparisonForm matrix (1 / 2), .negative⟩))
  | .northEast =>
      .and (.atom ⟨Hermitian.realComparisonForm matrix (1 / 2), .nonnegative⟩)
        (.atom ⟨Hermitian.imagComparisonForm matrix (1 / 2), .nonnegative⟩)
  | .north =>
      .and (.atom ⟨Hermitian.realComparisonForm matrix (-1 / 2), .positive⟩)
        (.and (.atom ⟨Hermitian.realComparisonForm matrix (1 / 2), .negative⟩)
          (.atom ⟨Hermitian.imagComparisonForm matrix (1 / 2), .nonnegative⟩))
  | .northWest =>
      .and (.atom ⟨Hermitian.realComparisonForm matrix (-1 / 2), .nonpositive⟩)
        (.atom ⟨Hermitian.imagComparisonForm matrix (1 / 2), .nonnegative⟩)
  | .west =>
      .and (.atom ⟨Hermitian.realComparisonForm matrix (-1 / 2), .nonpositive⟩)
        (.and (.atom ⟨Hermitian.imagComparisonForm matrix (-1 / 2), .positive⟩)
          (.atom ⟨Hermitian.imagComparisonForm matrix (1 / 2), .negative⟩))
  | .southWest =>
      .and (.atom ⟨Hermitian.realComparisonForm matrix (-1 / 2), .nonpositive⟩)
        (.atom ⟨Hermitian.imagComparisonForm matrix (-1 / 2), .nonpositive⟩)
  | .south =>
      .and (.atom ⟨Hermitian.realComparisonForm matrix (-1 / 2), .positive⟩)
        (.and (.atom ⟨Hermitian.realComparisonForm matrix (1 / 2), .negative⟩)
          (.atom ⟨Hermitian.imagComparisonForm matrix (-1 / 2), .nonpositive⟩))
  | .southEast =>
      .and (.atom ⟨Hermitian.realComparisonForm matrix (1 / 2), .nonnegative⟩)
        (.atom ⟨Hermitian.imagComparisonForm matrix (-1 / 2), .nonpositive⟩)

/-- The sector formula characterizes the homographic image's sector.

The denominator must be nonzero; each of the eight sectors retains its specified strict and weak boundary comparisons.
-/
theorem sectorFormula_iff
    (sector : Data.ComplexContinuedFraction.Encoding.Sector) (matrix : GaussianMatrix) (value :
      Data.Gaussian.Basic.Canonical)
    (denominatorNonzero : Homography.Basic.denominator matrix value ≠ 0) :
    (sectorFormula sector matrix).Holds value ↔
      sector.Holds (Homography.Basic.homographic matrix value) := by
  cases sector with
  | east =>
      exact and_congr (Hermitian.real_homographic_ge_iff matrix value (1 / 2) denominatorNonzero).symm (and_congr
        (Hermitian.imag_homographic_gt_iff matrix value (-1 / 2) denominatorNonzero).symm
        (Hermitian.imag_homographic_lt_iff matrix value (1 / 2) denominatorNonzero).symm)
  | northEast =>
      exact and_congr (Hermitian.real_homographic_ge_iff matrix value (1 / 2) denominatorNonzero).symm
        (Hermitian.imag_homographic_ge_iff matrix value (1 / 2) denominatorNonzero).symm
  | north =>
      exact and_congr (Hermitian.real_homographic_gt_iff matrix value (-1 / 2) denominatorNonzero).symm (and_congr
        (Hermitian.real_homographic_lt_iff matrix value (1 / 2) denominatorNonzero).symm
        (Hermitian.imag_homographic_ge_iff matrix value (1 / 2) denominatorNonzero).symm)
  | northWest =>
      exact and_congr (Hermitian.real_homographic_le_iff matrix value (-1 / 2) denominatorNonzero).symm
        (Hermitian.imag_homographic_ge_iff matrix value (1 / 2) denominatorNonzero).symm
  | west =>
      exact and_congr (Hermitian.real_homographic_le_iff matrix value (-1 / 2) denominatorNonzero).symm (and_congr
        (Hermitian.imag_homographic_gt_iff matrix value (-1 / 2) denominatorNonzero).symm
        (Hermitian.imag_homographic_lt_iff matrix value (1 / 2) denominatorNonzero).symm)
  | southWest =>
      exact and_congr (Hermitian.real_homographic_le_iff matrix value (-1 / 2) denominatorNonzero).symm
        (Hermitian.imag_homographic_le_iff matrix value (-1 / 2) denominatorNonzero).symm
  | south =>
      exact and_congr (Hermitian.real_homographic_gt_iff matrix value (-1 / 2) denominatorNonzero).symm (and_congr
        (Hermitian.real_homographic_lt_iff matrix value (1 / 2) denominatorNonzero).symm
        (Hermitian.imag_homographic_le_iff matrix value (-1 / 2) denominatorNonzero).symm)
  | southEast =>
      exact and_congr (Hermitian.real_homographic_ge_iff matrix value (1 / 2) denominatorNonzero).symm
        (Hermitian.imag_homographic_le_iff matrix value (-1 / 2) denominatorNonzero).symm
end Purelib.Geometry.CCL.Sector

end
