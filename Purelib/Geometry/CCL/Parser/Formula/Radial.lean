module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Data.CCL.Encoding.Parser.Semantics.Basic
import Purelib.Data.CCL.Encoding.Parser.Syntax
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.SignTest
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Projective.Hermitian.Formula.Basic
public import Purelib.Geometry.Projective.Hermitian.Formula.Pullback
import Purelib.Geometry.Projective.Hermitian.Radial
import Purelib.Geometry.Projective.Homography.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field

public section

open Purelib

open Purelib.Data.CCL.Encoding.Parser

open Purelib.Data.Rat

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

namespace Purelib.Geometry.CCL.Parser.Formula

/-- BoundaryFormula for one completed radial bracket through a homography. -/
@[expose] def radialFormula (kind : Syntax.BlockKind) (exponent : Nat)
  (matrix : GaussianMatrix) :
    Formula.BoundaryFormula :=
  let tailFormula : Formula.BoundaryFormula := match kind with
    | .initialHigh =>
        BoundaryFormula.and
          (BoundaryFormula.atom ⟨Hermitian.affineNormComparisonForm ((2 : Fraction.Rational) ^ exponent),
            .nonnegative⟩)
          (BoundaryFormula.atom ⟨Hermitian.affineNormComparisonForm
            ((2 : Fraction.Rational) ^ (exponent + 1)), .negative⟩)
    | .initialLow =>
        BoundaryFormula.and
          (BoundaryFormula.atom ⟨Hermitian.scaledNormComparisonForm exponent 1, .nonnegative⟩)
          (BoundaryFormula.atom ⟨Hermitian.scaledNormComparisonForm exponent 2, .negative⟩)
    | .loop =>
        BoundaryFormula.and
          (BoundaryFormula.atom ⟨Hermitian.affineNormComparisonForm ((2 : Fraction.Rational) ^ exponent),
            .positive⟩)
          (BoundaryFormula.atom ⟨Hermitian.affineNormComparisonForm
            ((2 : Fraction.Rational) ^ (exponent + 1)), .nonpositive⟩)
  BoundaryFormula.pullback matrix tailFormula

/-- The radial formula expresses the parser bracket after the homography.

A nonzero denominator identifies the pulled-back Hermitian comparisons with the appropriate initial or loop radial
inequalities. -/
theorem radialFormula_iff
    (kind : Syntax.BlockKind) (exponent : Nat) (matrix : GaussianMatrix) (value :
      Data.Gaussian.Basic.Canonical)
    (denominatorNonzero : Homography.Basic.denominator matrix value ≠ 0) :
    (radialFormula kind exponent matrix).Holds value ↔
      Semantics.Basic.radialBracket kind exponent (Homography.Basic.homographic matrix value) := by
  unfold radialFormula
  apply (BoundaryFormula.pullback_iff matrix _ value denominatorNonzero).trans
  cases kind with
  | initialHigh =>
      simp only [BoundaryFormula.Holds, Atom.Holds, Data.Rat.SignTest.Holds, Semantics.Basic.radialBracket,
        Hermitian.eval_affineNormComparisonForm, -eq_self, -iff_self]
      rewrite [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      exact and_congr Fraction.Order.Boundary.sub_nonnegative_iff Fraction.Order.Boundary.sub_negative_iff
  | initialLow =>
      simp only [BoundaryFormula.Holds, Atom.Holds, Data.Rat.SignTest.Holds, Semantics.Basic.radialBracket,
        Hermitian.eval_scaledNormComparisonForm, -eq_self, -iff_self]
      rewrite [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      exact and_congr Fraction.Order.Boundary.sub_nonnegative_iff Fraction.Order.Boundary.sub_negative_iff
  | loop =>
      simp only [BoundaryFormula.Holds, Atom.Holds, Data.Rat.SignTest.Holds, Semantics.Basic.radialBracket,
        Hermitian.eval_affineNormComparisonForm, -eq_self, -iff_self]
      rewrite [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      exact and_congr Fraction.Order.Boundary.sub_positive_iff Fraction.Order.Boundary.sub_nonpositive_iff
end Purelib.Geometry.CCL.Parser.Formula

end
