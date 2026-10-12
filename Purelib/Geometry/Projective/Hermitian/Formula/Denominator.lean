module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.SignTest
public import Purelib.Geometry.Projective.Hermitian.Affine
import Purelib.Geometry.Projective.Hermitian.Atom
public import Purelib.Geometry.Projective.Hermitian.Formula.Basic
public import Purelib.Geometry.Projective.Homography.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Geometry.Projective.Hermitian.Basic

open Purelib

open Purelib.Data.Rat

open Purelib.Data.Rat.SignTest

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Hermitian

open Purelib.Geometry.Projective.Hermitian.Formula

open Purelib.LinearAlgebra.Coordinates2.Matrix

section
@[expose] public section

/-!
# Finite Hermitian formulas for raw CCL parser states

Every predicate in an arbitrary finite raw-parser state is compiled into a
finite Boolean formula whose atoms are signs of four-coefficient rational
Hermitian forms.  Unfinished sector prefixes use the direct finite
disjunction of their `8/4/2` candidate rows.  This keeps the implementation
small while preserving the exact weak/strict boundary convention.
-/

namespace Purelib.Geometry.Projective.Hermitian.Formula

/-- The positive squared-norm test for a homography denominator.

The single Hermitian atom tests the affine expression given by the lower row of the matrix. -/
def denominatorFormula (matrix :
  GaussianMatrix) : Formula.BoundaryFormula :=
  .atom ⟨Hermitian.affineNormForm matrix.c matrix.d, .positive⟩

/-- The denominator formula holds exactly where the affine denominator is nonzero. -/
theorem denominatorFormula_iff (matrix :
  GaussianMatrix) (value : Data.Gaussian.Basic.Canonical) :
    (denominatorFormula matrix).Holds value ↔
      Homography.Basic.denominator matrix value ≠ 0 := by
  simp only [denominatorFormula, BoundaryFormula.Holds, Atom.Holds,
    Data.Rat.SignTest.Holds,
    Hermitian.eval_affineNormForm, Homography.Basic.denominator]
  constructor
  · intro positive zero
    rw [zero, Data.Gaussian.Norm.Basic.normSq_zero] at positive
    exact (lt_irrefl (0 : Fraction.Rational) positive).elim
  · exact Data.Gaussian.Norm.Basic.normSq_pos
end Purelib.Geometry.Projective.Hermitian.Formula

end
