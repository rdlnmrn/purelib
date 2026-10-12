module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.SignTest
import Purelib.Geometry.Projective.Hermitian.Atom
public import Purelib.Geometry.Projective.Hermitian.Formula.Basic
public import Purelib.Geometry.Projective.Hermitian.Pullback
import Purelib.Geometry.Projective.Homography.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Geometry.Projective.Hermitian.Basic

public section

open Purelib

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

namespace Purelib.Geometry.Projective.Hermitian.Formula

/-- Pull a tail-coordinate formula atom back through a matrix. -/
@[expose] def pullbackAtom (matrix :
  GaussianMatrix) (atom : Hermitian.Atom) : Hermitian.Atom :=
  ⟨Hermitian.pullbackForm matrix atom.form, atom.sign⟩

/-- Pull back every atom of a finite formula while preserving its conjunction and disjunction tree. -/
@[expose] def BoundaryFormula.pullback (matrix :
  GaussianMatrix) : Formula.BoundaryFormula → Formula.BoundaryFormula
  | BoundaryFormula.truth => BoundaryFormula.truth
  | BoundaryFormula.falsity => BoundaryFormula.falsity
  | BoundaryFormula.atom testAtom => BoundaryFormula.atom (pullbackAtom matrix
    testAtom)
  | BoundaryFormula.and left right =>
      BoundaryFormula.and (left.pullback matrix) (right.pullback matrix)
  | BoundaryFormula.or left right =>
      BoundaryFormula.or (left.pullback matrix) (right.pullback matrix)

/-- Away from the homography pole, the pulled-back formula holds exactly when the original holds at the homographic
image.

Each atom is transported by the positive denominator quadrance, preserving all sign conventions. -/
theorem BoundaryFormula.pullback_iff
    (matrix : GaussianMatrix) (formula : Formula.BoundaryFormula) (value :
      Data.Gaussian.Basic.Canonical)
    (denominatorNonzero : Homography.Basic.denominator matrix value ≠ 0) :
    (formula.pullback matrix).Holds value ↔
      formula.Holds (Homography.Basic.homographic matrix value) := by
  induction formula with
  | truth => exact Iff.rfl
  | falsity => exact Iff.rfl
  | atom atom =>
      simp only [Geometry.Projective.Hermitian.Formula.BoundaryFormula.pullback, BoundaryFormula.Holds, Atom.Holds,
        pullbackAtom,
        Hermitian.eval_pullbackForm matrix atom.form value denominatorNonzero, -eq_self, -iff_self]
      exact Data.Rat.SignTest.holds_mul_pos_iff atom.sign
        (Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix value))
        (atom.form.eval (Homography.Basic.homographic matrix value))
        (Data.Gaussian.Norm.Basic.normSq_pos denominatorNonzero)
  | and left right leftHypothesis rightHypothesis =>
      simp only [Geometry.Projective.Hermitian.Formula.BoundaryFormula.pullback, BoundaryFormula.Holds, -eq_self,
        -iff_self]
      exact and_congr leftHypothesis rightHypothesis
  | or left right leftHypothesis rightHypothesis =>
      simp only [Geometry.Projective.Hermitian.Formula.BoundaryFormula.pullback, BoundaryFormula.Holds, -eq_self,
        -iff_self]
      exact or_congr leftHypothesis rightHypothesis
end Purelib.Geometry.Projective.Hermitian.Formula

end
