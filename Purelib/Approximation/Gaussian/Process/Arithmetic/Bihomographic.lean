module
import Purelib.Approximation.Gaussian.Process.Apart
public import Purelib.Approximation.Gaussian.Process.Division
public import Purelib.Approximation.Gaussian.Process.Multiplication
public import Purelib.Approximation.Gaussian.Process.Addition
import Purelib.Data.Gaussian.Field
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Projective.Bihomographic.Affine
public import Purelib.Geometry.Projective.Bihomographic.Arithmetic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Bihomographic.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Bihomographic

open Purelib.Geometry.Projective.Line

open Purelib.Geometry.Projective.Line.Proj

section
@[expose] public section

/-!
# Bihomographic semantics of progressive arithmetic

The enclosure implementation computes `+`, `-`, `*`, and `/` directly on
finite rational balls.  This module proves that its candidate predicates are
the affine instances of the paper's bihomographic initial matrices and that
all input/output decoder substitutions compose exactly.  Thus the direct
implementation and the matrix account are two certified views of the same
finite arithmetic step.
-/

namespace Purelib.Approximation.Gaussian.Process.Arithmetic.Bihomographic

/-- Progressive addition candidates have exactly the initial bihomographic semantics. -/
theorem add_candidate
    (left right : Approximation.Gaussian.Process) {state : ((Approximation.Gaussian.Process.add left right)).State}
    {value : Canonical} (possible : ((Approximation.Gaussian.Process.add left right)).Possible state
        value) :
    ∃ x y : Canonical,
      left.Possible state.1 x ∧ right.Possible state.2 y ∧
        Proj.Equivalent ((Bihomographic.Arithmetic.initial .add).affineMap x y)
          (Proj.affine value) := by
  rcases possible with ⟨x, y, xPossible, yPossible, valueEqual⟩
  refine ⟨x, y, xPossible, yPossible, ?_⟩
  rw [valueEqual, Bihomographic.Arithmetic.initial_add]
  exact Equivalent.refl _

/-- Progressive subtraction candidates have exactly the initial bihomographic semantics. -/
theorem sub_candidate
    (left right : Approximation.Gaussian.Process) {state : ((Approximation.Gaussian.Process.sub left right)).State}
    {value : Canonical} (possible : ((Approximation.Gaussian.Process.sub left right)).Possible state
        value) :
    ∃ x y : Canonical,
      left.Possible state.1 x ∧ right.Possible state.2 y ∧
        Proj.Equivalent ((Bihomographic.Arithmetic.initial .sub).affineMap x y)
          (Proj.affine value) := by
  rcases possible with
    ⟨x, negativeY, xPossible, ⟨y, yPossible, negativeEqual⟩, valueEqual⟩
  refine ⟨x, y, xPossible, yPossible, ?_⟩
  have subtraction : x + -y = x - y := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.neg_re,
        Data.Gaussian.Basic.neg_im, Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im] <;> ring1
  rw [negativeEqual, subtraction] at valueEqual
  rw [valueEqual, Bihomographic.Arithmetic.initial_sub]
  exact Equivalent.refl _

/-- Progressive multiplication candidates have exactly the initial bihomographic semantics. -/
theorem mul_candidate
    (left right : Approximation.Gaussian.Process) {state : ((Approximation.Gaussian.Process.mul left right)).State}
    {value : Canonical} (possible : ((Approximation.Gaussian.Process.mul left right)).Possible state
        value) :
    ∃ x y : Canonical,
      left.Possible state.1 x ∧ right.Possible state.2 y ∧
        Proj.Equivalent ((Bihomographic.Arithmetic.initial .mul).affineMap x y)
          (Proj.affine value) := by
  rcases possible with ⟨x, y, xPossible, yPossible, valueEqual⟩
  refine ⟨x, y, xPossible, yPossible, ?_⟩
  rw [valueEqual, Bihomographic.Arithmetic.initial_mul]
  exact Equivalent.refl _

/-- Apartness-certified progressive division candidates have exactly the projective initial division semantics and an
affine quotient. -/
theorem div_candidate
    (left right : Approximation.Gaussian.Process)
    (apart : Approximation.Gaussian.Process.Apart right)
    {state : ((Approximation.Gaussian.Process.div left right) apart).State} {value : Canonical}
    (possible : ((Approximation.Gaussian.Process.div left right) apart).Possible state value) :
    ∃ x y : Canonical,
      left.Possible state.1 x ∧ right.Possible state.2 y ∧ y ≠ 0 ∧
        Proj.Equivalent ((Bihomographic.Arithmetic.initial .div).affineMap x y)
          (Proj.affine value) := by
  rcases possible with ⟨x, y, xPossible, yPossible, valueEqual⟩
  have lower := apart.lower state.2 (right.possible_inside yPossible)
  have normPositive : 0 < Data.Gaussian.Norm.Basic.normSq y := apart.positive.trans_le lower
  have yNonzero : y ≠ 0 := by
    intro yZero
    rw [yZero, Data.Gaussian.Norm.Basic.normSq_zero] at normPositive
    exact (lt_irrefl _ normPositive).elim
  refine ⟨x, y, xPossible, yPossible, yNonzero, ?_⟩
  rw [valueEqual]
  exact Affine.initial_div_equivalent x y yNonzero
end Purelib.Approximation.Gaussian.Process.Arithmetic.Bihomographic

end
