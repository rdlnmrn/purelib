module

public import Purelib.Algebra.Monogenic.Cyclic
import Purelib.Algebra.Ring.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# The finite coefficient algebra of a cyclic matrix

Commuting structural matrices retain exact executable scalar operations. The
cyclic reconstruction theorem proves commutativity, so this algebra requires
no quotient carrier, field completion or invertibility of arbitrary nonzeros.
-/

public section

namespace Purelib.Algebra.Monogenic.Cyclic

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.LinearAlgebra.Matrix
open Purelib.Algebra.FiniteSum.Fin

variable {K : Type*} [CommRing K] {dimension : Nat} {generator : SquareMatrix K dimension}

set_option genInjectivity false in
/-- An actual structural matrix commuting with the same retained cyclic generator.

The original matrix is the executable payload. Its retained equality certifies
membership in the cyclic coefficient algebra; no recomputation or quotient
equivalence replaces that matrix.
-/
structure Element (cyclic : Cyclic generator) where
  /-- The actual original structural matrix over the coefficient ring. -/
  matrix : SquareMatrix K dimension
  /-- The actual matrix commutes with the same original generator. -/
  commutes : Multiplication.mul matrix generator = Multiplication.mul generator matrix

constructive_injectivity Element

namespace Element

variable {cyclic : Cyclic generator}

/-- Equality of the retained original matrices identifies their certified algebra elements. -/
theorem ext {left right : Element cyclic} (same : left.matrix = right.matrix) : left = right := by
  cases left
  cases right
  cases same
  rfl

/-- Finite entry comparisons decide equality of the same retained algebra elements. -/
instance [DecidableEq K] : DecidableEq (Element cyclic) := fun left right =>
  if same : ∀ row column, left.matrix row column = right.matrix row column then
    isTrue (ext (matrix_ext same))
  else isFalse (fun equal => same (fun row column => matrix_eq_at (congrArg Element.matrix equal) row column))

/-- Retain the structural zero matrix as the algebra zero. -/
instance : Zero (Element cyclic) where
  zero := ⟨Arithmetic.zero, by
    apply matrix_ext
    intro row column
    rewrite [Multiplication.mul_apply, Multiplication.mul_apply]
    apply sumFin_congr
    intro middle
    rewrite [Arithmetic.zero_apply, Arithmetic.zero_apply, zero_mul, mul_zero]
    rfl⟩

/-- Retain the same scalar identity matrix as the algebra unit. -/
instance : One (Element cyclic) where
  one := ⟨Multiplication.scaleIdentity 1,
    (Multiplication.unit_mul generator).trans (Multiplication.mul_unit generator).symm⟩

/-- Add the same retained structural matrices and transport their original commutations. -/
instance : Add (Element cyclic) where
  add left right := ⟨Arithmetic.add left.matrix right.matrix, by
    rewrite [Arithmetic.add_mul, Arithmetic.mul_add, left.commutes, right.commutes]
    rfl⟩

/-- Negate the same retained structural matrix in the cyclic coefficient algebra. -/
instance : Neg (Element cyclic) where
  neg value := ⟨Arithmetic.scale (-1) value.matrix, by
    rewrite [Arithmetic.scale_mul, Arithmetic.mul_scale, value.commutes]
    rfl⟩

/-- Multiply the same retained structural matrices and compose their original commutations. -/
instance : Mul (Element cyclic) where
  mul left right := ⟨Multiplication.mul left.matrix right.matrix, by
    rewrite [Multiplication.mul_assoc, right.commutes, ← Multiplication.mul_assoc, left.commutes,
      Multiplication.mul_assoc]
    rfl⟩

/-- The original structural matrix operations give an executable commutative ring.

Commutativity follows from the same retained cyclic table. Only matrix
associativity and finite scalar readbacks enter the other ring laws.
-/
instance instCommRing : CommRing (Element cyclic) :=
  Purelib.Algebra.Ring.commRingOfAxioms
    (fun first second third => ext (Arithmetic.add_assoc first.matrix second.matrix third.matrix))
    (fun value => ext (Arithmetic.zero_add value.matrix))
    (fun value => ext (by
      apply matrix_ext
      intro row column
      change Arithmetic.add (Arithmetic.scale (-1) value.matrix) value.matrix row column =
        (Arithmetic.zero : SquareMatrix K dimension) row column
      rewrite [Arithmetic.add_apply, Arithmetic.scale_apply, Arithmetic.zero_apply]
      ring0))
    (fun first second third => ext (Multiplication.mul_assoc first.matrix second.matrix third.matrix))
    (fun left right => ext (cyclic.commuting_pair left.matrix right.matrix left.commutes right.commutes))
    (fun value => ext (Multiplication.unit_mul value.matrix))
    (fun factor left right => ext (Arithmetic.mul_add factor.matrix left.matrix right.matrix))
    (fun left right => left + -right) (fun _ _ => rfl)

/-- Multiplication consumes the same retained matrix payloads. -/
theorem mul_matrix (left right : Element cyclic) :
    (left * right).matrix = Multiplication.mul left.matrix right.matrix := rfl

/-- Addition consumes the same retained matrix payloads. -/
theorem add_matrix (left right : Element cyclic) :
    (left + right).matrix = Arithmetic.add left.matrix right.matrix := rfl

/-- Negation scales the same retained original matrix entries by negative one. -/
theorem neg_matrix (value : Element cyclic) : (-value).matrix = Arithmetic.scale (-1) value.matrix := rfl

/-- A finite sum reads the sum of the same original matrix entries. -/
theorem sumFin_apply {count : Nat} (values : Fin count → Element cyclic) (row column : Fin dimension) :
    (sumFin values).matrix row column = sumFin (fun index => (values index).matrix row column) := by
  induction count with
  | zero => exact Arithmetic.zero_apply row column
  | succ count previous =>
      rewrite [sumFin_succ, sumFin_succ, add_matrix, Arithmetic.add_apply, previous]
      rfl

/-- The same original distinguished column determines equality of two algebra elements. -/
theorem eq_of_column (left right : Element cyclic)
    (entries : ∀ row, left.matrix row cyclic.origin = right.matrix row cyclic.origin) : left = right := by
  apply ext
  apply matrix_ext
  intro row column
  rewrite [cyclic.reconstruct_entry left.matrix left.commutes row column,
    cyclic.reconstruct_entry right.matrix right.commutes row column]
  apply sumFin_congr
  intro index
  exact congrArg (· * cyclic.powers index row column) (entries index)

/-- A finite algebra power retains the same original finite matrix power. -/
theorem pow_matrix (value : Element cyclic) (exponent : Nat) :
    (value ^ exponent).matrix = Arithmetic.power value.matrix exponent := by
  induction exponent with
  | zero => rfl
  | succ exponent previous =>
      rewrite [pow_succ, mul_matrix, Arithmetic.power_succ, previous]
      rfl

/-- The same original generator is an element of its own cyclic coefficient algebra. -/
@[expose] def root (cyclic : Cyclic generator) : Element cyclic := ⟨generator, rfl⟩

/-- The retained algebra generator has its same original structural matrix. -/
theorem root_matrix (cyclic : Cyclic generator) : (root cyclic).matrix = generator := rfl

/-- Embed one coefficient as its retained scalar identity matrix. -/
@[expose] def scalar (cyclic : Cyclic generator) (value : K) : Element cyclic :=
  ⟨Multiplication.scaleIdentity value, by
    apply matrix_ext
    intro row column
    calc
      _ = value * generator row column :=
        (matrix_eq_at (Multiplication.scaleIdentity_mul value generator) row column).trans
          (matrixOfFn_apply _ row column)
      _ = generator row column * value := mul_comm _ _
      _ = _ := ((matrix_eq_at (Multiplication.mul_scaleIdentity generator value) row column).trans
        (matrixOfFn_apply _ row column)).symm⟩

/-- Multiplication by an embedded coefficient scales each original matrix entry. -/
theorem scalar_mul_apply (cyclic : Cyclic generator) (coefficient : K) (value : Element cyclic)
    (row column : Fin dimension) :
    (scalar cyclic coefficient * value).matrix row column = coefficient * value.matrix row column :=
  (matrix_eq_at (Multiplication.scaleIdentity_mul coefficient value.matrix) row column).trans
    (matrixOfFn_apply _ row column)

/-- Scalar embedding preserves zero with its original structural matrix. -/
theorem scalar_zero (cyclic : Cyclic generator) : scalar cyclic 0 = 0 := by
  apply ext
  apply matrix_ext
  intro row column
  change (Multiplication.scaleIdentity (0 : K)) row column = (Arithmetic.zero : SquareMatrix K dimension) row column
  rewrite [Multiplication.scaleIdentity_apply, Arithmetic.zero_apply]
  split <;> rfl

/-- Scalar embedding preserves the same original unit matrix. -/
theorem scalar_one (cyclic : Cyclic generator) : scalar cyclic 1 = 1 := rfl

/-- Scalar embedding preserves coefficient addition entry by entry. -/
theorem scalar_add (cyclic : Cyclic generator) (left right : K) :
    scalar cyclic (left + right) = scalar cyclic left + scalar cyclic right := by
  apply ext
  apply matrix_ext
  intro row column
  change Multiplication.scaleIdentity (left + right) row column =
    Arithmetic.add (Multiplication.scaleIdentity left) (Multiplication.scaleIdentity right) row column
  rewrite [Arithmetic.add_apply, Multiplication.scaleIdentity_apply, Multiplication.scaleIdentity_apply,
    Multiplication.scaleIdentity_apply]
  split
  · rfl
  · exact (add_zero (0 : K)).symm

/-- Scalar embedding preserves coefficient multiplication with the original structural product. -/
theorem scalar_mul (cyclic : Cyclic generator) (left right : K) :
    scalar cyclic (left * right) = scalar cyclic left * scalar cyclic right := by
  apply ext
  apply matrix_ext
  intro row column
  change Multiplication.scaleIdentity (left * right) row column =
    Multiplication.mul (Multiplication.scaleIdentity left) (Multiplication.scaleIdentity right) row column
  have product := matrix_eq_at
    (Multiplication.scaleIdentity_mul left (Multiplication.scaleIdentity right)) row column
  have productEntry : Multiplication.mul (Multiplication.scaleIdentity left) (Multiplication.scaleIdentity right)
      row column = left * Multiplication.scaleIdentity right row column :=
    product.trans (matrixOfFn_apply _ row column)
  rewrite [productEntry, Multiplication.scaleIdentity_apply, Multiplication.scaleIdentity_apply]
  split
  · rfl
  · exact (mul_zero left).symm

/-- Scalar embedding preserves coefficient negation with the same original matrices. -/
theorem scalar_neg (cyclic : Cyclic generator) (value : K) : scalar cyclic (-value) = -scalar cyclic value := by
  apply ext
  apply matrix_ext
  intro row column
  change Multiplication.scaleIdentity (-value) row column =
    Arithmetic.scale (-1) (Multiplication.scaleIdentity value) row column
  rewrite [Arithmetic.scale_apply, Multiplication.scaleIdentity_apply, Multiplication.scaleIdentity_apply]
  split <;> ring0

/-- The original distinguished coordinate proves that scalar embedding is injective. -/
theorem scalar_injective (cyclic : Cyclic generator) {left right : K}
    (same : scalar cyclic left = scalar cyclic right) : left = right := by
  have scalarEntry := matrix_eq_at (congrArg Element.matrix same) cyclic.origin cyclic.origin
  change Multiplication.scaleIdentity left cyclic.origin cyclic.origin =
    Multiplication.scaleIdentity right cyclic.origin cyclic.origin at scalarEntry
  rewrite [Multiplication.scaleIdentity_apply, Multiplication.scaleIdentity_apply,
    if_pos rfl, if_pos rfl] at scalarEntry
  exact scalarEntry

end Element

end Purelib.Algebra.Monogenic.Cyclic

end
