module

import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.Algebra.Field.Squares
import Purelib.Algebra.Field.ExplicitField
import Purelib.LinearAlgebra.Coordinates3.Vector

public import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Algebra.Group.Negation
import Purelib.Data.Nat.Order
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field
open scoped Purelib.Data.Nat

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

section
public section

/-!
# Rational rotations, section 3: anchors

This module formalizes Definitions 7 and 11, Lemma 8, Theorems 9, 12, and
13, and all four parts of Corollary 10.  Every matrix identity is checked by
finite coordinate normalization.
-/

namespace Purelib.LinearAlgebra.Coordinates3.Antisymmetric

variable {K : Type*} [ExplicitField K]

/-- Definition 7: the antisymmetric anchor matrix of `(t,r,s)`. -/
@[expose] def anchor (vector : Vector K) : Matrix3 K :=
  ⟨0, vector.s, -vector.r,
    -vector.s, 0, vector.t,
    vector.r, -vector.t, 0⟩

/-- The displayed inverse coordinate map from an antisymmetric matrix. -/
@[expose] def anchorVector (matrix : Matrix3 K) : Vector K :=
  ⟨matrix.rs, matrix.st, matrix.tr⟩

/-- Anchor construction preserves vector addition coordinatewise. -/
theorem anchor_add (left right : Vector K) :
    anchor (Vector3.add left right) =
      Matrix3.add (anchor left) (anchor right) := by
  ext <;> unfold anchor Vector3.add Matrix3.add <;> ring1

/-- Anchor construction preserves scalar multiplication coordinatewise. -/
theorem anchor_scale (scalar : K) (vector : Vector K) :
    anchor (Vector3.scale scalar vector) = Matrix3.scale scalar (anchor vector) := by
  ext <;> unfold anchor Vector3.scale Matrix3.scale <;> ring1

/-- The antisymmetric outer-product numerator is the anchor of the cross
product. -/
theorem outer_commutator_eq_anchor_cross (left right : Vector K) :
    Matrix3.sub (Matrix3.outer left right) (Matrix3.outer right left) =
      anchor (Vector3.cross left right) := by
  ext <;> unfold Matrix3.sub Matrix3.outer anchor Vector3.cross <;> ring1

/-- Negating a vector negates its anchor. -/
theorem anchor_neg (vector : Vector K) :
    anchor (Vector3.neg vector) = Matrix3.neg (anchor vector) := by
  ext <;> unfold anchor Vector3.neg Matrix3.neg <;> ring1

/-- Every anchor is antisymmetric. -/
theorem anchor_isAntisymmetric (vector : Vector K) :
    Matrix3.IsAntisymmetric (anchor vector) := by
  unfold Matrix3.IsAntisymmetric
  ext <;> unfold anchor Matrix3.transpose Matrix3.neg <;> ring1

/-- Reading the three independent entries of an anchor recovers its vector. -/
@[simp] theorem anchorVector_anchor (vector : Vector K) :
    anchorVector (anchor vector) = vector := by
  rfl

/-- The anchor map is injective, with `anchorVector` as an explicit left
inverse. -/
theorem anchor_injective {left right : Vector K}
    (equalAnchors : anchor left = anchor right) : left = right := by
  have recovered := congrArg anchorVector equalAnchors
  simpa only [anchorVector_anchor] using recovered

/-- In characteristic different from two, `anchorVector` is also a right
inverse on explicitly antisymmetric matrices. -/
theorem anchor_anchorVector_of_isAntisymmetric (matrix : Matrix3 K)
    (twoNonzero : (2 : K) ≠ 0)
    (antisymmetric : matrix.IsAntisymmetric) :
    anchor (anchorVector matrix) = matrix := by
  have ttRelation : matrix.tt = -matrix.tt :=
    congrArg Matrix3.tt antisymmetric
  have rrRelation : matrix.rr = -matrix.rr :=
    congrArg Matrix3.rr antisymmetric
  have ssRelation : matrix.ss = -matrix.ss :=
    congrArg Matrix3.ss antisymmetric
  have trRelation : matrix.rt = -matrix.tr :=
    congrArg Matrix3.tr antisymmetric
  have rsRelation : matrix.sr = -matrix.rs :=
    congrArg Matrix3.rs antisymmetric
  have stRelation : matrix.ts = -matrix.st :=
    congrArg Matrix3.st antisymmetric
  have ttZero : matrix.tt = 0 :=
    (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] (twoNonzero : (2 : K) ≠ 0) (value : K) (twiceZero : 2 *
      value = 0) => (Purelib.Algebra.Field.Characteristic.Nonzero.eq_zero_of_two_mul_eq_zero (K := K) twoNonzero value
      twiceZero : value = 0)) twoNonzero matrix.tt (by
      have shifted := congrArg (fun value => value + matrix.tt) ttRelation
      calc
        2 * matrix.tt = matrix.tt + matrix.tt := by ring1
        _ = -matrix.tt + matrix.tt := shifted
        _ = 0 := neg_add_cancel matrix.tt)
  have rrZero : matrix.rr = 0 :=
    (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] (twoNonzero : (2 : K) ≠ 0) (value : K) (twiceZero : 2 *
      value = 0) => (Purelib.Algebra.Field.Characteristic.Nonzero.eq_zero_of_two_mul_eq_zero (K := K) twoNonzero value
      twiceZero : value = 0)) twoNonzero matrix.rr (by
      have shifted := congrArg (fun value => value + matrix.rr) rrRelation
      calc
        2 * matrix.rr = matrix.rr + matrix.rr := by ring1
        _ = -matrix.rr + matrix.rr := shifted
        _ = 0 := neg_add_cancel matrix.rr)
  have ssZero : matrix.ss = 0 :=
    (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] (twoNonzero : (2 : K) ≠ 0) (value : K) (twiceZero : 2 *
      value = 0) => (Purelib.Algebra.Field.Characteristic.Nonzero.eq_zero_of_two_mul_eq_zero (K := K) twoNonzero value
      twiceZero : value = 0)) twoNonzero matrix.ss (by
      have shifted := congrArg (fun value => value + matrix.ss) ssRelation
      calc
        2 * matrix.ss = matrix.ss + matrix.ss := by ring1
        _ = -matrix.ss + matrix.ss := shifted
        _ = 0 := neg_add_cancel matrix.ss)
  apply Matrix3.ext
  · exact ttZero.symm
  · rfl
  · exact stRelation.symm
  · exact trRelation.symm
  · exact rrZero.symm
  · rfl
  · rfl
  · exact rsRelation.symm
  · exact ssZero.symm

/-- Lemma 8: right multiplication by the anchor is the cross product with
the anchor vector in the paper's row-vector convention. -/
theorem rowMul_anchor (vector other : Vector K) :
    Matrix3.rowMul other (anchor vector) = Vector3.cross vector other := by
  ext <;> unfold Matrix3.rowMul anchor Vector3.cross <;> ring1

/-- The anchor vector itself lies in the right kernel of its anchor. -/
@[simp] theorem rowMul_self_anchor (vector : Vector K) :
    Matrix3.rowMul vector (anchor vector) = Vector3.zero := by
  rw [rowMul_anchor]
  ext <;> unfold Vector3.cross Vector3.zero <;> ring1

/-- Theorem 9: the anchor product identity
`Aᵥ Aₓ = wᵀv - (v·w)I`. -/
theorem anchor_product (vector other : Vector K) :
    Matrix3.mul (anchor vector) (anchor other) =
      Matrix3.sub (Matrix3.outer other vector)
        (Matrix3.scale (Vector3.dot vector other) Matrix3.identity) := by
  ext <;> unfold Matrix3.mul anchor Matrix3.sub Matrix3.outer
    Matrix3.scale Matrix3.identity Vector3.dot <;> ring1

/-- Corollary 10.1: the square of an anchor. -/
theorem anchor_square (vector : Vector K) :
    Matrix3.mul (anchor vector) (anchor vector) =
      Matrix3.sub (Matrix3.outer vector vector)
        (Matrix3.scale (Vector3.quadrance vector) Matrix3.identity) := by
  simpa only [Vector3.quadrance] using anchor_product vector vector

/-- Corollary 10.2: the anchor commutator is the anchor of the reversed cross
product. -/
theorem anchor_commutator (vector other : Vector K) :
    Matrix3.sub
        (Matrix3.mul (anchor vector) (anchor other))
        (Matrix3.mul (anchor other) (anchor vector)) =
      anchor (Vector3.cross other vector) := by
  ext <;> unfold Matrix3.sub Matrix3.mul anchor Vector3.cross <;> ring1

/-- Corollary 10.3: the anchor sandwich identity. -/
theorem anchor_sandwich (vector other : Vector K) :
    Matrix3.mul (Matrix3.mul (anchor vector) (anchor other))
        (anchor vector) =
      Matrix3.scale (-(Vector3.dot vector other)) (anchor vector) := by
  ext <;> unfold Matrix3.mul Matrix3.scale anchor Vector3.dot <;> ring1

/-- Corollary 10.4: trace of a product of two anchors. -/
theorem trace_anchor_product (vector other : Vector K) :
    Matrix3.trace (Matrix3.mul (anchor vector) (anchor other)) =
      -2 * Vector3.dot vector other := by
  unfold Matrix3.trace Matrix3.mul anchor Vector3.dot
  ring1

/-- Definition 11: the anchor form `-tr(AB)/2`. -/
@[expose] def anchorForm (left right : Matrix3 K) : K :=
  -Matrix3.trace (Matrix3.mul left right) / 2

/-- Definition 11: quadrance induced by the anchor form. -/
@[expose] def anchorQuadrance (matrix : Matrix3 K) : K := anchorForm matrix matrix

/-- Theorem 12: anchors preserve the dot product when two is invertible. -/
theorem anchorForm_anchor (vector other : Vector K)
    (twoNonzero : (2 : K) ≠ 0) :
    anchorForm (anchor vector) (anchor other) = Vector3.dot vector other := by
  have cancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    ExplicitField.mul_inv_cancel 2 twoNonzero
  unfold anchorForm
  rw [Coordinates3.Antisymmetric.trace_anchor_product, ExplicitField.div_eq_mul_inv]
  calc
    -(-2 * Vector3.dot vector other) * (2 : K)⁻¹ =
        Vector3.dot vector other * (2 * (2 : K)⁻¹) := by ring1
    _ = Vector3.dot vector other := by rw [cancel, mul_one]

/-- The quadrance part of Theorem 12. -/
theorem anchorQuadrance_anchor (vector : Vector K)
    (twoNonzero : (2 : K) ≠ 0) :
    anchorQuadrance (anchor vector) = Vector3.quadrance vector := by
  unfold anchorQuadrance Vector3.quadrance
  exact anchorForm_anchor vector vector twoNonzero

/-- The determinant of every anchor vanishes by direct finite expansion. -/
theorem determinant_anchor (vector : Vector K) :
    Matrix3.determinant (anchor vector) = 0 := by
  unfold Matrix3.determinant anchor
  ring1

/-- The trace of every anchor vanishes. -/
theorem trace_anchor (vector : Vector K) :
    Matrix3.trace (anchor vector) = 0 := by
  unfold Matrix3.trace anchor
  ring1

/-- Theorem 13: `det(XI-Aᵥ)=X(X²+Q(v))`. -/
theorem characteristicValue_anchor (vector : Vector K) (X : K) :
    Matrix3.characteristicValue (anchor vector) X =
      X * (X ^ 2 + Vector3.quadrance vector) := by
  unfold Matrix3.characteristicValue Matrix3.determinant Matrix3.sub
    Matrix3.scale Matrix3.identity anchor Vector3.quadrance Vector3.dot
  ring1

end Purelib.LinearAlgebra.Coordinates3.Antisymmetric

end

section
@[expose] public section

/-!
# Rational rotations, section 7: recovering the anchor

The paper's boxed antisymmetric formula is the executable definition of a
rotation's anchor.  An explicit adjugate inverse for `I + ρ` ties that cached
value to the big Cayley transform; downstream proofs use the cached formula
rather than recomputing the inverse.
-/

namespace Purelib.LinearAlgebra.Coordinates3.Antisymmetric

variable {K : Type*} [ExplicitField K]

/-- The antisymmetric part `1/2 (M-Mᵀ)` used in Theorem 35. -/
def antisymmetricPart (matrix : Coordinates3.Matrix3 K) :
  Coordinates3.Matrix3 K :=
  Coordinates3.Matrix3.scale (1 / 2) (Coordinates3.Matrix3.sub matrix (Coordinates3.Matrix3.transpose matrix))

end Purelib.LinearAlgebra.Coordinates3.Antisymmetric

end

section
open Purelib
open Purelib.Algebra.Field
open Purelib.LinearAlgebra
open Purelib.LinearAlgebra.Coordinates3
namespace Purelib.LinearAlgebra.Coordinates3.Antisymmetric
variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- An antisymmetric displayed matrix whose square vanishes is zero.

Decidable equality and the nonvanishing of two permit cancellation in its coordinate identities. -/
public theorem
  antisymmetric_eq_zero_of_square_eq_zero
  [DecidableEq K]
    (matrix : Coordinates3.Matrix3 K) (twoNonzero : (2 : K) ≠ 0)
    (antisymmetric : matrix.IsAntisymmetric)
    (squareZero : Coordinates3.Matrix3.mul matrix matrix = Coordinates3.Matrix3.zero) :
    matrix = Coordinates3.Matrix3.zero := by
  let vector := Coordinates3.Antisymmetric.anchorVector matrix
  have encodes : Coordinates3.Antisymmetric.anchor vector = matrix :=
    Coordinates3.Antisymmetric.anchor_anchorVector_of_isAntisymmetric matrix twoNonzero antisymmetric
  have anchorSquareZero :
      Coordinates3.Matrix3.mul (Coordinates3.Antisymmetric.anchor vector) (Coordinates3.Antisymmetric.anchor vector) =
        Coordinates3.Matrix3.zero := by
    rw [encodes]
    exact squareZero
  have traceZero := congrArg Coordinates3.Matrix3.trace anchorSquareZero
  rw [Coordinates3.Antisymmetric.trace_anchor_product] at traceZero
  have traceMatrixZero :
      Coordinates3.Matrix3.trace (Coordinates3.Matrix3.zero : Coordinates3.Matrix3 K) = 0 := by
    unfold Coordinates3.Matrix3.trace
    unfold Coordinates3.Matrix3.zero
    ring1
  rw [traceMatrixZero] at traceZero
  change -2 * vector.quadrance = 0 at traceZero
  have quadranceZero : vector.quadrance = 0 := by
    apply (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] (twoNonzero : (2 : K) ≠ 0) {value : K} (twiceZero :
      2 * value = 0) => (Purelib.Algebra.Field.Characteristic.Nonzero.eq_zero_of_two_mul_eq_zero (K := K) twoNonzero
      value twiceZero : value = 0)) twoNonzero
    calc
      2 * vector.quadrance = -(-2 * vector.quadrance) := by ring1
      _ = 0 := by rw [traceZero]; ring1
  have outerZero : Coordinates3.Matrix3.outer vector vector = Coordinates3.Matrix3.zero := by
    calc
      Coordinates3.Matrix3.outer vector vector =
          Coordinates3.Matrix3.sub (Coordinates3.Matrix3.outer vector vector)
            (Coordinates3.Matrix3.scale vector.quadrance Coordinates3.Matrix3.identity) := by
              rw [quadranceZero]
              ext <;> unfold Coordinates3.Matrix3.sub Coordinates3.Matrix3.scale Coordinates3.Matrix3.identity <;>
                ring1
      _ = Coordinates3.Matrix3.mul (Coordinates3.Antisymmetric.anchor vector) (Coordinates3.Antisymmetric.anchor vector)
        :=
        (Coordinates3.Antisymmetric.anchor_square vector).symm
      _ = Coordinates3.Matrix3.zero := anchorSquareZero
  have tSquare := congrArg Coordinates3.Matrix3.tt outerZero
  have rSquare := congrArg Coordinates3.Matrix3.rr outerZero
  have sSquare := congrArg Coordinates3.Matrix3.ss outerZero
  change vector.t * vector.t = 0 at tSquare
  change vector.r * vector.r = 0 at rSquare
  change vector.s * vector.s = 0 at sSquare
  have vectorZero : vector = Vector3.zero := by
    apply Vector3.ext
    · exact (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] [DecidableEq K] {value : K} (squareZero : value *
      value = 0) => (Purelib.Algebra.Field.Squares.eq_zero_of_square_eq_zero (K := K) value (by simpa only [pow_two]
      using squareZero) : value = 0)) tSquare
    · exact (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] [DecidableEq K] {value : K} (squareZero : value *
      value = 0) => (Purelib.Algebra.Field.Squares.eq_zero_of_square_eq_zero (K := K) value (by simpa only [pow_two]
      using squareZero) : value = 0)) rSquare
    · exact (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] [DecidableEq K] {value : K} (squareZero : value *
      value = 0) => (Purelib.Algebra.Field.Squares.eq_zero_of_square_eq_zero (K := K) value (by simpa only [pow_two]
      using squareZero) : value = 0)) sSquare
  calc
    matrix = Coordinates3.Antisymmetric.anchor vector := encodes.symm
    _ = Coordinates3.Antisymmetric.anchor Vector3.zero := by rw [vectorZero]
    _ = Coordinates3.Matrix3.zero := by
      ext <;> unfold Coordinates3.Antisymmetric.anchor <;> unfold Vector3.zero Coordinates3.Matrix3.zero <;> ring1

end Purelib.LinearAlgebra.Coordinates3.Antisymmetric
end
