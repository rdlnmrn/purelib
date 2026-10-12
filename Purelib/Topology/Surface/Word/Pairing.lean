module
public import Purelib.LinearAlgebra.Vector.IntCast
public import Purelib.LinearAlgebra.Bilinear.Integral
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.Group.Negation
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Matrix.Basic

public import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Data

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

public section

/-!
# The integer alternating form computed by an ordered boundary word

Each letter is an executable finite integer vector of generator coefficients.
The ordered-pair sum computes an alternating matrix, with the total vector
cached alongside it. Contracting that matrix gives the exact area of the
primitive-increment word. No symplectic matrix or intersection labels are
assumed, and the translation term is retained for an unbalanced word.
This is the alternating area matrix: the commutator `a b (-a) (-b)`
has off-diagonal coefficient 2, not 1. Dividing by two and identifying
geometric intersection require additional topology, not a renaming.
-/

namespace Purelib.Topology.Surface.Word.Pairing
attribute [local instance high] Group.Negation.subNegZeroMonoid

open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea polygonBoundaryArea)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.LinearAlgebra

/-- Executable finite integer coefficient vectors for word letters. -/
abbrev Coefficients (count : Nat) := Data.Vector Int count
/-- Executable square integer matrices on the original generator index set. -/
abbrev IntegralMatrix (count : Nat) := LinearAlgebra.Matrix Int count

variable {count : Nat}

/-- Sum the coefficients at one generator over the ordered word. -/
@[expose] def totalAt : List (Pairing.Coefficients count) → Fin count → Int
  | [], _ => 0
  | letter :: rest, index => letter index + Purelib.Topology.Surface.Word.Pairing.totalAt rest index

/-- Compute one entry of the ordered word's alternating area matrix.

Each head letter pairs with the retained order of its tail, contributing the difference of the two cross-products. -/
@[expose] def pairingAt : List (Pairing.Coefficients count) → Fin count → Fin count → Int
  | [], _, _ => 0
  | letter :: rest, row, column =>
      letter row * Pairing.totalAt rest column - Pairing.totalAt rest row * letter column +
        Purelib.Topology.Surface.Word.Pairing.pairingAt rest row column

/-- Swapping the two generator indices negates the computed pairing entry. -/
theorem pairingAt_skew (word : List (Pairing.Coefficients count)) (row column : Fin count) :
    Pairing.pairingAt word row column = -Pairing.pairingAt word column row := by
  induction word with
  | nil => rfl
  | cons letter rest ih => rw [Pairing.pairingAt, Pairing.pairingAt, ih]; ring1

/-- Every diagonal entry of the computed alternating pairing is zero. -/
theorem pairingAt_diagonal (word : List (Pairing.Coefficients count)) (index : Fin count) : Pairing.pairingAt word index
  index = 0 := by
  induction word with
  | nil => rfl
  | cons letter rest ih => rw [Pairing.pairingAt, ih]; ring1

set_option genInjectivity false in
/-- Retain the total coefficient vector and alternating matrix of the original word.

Both retained caches carry entrywise certificates for that exact ordered
word. The executable builder computes each tail signature once and consumes
its original total vector and matrix while adding the displayed head. -/
structure Signature (word : List (Pairing.Coefficients count)) where
  /-- Cached total coefficient vector of the original word. -/ total : Pairing.Coefficients count
  /-- Each cached total entry agrees with the original word's coefficient sum. -/ total_eq : ∀ index, total index =
    Pairing.totalAt word index
  /-- Cached alternating area matrix of the original ordered word. -/ matrix : Pairing.IntegralMatrix count
  /-- Each cached matrix entry agrees with the ordered-pair computation. -/ matrix_eq : ∀ row column, matrix row column
    = Pairing.pairingAt word row column

constructive_injectivity Signature

namespace Signature

/-- Compute the total vector and alternating matrix while reusing each cached tail signature.

The original source word supplies one head and a retained tail signature. Both output caches consume that exact tail
once, and their entrywise certificates retain its original word identity. -/
@[expose] def build : (word : List (Pairing.Coefficients count)) → Pairing.Signature word
  | [] => ⟨Data.Vector.Basic.vectorOfFn fun _ => 0, fun index => Data.Vector.Basic.vectorOfFn_apply _ index,
      LinearAlgebra.Matrix.matrixOfFn fun _ _ => 0, fun row column =>
        LinearAlgebra.Matrix.matrixOfFn_apply _ row column⟩
  | letter :: rest =>
      let tail := Purelib.Topology.Surface.Word.Pairing.Signature.build rest
      { total := Data.Vector.Basic.vectorOfFn fun index => letter index + tail.total index
        total_eq := fun index => by rw [Data.Vector.Basic.vectorOfFn_apply, tail.total_eq]; rfl
        matrix := LinearAlgebra.Matrix.matrixOfFn fun row column =>
          letter row * tail.total column - tail.total row * letter column + tail.matrix row column
        matrix_eq := fun row column => by
          rw [LinearAlgebra.Matrix.matrixOfFn_apply, tail.total_eq, tail.total_eq,
            tail.matrix_eq]; rfl }

/-- The retained signature matrix is skew-symmetric. -/
theorem skew {word : List (Pairing.Coefficients count)} (signature : Pairing.Signature word) (row column : Fin count) :
    signature.matrix row column = -signature.matrix column row := by
  rw [signature.matrix_eq, signature.matrix_eq]
  exact Pairing.pairingAt_skew word row column

/-- The retained signature matrix has zero diagonal. -/
theorem diagonal {word : List (Pairing.Coefficients count)} (signature : Pairing.Signature word) (index : Fin count) :
    signature.matrix index index = 0 := by
  rw [signature.matrix_eq]
  exact Pairing.pairingAt_diagonal word index

end Signature

/-- Evaluate an integer coefficient vector in both coordinates of the primitive-point values. -/
@[expose] def linear (coefficients : Fin count → Int) (values : Fin count → Stokes.PrimitivePoint) : PrimitivePoint :=
  ⟨FiniteSum.Fin.sumFin fun index => (coefficients index : Gaussian.Basic.Canonical) * (values index).left,
    FiniteSum.Fin.sumFin fun index => (coefficients index : Gaussian.Basic.Canonical) * (values index).right⟩

/-- The zero coefficient vector evaluates to the zero primitive point.

Every displayed coefficient is the integer zero. Its retained ring cast and scalar multiplication contribute zero at
each original finite index. -/
theorem linear_zero (values : Fin count → Stokes.PrimitivePoint) : Pairing.linear (fun _ => 0) values =
  PrimitivePoint.zero := by
  unfold Pairing.linear
  change PrimitivePoint.mk _ _ = PrimitivePoint.mk _ _
  congr 1 <;> exact (FiniteSum.Fin.sumFin_congr (fun index => by rw [Ring.IntCast.cast_zero, zero_mul])).trans
    FiniteSum.Fin.sumFin_zero

/-- Adding integer coefficient rows adds their primitive-point readings.

Both original rows use the same retained primitive coordinates. Direct integer-cast addition and finite-sum linearity
distribute the displayed coefficients in each coordinate. -/
theorem linear_add (first last : Fin count → Int) (values : Fin count → Stokes.PrimitivePoint) :
    Pairing.linear (fun index => first index + last index) values = (Pairing.linear first values).add (Pairing.linear
      last values) := by
  have component (value : Fin count → Gaussian.Basic.Canonical) :
      FiniteSum.Fin.sumFin (fun index => ((first index + last index : Int) : Gaussian.Basic.Canonical) * value index) =
        FiniteSum.Fin.sumFin (fun index => (first index : Gaussian.Basic.Canonical) * value index) +
        FiniteSum.Fin.sumFin (fun index => (last index : Gaussian.Basic.Canonical) * value index) :=
    (FiniteSum.Fin.sumFin_congr (fun index => by rw [Ring.IntCast.add, add_mul])).trans (FiniteSum.Fin.sumFin_add _ _)
  exact congrArg₂ PrimitivePoint.mk (component (fun index => (values index).left))
    (component (fun index => (values index).right))

/-- Contract an integer matrix against the left and right primitive coordinates. -/
@[expose] def contract (matrix : Fin count → Fin count → Int) (values : Fin count → Stokes.PrimitivePoint) :
  Gaussian.Basic.Canonical :=
  FiniteSum.Fin.sumFin fun row => FiniteSum.Fin.sumFin fun column => (matrix row column : Gaussian.Basic.Canonical) *
    (values row).left * (values column).right

/-- Matrix contraction is additive in its integer matrix argument.

The same retained primitive coordinates multiply each original matrix entry.
Direct integer-cast addition and scalar finite-sum laws distribute those
entries without changing either matrix or the contraction order. -/
theorem contract_add (first last : Fin count → Fin count → Int) (values : Fin count → Stokes.PrimitivePoint) :
    Pairing.contract (fun row column => first row column + last row column) values = Pairing.contract first values +
      Pairing.contract last values := by
  unfold Pairing.contract
  calc
    _ = FiniteSum.Fin.sumFin (fun row =>
        FiniteSum.Fin.sumFin (fun column => (first row column : Gaussian.Basic.Canonical) * (values row).left * (values
          column).right) +
        FiniteSum.Fin.sumFin (fun column => (last row column : Gaussian.Basic.Canonical) * (values row).left * (values
          column).right)) := by
      apply FiniteSum.Fin.sumFin_congr; intro row
      exact (FiniteSum.Fin.sumFin_congr (fun column => by dsimp only; rw [Ring.IntCast.add, add_mul, add_mul])).trans
        (FiniteSum.Fin.sumFin_add _ _)
    _ = _ := FiniteSum.Fin.sumFin_add _ _

/-- The zero matrix has zero contraction against arbitrary primitive values.

Both finite scans retain their original index order and primitive coordinate factors. Every original integer matrix
entry casts to zero and contributes zero to those scans. -/
theorem contract_zero (values : Fin count → Stokes.PrimitivePoint) : Pairing.contract (fun _ _ => 0) values = 0 := by
  unfold Pairing.contract
  exact (FiniteSum.Fin.sumFin_congr (fun row =>
    (FiniteSum.Fin.sumFin_congr (fun column => by dsimp only; rw [Ring.IntCast.cast_zero, zero_mul, zero_mul])).trans
      FiniteSum.Fin.sumFin_zero)).trans FiniteSum.Fin.sumFin_zero

/-- Contracting a rank-two alternating coefficient matrix gives the area of the two linear readings.

The two original integer rows supply the ordered cross-products of the same primitive coordinates. Direct cast
subtraction and the existing finite-sum factor laws identify their alternating contraction. -/
theorem contract_wedge (first last : Fin count → Int) (values : Fin count → Stokes.PrimitivePoint) :
    Pairing.contract (fun row column => first row * last column - last row * first column) values =
      Stokes.edgeArea (Pairing.linear first values) (Pairing.linear last values) := by
  have product (left right : Fin count → Int) :
      FiniteSum.Fin.sumFin (fun row => FiniteSum.Fin.sumFin (fun column =>
        (left row : Gaussian.Basic.Canonical) * (right column : Gaussian.Basic.Canonical) * (values row).left * (values
          column).right)) =
      (FiniteSum.Fin.sumFin fun row => (left row : Gaussian.Basic.Canonical) * (values row).left) *
        (FiniteSum.Fin.sumFin fun column => (right column : Gaussian.Basic.Canonical) * (values column).right) := by
    calc
      _ = FiniteSum.Fin.sumFin (fun row => FiniteSum.Fin.sumFin (fun column =>
          ((left row : Gaussian.Basic.Canonical) * (values row).left) * ((right column : Gaussian.Basic.Canonical) *
            (values column).right))) := by
        apply FiniteSum.Fin.sumFin_congr; intro row
        apply FiniteSum.Fin.sumFin_congr; intro column
        ring1
      _ = _ := by rw [show (FiniteSum.Fin.sumFin fun row => FiniteSum.Fin.sumFin (fun column =>
          ((left row : Gaussian.Basic.Canonical) * (values row).left) * ((right column : Gaussian.Basic.Canonical) *
            (values column).right))) =
          FiniteSum.Fin.sumFin (fun row => ((left row : Gaussian.Basic.Canonical) * (values row).left) *
            FiniteSum.Fin.sumFin (fun column => (right column : Gaussian.Basic.Canonical) * (values column).right)) from
          FiniteSum.Fin.sumFin_congr (fun row => FiniteSum.Fin.sumFin_mul_left _ _)]; exact
            FiniteSum.Fin.sumFin_mul_right _ _
  calc
    _ = FiniteSum.Fin.sumFin (fun row => FiniteSum.Fin.sumFin (fun column =>
          (first row : Gaussian.Basic.Canonical) * (last column : Gaussian.Basic.Canonical) * (values row).left *
            (values column).right)) -
        FiniteSum.Fin.sumFin (fun row => FiniteSum.Fin.sumFin (fun column =>
          (last row : Gaussian.Basic.Canonical) * (first column : Gaussian.Basic.Canonical) * (values row).left *
            (values column).right)) := by
      unfold Pairing.contract
      calc
        _ = FiniteSum.Fin.sumFin (fun row =>
            FiniteSum.Fin.sumFin (fun column => (first row : Gaussian.Basic.Canonical) * (last column :
              Gaussian.Basic.Canonical) * (values row).left * (values column).right) -
            FiniteSum.Fin.sumFin (fun column => (last row : Gaussian.Basic.Canonical) * (first column :
              Gaussian.Basic.Canonical) * (values row).left * (values column).right)) := by
          apply FiniteSum.Fin.sumFin_congr; intro row
          exact (FiniteSum.Fin.sumFin_congr (fun column => by
            dsimp only
            rw [Ring.IntCast.sub, Ring.IntCast.intCast_mul, Ring.IntCast.intCast_mul, sub_mul, sub_mul])).trans
              (FiniteSum.Fin.sumFin_sub _ _)
        _ = _ := FiniteSum.Fin.sumFin_sub _ _
    _ = _ := by rw [product, product]; rfl

/-- Ordered interactions of the increment vectors, with no closing edge silently inserted. -/
@[expose] def area (values : Fin count → Stokes.PrimitivePoint) : List (Pairing.Coefficients count) →
  Gaussian.Basic.Canonical
  | [] => 0
  | letter :: rest => Stokes.edgeArea (Pairing.linear letter values) (Pairing.linear (Pairing.totalAt rest) values) +
    Purelib.Topology.Surface.Word.Pairing.area values rest

/-- The computed word pairing matrix contracts to its exact ordered increment area. -/
theorem contract_pairing (word : List (Pairing.Coefficients count)) (values : Fin count → Stokes.PrimitivePoint) :
    Pairing.contract (Pairing.pairingAt word) values = Pairing.area values word := by
  induction word with
  | nil => exact Pairing.contract_zero values
  | cons letter rest ih =>
      change Pairing.contract (fun row column =>
        (letter row * Pairing.totalAt rest column - Pairing.totalAt rest row * letter column) + Pairing.pairingAt rest
          row column) values = _
      rw [Pairing.contract_add, Pairing.contract_wedge, ih]
      rfl

/-- Walk the actual sequence of primitive increments from a displayed starting value. Unlike `polygonBoundaryArea`, this
also permits open words. -/
@[expose] def traceArea (values : Fin count → Stokes.PrimitivePoint) : Stokes.PrimitivePoint → List
  (Pairing.Coefficients count) → Gaussian.Basic.Canonical
  | _, [] => 0
  | start, letter :: rest =>
      Stokes.edgeArea start (start.add (Pairing.linear letter values)) + Purelib.Topology.Surface.Word.Pairing.traceArea
        values (start.add (Pairing.linear letter values)) rest

/-- A word's traced area splits into its translation term and ordered increment area.

The original starting point and total increment remain explicit, so the statement also covers unbalanced words. -/
theorem traceArea_eq (word : List (Pairing.Coefficients count)) (values : Fin count → Stokes.PrimitivePoint) (start :
  Stokes.PrimitivePoint) :
    Pairing.traceArea values start word = Stokes.edgeArea start (Pairing.linear (Pairing.totalAt word) values) +
      Pairing.area values word := by
  induction word generalizing start with
  | nil =>
      rw [Pairing.traceArea, Pairing.area]
      change (0 : Gaussian.Basic.Canonical) = Stokes.edgeArea start (Pairing.linear (fun _ => 0) values) + 0
      rw [Pairing.linear_zero]
      unfold Stokes.edgeArea PrimitivePoint.zero
      ring1
  | cons letter rest ih =>
      rw [Pairing.traceArea, ih, Pairing.area]
      change _ = Stokes.edgeArea start (Pairing.linear (fun index => letter index + Pairing.totalAt rest index) values)
        + _
      rw [Pairing.linear_add]
      simp only [Stokes.edgeArea, PrimitivePoint.add]
      ring1

/-- A word's traced area splits into its translation term and ordered increment area.

The original starting point and total increment remain explicit, so the statement also covers unbalanced words. -/
theorem Signature.traceArea_eq {word : List (Pairing.Coefficients count)} (signature : Pairing.Signature word)
    (values : Fin count → Stokes.PrimitivePoint) (start : Stokes.PrimitivePoint) :
    Pairing.traceArea values start word = Stokes.edgeArea start (Pairing.linear signature.total values) +
      Pairing.contract (fun row column => signature.matrix row column) values := by
  rw [Pairing.traceArea_eq]
  have total : Pairing.linear signature.total values = Pairing.linear (Pairing.totalAt word) values := by
    unfold Pairing.linear
    congr 1 <;> apply FiniteSum.Fin.sumFin_congr <;> intro index <;> rw [signature.total_eq]
  have matrix : Pairing.contract (fun row column => signature.matrix row column) values = Pairing.contract
    (Pairing.pairingAt word) values := by
    unfold Pairing.contract
    apply FiniteSum.Fin.sumFin_congr; intro row
    apply FiniteSum.Fin.sumFin_congr; intro column
    dsimp only
    rw [signature.matrix_eq]
  rw [total, matrix, Pairing.contract_pairing]

/-- Pointwise equal primitive values have the same integer-weighted evaluation.

The integer coefficient vector and finite index set are retained. Equality of
each complete primitive point transports both coordinate sums. -/
theorem linear_values_congr {count : Nat} (weights : Fin count → Int) {first last : Fin count → Stokes.PrimitivePoint}
    (equal : ∀ index, first index = last index) : Pairing.linear weights first = Pairing.linear weights last := by
  unfold Pairing.linear
  congr 1 <;> apply FiniteSum.Fin.sumFin_congr <;> intro index <;> rw [equal]

/-- Evaluating sums of primitive values adds their two weighted evaluations.

The same integer coefficients act on both supplied value families, and each
coordinate distributes over its retained finite sum. -/
theorem linear_values_add {count : Nat} (weights : Fin count → Int) (first last : Fin count → Stokes.PrimitivePoint) :
    Pairing.linear weights (fun index => (first index).add (last index)) =
      (Pairing.linear weights first).add (Pairing.linear weights last) := by
  unfold Pairing.linear
  change PrimitivePoint.mk _ _ = PrimitivePoint.mk (_ + _) (_ + _)
  congr 1 <;> apply (FiniteSum.Fin.sumFin_congr ?_).trans (FiniteSum.Fin.sumFin_add _ _) <;> intro index <;>
    dsimp only [PrimitivePoint.add] <;> ring1

/-- Nested integer-row evaluation equals the two coordinate bilinear contractions.

The original integral matrix, coefficient vector and primitive-point vector
retain the same finite indices; each coordinate reads the corresponding cast contraction. -/
theorem linear_rows {count : Nat} (matrix : LinearAlgebra.Matrix.IntegralMatrix count)
    (weights : Data.Vector Int count)
    (values : Data.Vector Stokes.PrimitivePoint count) :
    Pairing.linear weights (fun row => Pairing.linear (fun column => matrix row column) values) =
      ⟨LinearAlgebra.Bilinear.Integral.pairing matrix (LinearAlgebra.Vector.IntCast.castVector weights)
        (Data.Vector.Basic.vectorOfFn fun index => (values index).left),
        LinearAlgebra.Bilinear.Integral.pairing matrix (LinearAlgebra.Vector.IntCast.castVector weights)
          (Data.Vector.Basic.vectorOfFn fun index => (values index).right)⟩ := by
  unfold Pairing.linear Bilinear.Integral.pairing Bilinear.Matrix.Basic.bilinear
  congr 1 <;> apply FiniteSum.Fin.sumFin_congr <;> intro row <;> dsimp only <;>
    rw [← FiniteSum.Fin.sumFin_mul_left] <;> apply FiniteSum.Fin.sumFin_congr <;> intro column <;>
    rw [Vector.IntCast.castVector_apply, Data.Vector.Basic.vectorOfFn_apply] <;> ring1

end Purelib.Topology.Surface.Word.Pairing
