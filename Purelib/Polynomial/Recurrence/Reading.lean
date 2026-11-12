module

public import Purelib.Polynomial.Recurrence.Boundary.Shift
public import Purelib.Algebra.Ring.GaussianReading
public import Purelib.Polynomial.Dense.Map.Basic
import Purelib.Data.List.Reverse
import Purelib.Data.List.Map
import Purelib.Data.Vector.Basic
import Purelib.Algebra.FiniteSum.Fin

/-!
# Exact scalar readings of finite recurrence rows

An additive reading preserves the original Gaussian coefficient action even
when it has positive multiplication error. Its actual finite input window
therefore retains the original polynomial and Laurent equations exactly.
No replacement of a formal mode by powers of its observed root is used.
-/

public section

namespace Purelib.Polynomial.Recurrence.Reading

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.List
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial
open Purelib.Algebra.Ring (Weight GaussianReading)
open Purelib.Algebra.FiniteSum.Fin

variable {K : Type*} [CommRing K] {weight : Weight K} {scalar : Canonical → K}

/-- Materialize the same original finite input entries under their retained Gaussian reading. -/
@[expose] def values (reading : GaussianReading weight scalar) {count : Nat} (input : Vec K count) :
    Vec Canonical count := Vec.map reading.read input

/-- Each materialized coordinate reads exactly its original finite input entry. -/
theorem values_at (reading : GaussianReading weight scalar) {count : Nat} (input : Vec K count)
    (index : Fin count) : values reading input index = reading.read (input index) :=
  map_apply _ _ _

/-- The same zero fallback commutes with the original scalar reading at every finite coordinate. -/
theorem sample_eq (reading : GaussianReading weight scalar) {count : Nat} (input : Vec K count)
    (index : Nat) : reading.read (sample input index) = sample (values reading input) index := by
  by_cases inside : index < count
  · rewrite [sample, dif_pos inside, sample, dif_pos inside, values_at]
    rfl
  · rewrite [sample, dif_neg inside, sample, dif_neg inside]
    exact reading.mapZero

/-- Reversing an original mapped coefficient table preserves the same scalar at every occurrence. -/
private theorem coefficient_eq (source : DensePolynomial Canonical) (scalarZero : scalar 0 = 0)
    (index : Nat) :
    getD (Dense.Map.map scalar source).coeffs.reverse index 0 = scalar (getD source.coeffs.reverse index 0) := by
  rewrite [Dense.Map.map_coeffs, ← Reverse.map_reverse]
  exact (congrArg (fun fallback => getD (source.coeffs.reverse.map scalar) index fallback) scalarZero.symm).trans
    (getD_map scalar source.coeffs.reverse index 0)

omit [CommRing K] in
/-- The same mapped ascending coefficient range has the original finite number of slots. -/
private theorem coefficient_length (source : DensePolynomial Canonical) :
    (Dense.Map.map scalar source).coeffs.reverse.length = source.coeffs.reverse.length :=
  (Reverse.length_reverse _).trans ((Dense.Map.map_length scalar source).trans (Reverse.length_reverse _).symm)

/-- An original truncated Laurent row reads exactly through its same Gaussian coefficients and input window. -/
theorem row_eq (reading : GaussianReading weight scalar) (scalarZero : scalar 0 = 0)
    (source : DensePolynomial Canonical) (shift : Nat) {count : Nat} (input : Vec K count) (index : Nat) :
    reading.read (row (Dense.Map.map scalar source) shift input index) =
      row source shift (values reading input) index := by
  change reading.read (sumFin _) = sumFin _
  apply (map_sumFin reading.read reading.mapZero reading.mapAdd _).trans
  apply sumFin_congr_size (coefficient_length source)
  intro first second same
  rewrite [coefficient_eq source scalarZero, reading.mapScalarMul]
  rewrite [same]
  by_cases included : shift ≤ index + second.val
  · rewrite [if_pos included, if_pos included, sample_eq]
    rfl
  · rewrite [if_neg included, if_neg included, reading.mapZero]
    rfl

/-- The same original startup boundary vector reads as the actual Gaussian startup boundary. -/
theorem boundary_eq (reading : GaussianReading weight scalar) (scalarZero : scalar 0 = 0)
    (source : DensePolynomial Canonical) (shift : Nat) {count : Nat} (input : Vec K count) :
    values reading (boundary (Dense.Map.map scalar source) shift input) =
      boundary source shift (values reading input) := by
  apply vector_ext
  intro index
  rewrite [values_at, boundary_at, boundary_at]
  exact row_eq reading scalarZero source shift input index.val

/-- Reading the same finite columns preserves every original complete polynomial recurrence row. -/
theorem equations (reading : GaussianReading weight scalar) (scalarZero : scalar 0 = 0)
    (source : DensePolynomial Canonical) (shift : Nat) {count columns : Nat}
    (input : Vec (Vec K count) columns) (original : Boundary.Equations (Dense.Map.map scalar source) shift input) :
    Boundary.Equations source shift (Vec.map (values reading) input) := by
  intro index column
  have observed := congrArg reading.read (original index column)
  have rows : reading.read (sumFin (fun coefficient : Fin (Dense.Map.map scalar source).coeffs.reverse.length =>
      getD (Dense.Map.map scalar source).coeffs.reverse coefficient.val 0 *
        sample (input column) (index.val + coefficient.val))) =
      sumFin (fun coefficient : Fin source.coeffs.reverse.length =>
        getD source.coeffs.reverse coefficient.val 0 *
          sample ((Vec.map (values reading) input) column) (index.val + coefficient.val)) := by
    apply (map_sumFin reading.read reading.mapZero reading.mapAdd _).trans
    apply sumFin_congr_size (coefficient_length source)
    intro first second same
    rewrite [coefficient_eq source scalarZero, reading.mapScalarMul, same, sample_eq, map_apply]
    rfl
  exact rows.symm.trans (observed.trans reading.mapZero)

end Purelib.Polynomial.Recurrence.Reading

end
