module

public import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Algebra.FiniteSum.Fin
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.List.Membership
import Purelib.Data.List.OfFn.Basic
import Purelib.Algebra.Ring.IntCast
import Purelib.Tactic.Ring

/-! # Finite allowances for signed face corrections

Each original face occurrence keeps its integer multiplicity and bounded
face index. Squared coefficient norms and the literal occurrence count
convert bounds on those triangle readings into a bound on their signed sum.
-/

public section

namespace Purelib.Topology.Surface.Sewing.SewingRetraction

open Purelib
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_mul_right sumFin_congr sumFin_succ)
open Purelib.Algebra.Ring
open Purelib.Algebra.FiniteSum.Rational.Order (weight_sum_nonnegative)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq normSq_mul normSq_nonneg)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Gaussian.Norm.Sum.Indexed (sumFin_map normSq_sumFin_le_count_mul_sumFin)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Data.List
open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle)

variable {vertices faceCount : Nat}

/-- The literal signed face occurrences determine their count-weighted squared-error allowance.

The coefficient is the original integer cast into the Gaussian field. Its
squared norm weights that same occurrence's triangle bound, including
repeated faces and zero multiplicities. An empty correction has allowance zero.
-/
@[expose] def faceAllowance (terms : List (FaceTerm faceCount))
    (bounds : Fin faceCount → Rational) : Rational :=
  (terms.length : Rational) * sumFin (fun position : Fin terms.length =>
    let term := terms[position.val]'position.isLt
    normSq (term.1 : Canonical) * bounds term.2)

/-- Nonnegative triangle bounds give a nonnegative allowance for the original signed correction list. -/
theorem faceAllowance_nonnegative (terms : List (FaceTerm faceCount))
    (bounds : Fin faceCount → Rational) (nonnegative : ∀ index, 0 ≤ bounds index) :
    0 ≤ faceAllowance terms bounds :=
  Order.Arithmetic.mul_nonneg_direct
    (Cast.Order.natCast_le_direct (m := 0) (n := terms.length) (Nat.zero_le terms.length))
    (weight_sum_nonnegative _ (fun _position =>
      Order.Arithmetic.mul_nonneg_direct (normSq_nonneg _) (nonnegative _)))

/-- A common triangle bound factors through the same original correction's unit allowance.

Only the scalar bound changes. The original occurrence count, signed
multiplicities and bounded face indices remain unchanged.
-/
theorem faceAllowance_uniform (terms : List (FaceTerm faceCount)) (bound : Rational) :
    faceAllowance terms (fun _ => bound) = faceAllowance terms (fun _ => 1) * bound := by
  have scaled := sumFin_mul_right
    (fun position : Fin terms.length => normSq ((terms[position.val]'position.isLt).1 : Canonical)) bound
  have units := sumFin_congr
    (fun position : Fin terms.length => Field.mul_one_direct
      (normSq ((terms[position.val]'position.isLt).1 : Canonical)))
  change (terms.length : Rational) * sumFin (fun position : Fin terms.length =>
      normSq ((terms[position.val]'position.isLt).1 : Canonical) * bound) =
    ((terms.length : Rational) * sumFin (fun position : Fin terms.length =>
      normSq ((terms[position.val]'position.isLt).1 : Canonical) * 1)) * bound
  rewrite [scaled, units]
  exact (Field.mul_assoc _ _ _).symm

/-- The actual signed face sum is the ordered Gaussian sum of those same weighted triangle readings. -/
private theorem faceValue_eq_sum (faces : Fin faceCount → OrientedTriangle vertices)
    (value : OrientedEdge vertices → Canonical) (terms : List (FaceTerm faceCount)) :
    faceValue faces value terms =
      gaussianSum (terms.map (fun term => (term.1 : Canonical) * wordValue value (faces term.2).boundary)) := by
  induction terms with
  | nil => rfl
  | cons term rest ih =>
      change (term.1 : Canonical) * wordValue value (faces term.2).boundary + faceValue faces value rest =
        (term.1 : Canonical) * wordValue value (faces term.2).boundary + _
      exact congrArg ((term.1 : Canonical) * wordValue value (faces term.2).boundary + ·) ih

/-- Bounds on the original triangle readings pay the complete signed face correction.

Finite Cauchy charges the actual correction count once. Each original signed
multiplicity contributes its own squared coefficient norm; no face integral
or correction is assumed to vanish.
-/
theorem faceValue_le (faces : Fin faceCount → OrientedTriangle vertices)
    (value : OrientedEdge vertices → Canonical) (terms : List (FaceTerm faceCount))
    (bounds : Fin faceCount → Rational)
    (bounded : ∀ index, normSq (wordValue value (faces index).boundary) ≤ bounds index) :
    normSq (faceValue faces value terms) ≤ faceAllowance terms bounds := by
  let reading := fun term : FaceTerm faceCount => (term.1 : Canonical) * wordValue value (faces term.2).boundary
  have original := normSq_sumFin_le_count_mul_sumFin
    (fun position : Fin terms.length => reading (terms[position.val]'position.isLt))
    (fun position : Fin terms.length =>
      let term := terms[position.val]'position.isLt
      normSq (term.1 : Canonical) * bounds term.2)
    (fun position => by
      change normSq (((terms[position.val]'position.isLt).1 : Canonical) *
          wordValue value (faces (terms[position.val]'position.isLt).2).boundary) ≤ _
      rewrite [normSq_mul]
      exact Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (bounded _) (normSq_nonneg _))
  have same := (sumFin_map terms reading).trans (faceValue_eq_sum faces value terms).symm
  exact Eq.mp (congrArg (fun actual : Canonical => normSq actual ≤ faceAllowance terms bounds) same) original

/-- Multiply each original signed face multiplicity by the given integer, preserving its order and bounded index. -/
@[expose] def scale (coefficient : Int) (terms : List (FaceTerm faceCount)) : List (FaceTerm faceCount) :=
  terms.map (fun term => (coefficient * term.1, term.2))

/-- Scaling signed face multiplicities scales the actual complete face reading by the same integer. -/
theorem faceValue_scale (faces : Fin faceCount → OrientedTriangle vertices)
    (value : OrientedEdge vertices → Canonical) (coefficient : Int) (terms : List (FaceTerm faceCount)) :
    faceValue faces value (scale coefficient terms) = (coefficient : Canonical) * faceValue faces value terms := by
  induction terms with
  | nil =>
      change (0 : Canonical) = (coefficient : Canonical) * 0
      exact (Data.Gaussian.Basic.mul_zero _).symm
  | cons term rest ih =>
      change ((coefficient * term.1 : Int) : Canonical) * wordValue value (faces term.2).boundary +
          faceValue faces value (scale coefficient rest) =
        (coefficient : Canonical) *
          ((term.1 : Canonical) * wordValue value (faces term.2).boundary + faceValue faces value rest)
      rewrite [IntCast.intCast_mul, ih]
      ring1

/-- Flattening the original finite face-term groups adds their readings in the same index order. -/
theorem faceValue_flatten_ofFn (faces : Fin faceCount → OrientedTriangle vertices)
    (value : OrientedEdge vertices → Canonical) {count : Nat} (groups : Fin count → List (FaceTerm faceCount)) :
    faceValue faces value (List.ofFn groups).flatten = sumFin (fun index => faceValue faces value (groups index)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rewrite [OfFn.Basic.ofFn_succ, List.flatten_cons, faceValue_append, sumFin_succ]
      exact congrArg (faceValue faces value (groups 0) + ·) (ih (fun index => groups index.succ))

end Purelib.Topology.Surface.Sewing.SewingRetraction
