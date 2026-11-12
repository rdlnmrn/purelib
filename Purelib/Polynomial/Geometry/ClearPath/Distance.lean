module

public import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Pointwise squared-distance bounds on the original ordered clear edges

The predicate follows the original ClearPath spine. Its head claim concerns
every parameter of that exact retained edge, and its tail claim retains the
original endpoint indices. No alternative path or list of vertices is built.
-/

public section

namespace Purelib.Polynomial.Geometry.ClearPath

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Rational (Box)

variable {polynomial : GaussianPolynomial} {ambient : Box}

/-- Every unit-parameter point lies within the original segment's full squared endpoint displacement. -/
theorem ClearSegment.source_distance_le {start finish : Canonical}
    (segment : ClearSegment polynomial ambient start finish)
    (time : Fraction.Rational) (inside : 0 ≤ time ∧ time ≤ 1) :
    Norm.Basic.normSq (start - segment.pointAt time) ≤ Norm.Basic.normSq (finish - start) := by
  have paid := segment.normSq_pointAt_sub_zero_le_full time inside
  rewrite [segment.pointAt_zero, segment.pointAt_one, Norm.Bounds.normSq_sub_symm (segment.pointAt time) start] at paid
  exact paid

/-- Bound every actual unit-parameter point of every retained ordered edge from a fixed original point. -/
@[expose] def PointBound (center : Canonical) (bound : Fraction.Rational) :
    {start finish : Canonical} → ClearPath polynomial ambient start finish → Prop
  | _, _, .nil _ => True
  | _, _, .cons head tail =>
      (∀ time : Fraction.Rational, 0 ≤ time ∧ time ≤ 1 →
        Norm.Basic.normSq (center - head.pointAt time) ≤ bound) ∧ PointBound center bound tail

namespace PointBound

/-- Read the all-parameter bound for the SAME original first edge. -/
theorem head {center start middle finish : Canonical} {bound : Fraction.Rational}
    {edge : ClearSegment polynomial ambient start middle} {tail : ClearPath polynomial ambient middle finish}
    (paid : PointBound center bound (.cons edge tail)) (time : Fraction.Rational)
    (inside : 0 ≤ time ∧ time ≤ 1) : Norm.Basic.normSq (center - edge.pointAt time) ≤ bound :=
  paid.1 time inside

/-- Retain the entire original tail with its unchanged pointwise bound. -/
theorem tail {center start middle finish : Canonical} {bound : Fraction.Rational}
    {edge : ClearSegment polynomial ambient start middle} {tail : ClearPath polynomial ambient middle finish}
    (paid : PointBound center bound (.cons edge tail)) : PointBound center bound tail := paid.2

/-- Enlarge a scalar distance ceiling without changing the original path or any edge. -/
theorem mono {center start finish : Canonical} {first last : Fraction.Rational}
    {path : ClearPath polynomial ambient start finish}
    (paid : PointBound center first path) (increase : first ≤ last) : PointBound center last path := by
  induction path with
  | nil point => exact True.intro
  | cons edge tail ih =>
      exact ⟨fun time inside => (paid.1 time inside).trans increase, ih paid.2⟩

/-- One retained edge obeys twice its full displacement bound from its actual starting endpoint. -/
theorem single {start finish : Canonical} (edge : ClearSegment polynomial ambient start finish) :
    PointBound start (2 * Norm.Basic.normSq (finish - start)) (.cons edge (.nil finish)) := by
  refine ⟨?_, True.intro⟩
  intro time inside
  have enlarge : Norm.Basic.normSq (finish - start) ≤ 2 * Norm.Basic.normSq (finish - start) := by
    have known := Fraction.Order.Arithmetic.add_le_add_direct
      (Fraction.Order.Basic.le_refl (Norm.Basic.normSq (finish - start)))
      (Norm.Basic.normSq_nonneg (finish - start))
    rewrite [show Norm.Basic.normSq (finish - start) + 0 = Norm.Basic.normSq (finish - start) by ring1] at known
    exact known.trans_eq (by ring1)
  exact (edge.source_distance_le time inside).trans enlarge

/-- Two original edges whose displacement energies add to the whole energy pay a common source-distance bound.

The second-edge estimate includes the original first displacement. This
does not infer a whole-source bound merely from a second-edge width.
-/
theorem pair {start middle finish : Canonical}
    (first : ClearSegment polynomial ambient start middle)
    (last : ClearSegment polynomial ambient middle finish)
    (energy : Norm.Basic.normSq (middle - start) + Norm.Basic.normSq (finish - middle) =
      Norm.Basic.normSq (finish - start)) :
    PointBound start (2 * Norm.Basic.normSq (finish - start))
      (.cons first (.cons last (.nil finish))) := by
  have firstEnergy : Norm.Basic.normSq (middle - start) ≤ Norm.Basic.normSq (finish - start) := by
    have known := Fraction.Order.Arithmetic.add_le_add_direct
      (Fraction.Order.Basic.le_refl (Norm.Basic.normSq (middle - start)))
      (Norm.Basic.normSq_nonneg (finish - middle))
    rewrite [show Norm.Basic.normSq (middle - start) + 0 = Norm.Basic.normSq (middle - start) by ring1] at known
    exact known.trans_eq energy
  have enlarge := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct firstEnergy
    (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 2)
  refine ⟨?_, ?_, True.intro⟩
  · intro time inside
    exact ((single first).1 time inside).trans enlarge
  · intro time inside
    have localPaid := last.source_distance_le time inside
    have total := (Norm.Bounds.normSq_sub_le_via start middle (last.pointAt time)).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct
          (Fraction.Order.Basic.le_refl (Norm.Basic.normSq (start - middle))) localPaid)
        (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 2))
    rewrite [Norm.Bounds.normSq_sub_symm start middle, energy] at total
    exact total

end PointBound

end Purelib.Polynomial.Geometry.ClearPath

end
