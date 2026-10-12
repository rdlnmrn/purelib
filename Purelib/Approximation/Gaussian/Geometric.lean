module

import Purelib.Data.Rat.Fraction
public import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Gaussian.Name.Basic
public import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Init.Prelude
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Algebra

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric

open Purelib.Approximation.Rational.Geometric.Basic

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Synchronized finite matrix approximations

This file provides a small constructive algebra of Gaussian-rational sample
streams whose error allowance is an explicit quarter-power schedule.  Unlike
wrapping an intermediate CCL name and sampling it again, these operations
preserve the same finite sample index through every polynomial operation.

The final construction mirrors the total division-free scaled-inverse
algorithm in `Purelib.LinearAlgebra`.  It therefore produces finite
approximations to the canonical scalar and adjugate of every finite named
matrix without making an invertibility decision or choosing a completed
value.
-/

namespace Purelib.Approximation.Gaussian.Geometric

set_option genInjectivity false in
/-- A finite sample stream with an explicit geometric error scale. -/
structure GeometricApproximation where
  /-- The displayed Gaussian sample at each finite index. -/ sample : Nat -> Canonical
  /-- The rational scale of the indexed quarter-radius movement bound. -/ errorScale : Fraction.Rational
  /-- The retained geometric error scale is nonnegative. -/ errorScale_nonneg : 0 <= errorScale
  /-- Later samples are within the earlier index's retained quarter-radius allowance. -/ later_close : forall {earlier
    later : Nat}, earlier <= later ->
    Data.Gaussian.Norm.Basic.normSq (sample later - sample earlier) <=
      Geometric.Basic.quarterRadius errorScale earlier
  /-- A uniform rational bound on the squared norm of all samples. -/ centerBound : Fraction.Rational
  /-- The retained uniform squared-norm bound is nonnegative. -/ centerBound_nonneg : 0 <= centerBound
  /-- Every displayed sample satisfies the retained uniform squared-norm bound. -/ sample_bounded : forall index,
    Data.Gaussian.Norm.Basic.normSq (sample index) <= centerBound

constructive_injectivity GeometricApproximation

namespace GeometricApproximation

/-- Forget the displayed scale while retaining it as an ordinary productive finite approximation. -/
def toApproximation (source :
  Approximation.Gaussian.Geometric.GeometricApproximation) : Gaussian.Sequence.ApproximationData where
  sample := source.sample
  radiusSq := Geometric.Basic.quarterRadius source.errorScale
  radiusSq_nonneg :=
    Geometric.Basic.quarterRadius_nonneg source.errorScale_nonneg
  later_close := source.later_close
  refineIndex current target _ :=
    Search.firstQuarterBelow source.errorScale current target
  refineIndex_ge current target _ :=
    Search.firstQuarterBelow_ge
      source.errorScale current target
  refineIndex_accurate :=
    Search.firstQuarterBelow_accurate
      source.errorScale source.errorScale_nonneg
  centerBound := source.centerBound
  centerBound_nonneg := source.centerBound_nonneg
  sample_bounded := source.sample_bounded

/-- Forgetting the displayed geometric scale preserves each sample. -/
@[simp] theorem toApproximation_sample
    (source : Approximation.Gaussian.Geometric.GeometricApproximation) (index : Nat) :
    source.toApproximation.sample index = source.sample index := rfl

/-- The canonical nested sampler of an arbitrary productive CCL name. -/
def ofNamed (name : Gaussian.Name.Basic.Named) :
  Approximation.Gaussian.Geometric.GeometricApproximation where
  sample := (Sampling.approximation name).sample
  errorScale := 4
  errorScale_nonneg := by decide
  later_close :=
    (Sampling.approximation name).later_close
  centerBound :=
    (Sampling.approximation name).centerBound
  centerBound_nonneg :=
    (Sampling.approximation name).centerBound_nonneg
  sample_bounded :=
    (Sampling.approximation name).sample_bounded

/-- The geometric sampler of a name uses its canonical finite approximation sample. -/
@[simp] theorem ofNamed_sample (name :
  Gaussian.Name.Basic.Named) (index : Nat) :
    (Approximation.Gaussian.Geometric.GeometricApproximation.ofNamed name).sample index =
      (Sampling.approximation name).sample index := rfl

/-- A constant Gaussian rational, with zero movement allowance. -/
def exact (value : Canonical)
  : Approximation.Gaussian.Geometric.GeometricApproximation where
  sample := fun _ => value
  errorScale := 0
  errorScale_nonneg := le_rfl
  later_close := by
    intro earlier later order
    rw [sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
    exact Geometric.Basic.quarterRadius_nonneg le_rfl earlier
  centerBound := Data.Gaussian.Norm.Basic.normSq value
  centerBound_nonneg := Data.Gaussian.Norm.Basic.normSq_nonneg value
  sample_bounded := fun _ => le_rfl

/-- Every sample of an exact geometric approximation is the displayed Gaussian value. -/
@[simp] theorem exact_sample (value :
  Canonical) (index : Nat) :
    (Approximation.Gaussian.Geometric.GeometricApproximation.exact value).sample index = value := rfl

/-- Discard a finite prefix of a geometric approximation. The retained stream uses the original (conservative) error
scale; antitonicity of the quarter-radius schedule proves the shifted tail bound. -/
def drop (source :
  Approximation.Gaussian.Geometric.GeometricApproximation) (anchor : Nat) :
    Approximation.Gaussian.Geometric.GeometricApproximation where
  sample := fun index => source.sample (anchor + index)
  errorScale := source.errorScale
  errorScale_nonneg := source.errorScale_nonneg
  later_close := by
    intro earlier later order
    exact (source.later_close (by omega0)).trans
      (quarterRadius_antitone
        source.errorScale_nonneg (by omega0))
  centerBound := source.centerBound
  centerBound_nonneg := source.centerBound_nonneg
  sample_bounded := fun index => source.sample_bounded (anchor + index)

/-- Dropping a finite prefix shifts the original sample index by the retained anchor. -/
@[simp] theorem drop_sample (source :
  Approximation.Gaussian.Geometric.GeometricApproximation)
    (anchor index : Nat) :
    (source.drop anchor).sample index = source.sample (anchor + index) := rfl

/-- Dropping a finite prefix preserves the original conservative error scale. -/
@[simp] theorem drop_errorScale (source :
  Approximation.Gaussian.Geometric.GeometricApproximation)
    (anchor : Nat) :
    (source.drop anchor).errorScale = source.errorScale := rfl

/-- Pointwise negation preserves the geometric scale and center bound. -/
def neg (source :
  Approximation.Gaussian.Geometric.GeometricApproximation) : Approximation.Gaussian.Geometric.GeometricApproximation
  where
  sample := fun index => -source.sample index
  errorScale := source.errorScale
  errorScale_nonneg := source.errorScale_nonneg
  later_close := by
    intro earlier later order
    have movement := source.later_close order
    have identity :
        -source.sample later - -source.sample earlier =
          -(source.sample later - source.sample earlier) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im,
          Purelib.Data.Gaussian.Basic.neg_re, Purelib.Data.Gaussian.Basic.neg_im] <;> ring1
    rw [identity, Data.Gaussian.Norm.Basic.normSq_neg]
    exact movement
  centerBound := source.centerBound
  centerBound_nonneg := source.centerBound_nonneg
  sample_bounded := by
    intro index
    rw [Data.Gaussian.Norm.Basic.normSq_neg]
    exact source.sample_bounded index

/-- Negating a geometric approximation negates each sample. -/
@[simp] theorem neg_sample (source :
  Approximation.Gaussian.Geometric.GeometricApproximation) (index : Nat) :
    (Approximation.Gaussian.Geometric.GeometricApproximation.neg source).sample index = -source.sample index := rfl

/-- Equal-index Gaussian conjugation preserves every squared movement and global sample bound. -/
def conj (source :
  Approximation.Gaussian.Geometric.GeometricApproximation) : Approximation.Gaussian.Geometric.GeometricApproximation
  where
  sample := fun index => source.sample index |>.conj
  errorScale := source.errorScale
  errorScale_nonneg := source.errorScale_nonneg
  later_close := by
    intro earlier later order
    have movement := source.later_close order
    have identity :
        (source.sample later).conj - (source.sample earlier).conj =
          (source.sample later - source.sample earlier).conj := by
      apply Data.Gaussian.Basic.ext
      · rfl
      · change
          -(source.sample later).im - -(source.sample earlier).im =
            -((source.sample later).im - (source.sample earlier).im)
        ring1
    rw [identity]
    change Data.Gaussian.Norm.Basic.normSq
      (Data.Gaussian.Basic.conj (source.sample later - source.sample earlier)) ≤ _
    rw [Data.Gaussian.Norm.Basic.normSq_conj]
    exact movement
  centerBound := source.centerBound
  centerBound_nonneg := source.centerBound_nonneg
  sample_bounded := by
    intro index
    change Data.Gaussian.Norm.Basic.normSq
      (Data.Gaussian.Basic.conj (source.sample index)) ≤ source.centerBound
    rw [Data.Gaussian.Norm.Basic.normSq_conj]
    exact source.sample_bounded index

/-- Conjugating a geometric approximation conjugates each sample. -/
@[simp] theorem conj_sample (source :
  Approximation.Gaussian.Geometric.GeometricApproximation) (index : Nat) :
    (Approximation.Gaussian.Geometric.GeometricApproximation.conj source).sample index = (source.sample index).conj :=
      rfl

/-- Equal-index addition with a conservative rational movement bound. -/
def add (left right :
  Approximation.Gaussian.Geometric.GeometricApproximation) : Approximation.Gaussian.Geometric.GeometricApproximation
  where
  sample := fun index => left.sample index + right.sample index
  errorScale := 2 * (left.errorScale + right.errorScale)
  errorScale_nonneg :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg left.errorScale_nonneg right.errorScale_nonneg)
  later_close := by
    intro earlier later order
    have leftMovement := left.later_close order
    have rightMovement := right.later_close order
    have identity :
        left.sample later + right.sample later -
            (left.sample earlier + right.sample earlier) =
          (left.sample later - left.sample earlier) +
            (right.sample later - right.sample earlier) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im,
          Purelib.Data.Gaussian.Basic.add_re, Purelib.Data.Gaussian.Basic.add_im] <;> ring1
    rw [identity]
    calc
      Data.Gaussian.Norm.Basic.normSq
          ((left.sample later - left.sample earlier) +
            (right.sample later - right.sample earlier)) <=
        2 *
          (Data.Gaussian.Norm.Basic.normSq (left.sample later - left.sample earlier) +
            Data.Gaussian.Norm.Basic.normSq (right.sample later - right.sample earlier)) :=
        Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
      _ <= 2 *
          (Geometric.Basic.quarterRadius left.errorScale earlier +
            Geometric.Basic.quarterRadius right.errorScale earlier) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add leftMovement rightMovement) (by decide)
      _ = Geometric.Basic.quarterRadius
          (2 * (left.errorScale + right.errorScale)) earlier := by
        rw [Geometric.Basic.quarterRadius_eq_mul_pow,
          Geometric.Basic.quarterRadius_eq_mul_pow,
          Geometric.Basic.quarterRadius_eq_mul_pow]
        ring1
  centerBound := 2 * (left.centerBound + right.centerBound)
  centerBound_nonneg :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg left.centerBound_nonneg right.centerBound_nonneg)
  sample_bounded := by
    intro index
    exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add (left.sample_bounded index)
          (right.sample_bounded index)) (by decide))

/-- The sum approximation adds samples at the same index. -/
@[simp] theorem add_sample (left right :
  Approximation.Gaussian.Geometric.GeometricApproximation)
    (index : Nat) :
    (Approximation.Gaussian.Geometric.GeometricApproximation.add left right).sample index =
      left.sample index + right.sample index := rfl

/-- Equal-index subtraction. -/
def sub (left right :
  Approximation.Gaussian.Geometric.GeometricApproximation) : Approximation.Gaussian.Geometric.GeometricApproximation :=
  Approximation.Gaussian.Geometric.GeometricApproximation.add left
    (Approximation.Gaussian.Geometric.GeometricApproximation.neg right)

/-- The difference approximation subtracts samples at the same index. -/
@[simp] theorem sub_sample (left right :
  Approximation.Gaussian.Geometric.GeometricApproximation)
    (index : Nat) :
    (Approximation.Gaussian.Geometric.GeometricApproximation.sub left right).sample index =
      left.sample index - right.sample index := by
  change left.sample index + -right.sample index = _
  exact (sub_eq_add_neg _ _).symm

/-- Equal-index multiplication. Both global sample bounds are carried into the explicit movement scale, so no limit or
compactness argument is used. -/
def mul (left right :
  Approximation.Gaussian.Geometric.GeometricApproximation) : Approximation.Gaussian.Geometric.GeometricApproximation
  where
  sample := fun index => left.sample index * right.sample index
  errorScale :=
    2 * (left.errorScale * right.centerBound +
      left.centerBound * right.errorScale)
  errorScale_nonneg :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg
        (Fraction.Order.Arithmetic.mul_nonneg_direct
          left.errorScale_nonneg right.centerBound_nonneg)
        (Fraction.Order.Arithmetic.mul_nonneg_direct
          left.centerBound_nonneg right.errorScale_nonneg))
  later_close := by
    intro earlier later order
    have leftMovement := left.later_close order
    have rightMovement := right.later_close order
    have firstTerm :
        Data.Gaussian.Norm.Basic.normSq
            ((left.sample later - left.sample earlier) *
              right.sample later) <=
          Geometric.Basic.quarterRadius left.errorScale earlier *
            right.centerBound := by
      rw [Data.Gaussian.Norm.Basic.normSq_mul]
      exact Fraction.Order.Arithmetic.mul_le_mul_direct leftMovement
        (right.sample_bounded later) (Data.Gaussian.Norm.Basic.normSq_nonneg _)
        (Geometric.Basic.quarterRadius_nonneg
          left.errorScale_nonneg earlier)
    have secondTerm :
        Data.Gaussian.Norm.Basic.normSq
            (left.sample earlier *
              (right.sample later - right.sample earlier)) <=
          left.centerBound *
            Geometric.Basic.quarterRadius right.errorScale earlier := by
      rw [Data.Gaussian.Norm.Basic.normSq_mul]
      exact Fraction.Order.Arithmetic.mul_le_mul_direct
        (left.sample_bounded earlier) rightMovement (Data.Gaussian.Norm.Basic.normSq_nonneg _)
        left.centerBound_nonneg
    have identity :
        left.sample later * right.sample later -
            left.sample earlier * right.sample earlier =
          (left.sample later - left.sample earlier) * right.sample later +
            left.sample earlier *
              (right.sample later - right.sample earlier) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im,
          Purelib.Data.Gaussian.Basic.add_re, Purelib.Data.Gaussian.Basic.add_im, Purelib.Data.Gaussian.Basic.mul_re,
          Purelib.Data.Gaussian.Basic.mul_im] <;> ring1
    rw [identity]
    calc
      Data.Gaussian.Norm.Basic.normSq
          ((left.sample later - left.sample earlier) * right.sample later +
            left.sample earlier *
              (right.sample later - right.sample earlier)) <=
        2 *
          (Data.Gaussian.Norm.Basic.normSq
              ((left.sample later - left.sample earlier) *
                right.sample later) +
            Data.Gaussian.Norm.Basic.normSq
              (left.sample earlier *
                (right.sample later - right.sample earlier))) :=
        Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
      _ <= 2 *
          (Geometric.Basic.quarterRadius left.errorScale earlier *
              right.centerBound +
            left.centerBound *
              Geometric.Basic.quarterRadius right.errorScale earlier) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add firstTerm secondTerm) (by decide)
      _ = Geometric.Basic.quarterRadius
          (2 * (left.errorScale * right.centerBound +
            left.centerBound * right.errorScale)) earlier := by
        rw [Geometric.Basic.quarterRadius_eq_mul_pow,
          Geometric.Basic.quarterRadius_eq_mul_pow,
          Geometric.Basic.quarterRadius_eq_mul_pow]
        ring1
  centerBound := left.centerBound * right.centerBound
  centerBound_nonneg :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      left.centerBound_nonneg right.centerBound_nonneg
  sample_bounded := by
    intro index
    rw [Data.Gaussian.Norm.Basic.normSq_mul]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct
      (left.sample_bounded index) (right.sample_bounded index)
      (Data.Gaussian.Norm.Basic.normSq_nonneg _) left.centerBound_nonneg

/-- The product approximation multiplies samples at the same index. -/
@[simp] theorem mul_sample (left right :
  Approximation.Gaussian.Geometric.GeometricApproximation)
    (index : Nat) :
    (Approximation.Gaussian.Geometric.GeometricApproximation.mul left right).sample index =
      left.sample index * right.sample index := rfl

/-- A finite recursive sum retaining one common sample index. -/
def sum : {count : Nat} ->
    (Fin count -> Purelib.Approximation.Gaussian.Geometric.GeometricApproximation) ->
      Purelib.Approximation.Gaussian.Geometric.GeometricApproximation
  | 0, _ => exact 0
  | count + 1, values =>
      add (values 0)
        (sum fun index : Fin count => values index.succ)

/-- Sampling the finite recursive sum equals the finite sum of samples at the same index. -/
@[simp] theorem sum_sample {count : Nat}
    (values : Fin count -> Approximation.Gaussian.Geometric.GeometricApproximation) (index : Nat) :
    (Approximation.Gaussian.Geometric.GeometricApproximation.sum values).sample index =
      FiniteSum.Fin.sumFin
        (fun entry => (values entry).sample index) := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      change (values 0).sample index +
          (Approximation.Gaussian.Geometric.GeometricApproximation.sum (fun entry : Fin count => values
            entry.succ)).sample index = _
      rw [FiniteSum.Fin.sumFin_succ,
        inductionHypothesis (fun entry : Fin count => values entry.succ)]

end GeometricApproximation
end Purelib.Approximation.Gaussian.Geometric

end
