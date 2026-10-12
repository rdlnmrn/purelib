module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

public import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Recovering whole-segment endpoints from a saved proper subinterval

Two rational samples at distinct known affine parameters determine the entire
affine segment.  The v1 preparation snapshot already records those data, so
its omitted whole-segment endpoints need not be regenerated.  These theorems
restore endpoint geometry, not line clearances, owner history or path chains.
-/

namespace Purelib.Riemann.Transport.PreparedGeometryReplay

open Purelib.Riemann.Integration

section
open Purelib.Data
/-- The exact rational carrier of affine segment parameters. -/
abbrev Coordinate := Rat.Fraction.Rational
/-- The exact Gaussian rational carrier of affine segment coordinates. -/
abbrev Gaussian := Gaussian.Basic.Canonical

end

set_option genInjectivity false in
/-- The ordered endpoints determining an exact affine Gaussian segment. -/
structure Geometry where
  /-- The whole segment's coordinate at parameter zero. -/ start : Gaussian
  /-- The whole segment's coordinate at parameter one. -/ finish : Gaussian
deriving DecidableEq

constructive_injectivity Geometry

/-- Affine endpoint geometries are equal when both ordered endpoints agree. -/
theorem Geometry.ext {first second : Geometry}
    (start : first.start = second.start) (finish : first.finish = second.finish) :
    first = second := by
  cases first
  cases second
  cases start
  cases finish
  rfl

open Purelib.Data in
/-- Evaluate the affine segment at the supplied exact rational parameter. -/
def Geometry.at (geometry : Geometry) (parameter : Coordinate) : Gaussian :=
  geometry.start + Gaussian.Scale.scale parameter (geometry.finish - geometry.start)

set_option genInjectivity false in
/-- Two sampled Gaussian coordinates with their original affine parameters.

The validity predicate separately records that the parameters form a proper subinterval of the unit segment. -/
structure Inputs where
  /-- The sampled coordinate at the retained left parameter. -/ start : Gaussian
  /-- The sampled coordinate at the retained right parameter. -/ finish : Gaussian
  /-- The original affine parameter of the first sample. -/ left : Coordinate
  /-- The original affine parameter of the second sample. -/ right : Coordinate

constructive_injectivity Inputs

/-- The retained sample parameters form a proper subinterval of the unit interval. -/
def Inputs.Valid (input : Inputs) : Prop :=
  0 ≤ input.left ∧ input.left < input.right ∧ input.right ≤ 1

/-- Recover the whole affine endpoints by exact coordinatewise slope calculation.

For distinct sample parameters, the recovered line evaluates to both supplied samples and is uniquely determined by
them. -/
def recover (input : Inputs) : Geometry :=
  let dx := (input.finish.re - input.start.re) / (input.right - input.left)
  let dy := (input.finish.im - input.start.im) / (input.right - input.left)
  { start := ⟨input.start.re - input.left * dx, input.start.im - input.left * dy⟩
    finish := ⟨input.start.re + (1 - input.left) * dx,
      input.start.im + (1 - input.left) * dy⟩ }

/-- The scalar endpoint reconstruction evaluates to the original left sample. -/
private theorem recovered_left (a b left right : Coordinate) :
    let slope := (b - a) / (right - left)
    (a - left * slope) + left * ((a + (1 - left) * slope) - (a - left * slope)) = a := by
  dsimp only
  ring1

open Purelib.Data.Rat in
/-- At a distinct right parameter, scalar reconstruction gives the original right sample. -/
private theorem recovered_right (a b left right : Coordinate) (different : right - left ≠ 0) :
    let slope := (b - a) / (right - left)
    (a - left * slope) + right * ((a + (1 - left) * slope) - (a - left * slope)) = b := by
  dsimp only
  calc
    _ = a + ((b - a) / (right - left)) * (right - left) := by ring1
    _ = b := by rw [Fraction.Field.div_mul_cancel_of_ne _ _ different]; ring1

section
open Purelib.Data
/-- The recovered Gaussian segment gives the supplied left sample. -/
theorem recover_at_left (input : Inputs) : (recover input).at input.left = input.start := by
  apply Gaussian.Basic.ext <;>
    simp only [Geometry.at, recover, Gaussian.Scale.scale_re, Gaussian.Scale.scale_im,
      Gaussian.Basic.add_re, Gaussian.Basic.add_im,
      Gaussian.Basic.sub_re, Gaussian.Basic.sub_im]
  · exact recovered_left _ _ _ _
  · exact recovered_left _ _ _ _

/-- Distinct sample parameters make the recovered segment give the supplied right sample. -/
theorem recover_at_right (input : Inputs) (different : input.right - input.left ≠ 0) :
    (recover input).at input.right = input.finish := by
  apply Gaussian.Basic.ext <;>
    simp only [Geometry.at, recover, Gaussian.Scale.scale_re, Gaussian.Scale.scale_im,
      Gaussian.Basic.add_re, Gaussian.Basic.add_im,
      Gaussian.Basic.sub_re, Gaussian.Basic.sub_im]
  · exact recovered_right _ _ _ _ different
  · exact recovered_right _ _ _ _ different

end

open Purelib.Data.Rat in
/-- Two distinct affine samples recover the original scalar displacement. -/
private theorem sampled_slope (a b left right : Coordinate) (different : right - left ≠ 0) :
    ((a + right * (b - a)) - (a + left * (b - a))) / (right - left) = b - a := by
  rw [show (a + right * (b - a)) - (a + left * (b - a)) = (b - a) * (right - left) by ring1]
  rw [Fraction.Field.div_eq_mul_inv_direct, mul_assoc,
    Fraction.Field.mul_inv_cancel _ different, mul_one]

/-- Scalar affine samples at distinct parameters recover both original endpoints. -/
private theorem recovered_samples (a b left right : Coordinate)
    (different : right - left ≠ 0) :
    let sampleLeft := a + left * (b - a)
    let sampleRight := a + right * (b - a)
    let slope := (sampleRight - sampleLeft) / (right - left)
    sampleLeft - left * slope = a ∧ sampleLeft + (1 - left) * slope = b := by
  dsimp only
  rw [sampled_slope a b left right different]
  constructor <;> ring1

open Purelib.Data in
/-- Sampling an affine geometry at distinct parameters and recovering it gives the original geometry. -/
theorem recover_samples (geometry : Geometry) (left right : Coordinate) (different : right - left ≠ 0) :
    recover ⟨geometry.at left, geometry.at right, left, right⟩ = geometry := by
  apply Geometry.ext
  · apply Gaussian.Basic.ext
    · exact (recovered_samples geometry.start.re geometry.finish.re left right different).1
    · exact (recovered_samples geometry.start.im geometry.finish.im left right different).1
  · apply Gaussian.Basic.ext
    · exact (recovered_samples geometry.start.re geometry.finish.re left right different).2
    · exact (recovered_samples geometry.start.im geometry.finish.im left right different).2

set_option genInjectivity false in
/-- A valid sampled subinterval with a complete affine geometry matching both samples.

The endpoint equations and proper parameter bounds uniquely determine the retained whole segment. -/
structure Solution (input : Inputs) where
  /-- The retained complete affine segment geometry. -/ geometry : Geometry
  /-- The original parameters form a proper unit subinterval. -/ valid : input.Valid
  /-- Evaluation at the left parameter gives the retained first sample. -/ left_eq : geometry.at input.left =
    input.start
  /-- Evaluation at the right parameter gives the retained second sample. -/ right_eq : geometry.at input.right =
    input.finish

constructive_injectivity Solution

section
open Purelib.Data.Rat.Fraction.Order
/-- Construct the unique complete affine geometry of a valid sampled subinterval. -/
def solve (input : Inputs) (valid : input.Valid) : Solution input :=
  ⟨recover input, valid, recover_at_left input,
    recover_at_right input (Arithmetic.sub_pos_direct valid.2.1).ne'⟩

/-- Every valid affine solution equals the exact endpoint reconstruction. -/
theorem Solution.eq_recover {input : Inputs} (solution : Solution input) :
    solution.geometry = recover input := by
  have different : input.right - input.left ≠ 0 :=
    (Arithmetic.sub_pos_direct solution.valid.2.1).ne'
  have recovered := recover_samples solution.geometry input.left input.right different
  rw [solution.left_eq, solution.right_eq] at recovered
  exact recovered.symm

end

set_option genInjectivity false in
/-- An explicit violated parameter bound or sample equation in an affine geometry check. -/
inductive Invalidity where
  /-- The retained left parameter violates the lower unit-interval bound. -/ | leftOutside (input : Inputs) (failed : ¬
    0 ≤ input.left)
  /-- The retained right parameter violates the upper unit-interval bound. -/ | rightOutside (input : Inputs) (failed :
    ¬ input.right ≤ 1)
  /-- The retained sample parameters fail strict left-to-right order. -/ | unordered (input : Inputs) (failed : ¬
    input.left < input.right)
  /-- The actual left evaluation differs from the supplied first sample. -/ | leftMismatch (input : Inputs) (candidate :
    Geometry) (actual : Gaussian)
      (actual_eq : actual = candidate.at input.left) (failed : actual ≠ input.start)
  /-- The actual right evaluation differs from the supplied second sample. -/ | rightMismatch (input : Inputs)
    (candidate : Geometry) (actual : Gaussian)
      (actual_eq : actual = candidate.at input.right) (failed : actual ≠ input.finish)

constructive_injectivity Invalidity

/-- Validate a retained affine candidate through parameter bounds and two exact evaluations.

Success identifies its unique whole endpoints; failure retains the violated bound or the actual mismatching evaluation.
-/
def check (input : Inputs) (candidate : Geometry) : Except Invalidity (Solution input) :=
  if left : 0 ≤ input.left then
    if ordered : input.left < input.right then
      if right : input.right ≤ 1 then
        let atLeft := candidate.at input.left
        if leftEq : atLeft = input.start then
          let atRight := candidate.at input.right
          if rightEq : atRight = input.finish then
            .ok ⟨candidate, ⟨left, ordered, right⟩, leftEq, rightEq⟩
          else .error (.rightMismatch input candidate atRight rfl rightEq)
        else .error (.leftMismatch input candidate atLeft rfl leftEq)
      else .error (.rightOutside input right)
    else .error (.unordered input ordered)
  else .error (.leftOutside input left)

open Purelib.Curves in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Rat.Fraction.Order in
/-- A prepared edge's proper subinterval samples recover its original whole-segment endpoints.

The affine identity requires only strict parameter order and preserves the original endpoint geometry. -/
theorem recover_prepared {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (edge : PreparedConstantModels.PreparedEdge curve differential)
    (proper : edge.left.parameter < edge.request.endpoint.parameter) :
    recover ⟨edge.point 0, edge.point 1, edge.left.parameter, edge.request.endpoint.parameter⟩ =
      ⟨edge.start, edge.finish⟩ := by
  rw [edge.point_zero, edge.point_one]
  exact recover_samples ⟨edge.start, edge.finish⟩ _ _
    (Arithmetic.sub_pos_direct proper).ne'

open Purelib.Curves in
open Purelib.Curves.Hyperelliptic.Differentials in
/-- A checked solution for the original prepared edge's samples has the exact original endpoints. -/
theorem Solution.eq_prepared {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (edge : PreparedConstantModels.PreparedEdge curve differential)
    (solution : Solution
      ⟨edge.point 0, edge.point 1, edge.left.parameter, edge.request.endpoint.parameter⟩) :
    solution.geometry = ⟨edge.start, edge.finish⟩ :=
  solution.eq_recover.trans (recover_prepared edge solution.valid.2.1)

end Purelib.Riemann.Transport.PreparedGeometryReplay
