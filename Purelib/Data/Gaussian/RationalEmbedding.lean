module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
public import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field

import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Embedding finite rational coefficient tables in Gaussian polynomials

This is a structural map on finite lists, with evaluation, differentiation
and integration compatibility proved from the coefficient recursions.  It
does not identify polynomials by testing them on an infinite carrier.

The rational-side imports supply the existing finite coefficient calculus;
the Gaussian side supplies direct coefficient algebra.  No analytic
polynomial or completed scalar field is used.
-/

namespace Purelib.Data.Gaussian.RationalEmbedding

section RationalEmbedding

namespace PolynomialEmbedding

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Embed the supplied rational as the real coordinate of a canonical Gaussian with zero imaginary part. -/
def coordinate (value : Fraction.Rational) :
  Basic.Canonical := ⟨value, 0⟩

end PolynomialEmbedding
open Purelib.Data.Gaussian in
/-- The rational-coordinate embedding sends zero to Gaussian zero. -/
@[simp] theorem coordinate_zero :
  RationalEmbedding.PolynomialEmbedding.coordinate 0 = 0 := rfl

section
open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- The rational-coordinate embedding agrees with the canonical Gaussian natural cast. -/
@[simp] theorem coordinate_natCast (value : Nat) :
    RationalEmbedding.PolynomialEmbedding.coordinate (value : Fraction.Rational) = (value : Basic.Canonical) :=
  Basic.ext
    (Cast.natCast_re value).symm
    (Cast.natCast_im value).symm

/-- The rational-coordinate embedding preserves multiplication. -/
theorem coordinate_mul (left right : Fraction.Rational)
  :
    RationalEmbedding.PolynomialEmbedding.coordinate (left * right) = RationalEmbedding.PolynomialEmbedding.coordinate
      left * RationalEmbedding.PolynomialEmbedding.coordinate right := by
  apply Basic.ext <;>
    simp only [RationalEmbedding.PolynomialEmbedding.coordinate, Basic.mul_re,
      Basic.mul_im] <;> ring1

end

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The rational-coordinate embedding preserves division by a positive natural cast. -/
theorem coordinate_div_nat (value : Fraction.Rational)
  (degree : Nat) (positive : 0 < degree) :
    RationalEmbedding.PolynomialEmbedding.coordinate (value / (degree : Fraction.Rational)) =
      RationalEmbedding.PolynomialEmbedding.coordinate value / (degree : Basic.Canonical) := by
  have realNonzero : (degree : Fraction.Rational) ≠ 0 :=
    (Fraction.Cast.Order.natCast_pos_direct positive).ne'
  have gaussianNonzero : (degree : Basic.Canonical) ≠ 0 := by
    intro equal
    apply realNonzero
    have realEqual := congrArg Basic.re equal
    simpa only [Cast.natCast_re,
      Basic.zero_re] using realEqual
  apply Field.mul_right_cancel_of_ne gaussianNonzero
  calc
    RationalEmbedding.PolynomialEmbedding.coordinate (value / (degree : Fraction.Rational)) * (degree : Basic.Canonical)
      =
        RationalEmbedding.PolynomialEmbedding.coordinate ((value / (degree : Fraction.Rational)) * (degree :
          Fraction.Rational)) := by
      rw [coordinate_mul, coordinate_natCast]
    _ = RationalEmbedding.PolynomialEmbedding.coordinate value := congrArg
      RationalEmbedding.PolynomialEmbedding.coordinate
      (Fraction.Field.div_mul_cancel_of_ne value _ realNonzero)
    _ = (RationalEmbedding.PolynomialEmbedding.coordinate value / (degree : Basic.Canonical)) * (degree :
      Basic.Canonical) :=
      (Field.ExplicitField.div_mul_cancel _ gaussianNonzero).symm
end RationalEmbedding
end Purelib.Data.Gaussian.RationalEmbedding

end

section
@[expose] public section

/-!
# Progressive finite Taylor and multivariable CCL tables

The displayed higher-jet layer stores Gaussian rationals.  Here every entry is
instead a coherent productive CCL channel.  All operations recurse over the
displayed finite coefficient lists, and every resulting table inherits one
computable joint request from `ProgressiveFiniteTable`.
-/

namespace Purelib.Polynomial.Ascending.Gaussian.Progressive.Basic.TaylorJet
section TaylorJet

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Embed the supplied rational as a canonical Gaussian with zero imaginary coordinate. -/
def coordinateGaussian (value :
  Fraction.Rational) : Basic.Canonical := ⟨value, 0⟩
end TaylorJet

end Purelib.Polynomial.Ascending.Gaussian.Progressive.Basic.TaylorJet

end

section
@[expose] public section

/-!+# Generated, cached polynomial path partitions

The source is a finite ordered list of oriented polynomial segments.  A
partition restricts the polynomial as well as its geometry: the geometric
displacement supplies the Jacobian exactly once.  The constructors cache the
restricted polynomials, their samples and the assembled path model.  The
proof-facing integral is the existing Gaussian integration kernel's integral.
-/

namespace Purelib.Data.Gaussian.RationalEmbedding

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Embed the supplied rational parameter into the Gaussian real axis. -/
def parameter (value : Fraction.Rational) : Basic.Canonical := ⟨value, 0⟩

open Purelib.Data.Gaussian
/-- The rational parameter embedding sends zero to Gaussian zero. -/
@[simp] theorem parameter_zero : RationalEmbedding.parameter 0 = 0 := rfl
/-- The rational parameter embedding sends one to Gaussian one. -/
@[simp] theorem parameter_one : RationalEmbedding.parameter 1 = 1 := rfl
end Purelib.Data.Gaussian.RationalEmbedding

end

section
@[expose] public section

/-!
# One-sided rational pairs as ordinary CCL processes

This CCL-side bridge converts a lower/upper rational pair only when it carries
the explicit finite gap modulus in `FiniteMeasure.LocatedPair`.  The bare
one-sided processes remain rate-free.

The requested CCL squared-error target is translated to the strictly smaller
rational gap `target / (target + 1)`.  Its square is below `target`, so the
construction needs no square root, completion, limit, or unbounded search.
-/

namespace Purelib.Data.Gaussian.RationalEmbedding

section
open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- Construct the Gaussian point with the supplied real rational coordinate and zero imaginary coordinate. -/
def realPoint (value : Fraction.Rational) : Basic.Canonical :=
  ⟨value, 0⟩

/-- The real coordinate of the embedded rational point is the original rational. -/
@[simp] theorem realPoint_re (value : Fraction.Rational) :
    (RationalEmbedding.realPoint value).re = value :=
  rfl

/-- The imaginary coordinate of the embedded rational point is zero. -/
@[simp] theorem realPoint_im (value : Fraction.Rational) :
    (RationalEmbedding.realPoint value).im = 0 :=
  rfl

/-- Subtracting embedded rational points agrees with embedding their difference.

The real coordinates retain the original rational subtraction, and both imaginary coordinates remain zero. -/
@[simp] theorem realPoint_sub (left right : Fraction.Rational) :
    RationalEmbedding.realPoint left - RationalEmbedding.realPoint right = RationalEmbedding.realPoint (left - right) :=
      by
  apply Basic.ext
  · simp only [RationalEmbedding.realPoint_re, Basic.sub_re, -eq_self, -iff_self]
    rfl
  · simp only [RationalEmbedding.realPoint_im, Basic.sub_im]
    ring1

/-- The squared norm of an embedded real point is the square of its rational coordinate. -/
@[simp] theorem normSq_realPoint (value : Fraction.Rational) :
    Norm.Basic.normSq (RationalEmbedding.realPoint value) = value ^ 2 := by
  simp only [Norm.Basic.normSq, RationalEmbedding.realPoint_re, RationalEmbedding.realPoint_im]
  ring1
end

end Purelib.Data.Gaussian.RationalEmbedding

end

section
@[expose] public section

/-!
# Finite complex logarithm on a reduced Gaussian-rational disk

For a displayed Gaussian rational `z` with `normSq z <= 1/9`, this module
computes finite truncations of

`2 z (1 + z^2/3 + z^4/5 + ...)`.

The ellipsis is descriptive only.  The implementation is a finite Horner
recurrence indexed by a natural depth.  The input is already the reduced
argument `(u - 1) / (u + 1)`; constructing that quotient, proving its
denominator apart, and selecting a logarithm branch are handled separately.
-/

namespace Purelib.Data.Gaussian.RationalEmbedding

open Purelib.Data.Gaussian
open Purelib.Data.Rat
namespace ComplexLog

/-- Embed the supplied rational scalar into the Gaussian real axis. -/
def scalar (value : Fraction.Rational) : Basic.Canonical :=
  ⟨value, 0⟩

end ComplexLog
/-- The squared norm of an embedded rational scalar is its rational square. -/
@[simp] theorem normSq_scalar (value : Fraction.Rational) :
    Norm.Basic.normSq (RationalEmbedding.ComplexLog.scalar value) = value ^ 2 := by
  change value ^ 2 + 0 ^ 2 = value ^ 2
  ring1
end Purelib.Data.Gaussian.RationalEmbedding

end

section
@[expose] public section

/-!
# Finite logarithm Horner approximation

For a displayed positive rational input in `[1/2,2]`, this module computes only
finite truncations of `2z(1 + z²/3 + z⁴/5 + ⋯)`, where
`z = (x - 1)/(x + 1)`.  The ellipsis is descriptive only: every definition
below is structural recursion with a natural depth, and every semantic
predicate has an explicit later finite index witness.  No completed logarithm,
infinite series, or limit is introduced.
-/

namespace Purelib.Data.Gaussian.RationalEmbedding

open Purelib.Data.Gaussian
open Purelib.Data.Rat
namespace Log

/-- Embed the supplied rational into the canonical Gaussian carrier with zero imaginary coordinate. -/
def real (x : Fraction.Rational) : Basic.Canonical := ⟨x, 0⟩

end Log
/-- The squared norm of a difference of real embeddings is the square of the rational difference. -/
theorem normSq_real_sub (x y : Fraction.Rational) :
    Norm.Basic.normSq (RationalEmbedding.Log.real x - RationalEmbedding.Log.real y) = (x - y) ^ 2 := by
  change (x - y) ^ 2 + (0 - 0) ^ 2 = (x - y) ^ 2
  ring1
end Purelib.Data.Gaussian.RationalEmbedding

end
