module

import Purelib.Data.Rat.Fraction
public import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Multiplication
public import Purelib.Polynomial.Dense.Gaussian.Factorization.Identity

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Polynomial

section
@[expose] public section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

namespace Purelib.Polynomial.Clearance.Box.Line.Basic

set_option genInjectivity false in
/-- A positive polynomial quadrance bound on a displayed vertical line segment.

The fixed coordinate is retained explicitly; the other coordinate ranges over the ambient box's imaginary interval. -/
structure VerticalLineClearance
    (p : CoefficientPolynomial) (ambient : Geometry.Rational.Box) (x :
      Fraction.Rational)
      where
  /-- The uniform lower bound on polynomial quadrance along the segment. -/ bound : Fraction.Rational
  /-- The retained lower bound is positive. -/ positive : 0 < bound
  /-- Every parameter in the retained coordinate interval satisfies the quadrance bound. -/ lower : ∀ y :
    Fraction.Rational,
    ambient.yLower ≤ y → y ≤ ambient.yUpper →
    bound ≤ Canonical.normSq (p.eval (Gaussian.Components.Basic.point x y))

constructive_injectivity VerticalLineClearance

set_option genInjectivity false in
/-- A positive polynomial quadrance bound on a displayed horizontal line segment.

The fixed coordinate is retained explicitly; the other coordinate ranges over the ambient box's real interval. -/
structure HorizontalLineClearance
    (p : CoefficientPolynomial) (ambient : Geometry.Rational.Box) (y :
      Fraction.Rational)
      where
  /-- The uniform lower bound on polynomial quadrance along the segment. -/ bound : Fraction.Rational
  /-- The retained lower bound is positive. -/ positive : 0 < bound
  /-- Every parameter in the retained coordinate interval satisfies the quadrance bound. -/ lower : ∀ x :
    Fraction.Rational,
    ambient.xLower ≤ x → x ≤ ambient.xUpper →
    bound ≤ Canonical.normSq (p.eval (Gaussian.Components.Basic.point x y))

constructive_injectivity HorizontalLineClearance

namespace VerticalLineClearance

/-- Vertical-line clearance is closed under polynomial multiplication. -/
def mul
    {p q : CoefficientPolynomial} {ambient : Geometry.Rational.Box} {x :
      Fraction.Rational}
    (left : VerticalLineClearance p ambient x)
    (right : VerticalLineClearance q ambient x) :
    VerticalLineClearance (p * q) ambient x where
  bound := left.bound * right.bound
  positive := Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_pos_direct
    left.positive right.positive
  lower := by
    intro y lower upper
    rw [Dense.Basic.DensePolynomial.eval_mul, Canonical.normSq_mul]
    exact Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_le_mul_direct
      (left.lower y lower upper) (right.lower y lower upper)
      right.positive.le (Canonical.normSq_nonneg _)

end VerticalLineClearance

namespace HorizontalLineClearance

/-- Horizontal-line clearance is closed under polynomial multiplication. -/
def mul
    {p q : CoefficientPolynomial} {ambient : Geometry.Rational.Box} {y :
      Fraction.Rational}
    (left : HorizontalLineClearance p ambient y)
    (right : HorizontalLineClearance q ambient y) :
    HorizontalLineClearance (p * q) ambient y where
  bound := left.bound * right.bound
  positive := Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_pos_direct
    left.positive right.positive
  lower := by
    intro x lower upper
    rw [Dense.Basic.DensePolynomial.eval_mul, Canonical.normSq_mul]
    exact Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_le_mul_direct
      (left.lower x lower upper) (right.lower x lower upper)
      right.positive.le (Canonical.normSq_nonneg _)

end HorizontalLineClearance
end Purelib.Polynomial.Clearance.Box.Line.Basic

end

section
@[expose] public section

/-!
# Choice-free eight-cell complement of a central band

A strictly interior rectangle induces a `3 × 3` grid.  The middle cell is
the selected Newton band; the other eight cells inherit quantitative
clearance from the parent boundary and the four globally clear band sides.
-/

namespace Purelib.Polynomial.Geometry.CentralBandGrid
end Purelib.Polynomial.Geometry.CentralBandGrid

end

section
@[expose] public section

/-!
# Choice-free eliminant-safe Newton bands

Four bounded eliminant searches choose axis-parallel sides at distances
between `r` and `2r` from an extracted Newton center.  The sides carry
full-line Bézout clearances, while finite Taylor estimates transfer affine
winding four to the original polynomial on the selected rectangle.
-/

namespace Purelib.RootIsolation.Newton.Band
end Purelib.RootIsolation.Newton.Band

end

end

end

end

public section

namespace Purelib.Polynomial.Clearance.Box.Line.Basic

open Purelib.Polynomial.Dense.Gaussian

namespace VerticalLineClearance

/-- Transport the retained product clearance to its original coefficient source.

The original multiplication operation computes the same bound from both
supplied line certificates. The coefficient identity transports only its
pointwise evaluation guarantee; it does not replace either input polynomial.
-/
def ofProductIdentity {source leftPolynomial rightPolynomial : CoefficientPolynomial}
    {ambient : Geometry.Rational.Box} {x : Fraction.Rational}
    (identity : Factorization.Identity.ProductIdentity source leftPolynomial rightPolynomial)
    (left : VerticalLineClearance leftPolynomial ambient x)
    (right : VerticalLineClearance rightPolynomial ambient x) :
    VerticalLineClearance source ambient x :=
  let retained := left.mul right
  { bound := retained.bound
    positive := retained.positive
    lower := by
      intro y lower upper
      let point := Gaussian.Components.Basic.point x y
      have same : (leftPolynomial * rightPolynomial).eval point = source.eval point :=
        (Dense.Basic.DensePolynomial.eval_mul leftPolynomial rightPolynomial point).trans
          (Factorization.Identity.eval_factorization identity point).symm
      exact Eq.mp (congrArg (fun value : Canonical => retained.bound ≤ Canonical.normSq value) same)
        (retained.lower y lower upper) }

/-- Source transport retains the exact bound computed by the original line multiplication. -/
theorem ofProductIdentity_bound {source leftPolynomial rightPolynomial : CoefficientPolynomial}
    {ambient : Geometry.Rational.Box} {x : Fraction.Rational}
    (identity : Factorization.Identity.ProductIdentity source leftPolynomial rightPolynomial)
    (left : VerticalLineClearance leftPolynomial ambient x)
    (right : VerticalLineClearance rightPolynomial ambient x) :
    (ofProductIdentity identity left right).bound = (left.mul right).bound := by
  unfold ofProductIdentity
  rfl

/-- Canonical source transport retains the complete original multiplication certificate. -/
theorem ofProductIdentity_mul {leftPolynomial rightPolynomial : CoefficientPolynomial}
    {ambient : Geometry.Rational.Box} {x : Fraction.Rational}
    (identity : Factorization.Identity.ProductIdentity
      (leftPolynomial * rightPolynomial) leftPolynomial rightPolynomial)
    (left : VerticalLineClearance leftPolynomial ambient x)
    (right : VerticalLineClearance rightPolynomial ambient x) :
    ofProductIdentity identity left right = left.mul right := by
  unfold ofProductIdentity
  rfl

end VerticalLineClearance

namespace HorizontalLineClearance

/-- Transport the retained product clearance to its original coefficient source.

The original multiplication operation computes the same bound from both
supplied line certificates. The coefficient identity transports only its
pointwise evaluation guarantee; it does not replace either input polynomial.
-/
def ofProductIdentity {source leftPolynomial rightPolynomial : CoefficientPolynomial}
    {ambient : Geometry.Rational.Box} {y : Fraction.Rational}
    (identity : Factorization.Identity.ProductIdentity source leftPolynomial rightPolynomial)
    (left : HorizontalLineClearance leftPolynomial ambient y)
    (right : HorizontalLineClearance rightPolynomial ambient y) :
    HorizontalLineClearance source ambient y :=
  let retained := left.mul right
  { bound := retained.bound
    positive := retained.positive
    lower := by
      intro x lower upper
      let point := Gaussian.Components.Basic.point x y
      have same : (leftPolynomial * rightPolynomial).eval point = source.eval point :=
        (Dense.Basic.DensePolynomial.eval_mul leftPolynomial rightPolynomial point).trans
          (Factorization.Identity.eval_factorization identity point).symm
      exact Eq.mp (congrArg (fun value : Canonical => retained.bound ≤ Canonical.normSq value) same)
        (retained.lower x lower upper) }

/-- Source transport retains the exact bound computed by the original line multiplication. -/
theorem ofProductIdentity_bound {source leftPolynomial rightPolynomial : CoefficientPolynomial}
    {ambient : Geometry.Rational.Box} {y : Fraction.Rational}
    (identity : Factorization.Identity.ProductIdentity source leftPolynomial rightPolynomial)
    (left : HorizontalLineClearance leftPolynomial ambient y)
    (right : HorizontalLineClearance rightPolynomial ambient y) :
    (ofProductIdentity identity left right).bound = (left.mul right).bound := by
  unfold ofProductIdentity
  rfl

/-- Canonical source transport retains the complete original multiplication certificate. -/
theorem ofProductIdentity_mul {leftPolynomial rightPolynomial : CoefficientPolynomial}
    {ambient : Geometry.Rational.Box} {y : Fraction.Rational}
    (identity : Factorization.Identity.ProductIdentity
      (leftPolynomial * rightPolynomial) leftPolynomial rightPolynomial)
    (left : HorizontalLineClearance leftPolynomial ambient y)
    (right : HorizontalLineClearance rightPolynomial ambient y) :
    ofProductIdentity identity left right = left.mul right := by
  unfold ofProductIdentity
  rfl

end HorizontalLineClearance

end Purelib.Polynomial.Clearance.Box.Line.Basic

end
