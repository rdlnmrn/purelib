module

import Purelib.Data.Rat.Bounds.Abs

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Gap
public import Purelib.Polynomial.Clearance.Pair.Enclosure
public import Purelib.Polynomial.Clearance.Pair.Sample
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Bounds.Quadratic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Cached polynomial clearance leaves

Each leaf combines global quadratic floors with local enclosure gaps and an optional sample certificate. It retains the
selected floors and exact enclosures for one indexed polynomial pair and parameter interval.
-/

namespace Purelib.Polynomial.Clearance.Pair.Cover

-- Preserve the established nominal carrier name without widening this setting to other owners.

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial

namespace Leaf

set_option genInjectivity false in
/-- Retain the global quadratic floor certificates for a rational polynomial pair.

The two indexed certificates concern the exact supplied real and imaginary coefficient tables. They are computed once
and reused across all local clearance leaves. -/
public structure Source (realPolynomial imagPolynomial : Dense.Rational.Basic.CoordinatePolynomial) where
  /-- The retained global algebraic floor certificate for the real polynomial. -/ realQuadratic :
    Dense.Rational.Bounds.Quadratic.Certificate realPolynomial
  /-- The retained global algebraic floor certificate for the imaginary polynomial. -/ imagQuadratic :
    Dense.Rational.Bounds.Quadratic.Certificate imagPolynomial

constructive_injectivity Source

end Leaf

namespace Leaf.Source.mk

end Leaf.Source.mk

namespace Leaf.Source.mk

end Leaf.Source.mk

namespace Leaf.Source

/-- Compute the two global quadratic floor certificates for a rational polynomial pair.

Preparation normalizes each supplied coefficient table once. The source retains both resulting certificates for reuse
without recomposing either polynomial. -/
@[expose] public def prepare (realPolynomial imagPolynomial :
  Dense.Rational.Basic.CoordinatePolynomial) : Clearance.Pair.Cover.Leaf.Source realPolynomial imagPolynomial
  :=
  ⟨Dense.Rational.Bounds.Quadratic.prepare realPolynomial,
    Dense.Rational.Bounds.Quadratic.prepare imagPolynomial⟩

end Leaf.Source

set_option genInjectivity false in
/-- Cached enclosure, optional sample and exact floor data for one retained parameter interval.

Both coordinate floors combine the original global proposals with local enclosure gaps. The quadrance floor combines
their squares with an optional sample bound; zero remains inconclusive. -/
public structure Leaf {realPolynomial imagPolynomial : Dense.Rational.Basic.CoordinatePolynomial}
    (source : Clearance.Pair.Cover.Leaf.Source realPolynomial imagPolynomial) (parameters :
      Data.Rat.Interval.Bounds) where
  /-- The cached interval enclosures of both original polynomials. -/ enclosures : Clearance.Pair.Enclosure.Components
    realPolynomial imagPolynomial parameters
  /-- The cached real-coordinate absolute-value floor. -/ realFloor : Fraction.Rational
  /-- The real floor is exactly the maximum of its enclosure gap and original global quadratic proposal. -/ realFloor_eq
    : realFloor = max (Data.Rat.Interval.Gap.gap enclosures.realRange) source.realQuadratic.coordinateFloor
  /-- The cached imaginary-coordinate absolute-value floor. -/ imagFloor : Fraction.Rational
  /-- The imaginary floor is exactly the maximum of its enclosure gap and original global quadratic proposal. -/
    imagFloor_eq : imagFloor = max (Data.Rat.Interval.Gap.gap enclosures.imagRange) source.imagQuadratic.coordinateFloor
  /-- The optional retained sample-and-variation certificate for the same polynomial pair and interval. -/ sample :
    Option (Clearance.Pair.Sample.Certificate realPolynomial imagPolynomial parameters)
  /-- The cached pair quadrance lower bound. -/ normFloor : Fraction.Rational
  /-- The quadrance floor is exactly the maximum of the two squared coordinate floors and optional sample floor. -/
    normFloor_eq : normFloor = max (realFloor ^ 2 + imagFloor ^ 2)
    (Clearance.Pair.Sample.optionalNorm sample)
  /-- The cached lower bound on the larger absolute coordinate. -/ coordinateFloor : Fraction.Rational
  /-- The coordinate floor is exactly the maximum of its retained real and imaginary floors. -/ coordinateFloor_eq :
    coordinateFloor = max realFloor imagFloor

constructive_injectivity Leaf

namespace Leaf.mk

end Leaf.mk

namespace Leaf.mk

end Leaf.mk

namespace Leaf

variable {realPolynomial imagPolynomial : Dense.Rational.Basic.CoordinatePolynomial} {source :
  Purelib.Polynomial.Clearance.Pair.Cover.Leaf.Source realPolynomial imagPolynomial}
  {parameters : Data.Rat.Interval.Bounds}

/-- Construct one leaf from cached enclosures and an optional cached sample certificate.

A positive component floor avoids sample construction; otherwise the supplied sample is reused or one sample certificate
is computed. Every derived floor retains its exact defining equality. -/
@[expose] public def ofEnclosures (source : Clearance.Pair.Cover.Leaf.Source realPolynomial imagPolynomial)
    (enclosures : Clearance.Pair.Enclosure.Components realPolynomial imagPolynomial parameters)
    (cachedSample : Option (Clearance.Pair.Sample.Certificate realPolynomial imagPolynomial parameters) := none) :
    Leaf source parameters :=
  let realFloor := max (Data.Rat.Interval.Gap.gap enclosures.realRange) source.realQuadratic.coordinateFloor
  let imagFloor := max (Data.Rat.Interval.Gap.gap enclosures.imagRange) source.imagQuadratic.coordinateFloor
  let componentFloor := realFloor ^ 2 + imagFloor ^ 2
  let sample := if 0 < componentFloor then none else
    match cachedSample with
    | some certificate => some certificate
    | none => some (Clearance.Pair.Sample.prepare realPolynomial imagPolynomial parameters)
  { enclosures, realFloor, realFloor_eq := rfl, imagFloor, imagFloor_eq := rfl
    sample, normFloor := max componentFloor (Clearance.Pair.Sample.optionalNorm sample), normFloor_eq := rfl
    coordinateFloor := max realFloor imagFloor, coordinateFloor_eq := rfl }

/-- Compute the pair's interval enclosures and retain the resulting clearance leaf.

The initial leaf is constructed for the supplied source and interval. Refinement then consumes the fixed depth budget
and retains its actual certificate tree. -/
@[expose] public def prepare (source : Clearance.Pair.Cover.Leaf.Source realPolynomial imagPolynomial) (parameters :
  Data.Rat.Interval.Bounds) : Leaf source parameters :=
  ofEnclosures source (Clearance.Pair.Enclosure.Components.prepare realPolynomial
    imagPolynomial parameters)

/-- The retained real-coordinate floor is nonnegative.

The enclosure gap is nonnegative, and the retained real floor is its maximum with the global quadratic floor. -/
public theorem real_nonnegative (leaf : Leaf source parameters) : 0 ≤ leaf.realFloor := by
  rw [leaf.realFloor_eq]
  exact (Data.Rat.Interval.Gap.gap_nonnegative _).trans (Fraction.Order.Basic.le_max_left _ _)

/-- The retained imaginary-coordinate floor is nonnegative.

The enclosure gap is nonnegative, and the retained imaginary floor is its maximum with the global quadratic floor. -/
public theorem imag_nonnegative (leaf : Leaf source parameters) : 0 ≤ leaf.imagFloor := by
  rw [leaf.imagFloor_eq]
  exact (Data.Rat.Interval.Gap.gap_nonnegative _).trans (Fraction.Order.Basic.le_max_left _ _)

/-- The retained real-coordinate floor bounds the absolute real-polynomial value throughout the interval.

Interval containment bounds the enclosure gap, while the cached global quadratic certificate bounds the same real
polynomial value. Their maximum preserves both proposals. -/
public theorem real_le (leaf : Leaf source parameters) {parameter : Fraction.Rational}
    (inside : parameters.Contains parameter) : leaf.realFloor ≤ Fraction.abs (realPolynomial.eval parameter) := by
  rw [leaf.realFloor_eq]
  exact Fraction.Order.Basic.max_le (Data.Rat.Interval.Gap.gap_le_abs _ (leaf.enclosures.real_contains inside))
    (source.realQuadratic.lower parameter)

/-- The retained imaginary-coordinate floor bounds the absolute imaginary-polynomial value throughout the interval.

Interval containment bounds the enclosure gap, while the cached global quadratic certificate bounds the same imaginary
polynomial value. Their maximum preserves both proposals. -/
public theorem imag_le (leaf : Leaf source parameters) {parameter : Fraction.Rational}
    (inside : parameters.Contains parameter) : leaf.imagFloor ≤ Fraction.abs (imagPolynomial.eval parameter) := by
  rw [leaf.imagFloor_eq]
  exact Fraction.Order.Basic.max_le (Data.Rat.Interval.Gap.gap_le_abs _ (leaf.enclosures.imag_contains inside))
    (source.imagQuadratic.lower parameter)

/-- Squaring a nonnegative absolute-value lower bound gives a lower bound on the coordinate square.

The supplied floor is nonnegative and bounded by the canonical rational magnitude. Squaring that comparison and
identifying the magnitude square gives the value-square bound. -/
private theorem square_le {floor value : Fraction.Rational} (nonnegative : 0 ≤ floor)
    (bound : floor ≤ Fraction.abs value) : floor ^ 2 ≤ value ^ 2 := by
  have squared := Fraction.Order.Arithmetic.pow_le_pow_direct nonnegative bound 2
  rw [Bounds.Abs.abs_sq_direct] at squared
  exact squared

/-- The retained quadrance floor is nonnegative.

The squared coordinate floors are nonnegative. Their sum is below the retained maximum with the optional sample
proposal. -/
public theorem normFloor_nonnegative (leaf : Leaf source parameters) : 0 ≤ leaf.normFloor :=
  by
  rw [leaf.normFloor_eq]
  exact (add_nonneg (Fraction.Order.Arithmetic.sq_nonneg_direct _) (Fraction.Order.Arithmetic.sq_nonneg_direct _)).trans
    (Fraction.Order.Basic.le_max_left _ _)

/-- The retained maximum-coordinate floor is nonnegative.

The real-coordinate floor is nonnegative and below the cached maximum of both coordinate floors. -/
public theorem coordinateFloor_nonnegative (leaf : Leaf source parameters) : 0 ≤
  leaf.coordinateFloor := by
  rw [leaf.coordinateFloor_eq]
  exact leaf.real_nonnegative.trans (Fraction.Order.Basic.le_max_left _ _)

/-- The leaf's combined floor bounds the pair's evaluation quadrance throughout its original interval.

The enclosure or sample certificates bound the same two polynomial values on the supplied interval. The retained floor
readback combines those bounds without changing either coordinate. -/
public theorem normFloor_le (leaf : Leaf source parameters) {parameter : Fraction.Rational}
    (inside : parameters.Contains parameter) :
    leaf.normFloor ≤ realPolynomial.eval parameter ^ 2 + imagPolynomial.eval parameter ^ 2 := by
  rw [leaf.normFloor_eq]
  exact Fraction.Order.Basic.max_le
    (add_le_add (square_le leaf.real_nonnegative (leaf.real_le inside))
      (square_le leaf.imag_nonnegative (leaf.imag_le inside)))
    (Clearance.Pair.Sample.optionalNorm_le leaf.sample inside)

/-- The leaf's coordinate floor bounds the larger absolute coordinate throughout its original interval.

Each retained coordinate floor bounds its own polynomial magnitude. The maximum comparison preserves those two distinct
coordinate bounds. -/
public theorem coordinateFloor_le (leaf : Leaf source parameters) {parameter :
  Fraction.Rational}
    (inside : parameters.Contains parameter) :
    leaf.coordinateFloor ≤ max (Fraction.abs (realPolynomial.eval parameter)) (Fraction.abs (imagPolynomial.eval
      parameter)) := by
  rw [leaf.coordinateFloor_eq]
  exact Fraction.Order.Basic.max_le
    ((leaf.real_le inside).trans (Fraction.Order.Basic.le_max_left _ _))
    ((leaf.imag_le inside).trans (Fraction.Order.Basic.le_max_right _ _))

end Leaf

end Purelib.Polynomial.Clearance.Pair.Cover
