module

meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Clearance.Pair.Cover.Leaf
public import Purelib.Polynomial.Clearance.Pair.Cover.Prepare
import Purelib.Polynomial.Clearance.Pair.Enclosure
import Purelib.Polynomial.Clearance.Pair.Sample
import Purelib.Polynomial.Dense.Rational.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation

/-!
# Retained polynomial clearance results

A retained result caches the global source, initial enclosure leaf and bounded refinement tree with exact construction
equalities. Optional readbacks consume those cached aggregate floors without recomputing the tree.
-/

namespace Purelib.Polynomial.Clearance.Pair.Cover

-- Preserve the established nominal carrier name without widening this setting to other owners.

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial

set_option genInjectivity false in
/-- Retain the once-generated algebraic proposals with the completed cover.
The public path-bound record can cache this package as optional extra data.

The retained package links its source, initial leaf and finite refinement result by exact construction equalities.
Optional readbacks consume that same cached result. -/
public structure Retained (realPolynomial imagPolynomial : Dense.Rational.Basic.CoordinatePolynomial)
  (parameters : Data.Rat.Interval.Bounds) where
  /-- The once-computed global algebraic proposals for the original polynomial pair. -/ source :
    Clearance.Pair.Cover.Leaf.Source realPolynomial imagPolynomial
  /-- The retained source is exactly the output of the original source preparation. -/ source_eq : source =
    Clearance.Pair.Cover.Leaf.Source.prepare realPolynomial imagPolynomial
  /-- The optional original sample certificate available to the initial leaf. -/ cachedSample : Option
    (Clearance.Pair.Sample.Certificate realPolynomial imagPolynomial parameters)
  /-- The retained initial leaf on the original parameter interval. -/ initial : Leaf source
    parameters
  /-- The initial leaf is exactly the construction from its retained enclosures and supplied sample. -/ initial_eq :
    initial = Leaf.ofEnclosures source initial.enclosures cachedSample
  /-- The finite refinement depth actually used. -/ budget : Nat
  /-- The retained prepared cover and aggregate floor values. -/ result : Clearance.Pair.Cover.Prepare.Prepared source
    parameters
  /-- The result is exactly the bounded refinement of the original initial leaf. -/ result_eq : result =
    Clearance.Pair.Cover.Prepare.refine initial budget

constructive_injectivity Retained

namespace Retained

/-- Retain global algebraic proposals, the supplied enclosures and optional sample, then compute their bounded clearance
cover.

The initial leaf and refinement result carry exact construction equalities and the depth budget used to produce them. -/
@[expose] public def fromEnclosures {realPolynomial imagPolynomial :
  Dense.Rational.Basic.CoordinatePolynomial} {parameters : Data.Rat.Interval.Bounds}
    (enclosures : Clearance.Pair.Enclosure.Components realPolynomial imagPolynomial parameters)
    (cachedSample : Option (Clearance.Pair.Sample.Certificate realPolynomial imagPolynomial parameters) := none) :
    Retained realPolynomial imagPolynomial parameters :=
  let source := Clearance.Pair.Cover.Leaf.Source.prepare realPolynomial imagPolynomial
  let initial := Leaf.ofEnclosures source enclosures cachedSample
  { source, source_eq := rfl, cachedSample
    initial, initial_eq := rfl
    budget := Clearance.Pair.Cover.Prepare.defaultDepth
    result := Clearance.Pair.Cover.Prepare.refine initial Clearance.Pair.Cover.Prepare.defaultDepth, result_eq := rfl }

end Retained

namespace Retained

/-- Read the retained cover's quadrance floor, using zero when no cover is supplied.

An absent certificate reads zero. A present certificate projects its retained quadrance floor, without rebuilding its
source or cached observations. -/
@[expose] public def optionalNorm {realPolynomial imagPolynomial : Dense.Rational.Basic.CoordinatePolynomial}
  {parameters : Data.Rat.Interval.Bounds} :
    Option (Retained realPolynomial imagPolynomial parameters) → Fraction.Rational
  | none => 0
  | some retained => retained.result.normFloor

end Retained

namespace Retained

/-- Read the retained cover's coordinate floor, using zero when no cover is supplied.

An absent cover reads zero. A present cover projects its retained maximum-coordinate floor without refining the
certificate tree again. -/
@[expose] public def optionalCoordinate {realPolynomial imagPolynomial :
  Dense.Rational.Basic.CoordinatePolynomial} {parameters : Data.Rat.Interval.Bounds} :
    Option (Retained realPolynomial imagPolynomial parameters) → Fraction.Rational
  | none => 0
  | some retained => retained.result.coordinateFloor

end Retained

namespace Retained

/-- The optional retained quadrance floor is nonnegative.

The absent branch reads zero. The present branch uses the nonnegativity certificate of its retained tree or sample
floor. -/
public theorem optionalNorm_nonnegative {realPolynomial imagPolynomial :
  Dense.Rational.Basic.CoordinatePolynomial} {parameters : Data.Rat.Interval.Bounds}
    (extra : Option (Retained realPolynomial imagPolynomial parameters)) : 0 ≤
      Clearance.Pair.Cover.Retained.optionalNorm extra := by
  cases extra with
  | none => exact le_rfl
  | some retained => exact retained.result.cover.norm_nonnegative

end Retained

namespace Retained

/-- The optional retained coordinate floor is nonnegative.

The absent branch reads zero. The present branch uses the maximum-coordinate nonnegativity certificate of its retained
cover tree. -/
public theorem optionalCoordinate_nonnegative {realPolynomial imagPolynomial :
  Dense.Rational.Basic.CoordinatePolynomial} {parameters : Data.Rat.Interval.Bounds}
    (extra : Option (Retained realPolynomial imagPolynomial parameters)) : 0 ≤
      Clearance.Pair.Cover.Retained.optionalCoordinate extra := by
  cases extra with
  | none => exact le_rfl
  | some retained => exact retained.result.cover.coordinate_nonnegative

end Retained

namespace Retained

/-- The optional cover floor bounds pair evaluation quadrance throughout the retained interval.

Zero is bounded by the two nonnegative coordinate squares when no certificate is supplied. A present result transports
its retained uniform quadrance bound. -/
public theorem optionalNorm_le {realPolynomial imagPolynomial : Dense.Rational.Basic.CoordinatePolynomial}
  {parameters : Data.Rat.Interval.Bounds}
    (extra : Option (Retained realPolynomial imagPolynomial parameters)) {parameter :
      Fraction.Rational}
    (inside : parameters.Contains parameter) :
    Clearance.Pair.Cover.Retained.optionalNorm extra ≤ realPolynomial.eval parameter ^ 2 + imagPolynomial.eval parameter
      ^ 2 := by
  cases extra with
  | none =>
    exact add_nonneg (Fraction.Order.Arithmetic.sq_nonneg_direct _) (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  | some retained => exact retained.result.cover.norm_le inside

end Retained

namespace Retained

/-- The optional cover floor bounds the larger absolute coordinate throughout the retained interval.

The absent branch reads zero, below the larger nonnegative coordinate magnitude. A present result transports its
retained uniform coordinate bound. -/
public theorem optionalCoordinate_le {realPolynomial imagPolynomial :
  Dense.Rational.Basic.CoordinatePolynomial} {parameters : Data.Rat.Interval.Bounds}
    (extra : Option (Retained realPolynomial imagPolynomial parameters)) {parameter :
      Fraction.Rational}
    (inside : parameters.Contains parameter) :
    Clearance.Pair.Cover.Retained.optionalCoordinate extra ≤ max (Fraction.abs (realPolynomial.eval parameter))
      (Fraction.abs (imagPolynomial.eval parameter)) := by
  cases extra with
  | none => exact (Fraction.Order.Arithmetic.abs_nonneg_direct _).trans (Fraction.Order.Basic.le_max_left _ _)
  | some retained => exact retained.result.cover.coordinate_le inside

end Retained

end Purelib.Polynomial.Clearance.Pair.Cover
