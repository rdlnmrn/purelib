module

import Purelib.Algebra.Clifford.Lorentz.Matrix
public import Purelib.Examples.Geometry.Quadratic.Ternary.Lorentz
public import Purelib.Geometry.Quadratic.Ternary.Lorentz.Reflection
public import Purelib.Geometry.Quadratic.Ternary.Lorentz.NullConic
import Purelib.Geometry.Rotations.Ternary.Lorentz.Cayley
import Purelib.Geometry.Quadratic.Ternary.Lorentz
public import Purelib.Geometry.Rotations.Ternary.Theory
import Purelib.Geometry.Rotations.Ternary.Cayley.HalfTurn
import Purelib.Geometry.Rotations.Ternary.Cayley.Anchor
import Purelib.Geometry.Rotations.Ternary.Lorentz.Orientation
public import Purelib.Geometry.Rotations.Ternary.Lorentz.Causal
public import Purelib.Data.Rat.Fraction.ExplicitOrder.Sign
import Purelib.Geometry.Rotations.Ternary.Lorentz.Projective
import Purelib.Geometry.Rotations.Ternary.Lorentz.SquareClass
public import Purelib.Geometry.Rotations.Ternary.Lorentz.KernelCosets
import Purelib.Algebra.Quaternion.SplitMatrix
public import Purelib.Geometry.Rotations.Ternary.Lorentz.Finite
public import Purelib.Geometry.Rotations.Ternary.Clifford.RayCover
import Purelib.Geometry.Rotations.Ternary.Lorentz.Prescribed
public import Purelib.Geometry.Rotations.Axis.Finite
import Purelib.Geometry.Rotations.Ternary.Lorentz.Splitting
public import Purelib.Geometry.Rotations.Ternary.Reflection.Factorization
import Purelib.Geometry.Rotations.Ternary.Lorentz.Composition
public import Purelib.Geometry.Rotations.Ternary.Split.RationalConjugacy
public import Purelib.Polynomial.RecursiveDense.Rational.Avoidance
public import Purelib.Polynomial.RecursiveDense.Rational.Integral

/-!
# Rational rotations of three dimensional Minkowski space

Publication facade for N. J. Wildberger's *Rational rotations of three
dimensional Minkowski space: rotations, boosts and spinors*, supplied as
`RelativisticsRationalRotations3.pdf`.

The time-first Lorentz form and its dihedron matrix conversion retain the
original form-indexed Clifford owners. The projective correspondence,
reflection factorization, Cayley chart and spread theory are shared with
the general ternary library. `coverage.md` records the remaining source
claims and the distinction from the older split-coordinate specialization.
-/
