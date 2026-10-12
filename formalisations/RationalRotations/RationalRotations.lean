module

public import Purelib.Geometry.Rotations
public import Purelib.Geometry.Quadratic.Space3.Ordered
public import Purelib.Geometry.Rotations.Ternary.Euclidean
import Purelib.Geometry.Rotations.Ternary.Cayley.Matrix
import Purelib.Geometry.Rotations.Ternary.Cayley.Anchor
public import Purelib.Geometry.Rotations.Ternary.Reflection.Factorization
public import Purelib.Geometry.Rotations.Ternary.Cayley.Spread
import Purelib.Geometry.Quadratic.Ternary.Spread
import Purelib.Algebra.Quaternion.Matrix
import Purelib.Algebra.Quaternion.SplitMatrix
public import Purelib.Geometry.Rotations.Projective.Matrix
public import Purelib.Geometry.Rotations.Axis.Finite
public import Purelib.Geometry.Projective.Matrix.Finite
import Purelib.Algebra.Quadratic.Pair.ImaginaryField
public import Purelib.Examples.Geometry.Rotations.Caps
public import Purelib.Examples.Geometry.Rotations.Reflections
public import formalisations.RationalRotations.Chapters

-- Preserve the numbered theorem surface through its migrated subject owners.
public import Purelib.Examples.Geometry.Quadratic.Finite.Five
public import Purelib.Examples.Geometry.Rotations.AnchorProducts
public import Purelib.Examples.Geometry.Rotations.Breakdowns
public import Purelib.Examples.Geometry.Rotations.HalfSpreads
public import Purelib.Examples.Geometry.Rotations.Handedness
public import Purelib.Examples.Geometry.Rotations.PrescribedAxes
public import Purelib.Examples.Geometry.Rotations.RotationAnchors
public import Purelib.Geometry.Rotations.Cayley.FieldRealizations
public import Purelib.Geometry.Rotations.Projective.RayCover
public import Purelib.NumberTheory.SquareClass.Rational.Nonsquare
public import Purelib.Polynomial.RecursiveDense.Rational.Avoidance
public import Purelib.Polynomial.RecursiveDense.Rational.Integral

public import Purelib.Examples.Geometry.Rotations.FieldCounting
public import Purelib.Geometry.Rotations.FiniteField.Conjugacy

/-!
# Rational rotations of three-dimensional Euclidean space

A constructive, finite-coordinate formalization of N. J. Wildberger's
*Rational rotations of three dimensional Euclidean space*, updated against
the supplied `RationalRotationsQuaternions2.pdf`. The coverage ledger follows
this revision's numbering; existing subject-owned declarations retain their
mathematical names and the earlier development remains available.
-/
