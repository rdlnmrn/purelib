module

public import Purelib.Calculus.Jet.Quadratic.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
public import Purelib.Geometry.Rational.Box.Hull
public import Purelib.Geometry.Rational.Box.Point
import Purelib.Data.Gaussian.Field

/-! # Quadratic certificates from the original polynomial Horner bounds

The original polynomial and two displayed readings determine the value,
formal derivative and exact remainder. The existing finite Horner scan
computes a quadratic factor on a retained box. A constructor also computes
that box as the hull of the two original point boxes, so no enclosure or
Taylor comparison is supplied by its caller.
-/

public section

namespace Purelib.Calculus.Jet.Quadratic.Polynomial

open Purelib.Polynomial.Dense.Gaussian.Basic

open Purelib.Calculus.Jet.Quadratic.Basic
open Purelib.Data
open Purelib.Geometry
open Purelib.Polynomial

/-- The coordinatewise hull of the two original displayed reading points. -/
@[expose] def readingBox (first last : Gaussian.Basic.Canonical) : Rational.Box :=
  Rational.Box.Hull.hull (Rational.Box.Point.pointBox first) (Rational.Box.Point.pointBox last)

/-- The computed hull contains the original first reading. -/
theorem readingBox_first (first last : Gaussian.Basic.Canonical) :
    (readingBox first last).Contains first :=
  Rational.Box.Hull.hull_contains_left (Rational.Box.Point.pointBox_contains first)

/-- The computed hull contains the original last reading. -/
theorem readingBox_last (first last : Gaussian.Basic.Canonical) :
    (readingBox first last).Contains last :=
  Rational.Box.Hull.hull_contains_right (Rational.Box.Point.pointBox_contains last)

/-- Construct a quadratic certificate from the original polynomial and its retained two-point enclosure.

The existing coefficient-fold remainder bound is computed once and retained
as the certificate factor. The original polynomial's formal derivative gives
the slope, and its two evaluations give the actual base and output readings.
-/
@[expose] def certificateInBox (polynomial : CanonicalCoefficients.CoefficientPolynomial)
    (box : Rational.Box) (first last : Gaussian.Basic.Canonical)
    (firstInside : box.Contains first) (lastInside : box.Contains last) : Certificate (last - first) :=
  let base := polynomial.eval first
  let slope := (Dense.Gaussian.GCD.derivative polynomial).eval first
  let output := polynomial.eval last
  let remainder := output - base - (last - first) * slope
  let factor := Dense.Gaussian.Bounds.Box.Taylor.denseEvalTaylorRemainderBound polynomial box
  { base := base
    slope := slope
    output := output
    remainder := remainder
    expansion := rfl
    factor := factor
    factor_nonneg := (Dense.Gaussian.Bounds.Box.Taylor.denseHornerTaylorNormBounds_nonneg polynomial box).2.2
    remainder_le := by
      dsimp only [remainder, output, base, slope, factor]
      simp only [← Gaussian.Norm.Basic.normSq_eq_canonical]
      rewrite [Gaussian.Basic.mul_comm (last - first)]
      exact Dense.Gaussian.Bounds.Box.Taylor.normSq_dense_taylor_remainder_le polynomial lastInside firstInside }

/-- Compute the original two-point enclosure and its certified polynomial Taylor expansion.

Both displayed values are retained unchanged. The computed hull and existing
finite Horner bound supply all enclosure and remainder evidence internally.
-/
@[expose] def certificate (polynomial : CanonicalCoefficients.CoefficientPolynomial)
    (first last : Gaussian.Basic.Canonical) : Certificate (last - first) :=
  let box := readingBox first last
  certificateInBox polynomial box first last (readingBox_first first last) (readingBox_last first last)

/-- The constructed polynomial certificate retains the original first evaluation as its base. -/
theorem certificate_base (polynomial : CanonicalCoefficients.CoefficientPolynomial)
    (first last : Gaussian.Basic.Canonical) : (certificate polynomial first last).base = polynomial.eval first := rfl

/-- The constructed polynomial certificate retains the original last evaluation as its output. -/
theorem certificate_output (polynomial : CanonicalCoefficients.CoefficientPolynomial)
    (first last : Gaussian.Basic.Canonical) : (certificate polynomial first last).output = polynomial.eval last := rfl

/-- The constructed polynomial coefficient is the original formal derivative evaluated at the first reading. -/
theorem certificate_slope (polynomial : CanonicalCoefficients.CoefficientPolynomial)
    (first last : Gaussian.Basic.Canonical) :
    (certificate polynomial first last).slope = (Dense.Gaussian.GCD.derivative polynomial).eval first := rfl

/-- The retained factor is the original Horner remainder scan on the computed two-point hull. -/
theorem certificate_factor (polynomial : CanonicalCoefficients.CoefficientPolynomial)
    (first last : Gaussian.Basic.Canonical) :
    (certificate polynomial first last).factor =
      Dense.Gaussian.Bounds.Box.Taylor.denseEvalTaylorRemainderBound polynomial (readingBox first last) := rfl

end Purelib.Calculus.Jet.Quadratic.Polynomial
