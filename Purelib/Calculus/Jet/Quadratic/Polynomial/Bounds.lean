module

public import Purelib.Calculus.Jet.Quadratic.Polynomial
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Monotonicity
import Purelib.Data.Rat.Fraction.Order.Basic

/-! # Fixed-box bounds on the original two-reading polynomial certificate

The original certificate retains its computed two-point hull and Horner
factor. Both original point containments refine that hull into one fixed box;
the original finite coefficient-fold monotonicity bounds its actual factor
without rebuilding or replacing the certificate.
-/

public section

namespace Purelib.Calculus.Jet.Quadratic.Polynomial

open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

/-- Both original point containments place their computed two-point hull inside the same retained box. -/
private theorem readingBox_refines {box : Box} {first last : Canonical}
    (firstInside : box.Contains first) (lastInside : box.Contains last) :
    (readingBox first last).Refines box :=
  ⟨Fraction.Order.Basic.le_min firstInside.1 lastInside.1,
    Fraction.Order.Basic.max_le firstInside.2.1 lastInside.2.1,
    Fraction.Order.Basic.le_min firstInside.2.2.1 lastInside.2.2.1,
    Fraction.Order.Basic.max_le firstInside.2.2.2 lastInside.2.2.2⟩

/-- The original computed polynomial certificate factor obeys the fixed box's own original Horner remainder ceiling. -/
theorem certificate_factor_le_box (polynomial : CoefficientPolynomial) {box : Box} {first last : Canonical}
    (firstInside : box.Contains first) (lastInside : box.Contains last) :
    (certificate polynomial first last).factor ≤ Bounds.Box.Taylor.denseEvalTaylorRemainderBound polynomial box := by
  rewrite [certificate_factor]
  exact Bounds.Box.Monotonicity.denseEvalTaylorRemainderBound_le_of_refines polynomial
    (readingBox_refines firstInside lastInside)

end Purelib.Calculus.Jet.Quadratic.Polynomial
