module
import Purelib.Polynomial.Power.Gaussian
import Purelib.Polynomial.Power.Gaussian.Bezout
public import Purelib.Polynomial.Power.Gaussian.Squarefree
public import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Nat.Positive
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic

@[expose] public section

/-!
# Exact finite curve inputs for period examples

This lightweight module records the concrete squarefree cyclic curves used by
the finite-period examples.  Keeping the curve inputs separate from the
computed period witnesses lets executable examples import the same public
curves without eagerly initializing unrelated worked-example data.
-/

namespace Purelib.Riemann.Periods.PeriodCurves

open Purelib.Data in
/-- The executable Gaussian rational coefficient type. -/
abbrev Gaussian := Gaussian.Basic.Canonical
open Purelib.Polynomial in
/-- The dense Gaussian polynomial type used by the cyclic curve inputs. -/
abbrev GaussianPolynomial :=
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
open Purelib.Data in
/-- A positive natural degree with its retained positivity proof. -/
abbrev RootDegree := Nat.Positive.RootDegree

/-- The positive degree 3 with its executable positivity certificate. -/
def degreeThree : RootDegree := ⟨3, by decide⟩
/-- The positive degree 4 with its executable positivity certificate. -/
def degreeFour : RootDegree := ⟨4, by decide⟩
/-- The positive degree 5 with its executable positivity certificate. -/
def degreeFive : RootDegree := ⟨5, by decide⟩
/-- The positive degree 6 with its executable positivity certificate. -/
def degreeSix : RootDegree := ⟨6, by decide⟩
/-- The positive degree 7 with its executable positivity certificate. -/
def degreeSeven : RootDegree := ⟨7, by decide⟩
/-- The positive degree 1 with its executable positivity certificate. -/
def degreeOne : RootDegree := ⟨1, by decide⟩
/-- The positive degree 2 with its executable positivity certificate. -/
def degreeTwo : RootDegree := ⟨2, by decide⟩

section
open Purelib.Polynomial
/-- The dense Gaussian polynomial x to the power 1 minus one. -/
def linearPolynomial : GaussianPolynomial :=
  Purelib.Polynomial.Power.Gaussian.rootPolynomial 1 degreeOne

/-- The dense Gaussian polynomial x to the power 2 minus one. -/
def quadraticPolynomial : GaussianPolynomial :=
  Purelib.Polynomial.Power.Gaussian.rootPolynomial 1 degreeTwo

/-- The dense Gaussian polynomial x to the power 3 minus one. -/
def cubicPolynomial : GaussianPolynomial :=
  Purelib.Polynomial.Power.Gaussian.rootPolynomial 1 degreeThree

/-- The dense Gaussian polynomial x to the power 4 minus one. -/
def quarticPolynomial : GaussianPolynomial :=
  Purelib.Polynomial.Power.Gaussian.rootPolynomial 1 degreeFour

/-- The dense Gaussian polynomial x to the power 5 minus one. -/
def quinticPolynomial : GaussianPolynomial :=
  Purelib.Polynomial.Power.Gaussian.rootPolynomial 1 degreeFive

/-- The dense Gaussian polynomial x to the power 6 minus one. -/
def sexticPolynomial : GaussianPolynomial :=
  Purelib.Polynomial.Power.Gaussian.rootPolynomial 1 degreeSix

/-- The dense Gaussian polynomial x to the power 7 minus one. -/
def septicPolynomial : GaussianPolynomial :=
  Purelib.Polynomial.Power.Gaussian.rootPolynomial 1 degreeSeven

/-- The displayed linear polynomial is nonzero. -/
theorem linear_nonzero : linearPolynomial.isZero = false :=
  Power.Gaussian.Bezout.polynomial_nonzero 1 degreeOne

/-- The displayed quadratic polynomial is nonzero. -/
theorem quadratic_nonzero : quadraticPolynomial.isZero = false :=
  Power.Gaussian.Bezout.polynomial_nonzero 1 degreeTwo

/-- The displayed cubic polynomial is nonzero. -/
theorem cubic_nonzero : cubicPolynomial.isZero = false :=
  Power.Gaussian.Bezout.polynomial_nonzero 1 degreeThree

/-- The displayed quartic polynomial is nonzero. -/
theorem quartic_nonzero : quarticPolynomial.isZero = false :=
  Power.Gaussian.Bezout.polynomial_nonzero 1 degreeFour

/-- The displayed quintic polynomial is nonzero. -/
theorem quintic_nonzero : quinticPolynomial.isZero = false :=
  Power.Gaussian.Bezout.polynomial_nonzero 1 degreeFive

/-- The displayed sextic polynomial is nonzero. -/
theorem sextic_nonzero : sexticPolynomial.isZero = false :=
  Power.Gaussian.Bezout.polynomial_nonzero 1 degreeSix

/-- The displayed septic polynomial is nonzero. -/
theorem septic_nonzero : septicPolynomial.isZero = false :=
  Power.Gaussian.Bezout.polynomial_nonzero 1 degreeSeven

/-- The displayed linear polynomial has natural degree 1. -/
theorem linear_degree : linearPolynomial.natDegree = 1 :=
  Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree 1 degreeOne

/-- The displayed quadratic polynomial has natural degree 2. -/
theorem quadratic_degree : quadraticPolynomial.natDegree = 2 :=
  Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree 1 degreeTwo

/-- The displayed cubic polynomial has natural degree 3. -/
theorem cubic_degree : cubicPolynomial.natDegree = 3 :=
  Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree 1 degreeThree

/-- The displayed quartic polynomial has natural degree 4. -/
theorem quartic_degree : quarticPolynomial.natDegree = 4 :=
  Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree 1 degreeFour

/-- The displayed quintic polynomial has natural degree 5. -/
theorem quintic_degree : quinticPolynomial.natDegree = 5 :=
  Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree 1 degreeFive

/-- The displayed sextic polynomial has natural degree 6. -/
theorem sextic_degree : sexticPolynomial.natDegree = 6 :=
  Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree 1 degreeSix

/-- The displayed septic polynomial has natural degree 7. -/
theorem septic_degree : septicPolynomial.natDegree = 7 :=
  Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree 1 degreeSeven

/-- The executable squarefree certificate for x to the power 3 minus one. -/
def cubic_squarefree :
    Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate cubicPolynomial :=
  Power.Gaussian.Squarefree.squarefree (by decide : (1 : Gaussian) ≠ 0) degreeThree

/-- The executable squarefree certificate for x to the power 4 minus one. -/
def quartic_squarefree :
    Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate quarticPolynomial :=
  Power.Gaussian.Squarefree.squarefree (by decide : (1 : Gaussian) ≠ 0) degreeFour

/-- The executable squarefree certificate for x to the power 5 minus one. -/
def quintic_squarefree :
    Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate quinticPolynomial :=
  Power.Gaussian.Squarefree.squarefree (by decide : (1 : Gaussian) ≠ 0) degreeFive

/-- The executable squarefree certificate for x to the power 6 minus one. -/
def sextic_squarefree :
    Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate sexticPolynomial :=
  Power.Gaussian.Squarefree.squarefree (by decide : (1 : Gaussian) ≠ 0) degreeSix

/-- The executable squarefree certificate for x to the power 7 minus one. -/
def septic_squarefree :
    Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate septicPolynomial :=
  Power.Gaussian.Squarefree.squarefree (by decide : (1 : Gaussian) ≠ 0) degreeSeven

/-- The executable squarefree certificate for x to the power 1 minus one. -/
def linear_squarefree :
    Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate linearPolynomial :=
  Power.Gaussian.Squarefree.squarefree (by decide : (1 : Gaussian) ≠ 0) degreeOne

/-- The executable squarefree certificate for x to the power 2 minus one. -/
def quadratic_squarefree :
    Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate quadraticPolynomial :=
  Power.Gaussian.Squarefree.squarefree (by decide : (1 : Gaussian) ≠ 0) degreeTwo

end

open Purelib.Curves
/-- The genus-0 cyclic hyperelliptic curve y squared equals x to the power 1 minus one.

Retain the dense polynomial, its nonzeroness and squarefree certificates, and the exact odd degree shape. -/
def linearCurve : Hyperelliptic.Basic.HyperellipticCurve 0 where
  polynomial := linearPolynomial
  nonzero := linear_nonzero
  squarefree := linear_squarefree
  degreeShape := .odd (by simpa using linear_degree)

/-- The genus-0 cyclic hyperelliptic curve y squared equals x to the power 2 minus one.

Retain the dense polynomial, its nonzeroness and squarefree certificates, and the exact even degree shape. -/
def quadraticCurve : Hyperelliptic.Basic.HyperellipticCurve 0 where
  polynomial := quadraticPolynomial
  nonzero := quadratic_nonzero
  squarefree := quadratic_squarefree
  degreeShape := .even (by simpa using quadratic_degree)

/-- The genus-1 cyclic hyperelliptic curve y squared equals x to the power 3 minus one.

Retain the dense polynomial, its nonzeroness and squarefree certificates, and the exact odd degree shape. -/
def cubicCurve : Hyperelliptic.Basic.HyperellipticCurve 1 where
  polynomial := cubicPolynomial
  nonzero := cubic_nonzero
  squarefree := cubic_squarefree
  degreeShape := .odd (by simpa using cubic_degree)

/-- The genus-1 cyclic hyperelliptic curve y squared equals x to the power 4 minus one.

Retain the dense polynomial, its nonzeroness and squarefree certificates, and the exact even degree shape. -/
def quarticCurve : Hyperelliptic.Basic.HyperellipticCurve 1 where
  polynomial := quarticPolynomial
  nonzero := quartic_nonzero
  squarefree := quartic_squarefree
  degreeShape := .even (by simpa using quartic_degree)

/-- The genus-2 cyclic hyperelliptic curve y squared equals x to the power 5 minus one.

Retain the dense polynomial, its nonzeroness and squarefree certificates, and the exact odd degree shape. -/
def quinticCurve : Hyperelliptic.Basic.HyperellipticCurve 2 where
  polynomial := quinticPolynomial
  nonzero := quintic_nonzero
  squarefree := quintic_squarefree
  degreeShape := .odd (by simpa using quintic_degree)

/-- The genus-2 cyclic hyperelliptic curve y squared equals x to the power 6 minus one.

Retain the dense polynomial, its nonzeroness and squarefree certificates, and the exact even degree shape. -/
def sexticCurve : Hyperelliptic.Basic.HyperellipticCurve 2 where
  polynomial := sexticPolynomial
  nonzero := sextic_nonzero
  squarefree := sextic_squarefree
  degreeShape := .even (by simpa using sextic_degree)

/-- The genus-3 cyclic hyperelliptic curve y squared equals x to the power 7 minus one.

Retain the dense polynomial, its nonzeroness and squarefree certificates, and the exact odd degree shape. -/
def septicCurve : Hyperelliptic.Basic.HyperellipticCurve 3 where
  polynomial := septicPolynomial
  nonzero := septic_nonzero
  squarefree := septic_squarefree
  degreeShape := .odd (by simpa using septic_degree)

end Purelib.Riemann.Periods.PeriodCurves
