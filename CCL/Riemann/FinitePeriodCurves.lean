import CCL.Riemann.AlgebraicDifferentials
import CCL.Progressive.PowerMonodromy

/-!
# Exact finite curve inputs for period examples

This lightweight module records the concrete squarefree cyclic curves used by
the finite-period examples.  Keeping the curve inputs separate from the
computed period witnesses lets executable examples import the same public
curves without eagerly initializing unrelated worked-example data.
-/

namespace CCL.Riemann.FinitePeriodExamples

open CCL.Riemann.AlgebraicDifferentials

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev RootDegree := CCL.RootPowers.RootDegree

def degreeThree : RootDegree := ⟨3, by decide⟩
def degreeFour : RootDegree := ⟨4, by decide⟩
def degreeFive : RootDegree := ⟨5, by decide⟩
def degreeSix : RootDegree := ⟨6, by decide⟩
def degreeSeven : RootDegree := ⟨7, by decide⟩
def degreeOne : RootDegree := ⟨1, by decide⟩
def degreeTwo : RootDegree := ⟨2, by decide⟩

def linearPolynomial : GaussianPolynomial :=
  CCL.PowerMonodromy.polynomial 1 degreeOne

def quadraticPolynomial : GaussianPolynomial :=
  CCL.PowerMonodromy.polynomial 1 degreeTwo

def cubicPolynomial : GaussianPolynomial :=
  CCL.PowerMonodromy.polynomial 1 degreeThree

def quarticPolynomial : GaussianPolynomial :=
  CCL.PowerMonodromy.polynomial 1 degreeFour

def quinticPolynomial : GaussianPolynomial :=
  CCL.PowerMonodromy.polynomial 1 degreeFive

def sexticPolynomial : GaussianPolynomial :=
  CCL.PowerMonodromy.polynomial 1 degreeSix

def septicPolynomial : GaussianPolynomial :=
  CCL.PowerMonodromy.polynomial 1 degreeSeven

theorem linear_nonzero : linearPolynomial.isZero = false :=
  CCL.PowerMonodromy.polynomial_nonzero 1 degreeOne

theorem quadratic_nonzero : quadraticPolynomial.isZero = false :=
  CCL.PowerMonodromy.polynomial_nonzero 1 degreeTwo

theorem cubic_nonzero : cubicPolynomial.isZero = false :=
  CCL.PowerMonodromy.polynomial_nonzero 1 degreeThree

theorem quartic_nonzero : quarticPolynomial.isZero = false :=
  CCL.PowerMonodromy.polynomial_nonzero 1 degreeFour

theorem quintic_nonzero : quinticPolynomial.isZero = false :=
  CCL.PowerMonodromy.polynomial_nonzero 1 degreeFive

theorem sextic_nonzero : sexticPolynomial.isZero = false :=
  CCL.PowerMonodromy.polynomial_nonzero 1 degreeSix

theorem septic_nonzero : septicPolynomial.isZero = false :=
  CCL.PowerMonodromy.polynomial_nonzero 1 degreeSeven

theorem linear_degree : linearPolynomial.natDegree = 1 :=
  CCL.PowerMonodromy.polynomial_degree 1 degreeOne

theorem quadratic_degree : quadraticPolynomial.natDegree = 2 :=
  CCL.PowerMonodromy.polynomial_degree 1 degreeTwo

theorem cubic_degree : cubicPolynomial.natDegree = 3 :=
  CCL.PowerMonodromy.polynomial_degree 1 degreeThree

theorem quartic_degree : quarticPolynomial.natDegree = 4 :=
  CCL.PowerMonodromy.polynomial_degree 1 degreeFour

theorem quintic_degree : quinticPolynomial.natDegree = 5 :=
  CCL.PowerMonodromy.polynomial_degree 1 degreeFive

theorem sextic_degree : sexticPolynomial.natDegree = 6 :=
  CCL.PowerMonodromy.polynomial_degree 1 degreeSix

theorem septic_degree : septicPolynomial.natDegree = 7 :=
  CCL.PowerMonodromy.polynomial_degree 1 degreeSeven

def cubic_squarefree :
    RFAP.Squarefree.SquarefreeCertificate cubicPolynomial :=
  CCL.PowerMonodromy.squarefree (by decide : (1 : Gaussian) ≠ 0) degreeThree

def quartic_squarefree :
    RFAP.Squarefree.SquarefreeCertificate quarticPolynomial :=
  CCL.PowerMonodromy.squarefree (by decide : (1 : Gaussian) ≠ 0) degreeFour

def quintic_squarefree :
    RFAP.Squarefree.SquarefreeCertificate quinticPolynomial :=
  CCL.PowerMonodromy.squarefree (by decide : (1 : Gaussian) ≠ 0) degreeFive

def sextic_squarefree :
    RFAP.Squarefree.SquarefreeCertificate sexticPolynomial :=
  CCL.PowerMonodromy.squarefree (by decide : (1 : Gaussian) ≠ 0) degreeSix

def septic_squarefree :
    RFAP.Squarefree.SquarefreeCertificate septicPolynomial :=
  CCL.PowerMonodromy.squarefree (by decide : (1 : Gaussian) ≠ 0) degreeSeven

def linear_squarefree :
    RFAP.Squarefree.SquarefreeCertificate linearPolynomial :=
  CCL.PowerMonodromy.squarefree (by decide : (1 : Gaussian) ≠ 0) degreeOne

def quadratic_squarefree :
    RFAP.Squarefree.SquarefreeCertificate quadraticPolynomial :=
  CCL.PowerMonodromy.squarefree (by decide : (1 : Gaussian) ≠ 0) degreeTwo

/-- The odd linear genus-zero control `y² = x - 1`. -/
def linearCurve : HyperellipticCurve 0 where
  polynomial := linearPolynomial
  nonzero := linear_nonzero
  squarefree := linear_squarefree
  degreeShape := .odd (by simpa using linear_degree)

/-- The even quadratic genus-zero control `y² = x² - 1`. -/
def quadraticCurve : HyperellipticCurve 0 where
  polynomial := quadraticPolynomial
  nonzero := quadratic_nonzero
  squarefree := quadratic_squarefree
  degreeShape := .even (by simpa using quadratic_degree)

/-- The cyclic cubic elliptic curve `y² = x³ - 1`. -/
def cubicCurve : HyperellipticCurve 1 where
  polynomial := cubicPolynomial
  nonzero := cubic_nonzero
  squarefree := cubic_squarefree
  degreeShape := .odd (by simpa using cubic_degree)

/-- The cyclic quartic elliptic curve `y² = x⁴ - 1`. -/
def quarticCurve : HyperellipticCurve 1 where
  polynomial := quarticPolynomial
  nonzero := quartic_nonzero
  squarefree := quartic_squarefree
  degreeShape := .even (by simpa using quartic_degree)

/-- The odd-degree genus-two curve `y² = x⁵ - 1`. -/
def quinticCurve : HyperellipticCurve 2 where
  polynomial := quinticPolynomial
  nonzero := quintic_nonzero
  squarefree := quintic_squarefree
  degreeShape := .odd (by simpa using quintic_degree)

/-- The even-degree genus-two curve `y² = x⁶ - 1`. -/
def sexticCurve : HyperellipticCurve 2 where
  polynomial := sexticPolynomial
  nonzero := sextic_nonzero
  squarefree := sextic_squarefree
  degreeShape := .even (by simpa using sextic_degree)

/-- The odd-degree genus-three curve `y² = x⁷ - 1`. -/
def septicCurve : HyperellipticCurve 3 where
  polynomial := septicPolynomial
  nonzero := septic_nonzero
  squarefree := septic_squarefree
  degreeShape := .odd (by simpa using septic_degree)

end CCL.Riemann.FinitePeriodExamples
