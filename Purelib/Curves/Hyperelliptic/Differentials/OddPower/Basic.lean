module

import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
public import Purelib.Approximation.Gaussian.Name.Coherent.Power
public import Purelib.Polynomial.Dense.Gaussian.Basic
import Init.Prelude
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Evaluation
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Polynomial.Dense.Gaussian.Basic

section
@[expose] public section

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
-/

namespace Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic

/-! ## Odd-power algebraic integrands -/

set_option genInjectivity false in
/-- A displayed differential `scale * numerator(x) * dx / y^(2*denominatorPairs+1)`. -/
structure OddPowerDifferential where
  /-- The explicit Gaussian polynomial numerator of the differential. -/
  numerator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
  /-- The number of additional pairs of sheet-value factors in the odd denominator power. -/ denominatorPairs : Nat
  /-- The exact Gaussian scalar multiplying the polynomial numerator. -/ scale : Data.Gaussian.Basic.Canonical

constructive_injectivity Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential

namespace OddPowerDifferential

/-- The odd sheet-value exponent, twice the retained pair count plus one. -/
def denominatorExponent
  (differential : Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential) : Nat :=
  2 * differential.denominatorPairs + 1

/-- The actual productive coefficient name at one displayed point and sheet. Only division by the already apart sheet
value is used; higher reciprocal powers are total finite multiplications. -/
def value (differential :
  Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential) (point : Data.Gaussian.Basic.Canonical)
    (sheetValue : Coherent.CoherentNamed)
    (apart : Named.Apart sheetValue.name) :
    Coherent.CoherentNamed :=
  let numerator := Coherence.exact
    (differential.scale * differential.numerator.eval point)
  let reciprocal := CoherentNamed.div
    (Coherence.exact 1) sheetValue apart
  CoherentNamed.mul numerator
    (Power.namedPower reciprocal differential.denominatorExponent)

end OddPowerDifferential

end Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic

end
