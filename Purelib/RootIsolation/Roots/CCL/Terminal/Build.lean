module
import Purelib.Data.CCL.Encoding.Encoder.Blocks
public import Purelib.Data.CCL.Encoding.Encoder.Cylinder
import Purelib.Data.CCL.Encoding.Encoder.Integral
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.GaussianInt.Fraction.Basic
public import Purelib.Polynomial.Dense.Gaussian.Roots.Certificate
public import Purelib.RootIsolation.Roots.CCL.Terminal.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.GaussianInt.Basic
import Purelib.Polynomial.Dense.Evaluation

section
public section

/-!
# Choice-free box/CCL finite FTA interface

The winding calculation supplies the exact degree-many family and the total
shrinking box tracks.  Each finite accuracy request computes a nonzero
rational sample of its refined box, converts that sample to a canonical
Gaussian-integer fraction, and runs the terminating CCL encoder.  Thus the box
and projective records are carried together without extracting a quotient
representative or naming a completed root.
-/

namespace Purelib.RootIsolation.Roots.CCL.Terminal.Build

open Purelib
open Purelib.Data
open Purelib.Polynomial
open Purelib.RootIsolation

/-- Construct a nonzero exact-root terminal using its displayed rational CCL encoding.

Convert the supplied point once to its Gaussian-integer fraction, then retain
the completed blocks and bit word together with their exact readback equality. -/
@[expose] def nonzeroTerminal
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (point :
      Gaussian.Basic.Canonical) (root : p.eval point = 0)
    (nonzero : point ≠ 0) : Roots.CCL.Terminal.Basic.NonzeroTerminal p := by
  let fraction := GaussianInt.Fraction.ofGaussian point
  let numeratorNonzero :=
    GaussianInt.Fraction.ofGaussian_numerator_ne_zero nonzero
  let encoding := Data.CCL.Encoding.Encoder.Blocks.encodeBlocks fraction
    numeratorNonzero
  exact
    { point := point
      root := root
      nonzero := nonzero
      fraction := fraction
      fractionValue := GaussianInt.Fraction.ofGaussian_value point
      numeratorNonzero := numeratorNonzero
      encoding := encoding
      word := Data.CCL.Encoding.Encoder.Integral.encode fraction numeratorNonzero
      word_eq := Data.CCL.Encoding.Encoder.Cylinder.encode_eq_rawWord fraction
        numeratorNonzero }

/-- Tag a displayed exact root as zero or as a completed nonzero CCL terminal.

The exact point comparison selects the constructor. The nonzero branch
passes that same point, vanishing equation and nonzero witness to its encoder. -/
@[expose] def terminalOfExactRoot
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (root :
      Dense.Gaussian.Roots.Certificate.ExactRoot p) :
    Terminal p := by
  by_cases zero : root.point = 0
  · exact .zero (by simpa only [zero] using root.root)
  · exact .nonzero (Roots.CCL.Terminal.Build.nonzeroTerminal root.point root.root zero)

end Purelib.RootIsolation.Roots.CCL.Terminal.Build

end
