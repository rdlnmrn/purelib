module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Data.CCL.Encoding.Encoder.Blocks
import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.GaussianInt.Fraction.Basic
public import Purelib.Data.List.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Polynomial.Dense.Evaluation

-- Preserve the established `Terminal.Basic.Terminal` nominal carrier and methods.
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

namespace Purelib.RootIsolation.Roots.CCL

open Purelib
open Purelib.Data
open Purelib.Polynomial

namespace Terminal.Basic

set_option genInjectivity false in
/-- Complete finite CCL data for an exact nonzero Gaussian-rational root.

The stored point, displayed fraction, completed block encoding and cached raw
word belong to the same polynomial root and retain their reconstruction evidence. -/
structure NonzeroTerminal (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) where
  /-- The retained exact Gaussian rational root. -/ point : Gaussian.Basic.Canonical
  /-- The original polynomial vanishes at the retained point. -/ root : p.eval point = 0
  /-- The retained point is nonzero, as required by its finite CCL encoder. -/ nonzero : point ≠ 0
  /-- The retained Gaussian-integer fraction representing the exact point. -/ fraction : GaussianInt.Fraction
  /-- The retained fraction evaluates to the original point. -/ fractionValue : fraction.value = point
  /-- The fraction's numerator is nonzero. -/ numeratorNonzero : fraction.numerator ≠ 0
  /-- The completed finite block encoding of the retained fraction. -/ encoding :
    Data.CCL.Encoding.Encoder.Blocks.BlockEncoding fraction
  /-- The cached raw word read from the retained completed blocks. -/ word : List.Basic.BinaryWord
  /-- The cached word is exactly the retained block encoding's raw word. -/ word_eq : word =
    Data.CCL.Encoding.Block.Basic.rawWord encoding.blocks

constructive_injectivity NonzeroTerminal

end Terminal.Basic

open Purelib.RootIsolation in
set_option genInjectivity false in
/-- A finite terminal retains either the exact zero root or a completed nonzero encoding.

The zero constructor stores the polynomial equation at zero. The nonzero
constructor retains its displayed root and all cached CCL data. -/
inductive Terminal (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) where
  /-- The original polynomial has the distinguished exact root zero. -/ | zero (root : p.eval 0 = 0)
  /-- The nonzero exact root retains its fraction, encoding and cached word. -/ | nonzero (data :
    Roots.CCL.Terminal.Basic.NonzeroTerminal p)

constructive_injectivity Terminal

namespace Terminal

open Purelib.RootIsolation
/-- Read the terminal's exact Gaussian rational root. -/
@[expose] def point {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} : Terminal p →
  Gaussian.Basic.Canonical
  | .zero _ => 0
  | .nonzero data => data.point

/-- Return the cached word for a nonzero terminal; zero has its distinguished empty option. -/
@[expose] def word? {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} : Terminal p →
  Option
  List.Basic.BinaryWord
  | .zero _ => none
  | .nonzero data => some data.word

/-- The original polynomial vanishes at the terminal's retained point. -/
theorem eval_point {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (terminal :
  Terminal p) :
    p.eval terminal.point = 0 := by
  cases terminal with
  | zero root => exact root
  | nonzero data => exact data.root

/-- Terminal states have exact zero polynomial residual. -/
theorem residual_zero {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (terminal :
  Terminal p) :
    Data.Gaussian.Norm.Basic.normSq
        (p.eval terminal.point) = 0 := by
  rw [terminal.eval_point,
    Gaussian.Norm.Basic.normSq_zero]

/-- A nonzero terminal's completed blocks reconstruct its exact root. -/
theorem reconstruct
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (data :
      Roots.CCL.Terminal.Basic.NonzeroTerminal p) :
    data.encoding.point.Equivalent (Geometry.Projective.Line.Proj.affine data.point) := by
  rw [← data.fractionValue]
  exact data.encoding.reconstruct

end Terminal
end Purelib.RootIsolation.Roots.CCL

end
