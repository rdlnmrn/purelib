module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.CCL.Encoding.Parser.Semantics.Basic
import Purelib.Data.CCL.Encoding.Parser.Syntax
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Gaussian.Basic
public import Purelib.Geometry.CCL.Parser.Normalization
public import Purelib.Geometry.Projective.Hermitian.Affine
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Init.Prelude
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.CCL.Encoding.Parser

open Purelib.Data.ComplexContinuedFraction.Encoding

open Purelib.Geometry.CCL

open Purelib.Geometry.Projective

open Purelib.LinearAlgebra

section
@[expose] public section

/-!
# Finite Hermitian formulas for one raw CCL bit

Before a completed sector, the proposed child is just the next parser-state
formula at the unchanged affine tail.  On the third sector bit, the formula
checks the selected completed block and excludes its zero residual.  The
result is exactly the constructive one-bit semantic decision.
-/

namespace Purelib.Geometry.CCL.Parser.Formula

/-- Squared numerator of the normalized tail after subtraction of the candidate sector representative. -/
def residualForm
    (kind : Syntax.BlockKind) (exponent : Nat) (sector : Data.ComplexContinuedFraction.Encoding.Sector) :
    Hermitian.HermitianForm :=
  let matrix := Parser.normalizedMatrix kind exponent Coordinates2.Matrix.identityMatrix
  Hermitian.affineNormForm (matrix.a - sector.rep * matrix.c)
    (matrix.b - sector.rep * matrix.d)

/-- The residual form evaluates to the squared norm of the normalized value minus the sector representative. -/
theorem eval_residualForm
    (kind : Syntax.BlockKind) (exponent : Nat) (sector : Data.ComplexContinuedFraction.Encoding.Sector)
    (value : Data.Gaussian.Basic.Canonical) :
    (residualForm kind exponent sector).eval value =
      Data.Gaussian.Norm.Basic.normSq (Semantics.Basic.normalizedValue kind exponent value - sector.rep) := by
  cases kind <;>
    simp only [residualForm, Parser.normalizedMatrix, Parser.normalizationMatrix,
      Coordinates2.Matrix.identityMatrix, Coordinates2.Matrix.mul, Line.Matrix.scale, Semantics.Basic.normalizedValue,
      Hermitian.eval_affineNormForm, Data.Gaussian.Basic.zero_mul,
      Data.Gaussian.Basic.one_mul,
      Data.Gaussian.Basic.zero_add,
      Data.Gaussian.Basic.add_zero] <;>
    congr 1 <;>
    apply Data.Gaussian.Basic.ext <;>
      simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.mul_re,
        Data.Gaussian.Basic.mul_im, Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im,
        Data.Gaussian.Basic.zero_re, Data.Gaussian.Basic.zero_im, Data.Gaussian.Basic.one_re,
          Data.Gaussian.Basic.one_im] <;>
      ring1
end Purelib.Geometry.CCL.Parser.Formula

end
