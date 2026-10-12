module

import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Hermitian.Comparison
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
public import Purelib.Geometry.Projective.Hermitian.Parametrization.Comparison
import Purelib.Geometry.Projective.Homography.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Init.Prelude
meta import Purelib.Elab.ConstructiveInjectivity

section

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Hermitian

open Purelib.LinearAlgebra.Coordinates2.Matrix

section
@[expose] public section

/-!
# Finite descriptions of CCL atom boundaries

An unresolved Hermitian atom is useful to the equality-owner layer only when
its zero boundary retains constructive provenance.  The boundary is either a
rationally parameterized generalized circle/line, a finite explicit zero set,
or the identically-zero form.  This avoids recovering geometry from bare
coefficients by an unbounded search.
-/

namespace Purelib.Geometry.Projective.Hermitian.Chart

set_option genInjectivity false in
/-- Exact geometric source of a parameterized zero boundary. Retaining the matrix and the circle/line constructor makes
bounded chart generation a finite computation rather than reverse-engineering bare form coefficients. -/
inductive CurveSource (reference : GaussianMatrix) (form : Hermitian.HermitianForm) where
  /-- Retain a nonzero-radius norm boundary, invertible matrix, and its shared denominator row. -/ | norm (matrix :
    GaussianMatrix)
      (determinantNonzero :
        BoundaryAdjugate.determinant matrix ≠ 0)
      (lowerRow : matrix.c = reference.c ∧ matrix.d = reference.d)
      (base : Data.Gaussian.Basic.Canonical)
      (baseNonzero : base ≠ 0)
      (form_eq : form = Hermitian.normComparisonForm matrix (Data.Gaussian.Norm.Basic.normSq base))
  /-- Retain a vertical-coordinate boundary, invertible matrix, and its shared denominator row. -/ | real (matrix :
    GaussianMatrix)
      (determinantNonzero :
        BoundaryAdjugate.determinant matrix ≠ 0)
      (lowerRow : matrix.c = reference.c ∧ matrix.d = reference.d)
      (threshold : Fraction.Rational)
      (form_eq : form = Hermitian.realComparisonForm matrix threshold)
  /-- Retain a horizontal-coordinate boundary, invertible matrix, and its shared denominator row. -/ | imaginary (matrix
    : GaussianMatrix)
      (determinantNonzero :
        BoundaryAdjugate.determinant matrix ≠ 0)
      (lowerRow : matrix.c = reference.c ∧ matrix.d = reference.d)
      (threshold : Fraction.Rational)
      (form_eq : form = Hermitian.imagComparisonForm matrix threshold)

constructive_injectivity CurveSource

namespace CurveSource

/-- Primary affine chart of a geometric source. -/
def primary {reference : GaussianMatrix} {form : Hermitian.HermitianForm} :
    Geometry.Projective.Hermitian.Chart.CurveSource reference form → Parametrization form
  | .norm matrix determinantNonzero _lowerRow base _baseNonzero form_eq =>
      form_eq.symm ▸
        Parametrization.normComparison matrix
          determinantNonzero base
  | .real matrix determinantNonzero _lowerRow threshold form_eq =>
      form_eq.symm ▸
        Parametrization.realComparison matrix
          determinantNonzero threshold
  | .imaginary matrix determinantNonzero _lowerRow threshold form_eq =>
      form_eq.symm ▸
        Parametrization.imaginaryComparison matrix
          determinantNonzero threshold

/-- The circle's reciprocal chart supplies its missing projective parameter; coordinate lines need no companion. -/
def companions {reference : GaussianMatrix} {form : Hermitian.HermitianForm} :
    (source : Geometry.Projective.Hermitian.Chart.CurveSource reference form) → List (Parametrization
      form)
  | .norm matrix determinantNonzero _lowerRow base _baseNonzero form_eq =>
      [form_eq.symm ▸
        Parametrization.normComparisonReciprocal matrix
          determinantNonzero base]
  | .real _ _ _ _ _ | .imaginary _ _ _ _ _ => []

end CurveSource
end Purelib.Geometry.Projective.Hermitian.Chart

end

section
@[expose] public section

/-!
# Bounded finite charts for CCL branch boundaries

Circle boundaries use the primary and reciprocal stereographic charts on the
fixed rational cell `[-1,1]`.  Coordinate-line boundaries use one symmetric
cell whose radius is computed from a coefficient majorant for the affine
numerator and an explicitly supplied positive lower bound for the affine
denominator.  Each chart is immediately sent through the finite cleared-gcd
and Sturm event classifier.
-/

namespace Purelib.Geometry.Projective.Hermitian.Chart

namespace CurveSource

/-- Read the retained source matrix from any circle or coordinate-line boundary source. -/
def matrix {reference : GaussianMatrix} {form : Hermitian.HermitianForm} :
    Geometry.Projective.Hermitian.Chart.CurveSource reference form → GaussianMatrix
  | .norm matrix _ _ _ _ _ | .real matrix _ _ _ _ |
      .imaginary matrix _ _ _ _ => matrix

/-- Every source matrix has the same affine denominator as its displayed reference matrix. -/
theorem denominator_eq_reference
    {reference : GaussianMatrix} {form : Hermitian.HermitianForm}
    (source : Geometry.Projective.Hermitian.Chart.CurveSource reference form) (value : Data.Gaussian.Basic.Canonical) :
    Homography.Basic.denominator source.matrix value =
      Homography.Basic.denominator reference value := by
  cases source with
  | norm matrix _ lowerRow _ _ _ =>
      rcases lowerRow with ⟨left, right⟩
      change matrix.c * value + matrix.d =
        reference.c * value + reference.d
      rw [left, right]
  | real matrix _ lowerRow _ _ =>
      rcases lowerRow with ⟨left, right⟩
      change matrix.c * value + matrix.d =
        reference.c * value + reference.d
      rw [left, right]
  | imaginary matrix _ lowerRow _ _ =>
      rcases lowerRow with ⟨left, right⟩
      change matrix.c * value + matrix.d =
        reference.c * value + reference.d
      rw [left, right]

end CurveSource
end Purelib.Geometry.Projective.Hermitian.Chart

end

end
