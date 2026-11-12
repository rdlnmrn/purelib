module

public import Purelib.Polynomial.Elimination.Separated.Sylvester
public import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Coefficients
public import Purelib.Polynomial.Dense.Gaussian.Components.Selection
public import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Adjugate
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Evaluation
import Purelib.Data.Gaussian.Cast
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Checked scaled inverse preparation of an original separated Sylvester matrix -/

public section

namespace Purelib.Polynomial.Elimination.Separated.Preparation

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.LinearAlgebra.PolynomialMatrix
open Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled
open Purelib.Polynomial.Dense

set_option genInjectivity false in
/-- A proved failed nonzero scalar or original coefficient product on one retained proposal. -/
inductive Invalid (p : CoefficientPolynomial)
    (data : Basic.ScaledInverseData Canonical (p.natDegree + p.natDegree)) where
  /-- The proposed scalar polynomial is zero. -/
  | zero (failed : data.scalar.isZero ≠ false)
  /-- One complete original coefficient product failed. -/
  | products (failure : Coefficients.Invalid (Sylvester.separatedSylvester p) data)

constructive_injectivity Invalid

set_option genInjectivity false in
/-- The actual accepted proposal or retained failed proposal followed by the original total fallback. -/
inductive Construction (p : CoefficientPolynomial) :
    Basic.ScaledInverseData Canonical (p.natDegree + p.natDegree) → Type where
  /-- Retain both checked polynomial products of the actual accepted proposal. -/
  | checked {data} (products : Coefficients.Products (Sylvester.separatedSylvester p) data) : Construction p data
  /-- Retain the actual rejected proposal and its failure before the unchanged original fallback. -/
  | fallback (proposal : Basic.ScaledInverseData Canonical (p.natDegree + p.natDegree))
      (failure : Invalid p proposal) :
      Construction p (Compute.scaledInverseData (p.natDegree + p.natDegree) (Sylvester.separatedSylvester p))

constructive_injectivity Construction

set_option genInjectivity false in
/-- A retained nonzero polynomial scalar and scaled inverse of the same original Sylvester matrix.

The complete specialized product laws concern this same retained data. The
construction preserves acceptance checks or the rejected proposal and exact
original fallback; no supplied successful producer hypothesis is required.
-/
structure Prepared (p : CoefficientPolynomial) where
  /-- The actual retained polynomial scalar and inverse matrix. -/
  data : Basic.ScaledInverseData Canonical (p.natDegree + p.natDegree)
  /-- The retained scalar is a nonzero polynomial. -/
  nonzero : data.scalar.isZero = false
  /-- Both original scaled product identities hold at every displayed point. -/
  specializations : Coefficients.Specializations (Sylvester.separatedSylvester p) data
  /-- The original proposal and checked acceptance or fallback history. -/
  construction : Construction p data

constructive_injectivity Prepared

/-- Check the actual finite proposal and otherwise retain its failure with the certified original fallback.

Every nonzero source remains admitted. A rejected proposal changes neither
the original source nor the fallback's coefficient and product guarantees.
-/
def prepareWithProposal (p : CoefficientPolynomial) (nonzero : p.isZero = false)
    (proposal : Basic.ScaledInverseData Canonical (p.natDegree + p.natDegree)) : Prepared p :=
  let fallback := fun failure : Invalid p proposal =>
    { data := Compute.scaledInverseData (p.natDegree + p.natDegree) (Sylvester.separatedSylvester p)
      nonzero := Sylvester.separatedScalar_nonzero p nonzero
      specializations := fun point => Evaluation.scaledInverseData_spec point _ _
      construction := .fallback proposal failure }
  if scalarNonzero : proposal.scalar.isZero = false then
    match Coefficients.check (Sylvester.separatedSylvester p) proposal with
    | .ok products => ⟨proposal, scalarNonzero, products.specializations, .checked products⟩
    | .error failure => fallback (.products failure)
  else fallback (.zero scalarNonzero)

/-- Prepare the actual finite trace proposal on the same original source, retaining checked failure and fallback. -/
def prepare (p : CoefficientPolynomial) (nonzero : p.isZero = false) : Prepared p :=
  prepareWithProposal p nonzero (Adjugate.compute (Sylvester.separatedSylvester p))

namespace Prepared

/-- Read a nonzero rational coordinate of the same retained Gaussian scalar. -/
def eliminant {p : CoefficientPolynomial} (prepared : Prepared p) :=
  Gaussian.Components.Selection.selectedCoordinate prepared.data.scalar

/-- The selected coordinate is a nonzero rational polynomial. -/
theorem eliminant_nonzero {p : CoefficientPolynomial} (prepared : Prepared p) :
    prepared.eliminant.isZero = false :=
  Gaussian.Components.Selection.selectedCoordinate_nonzero _ prepared.nonzero

/-- Nonvanishing of the selected coordinate implies nonvanishing of this same retained scalar. -/
theorem scalar_ne_zero {p : CoefficientPolynomial} (prepared : Prepared p)
    (parameter : Purelib.Data.Rat.Fraction.Rational) (nonzero : prepared.eliminant.eval parameter ≠ 0) :
    prepared.data.scalar.eval (Purelib.Data.Gaussian.Cast.Path.ofCoordinate parameter) ≠ 0 := by
  intro scalarZero
  apply nonzero
  change (Gaussian.Components.Selection.selectedCoordinate prepared.data.scalar).eval parameter = 0
  rewrite [Gaussian.Components.Selection.eval_selectedCoordinate, scalarZero]
  split <;> rfl

end Prepared

end Purelib.Polynomial.Elimination.Separated.Preparation

end
