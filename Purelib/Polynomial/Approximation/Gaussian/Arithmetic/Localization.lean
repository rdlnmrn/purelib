module

public import Purelib.Polynomial.Approximation.Gaussian.Arithmetic
public import Purelib.Polynomial.Approximation.Gaussian.Localization.Selection
import Purelib.Polynomial.Approximation.Gaussian.Residual.Localization
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Original-channel selection and decisions for recursive arithmetic

The arithmetic cache retains both original input residuals and its actual
output sample program. One retained multiplicity preparation and stable
selection supply result-root comparison and exact zero/preparation on the
unchanged original operation.
-/

public section

namespace Purelib.Polynomial.Approximation.Gaussian.Arithmetic

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Companion (Operation)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)

variable {firstPolynomial secondPolynomial : CoefficientPolynomial} {firstChannel secondChannel : CoherentNamed}
variable {operation : Operation} {first : Residual firstPolynomial firstChannel}
variable {second : Residual secondPolynomial secondChannel}

/-- Prepare the same original arithmetic polynomial and actual output samples at their computed residual bound. -/
def prepareLocalization (arithmetic : Arithmetic operation first second) :
    Localization.Preparation arithmetic.polynomial arithmetic.result :=
  Localization.Preparation.ofResidual arithmetic.polynomial arithmetic.degreePositive arithmetic.result
    arithmetic.residualScale arithmetic.residualScale_nonnegative arithmetic.sample_residual

set_option genInjectivity false in
/-- A retained original arithmetic residual preparation and its actual stable result-root selection. -/
structure Selection (arithmetic : Arithmetic operation first second) where
  /-- The actual original output polynomial's multiplicity and root caches. -/
  preparation : Localization.Preparation arithmetic.polynomial arithmetic.result
  /-- Stable selection on this same original retained preparation. -/
  selected : Localization.Preparation.Selection preparation

constructive_injectivity Selection

/-- Select a stable result root by consuming an already stored original arithmetic preparation. -/
def selectPrepared (arithmetic : Arithmetic operation first second)
    (preparation : Localization.Preparation arithmetic.polynomial arithmetic.result) : Selection arithmetic :=
  ⟨preparation, preparation.select⟩

/-- Compute one original arithmetic preparation and stable result selection with its own finite bounds. -/
def select (arithmetic : Arithmetic operation first second) : Selection arithmetic :=
  arithmetic.selectPrepared arithmetic.prepareLocalization

/-- Read the same stored original result-root coherent channel from the retained arithmetic selection. -/
@[expose] def Selection.channel {arithmetic : Arithmetic operation first second}
    (selection : Selection arithmetic) : CoherentNamed := selection.selected.channel

/-- The unchanged original operation agrees with the same actual selected result-root channel. -/
def Selection.equivalent {arithmetic : Arithmetic operation first second} (selection : Selection arithmetic) :
    Equivalence.NamedEquivalent (Arithmetic.channel operation firstChannel secondChannel).name selection.channel.name :=
  arithmetic.equivalent.trans selection.selected.namedEquivalent

/-- Compute exact zero or denominator preparation for the unchanged original arithmetic operation. -/
def Selection.decide {arithmetic : Arithmetic operation first second} (selection : Selection arithmetic) :
    Division.Prepared.Decision (Arithmetic.channel operation firstChannel secondChannel) :=
  selection.selected.decideOriginal (Arithmetic.channel operation firstChannel secondChannel) arithmetic.equivalent

end Purelib.Polynomial.Approximation.Gaussian.Arithmetic

end
