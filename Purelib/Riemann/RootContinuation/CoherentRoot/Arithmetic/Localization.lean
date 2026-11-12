module

public import Purelib.Riemann.RootContinuation.CoherentRoot.Arithmetic
public import Purelib.Polynomial.Approximation.Gaussian.Localization.Selection
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Approximation.Gaussian.Arithmetic

/-!
# Finite localization of original root arithmetic samples

Both original input root realizations and the arithmetic elimination remain
the owners. Their computed residual budget prepares the original output
polynomial's multiplicity localization once. Positive radius requests select
nearby original factor-root data at a computed sufficient finite stage.
-/

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot.Arithmetic

open Purelib
open Purelib.Polynomial.Approximation.Gaussian renaming Arithmetic -> PolynomialArithmetic
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Companion (Operation)

variable {firstPolynomial secondPolynomial : GaussianPolynomial} {firstAmbient secondAmbient : Box}
variable {firstTrack : WindingOneTrack firstPolynomial firstAmbient}
variable {secondTrack : WindingOneTrack secondPolynomial secondAmbient}
variable {operation : Operation} {first : CertifiedName firstTrack} {second : CertifiedName secondTrack}

/-- Prepare multiplicity-aware sample localization from the same original arithmetic elimination and residual cache. -/
def prepareLocalization (arithmetic : Arithmetic operation first second) :
    Approximation.Gaussian.Localization.Preparation arithmetic.polynomial arithmetic.result :=
  Approximation.Gaussian.Localization.Preparation.ofResidual arithmetic.polynomial arithmetic.degree_pos
    arithmetic.result arithmetic.residualScale arithmetic.residualScale_nonnegative arithmetic.sample_residual

set_option genInjectivity false in
/-- An original arithmetic operation with its actual residual preparation and stable selected result-root occurrence. -/
structure Selection (arithmetic : Arithmetic operation first second) where
  /-- The retained original arithmetic polynomial's multiplicity localization and same root caches. -/
  preparation : Approximation.Gaussian.Localization.Preparation arithmetic.polynomial arithmetic.result
  /-- The computed stable root selection on this same retained preparation. -/
  selected : Approximation.Gaussian.Localization.Preparation.Selection preparation

constructive_injectivity Selection

/-- Select the original arithmetic result root using an already stored residual preparation without rerunning it. -/
def selectPrepared (arithmetic : Arithmetic operation first second)
    (preparation : Approximation.Gaussian.Localization.Preparation arithmetic.polynomial arithmetic.result) :
    Selection arithmetic := ⟨preparation, preparation.select⟩

/-- Prepare and select a stable result root of the same original arithmetic channels with computed finite bounds. -/
def select (arithmetic : Arithmetic operation first second) : Selection arithmetic :=
  arithmetic.selectPrepared arithmetic.prepareLocalization

/-- Read the same original selected result-root channel from the retained arithmetic selection cache. -/
@[expose] def Selection.channel {arithmetic : Arithmetic operation first second} (selection : Selection arithmetic) :
    Approximation.Gaussian.Name.Coherent.CoherentNamed := selection.selected.channel

/-- The unchanged original sum or product channel agrees with its same stored selected result-root channel. -/
def Selection.equivalent {arithmetic : Arithmetic operation first second} (selection : Selection arithmetic) :
    Approximation.Gaussian.Equivalence.NamedEquivalent
      (PolynomialArithmetic.channel operation first.value second.value).name selection.channel.name :=
  arithmetic.equivalent.trans selection.selected.namedEquivalent

/-- Compute exact zero or preparation of the unchanged original arithmetic channel using the retained selection. -/
def Selection.decide {arithmetic : Arithmetic operation first second} (selection : Selection arithmetic) :
    Approximation.Gaussian.Division.Prepared.Decision
      (PolynomialArithmetic.channel operation first.value second.value) :=
  selection.selected.decideOriginal (PolynomialArithmetic.channel operation first.value second.value)
    arithmetic.equivalent

end Purelib.Riemann.RootContinuation.CoherentRoot.Arithmetic

end
