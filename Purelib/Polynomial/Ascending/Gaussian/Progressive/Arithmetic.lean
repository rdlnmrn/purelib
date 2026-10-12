module
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
public import Purelib.Polynomial.Ascending.Gaussian.Progressive.Coefficients
public import Purelib.Polynomial.Ascending.Gaussian.Progressive.Basic

open Purelib.Polynomial.Ascending.Gaussian.Progressive.Basic (TaylorJet)

open Purelib.Approximation.Gaussian

open Purelib.Polynomial

section
@[expose] public section

/-!
# Progressive finite Taylor and multivariable CCL tables

The displayed higher-jet layer stores Gaussian rationals.  Here every entry is
instead a coherent productive CCL channel.  All operations recurse over the
displayed finite coefficient lists, and every resulting table inherits one
computable joint request from `ProgressiveFiniteTable`.
-/

namespace Purelib.Polynomial.Ascending.Gaussian.Progressive.Basic.TaylorJet
section

/-- Add coherent Taylor coefficient channels, retaining the unmatched tail. -/
def add (left right :
  TaylorJet) : TaylorJet :=
  ⟨Ascending.Gaussian.Progressive.Coefficients.addCoefficients left.coefficients right.coefficients⟩

/-- Negate each retained coherent Taylor coefficient channel. -/
def neg (jet :
  TaylorJet) : TaylorJet :=
  ⟨jet.coefficients.map Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.neg⟩

/-- Multiply each coherent Taylor coefficient by the supplied coherent scalar channel. -/
def scale (factor :
  Name.Coherent.CoherentNamed) (jet : TaylorJet) :
  TaylorJet :=
  ⟨Ascending.Gaussian.Progressive.Coefficients.scaleCoefficients factor jet.coefficients⟩

/-- Construct the complete finite convolution of two coherent Taylor tables.

Each coefficient is built from the existing channel arithmetic; no truncation is performed. -/
def mul (left right :
  TaylorJet) : TaylorJet :=
  ⟨Ascending.Gaussian.Progressive.Coefficients.mulCoefficients left.coefficients right.coefficients⟩

/-- Substitute one coherent Taylor table into another by finite Horner coefficient arithmetic. -/
def compose (outer inner :
  TaylorJet) : TaylorJet :=
  ⟨Ascending.Gaussian.Progressive.Coefficients.composeCoefficients outer.coefficients inner.coefficients⟩

/-- Retain only the initial `count` coherent Taylor coefficient channels. -/
def truncate (count : Nat) (jet :
  TaylorJet) : TaylorJet :=
  ⟨jet.coefficients.take count⟩

/-- Differentiate a coherent Taylor table using exact natural degree channels.

The constant channel is discarded and each remaining channel is multiplied by its original positive degree. -/
def derivative (jet :
  TaylorJet) : TaylorJet :=
  match jet.coefficients with
  | [] => ⟨[]⟩
  | _constant :: remaining => ⟨Ascending.Gaussian.Progressive.Coefficients.derivativeFrom 1 remaining⟩

/-- Compute the requested finite number of derivatives of a coherent Taylor table. -/
def derivativeOrder :
  TaylorJet → Nat → TaylorJet
  | jet, 0 => jet
  | jet, order + 1 => derivative
    (derivativeOrder jet order)
end

end Purelib.Polynomial.Ascending.Gaussian.Progressive.Basic.TaylorJet

end
