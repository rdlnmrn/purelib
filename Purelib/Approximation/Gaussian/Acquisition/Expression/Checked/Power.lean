module

public import Purelib.Approximation.Gaussian.Provenance.Algebraic
public import Purelib.Polynomial.Approximation.Gaussian.Residual.Power
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Exact power readings checked from the original admitted child residual -/

public section
namespace Purelib.Approximation.Gaussian.Acquisition.Expression.Checked

open Purelib.Approximation.Gaussian.Provenance
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Polynomial.Approximation.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)

set_option genInjectivity false in
/-- The same original child residual's actual pure-power inspection and matching requested exponent. -/
structure PowerReading {channel : CoherentNamed} (sidecar : Algebraic.Sidecar channel) (exponent : Nat) where
  /-- The actual original residual's inspected coefficient form and operational power identity. -/
  form : Residual.PowerForm sidecar.residual
  /-- This is the same once computed inspection of the original child's retained coefficients. -/
  form_eq : form = sidecar.residual.inspectPower
  /-- The requested exponent is the original residual's own positive degree. -/
  degree_eq : sidecar.polynomial.natDegree = exponent
  /-- The actual original coefficient table has its inspected monic pure-power form. -/
  coefficient_eq : sidecar.polynomial = Purelib.Polynomial.Power.Gaussian.rootPolynomial
    (-sidecar.polynomial.eval 0) ⟨sidecar.polynomial.natDegree, sidecar.residual.degreePositive⟩
  /-- The same retained inspection supplied this original-channel operational power identity. -/
  identity : Power.PowerIdentity channel sidecar.polynomial.natDegree (-sidecar.polynomial.eval 0)
  /-- These are the actual coefficient and power-identity data retained by the same original inspection. -/
  recognized : form = .recognized coefficient_eq identity

constructive_injectivity PowerReading

namespace PowerReading

/-- Read the exact coefficient on the unchanged original numerical power channel through the retained identity. -/
@[expose] def reading {channel : CoherentNamed} {sidecar : Algebraic.Sidecar channel} {exponent : Nat}
    (certificate : PowerReading sidecar exponent) :
    Rational.Basic.RationalSidecar (Power.namedPower channel exponent) :=
  ⟨-sidecar.polynomial.eval 0, by
    have equation := certificate.identity
    rewrite [certificate.degree_eq] at equation
    exact equation⟩

/-- The power reading is the parameter computed from those same retained original polynomial coefficients. -/
theorem reading_value {channel : CoherentNamed} {sidecar : Algebraic.Sidecar channel} {exponent : Nat}
    (certificate : PowerReading sidecar exponent) :
    certificate.reading.value = -sidecar.polynomial.eval 0 := rfl

/-- Inspect the actual child coefficients and requested exponent once, retaining the successful original form. -/
@[expose] def inspect {channel : CoherentNamed} (sidecar : Algebraic.Sidecar channel) (exponent : Nat) :
    Option (PowerReading sidecar exponent) :=
  let form := sidecar.residual.inspectPower
  if sameDegree : sidecar.polynomial.natDegree = exponent then
    match formEq : form with
    | .recognized coefficient identity => some ⟨form, rfl, sameDegree, coefficient, identity, formEq⟩
    | .other _ => none
  else none

end PowerReading

end Purelib.Approximation.Gaussian.Acquisition.Expression.Checked
end
