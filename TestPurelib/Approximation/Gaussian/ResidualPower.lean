module

import Purelib.Polynomial.Approximation.Gaussian.Residual.Power
meta import Purelib.Polynomial.Approximation.Gaussian.Residual.Power
import Purelib.Approximation.Gaussian.Acquisition.Expression.PowerReduction
meta import Purelib.Approximation.Gaussian.Acquisition.Expression.PowerReduction
meta import Purelib.Approximation.Gaussian.Acquisition.Expression.Normalization
meta import Purelib.Approximation.Gaussian.Acquisition.Annotated.Arithmetic
import Purelib.Data.Gaussian.Norm.Basic
meta import Purelib.Data.Gaussian.Norm.Basic
meta import Purelib.Approximation.Gaussian.Geometric

/-! # Original residual coefficient checks and automatic finite-power evidence -/

namespace TestPurelib.Approximation.Gaussian.ResidualPower

open Purelib
open Purelib.Polynomial
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Approximation.Gaussian.Acquisition.Expression.Basic

example {polynomial : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {channel : CoherentNamed} (residual : Polynomial.Approximation.Gaussian.Residual polynomial channel)
    (parameter : Purelib.Data.Gaussian.Basic.Canonical) (degree : Purelib.Data.Nat.Positive.RootDegree)
    (same : polynomial = Power.Gaussian.rootPolynomial parameter degree) :
    Provenance.Power.PowerIdentity channel degree.value parameter := residual.powerIdentity parameter degree same

/-- Execute the actual original coefficient test and automatic provenance reader on a retained algebraic atom. -/
private meta def check : IO Unit := do
  let sidecar := Provenance.Algebraic.Sidecar.ofRational (RationalSidecar.exact 3)
  match sidecar.residual.inspectPower with
  | .recognized _ _ => pure ()
  | .other _ => throw (IO.userError "monic linear residual failed its original coefficient check")
  let environment := fun (_ : Fin 1) => Acquisition.Annotated.algebraic sidecar
  let binding : Binding environment := ⟨.atom ⟨0, by decide +kernel⟩, environment ⟨0, by decide +kernel⟩, rfl⟩
  match binding.powerEvidence with
  | .known degree _ parameter _ =>
      unless degree = 1 ∧ parameter = 3 do
        throw (IO.userError "automatic algebraic power evidence lost the retained degree or coefficient")
  | _ => throw (IO.userError "original algebraic atom remained unsupported after a checked power identity")

  let polynomial : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial := ⟨[2, -6]⟩
  let nonmonic : Polynomial.Approximation.Gaussian.Residual polynomial (CoherentNamed.Coherence.exact 3) :=
    Polynomial.Approximation.Gaussian.Residual.ofGeometric (by decide +kernel)
      (Geometric.GeometricApproximation.exact 3)
      (Polynomial.Approximation.Gaussian.Residual.exact 3).equivalent 0 (by decide +kernel) (by
        intro index
        change Purelib.Data.Gaussian.Norm.Basic.normSq (polynomial.eval 3) ≤
          Purelib.Approximation.Rational.Geometric.Basic.quarterRadius 0 index
        rewrite [show polynomial.eval 3 = 0 by decide +kernel, Purelib.Data.Gaussian.Norm.Basic.normSq_zero]
        exact Purelib.Approximation.Rational.Geometric.Basic.quarterRadius_nonneg (by decide +kernel) index)
  match nonmonic.inspectPower with
  | .other _ => pure ()
  | .recognized _ _ =>
      throw (IO.userError "nonmonic original coefficients were silently replaced by a power polynomial")

#eval check

end TestPurelib.Approximation.Gaussian.ResidualPower
