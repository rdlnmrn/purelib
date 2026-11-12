module
import Purelib.Examples.Approximation.Gaussian.Provenance.Rational.Cancellation
import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.List.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Division.Prepared.Rational
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Division.Obstruction.Symbolic
import Purelib.Approximation.Gaussian.Division.Partial.Run
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Process.Imaginary.Separation.Conjugate
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Algebraic
meta import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Algebraic
meta import Purelib.Approximation.Gaussian.Provenance.Algebraic.Imaginary
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Provenance.Rational.Arithmetic
import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
import Purelib.Approximation.Gaussian.Sequence

import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Zero
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Gaussian.Equivalence.Zero
import Purelib.Approximation.Gaussian.Division.Prepared.Decision
import Purelib.Approximation.Gaussian.Name.Basic
import Mathlib.Data.Nat.Basic

/-! Exact rational sidecar arithmetic and erased-prefix regression checks. -/

namespace TestPurelib.Approximation.Gaussian.Provenance.Rational

open Purelib.Examples.Approximation.Gaussian.Provenance.Rational.Cancellation (withSidecar)

open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Approximation.Gaussian
open Purelib.Examples
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Coherent.Refinement
open Purelib.Approximation.Gaussian.Division
open Purelib.Approximation.Gaussian.Process.Imaginary
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation
open Purelib.LinearAlgebra.Matrix

/-- Exact rational provenance prepares the Gaussian value one. -/
theorem rational_nonzero_prepared :
    ∃ prepared, (RationalSidecar.exact (1 : Basic.Canonical)).decide = .prepared prepared :=
      ⟨_, rfl⟩

/-- Adding exact provenance for one and negative one excludes the sum. -/
theorem rational_sum_excluded :
    ∃ identity, ((RationalSidecar.exact (1 : Basic.Canonical)).add
      (RationalSidecar.exact (-1))).decide = .excluded identity := ⟨_, rfl⟩

/-- Multiplying exact provenance for one and negative one prepares the product. -/
theorem rational_product_prepared :
    ∃ prepared, ((RationalSidecar.exact (1 : Basic.Canonical)).mul
      (RationalSidecar.exact (-1))).decide = .prepared prepared := ⟨_, rfl⟩

/-- The original exact imaginary input used by the prepared-difference regression. -/
private def imaginary : Basic.Canonical := ⟨0, 1⟩

/-- The conjugated channel retains its exact rational reading and original comparison. -/
private def conjugated : RationalSidecar (CoherentNamed.conj (CoherentNamed.Coherence.exact imaginary)) :=
  ⟨Basic.conj imaginary, CoherentNamed.conj_exact imaginary⟩

/-- Prepare the actual original imaginary input minus its actual conjugated channel. -/
private def imaginaryDifference : Division.Prepared
    (Separation.conjugateDifference (CoherentNamed.Coherence.exact imaginary)) :=
  ((RationalSidecar.exact imaginary).add (Provenance.Rational.Arithmetic.negateRational conjugated)).prepare
    (by decide +kernel)

example : 0 < (Separation.ofConjugatePrepared imaginaryDifference).2.val.gap :=
  (Separation.ofConjugatePrepared imaginaryDifference).2.val.positive

example {value : Basic.Canonical}
    (possible : (CoherentNamed.Coherence.exact imaginary).name.process.Possible
      (Separation.ofConjugatePrepared imaginaryDifference).2.val.state value) :
    (Separation.ofConjugatePrepared imaginaryDifference).2.val.gap ^ 2 ≤ value.im ^ 2 :=
  (Separation.ofConjugatePrepared imaginaryDifference).2.val.squared_lower possible

/-- Exercise the retained imaginary inspection at an inverse-certified identity matrix. -/
private def checkImaginaryProvider : IO Unit := do
  let original := Provenance.Algebraic.Sidecar.ofRational (RationalSidecar.exact imaginary)
  let inspection := Provenance.Algebraic.Sidecar.inspectImaginary _ original
  let result := Algebraic.imaginaryProvider inspection
  match selected : result.1.val.compared.decision with
  | .excluded _ => throw (IO.userError "nonreal input lost its prepared imaginary difference")
  | .prepared _ =>
      have provider : Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Basic.Provider
          (CoherentNamed.Coherence.exact imaginary) := by
        have actual := result.2
        unfold Algebraic.ImaginaryProviderOutcome at actual
        rewrite [selected] at actual
        exact actual
      let denominator := provider Multiplication.identity Inverse.Right.identityInverse
      unless 0 < denominator.apart.certificate.lowerSq do
        throw (IO.userError "the original identity row lost its separated preparation")
  let real := Provenance.Algebraic.Sidecar.ofRational (RationalSidecar.exact 1)
  let rejected := Algebraic.imaginaryProvider (Provenance.Algebraic.Sidecar.inspectImaginary _ real)
  match rejected.1.val.compared.decision with
  | .excluded _ => pure ()
  | .prepared _ => throw (IO.userError "real input lost its retained zero imaginary-difference outcome")

#eval checkImaginaryProvider

/-- Forgetting rational provenance preserves the original emitted CCL prefix.

The underlying coherent channel and machine output remain definitionally the same retained data. -/
theorem forgetting_preserves_prefix :
    withSidecar.forget.channel.name.machine.emitted =
      withSidecar.channel.name.machine.emitted := rfl

end TestPurelib.Approximation.Gaussian.Provenance.Rational
