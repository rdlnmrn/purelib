module
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RationalFunctions.ArgumentPrinciple.CCL.Basic
public import Purelib.RootIsolation.Multiplicity.Side.CCL.Name
public import Purelib.RationalFunctions.ArgumentPrinciple.CCL.Index

section
public section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

namespace Purelib.RationalFunctions.ArgumentPrinciple.CCL.Basic
namespace NonzeroResult

section
open Purelib.Approximation
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.RationalFunctions
/-- Construct the productive arithmetic CCL name of an indexed retained zero site. -/
@[expose] def zeroArithmeticName
    {numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (result : ArgumentPrinciple.CCL.Basic.NonzeroResult numerator denominator)
    (index : (ArgumentPrinciple.CCL.Basic.NonzeroResult.ZeroIndex result)) :
    Gaussian.Name.Basic.Named :=
  Multiplicity.Side.CCL.Name.sideArithmeticName result.rfap.numeratorSites result.numeratorCCL index

/-- Construct the productive arithmetic CCL name of an indexed retained pole site. -/
@[expose] def poleArithmeticName
    {numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (result : ArgumentPrinciple.CCL.Basic.NonzeroResult numerator denominator)
    (index : (ArgumentPrinciple.CCL.Basic.NonzeroResult.PoleIndex result)) :
    Gaussian.Name.Basic.Named :=
  Multiplicity.Side.CCL.Name.sideArithmeticName result.rfap.denominatorSites result.denominatorCCL index

end

section
open Purelib.Data
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.RationalFunctions
/-- Advancing a zero-site name preserves its emitted prefix and produces exactly the requested number of bits. -/
theorem zeroArithmeticName_productive
    {numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (result : ArgumentPrinciple.CCL.Basic.NonzeroResult numerator denominator)
    (index : (ArgumentPrinciple.CCL.Basic.NonzeroResult.ZeroIndex result)) (count : Nat) :
    ((ArgumentPrinciple.CCL.Basic.NonzeroResult.zeroArithmeticName result) index).machine.emitted.IsPrefix
        (CCL.Transducer.Machine.Advance.advance
          ((ArgumentPrinciple.CCL.Basic.NonzeroResult.zeroArithmeticName result) index).machine count).emitted ∧
      (CCL.Transducer.Machine.Advance.advance
        ((ArgumentPrinciple.CCL.Basic.NonzeroResult.zeroArithmeticName result) index).machine count).emitted.length =
          count :=
  Multiplicity.Side.CCL.Name.sideArithmeticName_productive result.rfap.numeratorSites
    result.numeratorCCL index count

/-- Advancing a pole-site name preserves its emitted prefix and produces exactly the requested number of bits. -/
theorem poleArithmeticName_productive
    {numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (result : ArgumentPrinciple.CCL.Basic.NonzeroResult numerator denominator)
    (index : (ArgumentPrinciple.CCL.Basic.NonzeroResult.PoleIndex result)) (count : Nat) :
    ((ArgumentPrinciple.CCL.Basic.NonzeroResult.poleArithmeticName result) index).machine.emitted.IsPrefix
        (CCL.Transducer.Machine.Advance.advance
          ((ArgumentPrinciple.CCL.Basic.NonzeroResult.poleArithmeticName result) index).machine count).emitted ∧
      (CCL.Transducer.Machine.Advance.advance
        ((ArgumentPrinciple.CCL.Basic.NonzeroResult.poleArithmeticName result) index).machine count).emitted.length =
          count :=
  Multiplicity.Side.CCL.Name.sideArithmeticName_productive result.rfap.denominatorSites
    result.denominatorCCL index count

/-- Every finite advance of a zero-site name remains an exact cursor of its retained process and state. -/
theorem zeroArithmeticName_exact
    {numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (result : ArgumentPrinciple.CCL.Basic.NonzeroResult numerator denominator)
    (index : (ArgumentPrinciple.CCL.Basic.NonzeroResult.ZeroIndex result)) (count : Nat) :
    let name := (ArgumentPrinciple.CCL.Basic.NonzeroResult.zeroArithmeticName result) index
    CCL.Transducer.Machine.Semantics.Basic.ExactCursor
      name.process name.state
      (CCL.Transducer.Machine.Advance.advance name.machine count) :=
  Multiplicity.Side.CCL.Name.sideArithmeticName_exact result.rfap.numeratorSites
    result.numeratorCCL index count

/-- Every finite advance of a pole-site name remains an exact cursor of its retained process and state. -/
theorem poleArithmeticName_exact
    {numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (result : ArgumentPrinciple.CCL.Basic.NonzeroResult numerator denominator)
    (index : (ArgumentPrinciple.CCL.Basic.NonzeroResult.PoleIndex result)) (count : Nat) :
    let name := (ArgumentPrinciple.CCL.Basic.NonzeroResult.poleArithmeticName result) index
    CCL.Transducer.Machine.Semantics.Basic.ExactCursor
      name.process name.state
      (CCL.Transducer.Machine.Advance.advance name.machine count) :=
  Multiplicity.Side.CCL.Name.sideArithmeticName_exact result.rfap.denominatorSites
    result.denominatorCCL index count

end

end NonzeroResult
end Purelib.RationalFunctions.ArgumentPrinciple.CCL.Basic

end
