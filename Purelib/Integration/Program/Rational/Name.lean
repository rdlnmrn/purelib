module
import Purelib.Approximation.Gaussian.Sequence
public import Purelib.Integration.CCL.Program
import Purelib.Integration.Program.Rational.Antiderivative
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Sequence.Constant
import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
public import Purelib.Approximation.Gaussian.Sequence.Name.Exact
import Purelib.Integration.Polynomial.Rational.Cell.Basic
import Purelib.Integration.Polynomial.Rational.Path.Basic
import Purelib.Integration.Program.Rational.Basic
public import Purelib.Integration.Program.Rational.Exact
import Purelib.Polynomial.Ascending.Rational.Basic
import Purelib.Polynomial.Ascending.Rational.Integral
import Purelib.Integration.Program.Rational.Cached.Basic
public import Purelib.Integration.Program.Rational.Approximation
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Integration.CertifiedProgram

section
@[expose] public section

/-!
# General certified integration by finite path refinements

An integrand is supplied operationally: at each natural refinement it returns
one finite path of rational polynomial cell models and finite rational sample
certificates.  The integration program sums the exact polynomial cell
integrals.  A rational geometric modulus and a finite later-refinement
certificate turn those displayed sums into an ordinary productive CCL name.

There is no measure, completed partition, function-as-an-infinite-set, or
infinitesimal.  The only universal refinements are natural-number calls to the
supplied finite program.
-/

namespace Purelib.Integration.Program.Rational

section RefinementProgram

open Purelib.Approximation.Gaussian in
open Purelib.Integration.Program.Rational in
/-- Read the coherent Gaussian output from the original rational program's certified view. -/
def Basic.RefinementProgram.output (program : Basic.RefinementProgram) :
  Name.Coherent.CoherentNamed :=
  (program.certifiedView).program.output

section
open Purelib.Approximation.Gaussian
open Purelib.Data.Gaussian
open Purelib.Integration.Polynomial.Rational.Cell
open Purelib.Integration.Polynomial.Rational.Path
open Purelib.Integration.Program.Rational
open Purelib.Polynomial.Ascending
/-- The original exact-polynomial program output is equivalent to the exact name of its retained single-cell sample. -/
def Basic.RefinementProgram.exactPolynomial_equivalent (start finish :
  Basic.Canonical)
    (polynomial : Rational.Basic.CoefficientPolynomial) :
    Equivalence.NamedEquivalent
      (Basic.RefinementProgram.exactPolynomial start finish polynomial).output.name
      (Name.Basic.Named.exact
        ((Basic.PathModel.mk [Basic.CellModel.exact start finish polynomial]).integralSample)) := by
  let program := Basic.RefinementProgram.exactPolynomial start finish polynomial
  let value :=
    (Basic.PathModel.mk [Basic.CellModel.exact start finish polynomial]).integralSample
  let constant :=
    Sequence.Constant.constantApproximation value
  have samples : ∀ index, program.approximation.sample index =
      constant.sample index := by
    intro index
    change
      (Basic.PathModel.mk [Basic.CellModel.exact start finish polynomial]).integralSample =
        value
    rfl
  exact Equivalence.NamedEquivalent.trans
    (Sequence.Name.Equivalence.approximationEquivalent_toNamed
      (Sequence.Equivalence.approximationEquivalentOfSamplesEq
        program.approximation constant samples))
    (Equivalence.NamedEquivalent.symm
      (Sequence.Name.Exact.exact_toConstantNamed value))

/-- The original exact-polynomial output is equivalent to displacement times the unit-interval polynomial integral.

Both original segment endpoints and the exact original rational polynomial remain in the resulting named value. -/
def Basic.RefinementProgram.exactPolynomial_equivalent_integral (start
  finish : Basic.Canonical)
    (polynomial : Rational.Basic.CoefficientPolynomial) :
    Equivalence.NamedEquivalent
      (Basic.RefinementProgram.exactPolynomial start finish polynomial).output.name
      (Name.Basic.Named.exact
        ((finish - start) *
          Rational.Integral.definiteIntegral polynomial 0 1)) := by
  simpa only [Basic.PathModel.singleton_integralSample,
    Basic.CellModel.exact_integralSample] using
      Basic.RefinementProgram.exactPolynomial_equivalent start finish polynomial
end

section AntiderivativeProcess

open Purelib.Approximation.Gaussian
open Purelib.Integration.Program.Rational
/-- Read the approximation sequence from the retained original antiderivative-difference view. -/
def
  Antiderivative.RefinementProgram.AntiderivativeProcess.differenceApproximation
  (program : Basic.RefinementProgram)
    (antiderivative : Basic.RefinementProgram.AntiderivativeProcess program) : Sequence.ApproximationData :=
  (Basic.RefinementProgram.AntiderivativeProcess.differenceView program antiderivative).program.approximation

/-- Read the coherent output from the retained original antiderivative-difference view. -/
def Antiderivative.RefinementProgram.AntiderivativeProcess.differenceOutput
  (program : Basic.RefinementProgram)
    (antiderivative : Basic.RefinementProgram.AntiderivativeProcess program) : Name.Coherent.CoherentNamed :=
  (Basic.RefinementProgram.AntiderivativeProcess.differenceView program antiderivative).program.output

/-- The original program output is equivalent to its retained antiderivative-difference output.

The stagewise antiderivative certificates equate the exact original samples while both original producers and their
views remain intact. -/
def Antiderivative.RefinementProgram.AntiderivativeProcess.ftc_equivalent
  (program : Basic.RefinementProgram)
    (antiderivative : Basic.RefinementProgram.AntiderivativeProcess program) :
    Equivalence.NamedEquivalent
      program.output.name (Antiderivative.RefinementProgram.AntiderivativeProcess.differenceOutput program
        antiderivative).name :=
  Sequence.Name.Equivalence.approximationEquivalent_toNamed
    (Sequence.Equivalence.approximationEquivalentOfSamplesEq
      program.approximation (Antiderivative.RefinementProgram.AntiderivativeProcess.differenceApproximation program
        antiderivative)
      (by
        intro index
        exact (Antiderivative.RefinementProgram.AntiderivativeProcess.differenceSample_eq program antiderivative
          index).symm))

end AntiderivativeProcess

end RefinementProgram

end Purelib.Integration.Program.Rational

end
