module

import Purelib.RootIsolation.Multiplicity.Site.Realization
import Purelib.Approximation.Gaussian.Provenance.PolynomialRoot
import Purelib.Polynomial.Approximation.Gaussian.Residual
import Purelib.Polynomial.Approximation.Gaussian.Arithmetic
meta import Purelib.Polynomial.Approximation.Gaussian.Arithmetic
meta import Purelib.Approximation.Gaussian.Provenance.PolynomialRoot
import Purelib.Approximation.Gaussian.Division.Acquisition.Dispatch
import Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Admission
import Purelib.RootIsolation.Multiplicity.Family.Build
meta import Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Admission
meta import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
meta import Purelib.Polynomial.Dense.Gaussian.Linear.Translated.Squarefree
meta import Purelib.Polynomial.Dense.Gaussian.Squarefree.RootCofactor
meta import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Evaluation

/-!
# Original-source equations at retained multiplicity roots

A doubled factor uses the same root channel and cache. Original multiplicity
sites retain their actual context and cofactor, and their equations evaluate
the source polynomial rather than only its squarefree factor.
-/

namespace TestPurelib.RootIsolation.MultiplicityRealization

open Purelib.RootIsolation.Multiplicity.Site
open Purelib.RootIsolation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial
open Purelib.Polynomial.Approximation.Gaussian renaming Residual -> PolynomialResidual
open Purelib.Polynomial.Approximation.Gaussian renaming Arithmetic -> PolynomialArithmetic
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.RootContinuation
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Polynomial.Approximation.Gaussian.Evaluation
open Purelib.RootIsolation.Multiplicity

example {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack polynomial ambient}
    (root : CoherentRoot.CertifiedName track) :
    NamedEquivalent (Horner.polynomialEval (polynomial * polynomial) root.value).name (Coherence.exact 0).name :=
  root.factor_zero (polynomial * polynomial) polynomial
    (fun point => Dense.Basic.DensePolynomial.eval_mul polynomial polynomial point)
    (Dense.Gaussian.Bounds.Box.denseEvalNormBound polynomial ambient)
    (Dense.Gaussian.Bounds.Box.denseHornerNormBounds_nonneg polynomial ambient).1
    (fun index => Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormBound polynomial
      (root.sample_inside index))

example {source opposite : CoefficientPolynomial} (input : Basic.TrackSiteInput source opposite) :
    (Realization.ofInput input).cofactor = input.context.singleCofactor input.decomposition :=
  (Realization.ofInput input).cofactor_eq

example {source opposite : CoefficientPolynomial} (input : Basic.TrackSiteInput source opposite) :
    (Realization.ofInput input).root.approximation =
      (CoherentRoot.certifiedName input.track input.context.focus.degreePositive).approximation := rfl

example {source opposite : CoefficientPolynomial} (input : Basic.TrackSiteInput source opposite) :
    NamedEquivalent (Horner.polynomialEval source (Realization.ofInput input).root.value).name
      (Coherence.exact 0).name :=
  (Realization.ofInput input).equation

example {firstSource firstOpposite secondSource secondOpposite : CoefficientPolynomial}
    {firstInput : Basic.TrackSiteInput firstSource firstOpposite}
    {secondInput : Basic.TrackSiteInput secondSource secondOpposite}
    (first : Realization firstInput) (second : Realization secondInput) (firstStart secondStart : Nat) :
    CoherentRoot.CommonSource.PreparedComparison first.factorInput second.factorInput
      first.root second.root firstStart secondStart := first.compare second firstStart secondStart

example {polynomial : CoefficientPolynomial}
    (result : CCL.Polynomial.Basic.NonzeroResult polynomial)
    (index : CCL.Polynomial.Index.NonzeroResult.RootIndex result) :
    NamedEquivalent
      (Horner.polynomialEval polynomial (CCL.Polynomial.Admission.ofResult result index).channel).name
      (Coherence.exact 0).name :=
  (CCL.Polynomial.Admission.ofResult result index).equation

example {polynomial : CoefficientPolynomial}
    (result : CCL.Polynomial.Basic.NonzeroResult polynomial)
    (index : CCL.Polynomial.Index.NonzeroResult.RootIndex result) :
    NamedEquivalent (CCL.Polynomial.Name.NonzeroResult.rootName result index)
      (CCL.Polynomial.Admission.ofResult result index).channel.name :=
  (CCL.Polynomial.Admission.ofResult result index).equivalent

/-- Execute repeated-root admission and check its original multiplicity and both name readings. -/
private meta def checkRepeatedExactAdmission : IO Unit := do
  let linear := Dense.Gaussian.Linear.Translated.translatedCoordinate 1
  let polynomial := linear * linear
  match CCL.Polynomial.Build.isolate polynomial with
  | .zeroNumerator _ _ => throw (IO.userError "nonzero repeated polynomial was classified as zero")
  | .nonzero result =>
      match CCL.Polynomial.Index.NonzeroResult.rootIndices result with
      | [] => throw (IO.userError "repeated positive-degree polynomial lost its root site")
      | index :: remaining =>
          unless remaining.isEmpty do
            throw (IO.userError "repeated factor duplicated its geometric root site")
          let admission := CCL.Polynomial.Admission.ofResult result index
          unless admission.multiplicity = 2 do
            throw (IO.userError "original root admission lost the repeated source multiplicity")
          let sidecar := Provenance.PolynomialRoot.Sidecar.ofAdmission admission
          let numerical := sidecar.residualCertificate
          let sum := PolynomialArithmetic.ofResiduals .add numerical.2 (PolynomialResidual.exact 2)
          unless sum.result.sample 2 = 3 ∧ sum.polynomial.eval 3 = 0 do
            throw (IO.userError "original coefficient-first root admission did not feed recursive arithmetic")
          unless numerical.2.source.sample 3 = 1 ∧ sidecar.owner.polynomial = polynomial ∧
              sidecar.numerical.2.source.sample 4 = 1 do
            throw (IO.userError "root sidecar lost its original repeated source or stored numerical residual cache")
          let transported := sidecar.transport (Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent.refl _)
          unless transported.numerical.1 = sidecar.numerical.1 ∧
              transported.numerical.2.source.sample 5 = sidecar.numerical.2.source.sample 5 do
            throw (IO.userError "sidecar transport replaced its actual cached numerical owner data")
          let admitted := Purelib.Approximation.Gaussian.Name.Sampling.approximation admission.channel.name
          let original := Purelib.Approximation.Gaussian.Name.Sampling.approximation
            (CCL.Polynomial.Name.NonzeroResult.rootName result index)
          unless admitted.sample 0 = 1 ∧ original.sample 0 = 1 ∧ polynomial.eval (admitted.sample 0) = 0 do
            throw (IO.userError "coefficient-first admission changed the original exact root channel or source")

#eval checkRepeatedExactAdmission

example {source opposite : CoefficientPolynomial}
    (input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite)
    (index : Fin input.contexts.length) :
    input.buildFamily.observationAt index = input.observe (input.contexts.get index) :=
  input.buildFamily_observationAt index

example {polynomial : CoefficientPolynomial}
    {result : CCL.Polynomial.Basic.NonzeroResult polynomial}
    {index : CCL.Polynomial.Index.NonzeroResult.RootIndex result}
    (admission : CCL.Polynomial.Admission result index) :
    Purelib.Approximation.Gaussian.Division.Prepared.Decision admission.channel := admission.decide

/-- Execute retained linear division at an exact source root, checking its original quotient and nonzero reading. -/
private meta def checkRootCofactor : IO Unit := do
  let polynomial := Dense.Gaussian.Linear.Translated.translatedCoordinate 1
  let certificate := Dense.Gaussian.Squarefree.RootCofactor.ofRoot polynomial 1
    (Dense.Gaussian.Linear.Translated.Squarefree.translatedCoordinate_nonzero 1)
    (Dense.Gaussian.Linear.Translated.Squarefree.certificate 1) (by decide +kernel)
  unless certificate.value = 1 ∧ certificate.result.remainder.isZero ∧
      certificate.result.quotient.eval 4 = 1 do
    throw (IO.userError "displayed-root division lost its retained original quotient or nonzero point value")

#eval checkRootCofactor

example {channel : CoherentNamed}
    (sidecar : Provenance.PolynomialRoot.Sidecar channel)
    (numerator : CoherentNamed) (threshold : Rational) (positive : 0 < threshold) :
    (Division.Acquisition.Dispatch.acquire numerator
      (Division.Acquisition.State.start (Acquisition.Annotated.polynomialRoot sidecar))
      threshold positive).2.status = .ready ∨
    (Division.Acquisition.Dispatch.acquire numerator
      (Division.Acquisition.State.start (Acquisition.Annotated.polynomialRoot sidecar))
      threshold positive).2.status = .zero :=
  Division.Acquisition.Dispatch.acquire_symbolic_decisive numerator
    (Division.Acquisition.State.start (Acquisition.Annotated.polynomialRoot sidecar))
    threshold positive (.polynomialRoot sidecar) rfl rfl

example {channel : CoherentNamed} (sidecar : Provenance.PolynomialRoot.Sidecar channel) :
    Σ polynomial : CoefficientPolynomial, PolynomialResidual polynomial channel :=
  sidecar.residualCertificate

example {first second : CoherentNamed} (sidecar : Provenance.PolynomialRoot.Sidecar first)
    (equivalent : Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent second.name first.name) :
    (sidecar.transport equivalent).numerical = sidecar.numerical := sidecar.transport_numerical equivalent

end TestPurelib.RootIsolation.MultiplicityRealization
