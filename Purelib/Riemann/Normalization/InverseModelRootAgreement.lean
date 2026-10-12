module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Approximation.Gaussian.Equivalence

public import Purelib.Riemann.Normalization.InverseModelRootChannels

@[expose] public section

/-!
# Operational agreement of roots from the same retained inverse value

Changing the certified domain or residual bound does not change the Newton
root readings when the initial inverse value at the point agrees. The
comparison consumes both retained sample records and their certificates.
-/

namespace Purelib.Riemann.Normalization.InverseModelRootAgreement

open Purelib.Riemann.Normalization.InverseModelRootChannels (RootChannel)

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)

open Purelib.Approximation.Gaussian.Equivalence (Equivalent NamedEquivalent)

variable {polynomial : Polynomial} {firstBox lastBox : Box}
  {firstModel : Model polynomial firstBox} {lastModel : Model polynomial lastBox} {point : Gaussian}

open Purelib.Riemann in
open Purelib.Approximation in
open Purelib.Data in
/-- Equal initial inverse values give operationally equivalent retained root channels.

The certified domains and residual bounds may differ. Equality at the retained point identifies every finite Newton
sample; the constructed comparison retains both original sample approximations and their certificates. -/
def equivalent_of_value (first : RootChannel firstModel point) (last : RootChannel lastModel point)
    (equal : firstModel.value.eval point = lastModel.value.eval point) :
    Gaussian.Equivalence.NamedEquivalent first.certificate.value.name last.certificate.value.name := by
  let firstSamples := first.samples.approximation first.small first.inside
  let lastSamples := last.samples.approximation last.small last.inside
  have samplesEqual (index : Nat) : first.samples.sample index = last.samples.sample index := by
    rw [first.samples.sample_eq, last.samples.sample_eq, (Normalization.InverseModelRootSamples.Model.refine_eval
      firstModel), (Normalization.InverseModelRootSamples.Model.refine_eval lastModel), equal]
  let samples : Gaussian.Equivalence.Equivalent firstSamples lastSamples := {
    compare := fun leftStart rightStart target positive => by
      let comparison := (Gaussian.Equivalence.Equivalent.refl firstSamples).compare leftStart rightStart target positive
      refine ⟨comparison.leftIndex, comparison.rightIndex, comparison.left_ge, comparison.right_ge, ?_⟩
      intro left right leftLater rightLater
      have accurate := comparison.close leftLater rightLater
      change Gaussian.Norm.Basic.normSq
        (first.samples.sample left - first.samples.sample right) < target at accurate
      change Gaussian.Norm.Basic.normSq
        (first.samples.sample left - last.samples.sample right) < target
      rw [← samplesEqual right]
      exact accurate }
  exact first.samples_equivalent.symm.trans (samples.trans last.samples_equivalent)

end Purelib.Riemann.Normalization.InverseModelRootAgreement
