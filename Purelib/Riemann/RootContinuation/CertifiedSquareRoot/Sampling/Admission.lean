module

public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Data.Gaussian.Norm.Basic

/-! # Original tracked-root admission of paid process observations

An observation of the exact cached certificate also retains the original
tracked root's global residual threshold. This admission is distinct from
payment of a chosen accuracy request, which may be either larger or smaller.
Both claims concern the same original candidates and process state.
-/

public section

namespace Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling.ResidualObservation

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Branches

/-- Every original paid observation candidate preserves its tracked owner's original square-residual admission. -/
theorem candidate_residual_lt_target {parameter : Canonical} {root : Certificate parameter}
    {accuracy : AccuracyRequest} (sample : ResidualObservation root accuracy) (owner : Owner parameter)
    (cache_eq : root = owner.certificate owner.parameterNonzero) {candidate : Canonical}
    (possible : sample.observation.Possible candidate) :
    Norm.Basic.normSq (candidate * candidate - parameter) < SquareRootSheets.residualTarget parameter := by
  have originalPossible := possible
  rewrite [sample.observation_eq] at originalPossible
  have process_eq := congrArg (fun certificate : Certificate parameter => certificate.value.name.process) cache_eq
  have ownerPossible := Process.Sampling.possible_castState process_eq sample.state originalPossible
  have residual := CertifiedSquareRoot.root_candidate_residual_lt owner.parameterNonzero owner.track _ ownerPossible
  rewrite [← Norm.Basic.normSq_eq_canonical] at residual
  exact residual

/-- The paid witness preserves the original tracked root's residual threshold independently of its request. -/
theorem reading_residual_lt_target {parameter : Canonical} {root : Certificate parameter}
    {accuracy : AccuracyRequest} (sample : ResidualObservation root accuracy) (owner : Owner parameter)
    (cache_eq : root = owner.certificate owner.parameterNonzero) :
    Norm.Basic.normSq (sample.reading * sample.reading - parameter) < SquareRootSheets.residualTarget parameter :=
  sample.candidate_residual_lt_target owner cache_eq sample.observation.witness_possible

end Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling.ResidualObservation
