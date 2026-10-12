module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Integration.LegendreModularMonodromy
import Purelib.Approximation.Gaussian.Name.Apart.Exact
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Run
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.State
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Legendre.Monodromy
import Init.Prelude
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator
import Purelib.Data.Gaussian.Basic

section
public section

/-!
# Retryable acquisition of Legendre fractional denominators

The generic division preflight is reused at the exact transformed denominator.
A successful retained-state search is converted to the generalized modular
preparation by carrying its based denominator, whole-ball apartness, and
operational equivalence to the original process.
-/

namespace Purelib.Curves.Legendre.Acquisition.Denominator.Standard

open Purelib

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Apart.Exact

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Curves.Legendre
open Purelib.Riemann.Integration.LegendreModularMonodromy (StandardOnePreparation StandardZeroPreparation
  StandardInfinityPreparation one_denominator_one)

/-- Prepare the one-loop denominator as the exact constant one.

The certificate retains the constant's apartness floor and its operational
identity with the transformed denominator of the supplied coherent input. -/
@[expose] def standardOnePreparation (tau : Coherent.CoherentNamed) :
    StandardOnePreparation tau where
  prepared := Coherence.exact 1
  apart := exactApart 1 (by decide)
  equivalent := one_denominator_one tau

/-- Attempt zero-loop denominator acquisition from its initial state.

The result retains the supplied fuel and the original zero-loop monodromy
matrix, including an unresolved finite attempt when acquisition is incomplete. -/
@[expose] def attemptStandardZero (tau : Coherent.CoherentNamed) (fuel : Nat) :
    Run.RunResult Monodromy.zeroMatrix tau
      (State.initial Monodromy.zeroMatrix tau) fuel :=
  Run.attempt Monodromy.zeroMatrix tau
    (State.initial Monodromy.zeroMatrix tau) fuel

/-- Attempt infinity-loop denominator acquisition from its initial state.

The result retains the supplied fuel and the original infinity-loop monodromy
matrix, including an unresolved finite attempt when acquisition is incomplete. -/
@[expose] def attemptStandardInfinity (tau : Coherent.CoherentNamed) (fuel : Nat) :
    Run.RunResult Monodromy.infinityMatrix tau
      (State.initial Monodromy.infinityMatrix tau) fuel :=
  Run.attempt Monodromy.infinityMatrix tau
    (State.initial Monodromy.infinityMatrix tau) fuel

set_option genInjectivity false in
/-- Retain the zero and infinity denominator preparations together.

The two fields keep their respective preparation types and supplied values;
forming the pair performs no new denominator acquisition. -/
structure StandardReadyPayload (zeroType infinityType : Type 1) where
  /-- The retained prepared denominator for the standard zero-loop action. -/ zero : zeroType
  /-- The retained prepared denominator for the standard infinity-loop action. -/ infinity : infinityType

constructive_injectivity StandardReadyPayload

/-- Pair the standard denominator preparations for one coherent input.

The zero and infinity preparations retain that same input and their respective
standard monodromy actions. -/
@[expose] def StandardReady (tau : Coherent.CoherentNamed) : Type 1 :=
  StandardReadyPayload (StandardZeroPreparation tau)
    (StandardInfinityPreparation tau)

end Purelib.Curves.Legendre.Acquisition.Denominator.Standard

end
