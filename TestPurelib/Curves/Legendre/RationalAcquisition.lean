module

import Purelib.Curves.Legendre.Acquisition.Words
import Purelib.Approximation.Gaussian.Acquisition.Annotated.Basic
import Purelib.Topology.Knot.Braid.Word.Basic

/-!
# Exact rational word acquisition preserves the original retained state

Real rational source evidence selects ordered domain inspection for every
finite word. The report retains the original source state and request index,
while continuation uses its exact cached executed-prefix output.
-/

namespace TestPurelib.Curves.Legendre.RationalAcquisition

open Purelib.Curves.Legendre.Acquisition
open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Topology.Knot
open Purelib.Riemann.RootContinuation
open Purelib.Approximation.Gaussian.Acquisition (Provenance)

example {channel : CoherentNamed} (root : SquareRootSidecar.Sidecar channel) (zero : root.parameter = 0) :
    ∃ reading, (Provenance.squareRoot root).rationalReading = some reading ∧ reading.value = 0 :=
  Provenance.rationalReading_zero_root root zero

example {channel : CoherentNamed} (root : SquareRootSidecar.Sidecar channel) (zero : root.parameter = 0)
    (word : Braid.Word 3) :
    (Words.acquire (Words.State.start ⟨channel, some (Provenance.squareRoot root)⟩)
      word 1 (by decide +kernel)).1.route = .exact :=
  (Words.acquire_zero_root (Words.State.start ⟨channel, some (Provenance.squareRoot root)⟩)
    root zero rfl rfl rfl word 1 (by decide +kernel)).1

example (word : Braid.Word 3) :
    (Words.acquire (Words.State.start
      ⟨_, some (Provenance.squareRoot SquareRootSidecar.zeroSidecar)⟩) word 1 (by decide +kernel)).1.route =
      .exact :=
  (Words.acquire_zero_root (Words.State.start
    ⟨_, some (Provenance.squareRoot SquareRootSidecar.zeroSidecar)⟩)
    SquareRootSidecar.zeroSidecar rfl rfl rfl rfl word 1 (by decide +kernel)).1

example (word : Braid.Word 3) :
    (Words.acquire (Words.State.start (Annotated.rational 0)) word 1 (by decide +kernel)).1.route = .exact :=
  Words.start_exact (Annotated.rational 0) 0 rfl rfl word 1 (by decide +kernel)

example (word : Braid.Word 3) :
    (Words.acquire (Words.State.start (Annotated.rational 1)) word 1 (by decide +kernel)).1.next.state =
      (Words.State.start (Annotated.rational 1)).state :=
  Words.start_exact_state (Annotated.rational 1) 1 rfl rfl word 1 (by decide +kernel)

example (word : Braid.Word 3) :
    ∃ result, (Words.acquire (Words.State.start (Annotated.rational 0)) word 1 (by decide +kernel)).2 =
      .exact result :=
  Words.start_exact_result (Annotated.rational 0) 0 rfl rfl word 1 (by decide +kernel)

example {tau : CoherentNamed} (word : Braid.Word 3) (result : Words.Report.RationalResult tau word) :
    result.continuePrefix.provenance = some (.rational result.execution.reading) :=
  result.continuePrefix_provenance

example (word : Braid.Word 3) :
    (Words.acquire (Words.State.start (Annotated.rational 0)) word 1
      (by decide +kernel)).1.next.state.retained.nextIndex =
      (Words.State.start (Annotated.rational 0)).state.retained.nextIndex :=
  (Words.acquire (Words.State.start (Annotated.rational 0)) word 1 (by decide +kernel)).1.index_eq

example {tau : CoherentNamed} (input : Words.State.Input tau)
    (reading : Purelib.Approximation.Gaussian.Provenance.Rational.Basic.RationalSidecar tau)
    (cached : input.cachedRational = some reading) (provider : input.provider = none)
    (separation : input.separation = none) (word : Braid.Word 3) :
    Words.acquire input word 1 (by decide +kernel) = Words.rational input reading word 1 :=
  Words.acquire_cached_rational input reading cached provider separation word 1 (by decide +kernel)

example {tau : CoherentNamed} (input : Words.State.Input tau)
    (reading : Purelib.Approximation.Gaussian.Provenance.Rational.Basic.RationalSidecar tau) (word : Braid.Word 3) :
    (Words.rational input reading word 1).1.next.cachedRational = some reading :=
  Words.rational_cached input reading word 1

end TestPurelib.Curves.Legendre.RationalAcquisition
