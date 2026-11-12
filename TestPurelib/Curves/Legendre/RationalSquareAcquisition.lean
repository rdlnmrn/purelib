module

import Purelib.Curves.Legendre.Acquisition.Words
import Purelib.Riemann.RootContinuation.SquareRootSidecar
meta import Purelib.Curves.Legendre.Acquisition.Words
meta import Purelib.Riemann.RootContinuation.SquareRootSidecar
meta import Purelib.Topology.Knot.Braid.Basic
meta import Purelib.Data.Gaussian.Field
meta import Purelib.Data.Rat.Fraction

/-!
# Rational-square roots use exact ordered word domains and cached resume

Both original isolated sheets receive exact source readings. An inverse upper
shear pair has identity final matrix; at the positive unit sheet its first
period step has a pole. The same request succeeds at the negative sheet.
Continuation at the original input consumes the cached scalar reading.
-/

namespace TestPurelib.Curves.Legendre.RationalSquareAcquisition

open Purelib.Curves.Legendre.Acquisition
open Purelib.Approximation.Gaussian.Acquisition (Annotated Provenance)
open Purelib.Riemann.RootContinuation
open Purelib.Topology.Knot
open Purelib.Data.Gaussian.Basic (Canonical)

/-- Inspect both original sheets once, then request the inverse shear pair using their same saved exact readings. -/
private meta def checkWords : IO Unit := do
  let forward : Braid.Generator 3 := ⟨1, .positive⟩
  let backward := forward.reverse
  let word : Braid.Word 3 := [forward, backward]
  let mut values : List Canonical := []
  for sheet in ([0, 1] : List (Fin 2)) do
    let retained := SquareRootSidecar.isolated 1 sheet
    let original : Annotated := ⟨retained.1, some (Provenance.squareRoot retained.2)⟩
    let first := Words.acquire (Words.State.start original) [] 1 (by decide +kernel)
    match first.2 with
    | .exact result =>
        values := result.source.value :: values
        unless first.1.next.cachedRational.isSome do
          throw (IO.userError "rational-square acquisition did not cache its exact original reading")
        unless first.1.next.state.retained.nextIndex = 0 do
          throw (IO.userError "exact root classification changed the original acquisition request index")
        let resumed := first.resume word 1 (by decide +kernel)
        match resumed.2 with
        | .exact continued =>
            unless continued.source.value = result.source.value do
              throw (IO.userError "resume did not consume the same cached original rational reading")
            if result.source.value = 1 then
              unless continued.execution.firstUndefined = some 0 ∧ continued.execution.prefix.length = 0 do
                throw (IO.userError "final-matrix identity hid the rational-square root's first original pole")
            else
              unless continued.execution.firstUndefined = none ∧ continued.execution.reading.value = -1 do
                throw (IO.userError "the defined inverse word failed at the negative original unit sheet")
        | _ => throw (IO.userError "cached rational-square resume left the exact ordered domain route")
    | _ => throw (IO.userError "a rational-square root fell through to numerical word acquisition")
  unless values = [1, -1] ∨ values = [-1, 1] do
    throw (IO.userError "exact word acquisition did not retain both original rational root sheets")

#eval checkWords

end TestPurelib.Curves.Legendre.RationalSquareAcquisition
