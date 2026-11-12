module

import Purelib.Curves.Legendre.Acquisition.Words
import Purelib.Approximation.Gaussian.Acquisition.Expression.Compile
import Purelib.Riemann.RootContinuation.SquareRootSidecar
meta import Purelib.Curves.Legendre.Acquisition.Words
meta import Purelib.Approximation.Gaussian.Acquisition.Expression.Compile
meta import Purelib.Riemann.RootContinuation.SquareRootSidecar
meta import Purelib.Topology.Knot.Braid.Basic

/-!
# Composite expression evidence reaches cached word acquisition

The original real quadratic input is a polynomial of a retained `1+r`
channel. Inferred coordinates prepare its finite words without imaginary
separation or supplied denominator certificates. The later request reuses
that same retained all-row provider and source state.
-/

namespace TestPurelib.Curves.Legendre.CompositeAcquisition

open Purelib.Curves.Legendre.Acquisition
open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Acquisition.Expression.Basic
open Purelib.Riemann.RootContinuation
open Purelib.Topology.Knot

/-- Composite source coordinates select word preparation and retain its provider for the next request. -/
private meta def checkWords : IO Unit := do
  let word : Braid.Word 3 := [⟨0, .positive⟩]
  for sheet in ([0, 1] : List (Fin 2)) do
    let root := SquareRootSidecar.isolated 2 sheet
    let rootEnvironment : Fin 1 → Annotated := fun _ => ⟨root.1, some (.squareRoot root.2)⟩
    let composite := (Expr.add (.rational 1) (.atom 0)).compile rootEnvironment
    let environment : Fin 1 → Annotated := fun _ => composite
    let input := (Expr.mul (.atom 0) (.add (.atom 0) (.rational 1))).compile environment
    let first := Words.acquire (Words.State.start input) [] 1 (by decide +kernel)
    match first.2 with
    | .ready _ =>
        unless first.1.next.provider.isSome do
          throw (IO.userError "inferred composite coordinates did not retain their word provider")
        unless first.1.next.state.retained.nextIndex = 0 do
          throw (IO.userError "coordinate word preparation changed the original request index")
        let resumed := first.resume word 1 (by decide +kernel)
        match resumed.2 with
        | .ready _ =>
            unless resumed.1.route = .cached do
              throw (IO.userError "composite word resume did not select its same cached provider")
            unless resumed.1.next.state.retained.nextIndex = first.1.next.state.retained.nextIndex do
              throw (IO.userError "cached word preparation changed the retained source state index")
        | _ => throw (IO.userError "an admitted real composite input failed its finite word request")
    | _ => throw (IO.userError "inferred composite coordinates fell through to numerical word acquisition")

#eval checkWords

end TestPurelib.Curves.Legendre.CompositeAcquisition
