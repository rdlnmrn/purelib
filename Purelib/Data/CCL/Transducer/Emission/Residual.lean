module
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Apart
import Purelib.Approximation.Gaussian.Enclosure.Ball.Bounds
public import Purelib.Approximation.Gaussian.Process.Bounds
public import Purelib.Approximation.Gaussian.Process.Gamma.Inverse.Scale
public import Purelib.Data.CCL.Encoding.Padding.Process
public import Purelib.Data.CCL.Transducer.Emission.Loop
import Purelib.Data.CCL.Transducer.Mode.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.CCL.Transducer.Emission.Basic
import Purelib.Data.List.Basic
import Purelib.Approximation.Gaussian.Enclosure.Residual
import Purelib.Data.CCL.Encoding.Padding.Residual
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Order.Basic

section
@[expose] public section

/-!
# Productive progressive CCL output transducer

This is the finite-prefix controller for the redundant arithmetic layer.  A
loop mode represents a normalized progressive tail.  A residual mode is used
after a sector has been emitted but before equality with its representative
can be decided.  It either emits finite unary padding or, once apartness is
visible, changes to the exact normalized inverse chart.

The canonical terminating rational encoder is not changed.  This controller
only produces the progressive, potentially non-returning arithmetic word.
-/

namespace Purelib.Data.CCL.Transducer.Emission.Residual

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Gaussian in
/-- Turn an apart residual refinement into the exact normalized-inverse loop state at the retained count.

Use the same padding-refined state and apart certificate as the inverse process base. Transfer the retained upper bound
to that state and keep its original count and strict padding comparison in the loop-domain construction. -/
def residualApartLoopState (current : Mode.Basic.ResidualState)
    (certificate : Approximation.Gaussian.Enclosure.Ball.Apart
      (current.process.ball
        (Padding.Process.residualState
          current.process current.state (current.count + 1)))) : Mode.Basic.LoopState :=
  let refined := Padding.Process.residualState
    current.process current.state (current.count + 1)
  have upperBoundAtRefined : ∀ {value : Basic.Canonical},
      current.process.Possible refined value →
        Data.Gaussian.Norm.Basic.normSq value ≤ current.upper := by
    intro value possible
    exact current.upperBound
      (current.process.refine_persists current.state _ _ possible)
  { kind := .loop
    count := current.count
    process := Process.Gamma.Inverse.Scale.normalizedInverseProcess current.process refined
      certificate current.count
    state := Process.Gamma.Inverse.Scale.normalizedInverseInitial current.process refined
      certificate current.count
    domain := Process.Gamma.Inverse.Scale.normalizedInverseLoopDomain current.process refined
      certificate current.count current.upper upperBoundAtRefined
        current.upperStrict }

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Transducer in
/-- Refine the residual at the successor requested count and emit the chunk selected by its exact small-or-apart
decision.

A small decision emits a true padding bit and retains that refined state with its certified small upper bound. An apart
decision invokes the loop step on the normalized inverse of the same retained residual refinement. -/
def residualStep (current : Mode.Basic.ResidualState) :
  Data.CCL.Transducer.Emission := by
  let requestedCount := current.count + 1
  let refined := Padding.Process.residualState
    current.process current.state requestedCount
  match decision : Padding.Process.decideResidual
      current.process current.state requestedCount with
  | .small certificate =>
      exact
        { bits := [true]
          nonempty := by decide
          next := .residual
            { process := current.process
              state := refined
              count := requestedCount
              upper := Enclosure.Ball.Bounds.smallUpper (current.process.ball refined)
              upperBound := fun possible =>
                Process.Bounds.smallUpper_bound certificate possible
              upperStrict := certificate } }
  | .apart certificate =>
      exact Emission.Loop.loopStep (residualApartLoopState current certificate)

end Purelib.Data.CCL.Transducer.Emission.Residual

end
