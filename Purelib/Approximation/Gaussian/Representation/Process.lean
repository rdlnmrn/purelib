module
import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Representation.Basic

public import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Order
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian

section
@[expose] public section

/-!
# Finite enclosure representations and direct translations

This module instantiates the generic protocol for rational balls, rational
boxes, boxed raw CCL prefixes, finite fast-Cauchy indices, and states of an
arbitrary progressive enclosure process.
-/

namespace Purelib.Approximation.Gaussian.Representation.Process
open Purelib.Data.Gaussian.Basic.Canonical

namespace Ball
end Ball

/-- States of a progressive process ordered by direct candidate-predicate inclusion. This deliberately avoids inventing
a global reachability relation between heterogeneous state types. -/
def processRepresentation (process :
  Approximation.Gaussian.Process) : Approximation.Gaussian.Representation where
  Observation := process.State
  Possible state value := process.Possible state value
  witness state := (process.witness state).val
  witness_possible state := (process.witness state).property
  Refines inner outer := ∀ {value : Data.Gaussian.Basic.Canonical},
    process.Possible inner value → process.Possible outer value
  refines_refl := by
    intro state value possible
    exact possible
  refines_trans := by
    intro inner middle outer innerMiddle middleOuter value possible
    exact middleOuter (innerMiddle possible)
  possible_persists refines possible := refines possible
  precisionSq state := (process.ball state).radiusSq
  precisionSq_nonneg state := (process.ball state).radiusSq_nonneg
  boundary := .closed
end Purelib.Approximation.Gaussian.Representation.Process

end
