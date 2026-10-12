module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Process.Basic
public import Purelib.Approximation.Gaussian.Process.Normalization.Basic
public import Purelib.Data.CCL.Encoding.Padding.Residual
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Elab.Deriving.Repr
meta import Purelib.Elab.ConstructiveInjectivity

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

namespace Purelib.Data.CCL.Transducer

namespace Mode.Basic

/-- Distinguish an initial-high normalization loop from a subsequent residual loop. -/
inductive RegularKind where
  /-- Continue the initial-high normalization branch. -/ | initialHigh
  /-- Retain the subsequent loop branch or its exact certified loop-state record. -/ | loop
deriving DecidableEq

derive_exposed_repr Purelib.Data.CCL.Transducer.Mode.Basic.RegularKind

end Mode.Basic
namespace Mode.Basic

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL in
set_option genInjectivity false in

/-- Retain a normalization loop's kind, count, Gaussian process, exact state and global loop-domain certificate.

The domain belongs to the same process and bounds every possible value at any of its states. The current state and
counter remain available for the next certified emission. -/
structure LoopState where
  /-- The retained initial-high or subsequent-loop branch. -/ kind : Transducer.Mode.Basic.RegularKind
  /-- The retained unary or residual-padding count. -/ count : Nat
  /-- The exact Gaussian approximation process owning this state. -/ process : Approximation.Gaussian.Process
  /-- The retained state of that same process. -/ state : process.State
  /-- The loop-domain certificate belonging to the exact retained process. -/ domain :
    Process.Normalization.Basic.LoopDomain process

constructive_injectivity LoopState

end Mode.Basic
namespace Mode.Basic.LoopState

end Mode.Basic.LoopState
namespace Mode.Basic

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
set_option genInjectivity false in

/-- Retain a Gaussian residual process state with a common squared-norm upper bound below its exact padding target.

The upper-bound proof covers every possible value of the stored state. The strict target comparison uses the same
retained upper bound and residual count. -/
structure ResidualState where
  /-- The exact Gaussian approximation process owning this state. -/ process : Approximation.Gaussian.Process
  /-- The retained state of that same process. -/ state : process.State
  /-- The retained unary or residual-padding count. -/ count : Nat
  /-- The retained rational squared-norm upper bound for this residual state. -/ upper : Fraction.Rational
  /-- Every value possible at this retained state satisfies its required squared-norm bound. -/ upperBound : ∀ {value :
    Basic.Canonical}, process.Possible state value →
    Gaussian.Norm.Basic.normSq value ≤ upper
  /-- The retained residual upper bound is strictly below the padding target at the same count. -/ upperStrict : upper <
    Padding.Residual.paddingTarget count

constructive_injectivity ResidualState

end Mode.Basic
namespace Mode.Basic.ResidualState

end Mode.Basic.ResidualState
namespace Mode.Basic

open Purelib.Approximation.Gaussian in
set_option genInjectivity false in

/-- Retain a Gaussian process and one of its exact states before initial normalization. -/
structure InitialState where
  /-- The exact Gaussian approximation process owning this state. -/ process : Approximation.Gaussian.Process
  /-- The retained state of that same process. -/ state : process.State

constructive_injectivity InitialState

end Mode.Basic
namespace Mode.Basic.InitialState

end Mode.Basic.InitialState
namespace Mode.Basic

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
set_option genInjectivity false in

/-- Retain a low-normalization count and exact Gaussian process state with squared norm strictly below 43/20.

The uniform bound belongs to every value possible at that retained state; both the original process owner and its
dependent state are preserved. -/
structure LowState where
  /-- The retained unary or residual-padding count. -/ count : Nat
  /-- The exact Gaussian approximation process owning this state. -/ process : Approximation.Gaussian.Process
  /-- The retained state of that same process. -/ state : process.State
  /-- Every value possible at this retained state satisfies its required squared-norm bound. -/ upperBound : ∀ {value :
    Basic.Canonical}, process.Possible state value →
    Gaussian.Norm.Basic.normSq value < 43 / 20

constructive_injectivity LowState

end Mode.Basic
namespace Mode.Basic.LowState

end Mode.Basic.LowState
open Purelib.Data.CCL in
set_option genInjectivity false in
/-- Retain exactly one initial, low, loop or residual transducer state with its corresponding process owner and
certificates.

Each constructor keeps the original dependent state record. Mode changes therefore carry the exact process, bounds and
counters required by that phase. -/
inductive Mode where
  /-- Retain the exact initial process-state record. -/ | initial (state : Transducer.Mode.Basic.InitialState)
  /-- Retain the exact low-normalization state and its bound. -/ | low (state : Transducer.Mode.Basic.LowState)
  /-- Retain the subsequent loop branch or its exact certified loop-state record. -/ | loop (state :
    Transducer.Mode.Basic.LoopState)
  /-- Retain the exact residual process state, upper bound and padding comparison. -/ | residual (state :
    Transducer.Mode.Basic.ResidualState)

constructive_injectivity Mode

namespace Mode.initial

end Mode.initial
namespace Mode.low

end Mode.low
namespace Mode.loop

end Mode.loop
namespace Mode.residual

end Mode.residual
end Purelib.Data.CCL.Transducer

end
