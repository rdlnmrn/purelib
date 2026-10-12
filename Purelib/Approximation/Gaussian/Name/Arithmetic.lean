module
public import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Basic
public import Purelib.Approximation.Gaussian.Process.Addition
public import Purelib.Approximation.Gaussian.Process.Division
public import Purelib.Approximation.Gaussian.Process.Multiplication

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Approximation.Gaussian.Process.Basic

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Approximation.Gaussian

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

namespace Purelib.Approximation.Gaussian.Name.Basic
namespace Named

/-- Add two Gaussian names, retaining the pair of their original process states. -/
def add (left right : Gaussian.Name.Basic.Named) :
  Gaussian.Name.Basic.Named :=
  { process := Approximation.Gaussian.Process.add
      left.process right.process
    state := (left.state, right.state) }

/-- Negate a Gaussian name while retaining its original process state. -/
def neg (name : Gaussian.Name.Basic.Named) :
  Gaussian.Name.Basic.Named :=
  { process := Approximation.Gaussian.Process.neg name.process
    state := name.state }

/-- Subtract two Gaussian names, retaining the pair of their original process states. -/
def sub (left right : Gaussian.Name.Basic.Named) :
  Gaussian.Name.Basic.Named :=
  { process := Approximation.Gaussian.Process.sub
      left.process right.process
    state := (left.state, right.state) }

/-- Multiply two Gaussian names, retaining the pair of their original process states. -/
def mul (left right : Gaussian.Name.Basic.Named) :
  Gaussian.Name.Basic.Named :=
  { process := Approximation.Gaussian.Process.mul
      left.process right.process
    state := (left.state, right.state) }

/-- Divide two Gaussian names using the denominator's retained whole-ball apartness certificate and the original pair of
states. -/
def div (left right : Gaussian.Name.Basic.Named) (apart :
  Named.Apart right) : Gaussian.Name.Basic.Named :=
  { process := Approximation.Gaussian.Process.div
      left.process right.process apart.certificate
    state := (left.state, right.state) }
end Named

end Purelib.Approximation.Gaussian.Name.Basic

end
