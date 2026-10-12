module
meta import Purelib.Elab.ConstructiveInjectivity

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.RootIsolation.Progressive.Chamber.Basic
import Purelib.RootIsolation.Progressive.Chamber.State
public import Purelib.RootIsolation.Progressive.Chamber.State.Refinement
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Progressive.Chamber.History
open Purelib.Data.Gaussian

set_option genInjectivity false in
/-- A finite request history is the small-universe operational state exposed
to the generic CCL process.  Replaying it deterministically reconstructs the
proof-rich chamber state; the coefficient channels themselves remain fixed
parameters rather than data stored inside the process state. -/
inductive ChamberRequestHistory : Type
  /-- The initial chamber request, before any positive-width refinement. -/ | initial
  /-- Append a positive-width request to the exact preceding chamber history. -/ | refine (previous :
    ChamberRequestHistory) (epsilon : Fraction.Rational)
      (positive : 0 < epsilon)

constructive_injectivity ChamberRequestHistory

end Purelib.RootIsolation.Progressive.Chamber.History

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Progressive.Chamber.Basic.SimpleRootChamber
open Purelib.Data.Gaussian

/-- Deterministically replay a finite request history through the certified
controller. -/
def run
    {reference : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} (chamber :
      Progressive.Chamber.Basic.SimpleRootChamber reference) :
    Progressive.Chamber.History.ChamberRequestHistory → Progressive.Chamber.State.ChamberContinuationState chamber
  | .initial => Progressive.Chamber.State.ChamberContinuationState.initial chamber
  | .refine previous epsilon positive =>
      (chamber.run previous).next epsilon positive

end Purelib.RootIsolation.Progressive.Chamber.Basic.SimpleRootChamber

end
