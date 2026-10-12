module
public import Purelib.Curves.Legendre.Periods.Jets.Channels
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Table.Basic
import Purelib.Approximation.Gaussian.Table.CCL.Request
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Jets.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Table.CCL

open Purelib.Curves.Legendre

open Purelib.Curves.Legendre.Periods

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
-/

namespace Purelib.Curves.Legendre.Periods.Jets.Basic.SynchronizedPeriodJet

/-- The finite channel table retaining the original synchronized jet's six productive outputs. -/
def table {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : Jets.Basic.SynchronizedPeriodJet frame) : Gaussian.Table.Basic.ChannelTable :=
  ⟨jet.channels⟩

/-- Every value channel answers one request shared by all six channels. -/
theorem value_joint_request {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : Jets.Basic.SynchronizedPeriodJet frame) (coordinate : Fin 2)
    (target : Fraction.Rational) (positive : 0 < target) (count : Nat) :
    Request.RequestContract jet.channels
      (jet.valueName coordinate) target positive count :=
  jet.table.member_bitstream_and_allowance
    (jet.valueName_mem_channels coordinate) target positive count

/-- Every first-derivative channel answers the same joint request. -/
theorem first_joint_request {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : Jets.Basic.SynchronizedPeriodJet frame) (coordinate : Fin 2)
    (target : Fraction.Rational) (positive : 0 < target) (count : Nat) :
    Request.RequestContract jet.channels
      (jet.firstName coordinate) target positive count :=
  jet.table.member_bitstream_and_allowance
    (jet.firstName_mem_channels coordinate) target positive count

/-- Every second-derivative channel answers the same joint request. -/
theorem second_joint_request {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : Jets.Basic.SynchronizedPeriodJet frame) (coordinate : Fin 2)
    (target : Fraction.Rational) (positive : 0 < target) (count : Nat) :
    Request.RequestContract jet.channels
      (jet.secondName coordinate) target positive count :=
  jet.table.member_bitstream_and_allowance
    (jet.secondName_mem_channels coordinate) target positive count

end Purelib.Curves.Legendre.Periods.Jets.Basic.SynchronizedPeriodJet

end
