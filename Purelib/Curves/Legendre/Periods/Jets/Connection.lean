module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Arithmetic.Add
import Purelib.Approximation.Gaussian.Arithmetic.Mul
import Purelib.Approximation.Gaussian.Coherent.Additive
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Vector.Operational.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Schedule.Common
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Jets.Basic
public import Purelib.Curves.Legendre.Periods.Jets.Subdivision
import Purelib.Curves.Legendre.PicardFuchs.Clearance
public import Purelib.Curves.Legendre.PicardFuchs.Connection
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Integration.Program.Gaussian.Name
public import Purelib.Integration.Path.Primitive
public import Purelib.Integration.Program.Comparison.Budget
public import Purelib.Integration.Program.Comparison.Scheduled
import Init.Prelude
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Arithmetic

open Purelib.Approximation.Gaussian.Coherent

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Approximation.Gaussian.Vector

open Purelib.Approximation.Rational

open Purelib.Approximation.Schedule

open Purelib.Curves.Legendre

open Purelib.Curves.Legendre.Periods

open Purelib.Curves.Legendre.Periods.Jets

open Purelib.Curves.Legendre.PicardFuchs

open Purelib.Curves.Legendre.PicardFuchs.Clearance

open Purelib.Integration

open Purelib.Integration.Path

open Purelib.Integration.Path.Primitive

open Purelib.Integration.Program.Comparison

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

namespace Purelib.Curves.Legendre.Periods.Jets.Connection

/-- The canonical symbolic reduction selected by a row of the genus-one period vector. -/
def connectionReduction (parameter :
  Data.Gaussian.Basic.Canonical) (coordinate : Fin 2) :
    Connection.ConnectionReduction parameter :=
  if coordinate = 0 then Connection.firstConnectionReduction parameter
  else Connection.secondConnectionReduction parameter

/-- The zero coordinate uses the first original symbolic connection reduction. -/
@[simp] theorem connectionReduction_zero (parameter :
  Data.Gaussian.Basic.Canonical) :
    Curves.Legendre.Periods.Jets.Connection.connectionReduction parameter 0 = Connection.firstConnectionReduction
      parameter :=
  rfl

/-- The one coordinate uses the second original symbolic connection reduction. -/
@[simp] theorem connectionReduction_one (parameter :
  Data.Gaussian.Basic.Canonical) :
    Purelib.Curves.Legendre.Periods.Jets.Connection.connectionReduction parameter 1 =
      Connection.secondConnectionReduction parameter := by
  unfold Curves.Legendre.Periods.Jets.Connection.connectionReduction
  rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]

/-- The left side `2 lambda (1-lambda) u'` of one connection row. -/
def connectionScaledFirst {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : Jets.Basic.SynchronizedPeriodJet frame) (coordinate : Fin 2) : Coherent.CoherentNamed :=
  Mul.scaleName (ParameterClearance.connectionDenominator parameter)
    (jet.firstName coordinate)

/-- The fraction-free connection matrix numerator `[[lambda,-1],[lambda,-lambda]]` acting on the two value channels. -/
def connectionAction {parameter : Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : Jets.Basic.SynchronizedPeriodJet frame) (coordinate : Fin 2) : Coherent.CoherentNamed :=
  if coordinate = 0 then
    Additive.subtractName (Mul.scaleName parameter (jet.valueName 0)) (jet.valueName 1)
  else
    Additive.subtractName (Mul.scaleName parameter (jet.valueName 0))
      (Mul.scaleName parameter (jet.valueName 1))

/-- The first connection row is the original parameter-scaled first value minus the second value. -/
@[simp] theorem connectionAction_zero {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : Jets.Basic.SynchronizedPeriodJet frame) :
    Curves.Legendre.Periods.Jets.Connection.connectionAction jet 0 =
      Additive.subtractName (Mul.scaleName parameter (jet.valueName 0))
        (jet.valueName 1) := rfl

/-- The second connection row subtracts the parameter-scaled second value from the parameter-scaled first value. -/
@[simp] theorem connectionAction_one {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : Jets.Basic.SynchronizedPeriodJet frame) :
    Purelib.Curves.Legendre.Periods.Jets.Connection.connectionAction jet 1 =
      Additive.subtractName (Mul.scaleName parameter (jet.valueName 0))
        (Mul.scaleName parameter (jet.valueName 1)) := by
  unfold Curves.Legendre.Periods.Jets.Connection.connectionAction
  rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]

/-- Add the retained coordinate primitive-boundary integral to the original connection action. -/
def connectionWithPrimitive {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : Jets.Basic.SynchronizedPeriodJet frame)
    (primitive : Fin 2 -> ClosedPrimitiveBoundary)
    (coordinate : Fin 2) : Coherent.CoherentNamed :=
  CoherentNamed.add (Curves.Legendre.Periods.Jets.Connection.connectionAction jet coordinate)
    (primitive coordinate).integralSum

set_option genInjectivity false in
/-- Complete finite evidence for both rows of the fraction-free connection. The canonical polynomial reductions are
fixed by `connectionReduction`; this certificate supplies their closed primitive realizations and one common finite
schedule/error allocation for comparing the actual period programs. -/
structure ConnectionCertificate {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : Jets.Basic.SynchronizedPeriodJet frame) where
  /-- The retained explicit clearance of the original Legendre parameter from zero and one. -/ clearance :
    Clearance.ParameterClearance parameter
  /-- The retained closed primitive boundary for each original connection coordinate. -/ primitive : Fin 2 ->
    ClosedPrimitiveBoundary
  /-- The retained common subdivision links all original value and derivative quadrature cells. -/ subdivision :
    Subdivision.JetCommonSubdivision jet
  /-- The retained common finite schedule for the original target and comparison programs. -/ schedule :
    Common.CommonSchedule
  /-- The retained complete finite error allocation for the original connection comparison. -/ budget :
    Budget.JetErrorBudget
  /-- The original scaled-derivative and action-plus-primitive samples satisfy the retained scheduled geometric error
    bound. -/ connection_samples_close : forall coordinate request,
    Data.Gaussian.Norm.Basic.normSq
        (((Program.Gaussian.Basic.RefinementProgram.ofCoherentNamed
          (Curves.Legendre.Periods.Jets.Connection.connectionScaledFirst jet
          coordinate)).model
            (schedule.targetIndex request)).integralSample -
          ((Program.Gaussian.Basic.RefinementProgram.ofCoherentNamed
            (Curves.Legendre.Periods.Jets.Connection.connectionWithPrimitive jet primitive coordinate)).model
              (schedule.comparisonIndex request)).integralSample) <=
      Geometric.Basic.quarterRadius budget.total request

constructive_injectivity ConnectionCertificate

namespace ConnectionCertificate

/-- The scheduled finite comparison realizes the canonical algebraic connection row together with its exact
differential. -/
def coordinate_with_primitive {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    {jet : Jets.Basic.SynchronizedPeriodJet frame}
    (certificate : Curves.Legendre.Periods.Jets.Connection.ConnectionCertificate jet) (coordinate : Fin 2) :
    Gaussian.Equivalence.NamedEquivalent (Curves.Legendre.Periods.Jets.Connection.connectionScaledFirst jet
      coordinate).name
      (Curves.Legendre.Periods.Jets.Connection.connectionWithPrimitive jet certificate.primitive coordinate).name :=
  Scheduled.namedEquivalent_of_scheduled_samples _ _ certificate.schedule
    certificate.budget.total certificate.budget.total_nonnegative
    (certificate.connection_samples_close coordinate)

/-- The original closed primitive-boundary contribution is operationally zero and can be removed from the retained
connection action. -/
public def action_primitive_to_action
  {parameter : Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    {jet : Jets.Basic.SynchronizedPeriodJet frame}
    (certificate : Curves.Legendre.Periods.Jets.Connection.ConnectionCertificate jet) (coordinate : Fin 2) :
    Gaussian.Equivalence.NamedEquivalent
      (Curves.Legendre.Periods.Jets.Connection.connectionWithPrimitive jet certificate.primitive coordinate).name
      (Curves.Legendre.Periods.Jets.Connection.connectionAction jet coordinate).name := by
  let action := Curves.Legendre.Periods.Jets.Connection.connectionAction jet coordinate
  let primitive := (certificate.primitive coordinate).integralSum
  let zero := Coherence.exact 0
  have discardPrimitive : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add action primitive).name
      (CoherentNamed.add action zero).name :=
    Congruence.coherentAdd_respects action action
      primitive zero
      (NamedEquivalent.refl action.name)
      (Primitive.exactDifferential_closed_operational_zero
        (certificate.primitive coordinate))
  exact NamedEquivalent.trans discardPrimitive
    (Add.coherentAdd_zero_right action)

/-- One row of the finite fraction-free Gauss--Manin connection, `2 lambda (1-lambda) U' =
[[lambda,-1],[lambda,-lambda]] U`. -/
def coordinate_connection {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    {jet : Jets.Basic.SynchronizedPeriodJet frame}
    (certificate : Curves.Legendre.Periods.Jets.Connection.ConnectionCertificate jet) (coordinate : Fin 2) :
    Gaussian.Equivalence.NamedEquivalent (Curves.Legendre.Periods.Jets.Connection.connectionScaledFirst jet
      coordinate).name
      (Curves.Legendre.Periods.Jets.Connection.connectionAction jet coordinate).name :=
  NamedEquivalent.trans
    (certificate.coordinate_with_primitive coordinate)
    (certificate.action_primitive_to_action coordinate)

/-- Vector form of the finite fraction-free Gauss--Manin connection. -/
def connection {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    {jet : Jets.Basic.SynchronizedPeriodJet frame}
    (certificate : Curves.Legendre.Periods.Jets.Connection.ConnectionCertificate jet) :
    Operational.Basic.VectorEquivalent
      (fun coordinate => Curves.Legendre.Periods.Jets.Connection.connectionScaledFirst jet coordinate)
      (fun coordinate => Curves.Legendre.Periods.Jets.Connection.connectionAction jet coordinate) :=
  certificate.coordinate_connection

end ConnectionCertificate

end Purelib.Curves.Legendre.Periods.Jets.Connection

end
