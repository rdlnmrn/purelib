module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Arithmetic.Mul
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Schedule.Common
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Jets.Basic
public import Purelib.Curves.Legendre.Periods.Jets.Subdivision
public import Purelib.Curves.Legendre.PicardFuchs.Clearance
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Integration.Program.Gaussian.Name
public import Purelib.Integration.Path.Primitive
public import Purelib.Integration.Program.Comparison.Budget
public import Purelib.Integration.Program.Comparison.Scheduled
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Arithmetic

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Approximation.Rational

open Purelib.Approximation.Schedule

open Purelib.Curves.Legendre

open Purelib.Curves.Legendre.Periods

open Purelib.Curves.Legendre.Periods.Jets

open Purelib.Curves.Legendre.PicardFuchs

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

namespace Purelib.Curves.Legendre.Periods.Jets.PicardFuchs

/-! ## Fraction-free Picard--Fuchs residual -/

/-- The retained second-derivative value channel scaled by four times the original parameter times one minus that
parameter. -/
def picardFuchsSecondTerm {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : Jets.Basic.SynchronizedPeriodJet frame) : Coherent.CoherentNamed :=
  Mul.scaleName (4 * parameter * (1 - parameter)) (jet.secondName 0)

/-- The retained first-derivative value channel scaled by four times one minus twice the original parameter. -/
def picardFuchsFirstTerm {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : Jets.Basic.SynchronizedPeriodJet frame) : Coherent.CoherentNamed :=
  Mul.scaleName (4 * (1 - 2 * parameter)) (jet.firstName 0)

/-- The actual coherent arithmetic expression `4 lambda (1-lambda) u'' + 4(1-2 lambda) u' - u`. -/
def picardFuchsResidual {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : Jets.Basic.SynchronizedPeriodJet frame) : Coherent.CoherentNamed :=
  CoherentNamed.add
    (CoherentNamed.add
      (picardFuchsSecondTerm jet)
        (picardFuchsFirstTerm jet))
    (CoherentNamed.neg (jet.valueName 0))

set_option genInjectivity false in
/-- Finite analytic evidence which realizes the fixed symbolic `picardFuchsReduction` on the synchronized period jet. -/
structure PicardFuchsCertificate {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : Jets.Basic.SynchronizedPeriodJet frame) where
  /-- The retained explicit clearance of the original Legendre parameter from zero and one. -/ clearance :
    Clearance.ParameterClearance parameter
  /-- The original closed primitive boundary realizing the retained differential reduction. -/ primitive :
    ClosedPrimitiveBoundary
  /-- The retained common subdivision of the original value and derivative quadrature cells. -/ subdivision :
    Subdivision.JetCommonSubdivision jet
  /-- The retained common schedule for the original residual and primitive comparison programs. -/ schedule :
    Common.CommonSchedule
  /-- The retained complete finite error allocation for the residual comparison. -/ budget : Budget.JetErrorBudget
  /-- The original residual and primitive-boundary samples satisfy the retained scheduled geometric error bound. -/
    residual_samples_close : forall request,
    Data.Gaussian.Norm.Basic.normSq
        (((Program.Gaussian.Basic.RefinementProgram.ofCoherentNamed
          (picardFuchsResidual jet)).model
            (schedule.targetIndex request)).integralSample -
          ((Program.Gaussian.Basic.RefinementProgram.ofCoherentNamed primitive.integralSum).model
            (schedule.comparisonIndex request)).integralSample) <=
      Geometric.Basic.quarterRadius budget.total request

constructive_injectivity Purelib.Curves.Legendre.Periods.Jets.PicardFuchs.PicardFuchsCertificate

namespace PicardFuchsCertificate

/-- The finite comparison identifies the actual residual with the exact primitive dictated by the polynomial reduction.
-/
def residual_equivalent_primitive
  {parameter : Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    {jet : Jets.Basic.SynchronizedPeriodJet frame}
    (certificate : Curves.Legendre.Periods.Jets.PicardFuchs.PicardFuchsCertificate jet) :
    Gaussian.Equivalence.NamedEquivalent (Curves.Legendre.Periods.Jets.PicardFuchs.picardFuchsResidual jet).name
      certificate.primitive.integralSum.name :=
  Scheduled.namedEquivalent_of_scheduled_samples _ _ certificate.schedule
    certificate.budget.total certificate.budget.total_nonnegative
    certificate.residual_samples_close

/-- Finite operational Legendre Picard--Fuchs equation. Its six channels use one displayed lifted cycle, and the
certificate exposes the common schedule and complete finite error allocation used to make the residual vanish. -/
def operational_zero {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    {jet : Jets.Basic.SynchronizedPeriodJet frame}
    (certificate : Curves.Legendre.Periods.Jets.PicardFuchs.PicardFuchsCertificate jet) :
    Gaussian.Equivalence.NamedEquivalent (Curves.Legendre.Periods.Jets.PicardFuchs.picardFuchsResidual jet).name
      (Coherence.exact 0).name :=
  NamedEquivalent.trans
    certificate.residual_equivalent_primitive
    (Primitive.exactDifferential_closed_operational_zero
      certificate.primitive)

end PicardFuchsCertificate

end Purelib.Curves.Legendre.Periods.Jets.PicardFuchs

end
