module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Integration.Program.Gaussian.Presentation
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic
public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path
import Purelib.Geometry.Path.Gaussian.Lifted.Refinement
public import Purelib.Integration.Path.Lifted.Program
import Init.Prelude
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Closed
import Purelib.Integration.Path.Lifted.Model
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Integration.Program.Gaussian.Name

section

open Purelib

open Purelib.Approximation.Gaussian.Name

open Purelib.Curves

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Differentials

open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path

open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path.Basis

open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path.Jets

open Purelib.Data.Rat

open Purelib.Geometry.Path.Gaussian.Lifted

open Purelib.Integration.Path.Lifted

open Purelib.Integration.Program.Gaussian

open Purelib.Integration.Program.Gaussian.Basic

section
@[expose] public section

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

namespace Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period.Basis

set_option genInjectivity false in
/-- A persistent period program whose every finite integrand observation is uniformly certified to be the requested
algebraic differential on the chosen sheet. -/
structure CertifiedPeriodProgram {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (differential : Differentials.Basic.Differential genus)
    (cycle : Refinement.LiftedCycleRefinement 2) where
  /-- The original finite integral program retained by this algebraically certified period. -/ integral :
    RefinementProgram
  /-- At every refinement, the exact original integral cells uniformly certify the corresponding lifted-cycle
    realization. -/ certificates : forall index,
    Basis.UniformPathCertificates curve differential (integral.model index).cells
      (cycle.liftedPath index).path

constructive_injectivity CertifiedPeriodProgram

namespace CertifiedPeriodProgram

/-- Cache a proved dominating rational error scale without changing any finite cycle model or uniform differential
certificate. -/
def withLargerErrorScale {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus} {cycle : Refinement.LiftedCycleRefinement 2}
    (program : Curves.Hyperelliptic.Integration.Algebraic.Period.Basis.CertifiedPeriodProgram curve differential cycle)
    (scale : Fraction.Rational)
    (scaleNonnegative : 0 <= scale)
    (dominates : program.integral.errorScale <= scale) :
    Curves.Hyperelliptic.Integration.Algebraic.Period.Basis.CertifiedPeriodProgram curve differential cycle where
  integral := (RefinementProgram.withLargerErrorScale program.integral) scale scaleNonnegative
    dominates
  certificates := program.certificates

/-- Forget algebraic certification while retaining the exact original finite integral process and lifted cycle. -/
def toPeriodProgram {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus} {cycle : Refinement.LiftedCycleRefinement 2}
    (program : Curves.Hyperelliptic.Integration.Algebraic.Period.Basis.CertifiedPeriodProgram curve differential cycle)
      :
    Program.PeriodProgram cycle where
  integral := program.integral
  follows := fun index => UniformPathCertificates.toFollowedBy
    (program.certificates index)

/-- Read the original coherent output name of the retained certified period program. -/
def output {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus} {cycle : Refinement.LiftedCycleRefinement 2}
    (program : Curves.Hyperelliptic.Integration.Algebraic.Period.Basis.CertifiedPeriodProgram curve differential cycle)
      :
    Coherent.CoherentNamed :=
  program.toPeriodProgram.output

/-- Each refined cell list has exactly the cell count of its original lifted-cycle refinement. -/
theorem refinement_cellCount {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential : Differentials.Basic.Differential genus}
    {cycle : Refinement.LiftedCycleRefinement 2}
    (program : Curves.Hyperelliptic.Integration.Algebraic.Period.Basis.CertifiedPeriodProgram curve differential cycle)
    (index : Nat) :
    (program.integral.model index).cells.length =
      (cycle.liftedPath index).cellCount :=
  program.toPeriodProgram.refinement_cellCount index

end CertifiedPeriodProgram

end Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period.Basis

end

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

namespace Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period.Jets

set_option genInjectivity false in
/-- A persistent finite integral program uniformly realizing one displayed odd-power algebraic differential on one
displayed lifted cycle. -/
structure CertifiedPeriodProgram {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : OddPower.Basic.OddPowerDifferential)
    (cycle : Refinement.LiftedCycleRefinement 2) where
  /-- The original finite integral program retained by this algebraically certified period. -/ integral :
    RefinementProgram
  /-- At every refinement, the exact original integral cells uniformly certify the corresponding lifted-cycle
    realization. -/ certificates : forall index,
    Jets.UniformPathCertificates curve differential (integral.model index).cells
      (cycle.liftedPath index).path

constructive_injectivity CertifiedPeriodProgram

namespace CertifiedPeriodProgram

/-- Forget algebraic certification while retaining the exact original finite integral process and lifted cycle. -/
def toPeriodProgram {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : OddPower.Basic.OddPowerDifferential}
    {cycle : Refinement.LiftedCycleRefinement 2}
    (program : Curves.Hyperelliptic.Integration.Algebraic.Period.Jets.CertifiedPeriodProgram curve differential cycle) :
    Program.PeriodProgram cycle where
  integral := program.integral
  follows := fun index => UniformPathCertificates.toFollowedBy
    (program.certificates index)

/-- Read the original coherent output name of the retained certified period program. -/
def output {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : OddPower.Basic.OddPowerDifferential}
    {cycle : Refinement.LiftedCycleRefinement 2}
    (program : Curves.Hyperelliptic.Integration.Algebraic.Period.Jets.CertifiedPeriodProgram curve differential cycle) :
    Coherent.CoherentNamed := program.integral.output

end CertifiedPeriodProgram

end Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period.Jets

end

end
