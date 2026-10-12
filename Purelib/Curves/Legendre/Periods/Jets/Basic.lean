module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Legendre.Paths
public import Purelib.Curves.Legendre.Periods.Fibre
public import Purelib.Curves.Legendre.Periods.Jets.Specification
import Purelib.Geometry.Path.Gaussian.Lifted.Refinement
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Coherent

open Purelib

open Purelib.Approximation.Gaussian.Name

open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period

open Purelib.Curves.Legendre

open Purelib.Curves.Legendre.Periods

open Purelib.Curves.Legendre.Periods.Jets

open Purelib.Geometry.Path.Gaussian.Lifted

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

namespace Purelib.Curves.Legendre.Periods.Jets.Basic

/-! ## One common lifted-cycle period jet -/

set_option genInjectivity false in
/-- Value, first derivative, and second derivative are certified on literally the same displayed lifted cycle for each
of the two genus-one coordinates. -/
structure SynchronizedPeriodJet {parameter :
  Data.Gaussian.Basic.Canonical}
    (frame : Paths.Frame parameter) where
  /-- The original shared lifted cycle refinement for each of the two period coordinates. -/ cycle : Fin 2 ->
    Refinement.LiftedCycleRefinement 2
  /-- The certified value-period program on the original coordinate cycle. -/ value : forall coordinate,
    Jets.CertifiedPeriodProgram
      (Fibre.frameCurve frame)
      (Specification.valueSpecification coordinate) (cycle coordinate)
  /-- The certified first parameter-derivative program on that same original coordinate cycle. -/ first : forall
    coordinate,
    Jets.CertifiedPeriodProgram
      (Fibre.frameCurve frame)
      (Specification.firstDerivativeSpecification coordinate) (cycle coordinate)
  /-- The certified second parameter-derivative program on that same original coordinate cycle. -/ second : forall
    coordinate,
    Jets.CertifiedPeriodProgram
      (Fibre.frameCurve frame)
      (Specification.secondDerivativeSpecification coordinate) (cycle coordinate)

constructive_injectivity Purelib.Curves.Legendre.Periods.Jets.Basic.SynchronizedPeriodJet

namespace SynchronizedPeriodJet

/-- Read the retained value-period program output at the original coordinate. -/
def valueName {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : Curves.Legendre.Periods.Jets.Basic.SynchronizedPeriodJet frame) (coordinate : Fin 2) : Coherent.CoherentNamed
      :=
  (jet.value coordinate).output

/-- Read the retained first-derivative period program output at the original coordinate. -/
def firstName {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : Curves.Legendre.Periods.Jets.Basic.SynchronizedPeriodJet frame) (coordinate : Fin 2) : Coherent.CoherentNamed
      :=
  (jet.first coordinate).output

/-- Read the retained second-derivative period program output at the original coordinate. -/
def secondName {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : Curves.Legendre.Periods.Jets.Basic.SynchronizedPeriodJet frame) (coordinate : Fin 2) : Coherent.CoherentNamed
      :=
  (jet.second coordinate).output
end SynchronizedPeriodJet

end Purelib.Curves.Legendre.Periods.Jets.Basic

end
