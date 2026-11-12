module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Legendre.Paths
public import Purelib.Curves.Legendre.Periods.Fibre
public import Purelib.Curves.Legendre.Periods.Jets.Specification
public import Purelib.Curves.Legendre.Periods.Jets.Source.Attachment
import Purelib.Geometry.Path.Gaussian.Lifted.Refinement
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Coherent

/-!
# Differential channels on one retained Legendre cycle

The channel index selects `dx/y` or `x dx/y`, independently of the cycle
index in a period matrix. All six value and symbolic derivative programs
retain one common lifted cycle. Separate instances on the A and B cycles
therefore give the two columns of the differential-by-cycle period matrix.
The original source attachment derives fixed-parameter differential relations.
These algebraic programs and that attachment alone do not assert a parameter-variation law.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Basic

open Purelib
open Purelib.Approximation.Gaussian.Name
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Periods
open Purelib.Geometry.Path.Gaussian.Lifted

set_option genInjectivity false in
/-- Both differential channels and their symbolic derivatives are certified on one shared lifted cycle.

The differential index selects the numerator, never a different cycle. The
retained programs certify algebraic integrands; actual parameter-variation
estimates must additionally account for transport of this cycle. -/
structure SynchronizedPeriodJet {parameter :
  Data.Gaussian.Basic.Canonical}
    (frame : Paths.Frame parameter) where
  /-- The original lifted cycle shared by every differential and derivative channel. -/ cycle :
    Refinement.LiftedCycleRefinement 2
  /-- The certified value integral for each differential on the retained common cycle. -/ value : forall coordinate,
    Jets.CertifiedPeriodProgram
      (Fibre.frameCurve frame)
      (Specification.valueSpecification parameter coordinate) cycle
  /-- The certified first symbolic derivative integral on the retained common cycle. -/ first : forall
    coordinate,
    Jets.CertifiedPeriodProgram
      (Fibre.frameCurve frame)
      (Specification.firstDerivativeSpecification parameter coordinate) cycle
  /-- The certified second symbolic derivative integral on the retained common cycle. -/ second : forall
    coordinate,
    Jets.CertifiedPeriodProgram
      (Fibre.frameCurve frame)
      (Specification.secondDerivativeSpecification parameter coordinate) cycle
  /-- The original fixed-parameter cell-source attachment shared by these same six retained programs. -/
  source : Source.Attachment frame cycle value first second

constructive_injectivity SynchronizedPeriodJet

namespace SynchronizedPeriodJet

/-- Retain six original certified programs with their identical fixed-parameter cell-source attachment.

The attachment preserves the original chart owners and literal cell lists.
It certifies fixed-parameter differential relations; parameter-variation
realization remains a separate certificate on these retained channels.
-/
@[expose] def ofSource {parameter : Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    (cycle : Refinement.LiftedCycleRefinement 2)
    (value : ∀ coordinate, Jets.CertifiedPeriodProgram (Fibre.frameCurve frame)
      (Specification.valueSpecification parameter coordinate) cycle)
    (first : ∀ coordinate, Jets.CertifiedPeriodProgram (Fibre.frameCurve frame)
      (Specification.firstDerivativeSpecification parameter coordinate) cycle)
    (second : ∀ coordinate, Jets.CertifiedPeriodProgram (Fibre.frameCurve frame)
      (Specification.secondDerivativeSpecification parameter coordinate) cycle)
    (source : Source.Attachment frame cycle value first second) : SynchronizedPeriodJet frame :=
  ⟨cycle, value, first, second, source⟩

/-- Read the retained value-period program output at the original coordinate. -/
@[expose] def valueName {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : SynchronizedPeriodJet frame) (coordinate : Fin 2) : Coherent.CoherentNamed
      :=
  (jet.value coordinate).output

/-- Read the retained first-derivative period program output at the original coordinate. -/
@[expose] def firstName {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : SynchronizedPeriodJet frame) (coordinate : Fin 2) : Coherent.CoherentNamed
      :=
  (jet.first coordinate).output

/-- Read the retained second-derivative period program output at the original coordinate. -/
@[expose] def secondName {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : SynchronizedPeriodJet frame) (coordinate : Fin 2) : Coherent.CoherentNamed
      :=
  (jet.second coordinate).output
end SynchronizedPeriodJet

end Purelib.Curves.Legendre.Periods.Jets.Basic
