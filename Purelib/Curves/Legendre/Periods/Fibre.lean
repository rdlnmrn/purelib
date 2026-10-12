module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Approximation.Gaussian.Vector.Operational.Basic
import Purelib.Integration.Program.Gaussian.Name
import Purelib.Integration.Program.Gaussian.Basic
public import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
public import Purelib.Curves.Legendre.Paths
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.RootIsolation.Progressive.Chamber.Basic
import Purelib.RootIsolation.Progressive.Chamber.Frame

open Purelib

open Purelib.Approximation.Gaussian.Vector

open Purelib.Curves

open Purelib.Curves.Legendre

open Purelib.Integration

open Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic

open Purelib.Riemann.Periods

section
@[expose] public section

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

namespace Purelib.Curves.Legendre.Periods.Fibre

/-! ## Exact endpoint fibres -/

/-- The genus-one curve carried by one Legendre root frame. Its finite squarefree certificate is reused from the
displayed simple-root chamber. -/
def frameCurve {parameter : Data.Gaussian.Basic.Canonical} (frame :
  Paths.Frame parameter) :
    Hyperelliptic.Basic.HyperellipticCurve 1 where
  polynomial := Paths.polynomial parameter
  nonzero := Paths.polynomial_isZero parameter
  squarefree := by
    have certificate := frame.chamber.chamber.squarefree
    change Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate
      frame.chamber.polynomial at certificate
    rw [frame.polynomial_eq] at certificate
    exact certificate
  degreeShape := .odd (Paths.polynomial_natDegree parameter)

/-- The genus-one curve constructed from the retained root frame has its exact displayed Legendre polynomial. -/
@[simp] theorem frameCurve_polynomial {parameter :
  Data.Gaussian.Basic.Canonical}
    (frame : Paths.Frame parameter) :
    (frameCurve frame).polynomial = Paths.polynomial parameter := rfl

set_option genInjectivity false in
/-- Certified raw periods on the exact fibre selected by one frame. -/
structure FibreData {parameter : Data.Gaussian.Basic.Canonical} (frame :
  Paths.Frame parameter) where
  /-- The certified period programs on this exact frame-selected genus-one curve. -/ periods : PeriodMatrix.PeriodData
    (frameCurve frame)

constructive_injectivity Purelib.Curves.Legendre.Periods.Fibre.FibreData

namespace FibreData

/-- The `a` and `b` refinement programs in locked column-vector order. -/
def rawRefinement {parameter : Data.Gaussian.Basic.Canonical}
  {frame : Paths.Frame parameter}
    (data : Curves.Legendre.Periods.Fibre.FibreData frame) (coordinate : Fin 2) :
      Program.Gaussian.Basic.RefinementProgram :=
  if coordinate = 0 then
    (data.periods.aProgram 0 0).integral
  else
    (data.periods.bProgram 0 0).integral

/-- The productive raw period vector in the same order. -/
def rawPeriods {parameter : Data.Gaussian.Basic.Canonical} {frame
  : Paths.Frame parameter}
    (data : Curves.Legendre.Periods.Fibre.FibreData frame) : Operational.Basic.RawPeriodVector :=
  fun coordinate => (data.rawRefinement coordinate).output

/-- Each retained raw period coordinate is the output of its original refinement program. -/
@[simp] theorem rawPeriods_apply {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter} (data : Curves.Legendre.Periods.Fibre.FibreData frame) (coordinate : Fin 2) :
    data.rawPeriods coordinate = (data.rawRefinement coordinate).output := rfl

/-- The first raw coordinate is exactly the certified genus-one `a` period. -/
theorem rawRefinement_zero {parameter :
  Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    (data : Curves.Legendre.Periods.Fibre.FibreData frame) :
    data.rawRefinement 0 = (data.periods.aProgram 0 0).integral := rfl

/-- The second raw coordinate is exactly the certified genus-one `b` period. -/
theorem rawRefinement_one {parameter :
  Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    (data : Curves.Legendre.Periods.Fibre.FibreData frame) :
    data.rawRefinement 1 = (data.periods.bProgram 0 0).integral := by
  unfold Periods.Fibre.FibreData.rawRefinement
  rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]

end FibreData
end Purelib.Curves.Legendre.Periods.Fibre

end
