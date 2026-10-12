module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Legendre.Paths
public import Purelib.Curves.Legendre.Periods.Jets.Basic
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Periods.Jets.Specification
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic

open Purelib

open Purelib.Curves.Legendre

open Purelib.Curves.Legendre.Periods

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

namespace Purelib.Curves.Legendre.Periods.Jets.Subdivision

set_option genInjectivity false in
/-- A displayed finite owner set simultaneously covering the value, first-, and second-derivative quadrature cells at
every requested refinement. The three programs may use different literal cell lists, but their comparison is therefore
not allowed to hide unrelated subdivisions. -/
structure JetCommonSubdivision {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : Jets.Basic.SynchronizedPeriodJet frame) where
  /-- The retained common finite owner count for each original coordinate and refinement. -/ commonCount : Fin 2 -> Nat
    -> Nat
  /-- Map each common occurrence to its original value-program quadrature cell. -/ valueOwner : forall coordinate
    refinement,
    Fin (commonCount coordinate refinement) ->
      Fin ((jet.value coordinate).integral.model refinement).cells.length
  /-- Map each common occurrence to its original first-derivative quadrature cell. -/ firstOwner : forall coordinate
    refinement,
    Fin (commonCount coordinate refinement) ->
      Fin ((jet.first coordinate).integral.model refinement).cells.length
  /-- Map each common occurrence to its original second-derivative quadrature cell. -/ secondOwner : forall coordinate
    refinement,
    Fin (commonCount coordinate refinement) ->
      Fin ((jet.second coordinate).integral.model refinement).cells.length
  /-- Every original value-program quadrature cell is reached by a retained common occurrence. -/ valueCovered : forall
    coordinate refinement
      (cell : Fin
        ((jet.value coordinate).integral.model refinement).cells.length),
    ∃ common : Fin (commonCount coordinate refinement),
      valueOwner coordinate refinement common = cell
  /-- Every original first-derivative quadrature cell is reached by a retained common occurrence. -/ firstCovered :
    forall coordinate refinement
      (cell : Fin
        ((jet.first coordinate).integral.model refinement).cells.length),
    ∃ common : Fin (commonCount coordinate refinement),
      firstOwner coordinate refinement common = cell
  /-- Every original second-derivative quadrature cell is reached by a retained common occurrence. -/ secondCovered :
    forall coordinate refinement
      (cell : Fin
        ((jet.second coordinate).integral.model refinement).cells.length),
    ∃ common : Fin (commonCount coordinate refinement),
      secondOwner coordinate refinement common = cell

constructive_injectivity Purelib.Curves.Legendre.Periods.Jets.Subdivision.JetCommonSubdivision

end Purelib.Curves.Legendre.Periods.Jets.Subdivision

end
