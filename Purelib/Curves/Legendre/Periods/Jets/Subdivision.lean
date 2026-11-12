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
import Purelib.Integration.Path.Lifted.Model
import Purelib.Integration.Path.Lifted.Program
import Purelib.Geometry.Path.Gaussian.Lifted.Closed

open Purelib

open Purelib.Curves.Legendre

open Purelib.Curves.Legendre.Periods

section
public section

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
/-- Ordered cell owners for the common lifted path at every refinement.

The common count is the retained path's cell count, and every map preserves
the original cell ordinal. The certified programs may retain different
polynomials and allowances on those identical oriented physical intervals. -/
structure JetCommonSubdivision {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : Jets.Basic.SynchronizedPeriodJet frame) where
  /-- The retained common finite owner count for each original coordinate and refinement. -/ commonCount : Fin 2 -> Nat
    -> Nat
  /-- Every differential uses exactly the retained common lifted path's cell count. -/ commonCount_eq :
    forall coordinate refinement,
      commonCount coordinate refinement = (jet.cycle.liftedPath refinement).cellCount
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
  /-- The value map preserves the original oriented cell ordinal. -/ valueOrdinal : forall coordinate refinement
    (common : Fin (commonCount coordinate refinement)), (valueOwner coordinate refinement common).val = common.val
  /-- The first derivative map preserves the same original cell ordinal. -/ firstOrdinal : forall coordinate refinement
    (common : Fin (commonCount coordinate refinement)), (firstOwner coordinate refinement common).val = common.val
  /-- The second derivative map preserves the same original cell ordinal. -/ secondOrdinal :
    forall coordinate refinement
    (common : Fin (commonCount coordinate refinement)), (secondOwner coordinate refinement common).val = common.val
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

constructive_injectivity JetCommonSubdivision

open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Geometry.Path.Gaussian.Lifted.Basic
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic

namespace JetCommonSubdivision

/-- Construct ordered common cell owners directly from the six retained path certificates.

No subdivision search or covering witness is an input. Each finite index is
transported along the certified equality of its program's cell count with
the common lifted path count, without recomputing any integral model. -/
@[expose] def ofJet {parameter : Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter} (jet : Basic.SynchronizedPeriodJet frame) :
    Subdivision.JetCommonSubdivision jet where
  commonCount := fun _ refinement => (jet.cycle.liftedPath refinement).cellCount
  commonCount_eq := fun _ _ => rfl
  valueOwner := fun coordinate refinement common =>
    Fin.cast ((jet.value coordinate).toPeriodProgram.refinement_cellCount refinement).symm common
  firstOwner := fun coordinate refinement common =>
    Fin.cast ((jet.first coordinate).toPeriodProgram.refinement_cellCount refinement).symm common
  secondOwner := fun coordinate refinement common =>
    Fin.cast ((jet.second coordinate).toPeriodProgram.refinement_cellCount refinement).symm common
  valueOrdinal := fun _ _ _ => rfl
  firstOrdinal := fun _ _ _ => rfl
  secondOrdinal := fun _ _ _ => rfl
  valueCovered := fun coordinate refinement cell =>
    ⟨Fin.cast ((jet.value coordinate).toPeriodProgram.refinement_cellCount refinement) cell, Fin.ext rfl⟩
  firstCovered := fun coordinate refinement cell =>
    ⟨Fin.cast ((jet.first coordinate).toPeriodProgram.refinement_cellCount refinement) cell, Fin.ext rfl⟩
  secondCovered := fun coordinate refinement cell =>
    ⟨Fin.cast ((jet.second coordinate).toPeriodProgram.refinement_cellCount refinement) cell, Fin.ext rfl⟩

/-- Read the original value model at its retained ordered common occurrence. -/
@[expose] def valueCell {parameter : Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter} {jet : Basic.SynchronizedPeriodJet frame}
    (subdivision : Subdivision.JetCommonSubdivision jet) (coordinate : Fin 2) (refinement : Nat)
    (common : Fin (subdivision.commonCount coordinate refinement)) : CellModel :=
  let owner := subdivision.valueOwner coordinate refinement common
  ((jet.value coordinate).integral.model refinement).cells.get owner

/-- Read the original first derivative model at the same ordered common occurrence. -/
@[expose] def firstCell {parameter : Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter} {jet : Basic.SynchronizedPeriodJet frame}
    (subdivision : Subdivision.JetCommonSubdivision jet) (coordinate : Fin 2) (refinement : Nat)
    (common : Fin (subdivision.commonCount coordinate refinement)) : CellModel :=
  let owner := subdivision.firstOwner coordinate refinement common
  ((jet.first coordinate).integral.model refinement).cells.get owner

/-- Read the original second derivative model at the same ordered common occurrence. -/
@[expose] def secondCell {parameter : Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter} {jet : Basic.SynchronizedPeriodJet frame}
    (subdivision : Subdivision.JetCommonSubdivision jet) (coordinate : Fin 2) (refinement : Nat)
    (common : Fin (subdivision.commonCount coordinate refinement)) : CellModel :=
  let owner := subdivision.secondOwner coordinate refinement common
  ((jet.second coordinate).integral.model refinement).cells.get owner

/-- The retained value and first derivative cells have identical physical intervals and orientation. -/
theorem value_first_endpoints {parameter : Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter} {jet : Basic.SynchronizedPeriodJet frame}
    (subdivision : Subdivision.JetCommonSubdivision jet) (coordinate : Fin 2) (refinement : Nat)
    (common : Fin (subdivision.commonCount coordinate refinement)) :
    (subdivision.valueCell coordinate refinement common).start =
        (subdivision.firstCell coordinate refinement common).start ∧
      (subdivision.valueCell coordinate refinement common).finish =
        (subdivision.firstCell coordinate refinement common).finish := by
  have valueBound := (subdivision.valueOwner coordinate refinement common).isLt
  rewrite [subdivision.valueOrdinal coordinate refinement common] at valueBound
  have firstBound := (subdivision.firstOwner coordinate refinement common).isLt
  rewrite [subdivision.firstOrdinal coordinate refinement common] at firstBound
  have valueIndex : subdivision.valueOwner coordinate refinement common = ⟨common.val, valueBound⟩ :=
    Fin.ext (subdivision.valueOrdinal coordinate refinement common)
  have firstIndex : subdivision.firstOwner coordinate refinement common = ⟨common.val, firstBound⟩ :=
    Fin.ext (subdivision.firstOrdinal coordinate refinement common)
  unfold valueCell firstCell
  dsimp only
  rewrite [valueIndex, firstIndex]
  exact LiftedPath.followedBy_same_endpoints
    ((jet.value coordinate).toPeriodProgram.follows refinement)
    ((jet.first coordinate).toPeriodProgram.follows refinement) common.val valueBound firstBound

/-- The retained value and second derivative cells have identical physical intervals and orientation. -/
theorem value_second_endpoints {parameter : Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter} {jet : Basic.SynchronizedPeriodJet frame}
    (subdivision : Subdivision.JetCommonSubdivision jet) (coordinate : Fin 2) (refinement : Nat)
    (common : Fin (subdivision.commonCount coordinate refinement)) :
    (subdivision.valueCell coordinate refinement common).start =
        (subdivision.secondCell coordinate refinement common).start ∧
      (subdivision.valueCell coordinate refinement common).finish =
        (subdivision.secondCell coordinate refinement common).finish := by
  have valueBound := (subdivision.valueOwner coordinate refinement common).isLt
  rewrite [subdivision.valueOrdinal coordinate refinement common] at valueBound
  have secondBound := (subdivision.secondOwner coordinate refinement common).isLt
  rewrite [subdivision.secondOrdinal coordinate refinement common] at secondBound
  have valueIndex : subdivision.valueOwner coordinate refinement common = ⟨common.val, valueBound⟩ :=
    Fin.ext (subdivision.valueOrdinal coordinate refinement common)
  have secondIndex : subdivision.secondOwner coordinate refinement common = ⟨common.val, secondBound⟩ :=
    Fin.ext (subdivision.secondOrdinal coordinate refinement common)
  unfold valueCell secondCell
  dsimp only
  rewrite [valueIndex, secondIndex]
  exact LiftedPath.followedBy_same_endpoints
    ((jet.value coordinate).toPeriodProgram.follows refinement)
    ((jet.second coordinate).toPeriodProgram.follows refinement) common.val valueBound secondBound

end JetCommonSubdivision

end Purelib.Curves.Legendre.Periods.Jets.Subdivision

end
