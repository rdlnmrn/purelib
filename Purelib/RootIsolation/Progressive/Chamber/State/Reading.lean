module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Relation
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
public import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Transport.Coarse
import Purelib.RootIsolation.Progressive.Chamber.Basic
import Purelib.RootIsolation.Progressive.Chamber.State
import Purelib.Tactic.Ring
public import Purelib.RootIsolation.Progressive.Chamber.State.Request
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Refinement
import Purelib.RootIsolation.Owner.Family.Basic
import Purelib.RootIsolation.Owner.Local.Basic

open Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table (CoefficientTable)
open Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable (AllowancesLt)
open Purelib.RootIsolation.Progressive.Chamber.Basic (SimpleRootChamber)

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

namespace Purelib.RootIsolation.Progressive.Chamber.State
open Purelib.Data.Gaussian
namespace ChamberContinuationState

/-- The exact simultaneous coefficient reading used by one continuation
step. -/
def nextTable
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) : CoefficientTable :=
  state.table.refine (state.coefficientTarget epsilon)
    (state.coefficientTarget_pos positive)
end ChamberContinuationState

end Purelib.RootIsolation.Progressive.Chamber.State

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

namespace Purelib.RootIsolation.Progressive.Chamber.State
open Purelib.Data.Gaussian
namespace ChamberContinuationState

/-- The next simultaneous coefficient reading meets the original joint coefficient target. -/
theorem
  nextTable_small_coefficientTarget
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) :
    AllowancesLt (state.nextTable epsilon
      positive).entries
      (state.coefficientTarget epsilon) :=
  state.table.refine_allowances_lt (state.coefficientTarget epsilon)
    (state.coefficientTarget_pos positive)
end ChamberContinuationState

end Purelib.RootIsolation.Progressive.Chamber.State

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

namespace Purelib.RootIsolation.Progressive.Chamber.State
open Purelib.Data.Gaussian
namespace ChamberContinuationState

/-- The next table retains the same coefficient channels as the current table. -/
theorem same_nextTable
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) :
    Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.SameChannels state.table.entries
      (state.nextTable epsilon positive).entries :=
  state.table.sameChannels_refine (state.coefficientTarget epsilon)
    (state.coefficientTarget_pos positive)
end ChamberContinuationState

end Purelib.RootIsolation.Progressive.Chamber.State

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

namespace Purelib.RootIsolation.Progressive.Chamber.State
open Purelib.Data.Gaussian
namespace ChamberContinuationState

/-- The next coefficient table's polynomial retains degree at least two. -/
theorem nextTableDegreeAtLeastTwo
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) :
    2 ≤ (state.nextTable epsilon positive).polynomial.natDegree := by
  rw [(state.nextTable epsilon positive).polynomial_natDegree,
    ← CoefficientTable.degree_eq_of_sameChannels
      (state.same_nextTable epsilon positive), state.table_degree]
  exact chamber.degreeAtLeastTwo
end ChamberContinuationState

end Purelib.RootIsolation.Progressive.Chamber.State

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

namespace Purelib.RootIsolation.Progressive.Chamber.State
open Purelib.Data.Gaussian
namespace ChamberContinuationState

/-- The next coefficient reading meets the original permanent chamber budget. -/
theorem nextTable_chamberSmall
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) :
    AllowancesLt (state.nextTable epsilon
      positive).entries
      chamber.target :=
  (state.nextTable_small_coefficientTarget epsilon positive).mono
    (state.coefficientTarget_le_chamber epsilon)
end ChamberContinuationState

end Purelib.RootIsolation.Progressive.Chamber.State

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

namespace Purelib.RootIsolation.Progressive.Chamber.State
open Purelib.Data.Gaussian
namespace ChamberContinuationState

/-- The next coefficient reading meets the currently retained guard budget. -/
theorem nextTable_guardSmall
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) :
    AllowancesLt (state.nextTable epsilon
      positive).entries
      state.guardTarget :=
  (state.nextTable_small_coefficientTarget epsilon positive).mono
    (state.coefficientTarget_le_guard epsilon)
end ChamberContinuationState

end Purelib.RootIsolation.Progressive.Chamber.State

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

namespace Purelib.RootIsolation.Progressive.Chamber.State
open Purelib.Data.Gaussian
namespace ChamberContinuationState

/-- The next coefficient reading meets the computed next-step guard budget. -/
theorem nextTable_nextGuardSmall
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) :
    AllowancesLt (state.nextTable epsilon
      positive).entries
      (state.nextGuardTarget epsilon) :=
  (state.nextTable_small_coefficientTarget epsilon positive).mono
    (state.coefficientTarget_le_nextGuard epsilon)
end ChamberContinuationState

end Purelib.RootIsolation.Progressive.Chamber.State

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

namespace Purelib.RootIsolation.Progressive.Chamber.State
open Purelib.Data.Gaussian
namespace ChamberContinuationState

/-- The next coefficient table retains the original reference table's coefficient channels. -/
theorem reference_same_nextTable
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) :
    Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.SameChannels reference.entries
      (state.nextTable epsilon positive).entries :=
  CoefficientTable.sameChannels_trans state.same
    (state.same_nextTable epsilon positive)
end ChamberContinuationState

end Purelib.RootIsolation.Progressive.Chamber.State

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

namespace Purelib.RootIsolation.Progressive.Chamber.State
open Purelib.Data.Gaussian
namespace ChamberContinuationState

/-- The next coefficient table's polynomial has positive degree. -/
theorem nextTableDegreePositive
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) :
    0 < (state.nextTable epsilon positive).polynomial.natDegree :=
  (show (0 : Nat) < 2 by decide).trans_le
    (state.nextTableDegreeAtLeastTwo epsilon positive)
end ChamberContinuationState

end Purelib.RootIsolation.Progressive.Chamber.State

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

namespace Purelib.RootIsolation.Progressive.Chamber.State
open Purelib.Data.Gaussian
namespace ChamberContinuationState

/-- Retain the checked coefficient transport on one original owner box and its saved budget parent.

The current and next readings share their channels and guard allowance; the original clearance and stable refinement
bound certify transport. -/
def transferAt
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (index : chamber.Index) :
    Dense.Gaussian.Coefficient.Progressive.Transport.Coarse.CoarseStableChannelReadings state.table
      (state.nextTable epsilon positive) state.guardTarget
      state.guardPositive (state.family.owner index).box
      (state.budgetBox index) where
  same := state.same_nextTable epsilon positive
  leftSmall := state.guardSmall
  rightSmall := state.nextTable_guardSmall epsilon positive
  proper := (state.family.owner index).proper
  refinesBudget := state.ownerRefinesBudget index
  clearance := (state.family.owner index).clearance
  budget_lt := state.stable index
end ChamberContinuationState

end Purelib.RootIsolation.Progressive.Chamber.State

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

namespace Purelib.RootIsolation.Progressive.Chamber.State
open Purelib.Data.Gaussian
namespace ChamberContinuationState

/-- The transported right clearance has exactly the retained transported-clearance bound. -/
@[simp] theorem
  transferAt_clearance_bound
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (index : chamber.Index) :
    (state.transferAt epsilon positive index).explicitRightClearance.bound =
      state.transportedClearanceBound index := rfl
end ChamberContinuationState

end Purelib.RootIsolation.Progressive.Chamber.State

end
