module
meta import Purelib.Elab.ConstructiveInjectivity

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Relation
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.RootIsolation.Owner.Family.Basic
public import Purelib.RootIsolation.Progressive.Chamber.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Bounds
import Purelib.RootIsolation.Owner.Local.Basic

open Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table (CoefficientTable)
open Purelib.RootIsolation.Progressive.Chamber.Basic (SimpleRootChamber)

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

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

/-! ## Executable chamber-continuation state -/

set_option genInjectivity false in
/-- One finite state of the repeatable simple-root controller.  `budgetBox`
is the retained parent on which the *next* coefficient perturbation was
budgeted; the live owner may already be strictly smaller. -/
structure ChamberContinuationState
    {reference : CoefficientTable} (chamber :
      SimpleRootChamber reference)
    where
  /-- The current retained coefficient table. -/ table : CoefficientTable
  /-- The current and reference tables retain the same coefficient channels. -/ same :
    Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.SameChannels reference.entries table.entries
  /-- The current coefficient allowances meet the original chamber target. -/ chamberSmall :
    Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.AllowancesLt table.entries chamber.target
  /-- The actual retained owner family for the current table polynomial. -/ family : Owner.Family.Basic.OwnerFamily
    table.polynomial reference.degree
  /-- Each current owner box refines its original chamber owner box. -/ refinesSeed : ∀ index : chamber.Index,
    (family.owner index).box.Refines (chamber.owners.owner index).box
  /-- The retained scalar target for the next coefficient perturbation. -/ guardTarget : Fraction.Rational
  /-- The retained next-step target is strictly positive. -/ guardPositive : 0 < guardTarget
  /-- The current coefficient allowances fit the retained next-step target. -/ guardSmall :
    Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.AllowancesLt table.entries guardTarget
  /-- The actual parent box on which each next perturbation was budgeted. -/ budgetBox : chamber.Index →
    Box
  /-- Each live owner box refines its retained budget parent. -/ ownerRefinesBudget : ∀ index : chamber.Index,
    (family.owner index).box.Refines (budgetBox index)
  /-- Each budget parent's refinement bound fits the corresponding live owner's original clearance. -/ stable : ∀ index
    : chamber.Index,
    table.refinementEvaluationBound guardTarget (budgetBox index) <
      (family.owner index).clearance.bound

constructive_injectivity ChamberContinuationState

end Purelib.RootIsolation.Progressive.Chamber.State

end

section
public section

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

/-- Initialize the continuation state with the original chamber table and owner family.

The next perturbation is budgeted on those same owner boxes with the original positive chamber target. -/
@[expose] def initial
    {reference : CoefficientTable} (chamber :
      SimpleRootChamber reference) :
    Progressive.Chamber.State.ChamberContinuationState chamber where
  table := reference
  same := CoefficientTable.sameChannels_refl reference.entries
  chamberSmall := chamber.referenceSmall
  family := chamber.owners
  refinesSeed := fun index =>
    Box.refines_refl (chamber.owners.owner index).box
  guardTarget := chamber.target
  guardPositive := chamber.target_pos
  guardSmall := chamber.referenceSmall
  budgetBox := fun index => (chamber.owners.owner index).box
  ownerRefinesBudget := fun index =>
    Box.refines_refl (chamber.owners.owner index).box
  stable := by
    intro index
    have targetLe := chamber.target_le_stability index
    have scaleNonnegative : 0 ≤ reference.refinementEvaluationScale
        (chamber.owners.owner index).box :=
      (reference.refinementEvaluationScale_pos
        (chamber.owners.owner index).box).le
    have localBudget := reference.refinementEvaluationBound_stabilityTarget_lt
      (chamber.owners.owner index).box
      (chamber.owners.owner index).clearance
    rw [reference.refinementEvaluationBound_eq_target_mul_scale] at localBudget ⊢
    exact (Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      targetLe scaleNonnegative).trans_lt localBudget
end ChamberContinuationState

end Purelib.RootIsolation.Progressive.Chamber.State

end

section
public section

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

/-- The live table has the same degree as the original reference table. -/
theorem table_degree
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) :
    state.table.degree = reference.degree :=
  (CoefficientTable.degree_eq_of_sameChannels state.same).symm

/-- The live continuation polynomial retains the original degree lower bound of two. -/
theorem polynomialDegreeAtLeastTwo
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) :
    2 ≤ state.table.polynomial.natDegree := by
  rw [state.table.polynomial_natDegree, state.table_degree]
  exact chamber.degreeAtLeastTwo
end ChamberContinuationState

end Purelib.RootIsolation.Progressive.Chamber.State

end

section
public section

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

/-- The live continuation polynomial has positive degree. -/
theorem polynomialDegreePositive
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) :
    0 < state.table.polynomial.natDegree :=
  (show (0 : Nat) < 2 by decide).trans_le state.polynomialDegreeAtLeastTwo
end ChamberContinuationState

end Purelib.RootIsolation.Progressive.Chamber.State

end

section
public section

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

namespace Purelib.CCL.Progressive.PolynomialRoots
open Purelib.Data.Gaussian
namespace ChamberContinuationState

end ChamberContinuationState

end Purelib.CCL.Progressive.PolynomialRoots

end
