module

import Purelib.Data.Gaussian.Basic
import Purelib.RootIsolation.Progressive.Chamber.State.Request
public import Purelib.RootIsolation.Progressive.Chamber.State.Extraction
import Purelib.RootIsolation.Progressive.Chamber.State.Reading
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.RootIsolation.Progressive.Chamber.Basic
import Purelib.RootIsolation.Progressive.Chamber.State
import Purelib.Tactic.Ring
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.RootIsolation.Owner.Family.Basic
import Purelib.RootIsolation.Owner.Local.Basic

open Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table (CoefficientTable)
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

/-- One complete executable coefficient/root refinement. -/
def next
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) : Progressive.Chamber.State.ChamberContinuationState chamber where
  table := state.nextTable epsilon positive
  same := state.reference_same_nextTable epsilon positive
  chamberSmall := state.nextTable_chamberSmall epsilon positive
  family := state.nextFamily epsilon positive
  refinesSeed := by
    intro index
    exact (state.nextFamily_nested epsilon positive index).trans
      (state.refinesSeed index)
  guardTarget := state.nextGuardTarget epsilon
  guardPositive := state.nextGuardTarget_pos positive
  guardSmall := state.nextTable_nextGuardSmall epsilon positive
  budgetBox := fun index => (state.family.owner index).box
  ownerRefinesBudget := state.nextFamily_nested epsilon positive
  stable := state.nextFamily_stable epsilon positive
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

/-- The next continuation state's indexed owner box meets the original positive accuracy request. -/
theorem next_accurate
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (index : chamber.Index) :
    ((state.next epsilon positive).family.owner index).box.diagonalSq ≤
      epsilon ^ 2 :=
  state.nextFamily_accurate epsilon positive index

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

/-- The next continuation state's indexed owner box refines its original predecessor. -/
theorem next_nested
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (index : chamber.Index) :
    ((state.next epsilon positive).family.owner index).box.Refines
      (state.family.owner index).box :=
  state.nextFamily_nested epsilon positive index
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

/-- The next continuation state's indexed owner box lies strictly inside its original predecessor. -/
theorem next_strict
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (index : chamber.Index) :
    ((state.next epsilon positive).family.owner index).box.StrictInterior
      (state.family.owner index).box :=
  state.nextFamily_strict epsilon positive index
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

/-- The next continuation state retains exactly the coefficient table selected by the original request. -/
@[simp] theorem next_table
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) :
    (state.next epsilon positive).table = state.nextTable epsilon positive := rfl
end ChamberContinuationState

end Purelib.RootIsolation.Progressive.Chamber.State

end
