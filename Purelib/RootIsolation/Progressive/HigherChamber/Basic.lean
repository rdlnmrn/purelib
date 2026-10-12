module
import Purelib.Data.List.OfFn.Basic
meta import Purelib.Elab.ConstructiveInjectivity

import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Stability
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Bounds
public import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Refinement
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.List.Minimum
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Relation
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
public import Purelib.RootIsolation.FTA.Squarefree.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

open Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table (CoefficientTable)
open Purelib.RootIsolation.FTA.Squarefree (AdapterResult)

open Purelib.Data.Rat

open Purelib

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

namespace Purelib.RootIsolation.Progressive
open Purelib.Data.Gaussian

/-! ## A complete finite family of transported simple-root owners -/

set_option genInjectivity false in
/-- One higher-degree simple-root chamber.  The current displayed monic
polynomial already has its exact degree-many RFAP isolation.  A single common
coefficient target is small enough on every owner boundary, and the next
exact rational reading carries the squarefree certificate needed for further
Newton refinement. -/
structure HigherChamber
    (table : CoefficientTable) (target : Fraction.Rational)
    (positive : 0 < target) where
  /-- The original displayed polynomial has degree at least two. -/ degreeAtLeastTwo : 2 ≤ table.polynomial.natDegree
  /-- The original current coefficient allowances fit the retained common target. -/ currentSmall :
    Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.AllowancesLt table.entries target
  /-- The exact original degree-sized isolated owner family. -/ owners : AdapterResult table.polynomial
  /-- The next exact coefficient reading has its retained squarefree certificate. -/ nextSquarefree :
    Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate
    (table.refine target positive).polynomial
  /-- The original perturbation bound is strictly below each retained owner's boundary clearance. -/ stable : ∀ index :
    Fin table.polynomial.natDegree,
    table.refinementEvaluationBound target
        (owners.trackAt index).initial.box <
      (owners.trackAt index).initial.clearance.bound

constructive_injectivity HigherChamber

end Purelib.RootIsolation.Progressive

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

namespace Purelib.RootIsolation.Progressive.HigherChamber.Basic
open Purelib.Data.Gaussian

/-- Per-owner coefficient targets computed from the current exact boundary
clearances and Horner scales. -/
def higherOwnerStabilityTargets
    (table : CoefficientTable)
    (owners : AdapterResult table.polynomial) : List Fraction.Rational :=
  List.ofFn fun index : Fin table.polynomial.natDegree =>
    table.stabilityTarget (owners.trackAt index).initial.box
      (owners.trackAt index).initial.clearance
end Purelib.RootIsolation.Progressive.HigherChamber.Basic

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

namespace Purelib.RootIsolation.Progressive.HigherChamber.Basic
open Purelib.Data.Gaussian

/-- Every original owner's computed coefficient-stability target is strictly positive. -/
theorem higherOwnerStabilityTargets_positive
    (table : CoefficientTable)
    (owners : AdapterResult table.polynomial) :
    ∀ target ∈ Progressive.HigherChamber.Basic.higherOwnerStabilityTargets table owners, 0 < target := by
  intro target member
  rw [Progressive.HigherChamber.Basic.higherOwnerStabilityTargets] at member
  rcases Data.List.OfFn.Basic.mem_ofFn.mp member with ⟨index, rfl⟩
  exact table.stabilityTarget_pos (owners.trackAt index).initial.box
    (owners.trackAt index).initial.clearance
end Purelib.RootIsolation.Progressive.HigherChamber.Basic

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

namespace Purelib.RootIsolation.Progressive.HigherChamber.Basic
open Purelib.Data.Gaussian

/-- One positive coefficient target simultaneously safe on all exactly
degree-many owner boundaries. -/
def higherStabilityTarget
    (table : CoefficientTable)
    (owners : AdapterResult table.polynomial) : Fraction.Rational :=
  Data.Rat.List.Minimum.positiveMinimum (Progressive.HigherChamber.Basic.higherOwnerStabilityTargets table owners)
end Purelib.RootIsolation.Progressive.HigherChamber.Basic

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

namespace Purelib.RootIsolation.Progressive.HigherChamber.Basic
open Purelib.Data.Gaussian

/-- The computed common coefficient target fits each original owner's individual boundary budget. -/
theorem higherStabilityTarget_le_owner
    (table : CoefficientTable)
    (owners : AdapterResult table.polynomial)
    (index : Fin table.polynomial.natDegree) :
    Progressive.HigherChamber.Basic.higherStabilityTarget table owners ≤
      table.stabilityTarget (owners.trackAt index).initial.box
        (owners.trackAt index).initial.clearance := by
  apply Data.Rat.List.Minimum.positiveMinimum_le_of_mem
  rw [Progressive.HigherChamber.Basic.higherOwnerStabilityTargets]
  exact Data.List.OfFn.Basic.mem_ofFn.mpr ⟨index, rfl⟩
end Purelib.RootIsolation.Progressive.HigherChamber.Basic

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

namespace Purelib.RootIsolation.Progressive.HigherChamber.Basic
open Purelib.Data.Gaussian

/-- The retained degree-indexed owner family has a strictly positive common coefficient target. -/
theorem higherStabilityTarget_pos
    (table : CoefficientTable)
    (owners : AdapterResult table.polynomial) :
    0 < Progressive.HigherChamber.Basic.higherStabilityTarget table owners :=
  Data.Rat.List.Minimum.positiveMinimum_pos _
    (Progressive.HigherChamber.Basic.higherOwnerStabilityTargets_positive table owners)
end Purelib.RootIsolation.Progressive.HigherChamber.Basic

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

namespace Purelib.RootIsolation.Progressive.HigherChamber.Basic
open Purelib.Data.Gaussian

/-- Public constructor which computes the common perturbation target from
the complete owner family.  The caller supplies only the semantic statement
that the current coefficient allowances have already crossed that target
and the finite squarefree result of the next displayed reading. -/
def higherChamberOfComputedTarget
    (table : CoefficientTable)
    (degreeAtLeastTwo : 2 ≤ table.polynomial.natDegree)
    (owners : AdapterResult table.polynomial)
    (currentSmall : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.AllowancesLt table.entries
      (Progressive.HigherChamber.Basic.higherStabilityTarget table owners))
    (nextSquarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate
      (table.refine (Progressive.HigherChamber.Basic.higherStabilityTarget table owners)
        (Progressive.HigherChamber.Basic.higherStabilityTarget_pos table owners)).polynomial) :
    HigherChamber table (Progressive.HigherChamber.Basic.higherStabilityTarget table
      owners)
      (Progressive.HigherChamber.Basic.higherStabilityTarget_pos table owners) where
  degreeAtLeastTwo := degreeAtLeastTwo
  currentSmall := currentSmall
  owners := owners
  nextSquarefree := nextSquarefree
  stable := by
    intro index
    let box := (owners.trackAt index).initial.box
    let clearance := (owners.trackAt index).initial.clearance
    let common := Progressive.HigherChamber.Basic.higherStabilityTarget table owners
    let localTarget := table.stabilityTarget box clearance
    have commonLe : common ≤ localTarget :=
      Progressive.HigherChamber.Basic.higherStabilityTarget_le_owner table owners index
    have scaleNonnegative :
        0 ≤ table.refinementEvaluationScale box :=
      (table.refinementEvaluationScale_pos box).le
    have localBudget :=
      table.refinementEvaluationBound_stabilityTarget_lt box clearance
    rw [table.refinementEvaluationBound_eq_target_mul_scale] at localBudget ⊢
    exact (Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      commonLe scaleNonnegative).trans_lt
        localBudget

end Purelib.RootIsolation.Progressive.HigherChamber.Basic

end
