module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Relation
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
public import Purelib.Polynomial.Dense.Gaussian.Degree
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Bezout
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Budget.Majorants
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Majorants
import Purelib.Polynomial.Elimination.Axis.Certificate
public import Purelib.Polynomial.Elimination.Axis.Separated
import Purelib.RootIsolation.Newton.Extraction.Majorized.Basic
public import Purelib.RootIsolation.Newton.Extraction.Majorized.Build
import Purelib.RootIsolation.Owner.Family.Basic
import Purelib.RootIsolation.Progressive.Chamber.Basic
import Purelib.RootIsolation.Progressive.Chamber.State
public import Purelib.RootIsolation.Progressive.Chamber.State.Reading
import Purelib.RootIsolation.Progressive.Chamber.State.Request
import Purelib.RootIsolation.State.Raw
import Purelib.Tactic.Ring
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Bezout
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Bounds
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Transport.Coarse
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Budget.Data
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.RootIsolation.Newton.Extraction.Separated.Basic
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.RootIsolation.Progressive.Extraction.Majorants

open Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table (CoefficientTable)
open Purelib.RootIsolation.Progressive.Chamber.Basic (SimpleRootChamber)

open Purelib.Data.Rat

open Purelib.Geometry.Rational

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

/-- Build the original extraction majorants for the next coefficient reading on a retained owner box.

The fixed reference table and chamber allowance bound control the derivative, Lipschitz and Taylor quantities of the
admitted next reading. -/
def majorantsAt
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (index : chamber.Index) :
    Dense.Gaussian.Newton.Box.Majorants.ExtractionMajorants
      (state.nextTable epsilon positive).polynomial
      (state.family.owner index).box :=
  reference.admittedExtractionMajorants (state.nextTable epsilon positive)
    chamber.target chamber.target_pos
    (state.reference_same_nextTable epsilon positive) chamber.referenceSmall
    (state.nextTable_chamberSmall epsilon positive)
    (state.family.owner index).box
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

/-- Construct the separated axis eliminants for the next retained coefficient reading.

The original positive-degree witness supplies nonzeroness and the exact degree-indexed elimination certificate. -/
def nextElimination
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) :
    Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate
      (state.nextTable epsilon positive).polynomial
      (Elimination.Axis.Separated.separatedEliminationDegree
        (state.nextTable epsilon positive).polynomial) :=
  Elimination.Axis.Separated.separatedAxisEliminationCertificate
    (state.nextTable epsilon positive).polynomial
    (Dense.Gaussian.Degree.Global.isZero_false_of_natDegree_pos
      (state.nextTableDegreePositive epsilon positive))
    (state.nextTableDegreePositive epsilon positive)
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

/-- Robust derivative separation for the next reading, restricted from the
fixed reference owner to the current live owner. -/
def separationAt
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (index : chamber.Index) :
    Dense.Gaussian.Derivative.Separation.Basic.Certificate
      (state.nextTable epsilon positive).polynomial
      (state.family.owner index).box := by
  let seedBox := (chamber.owners.owner index).box
  let localTarget := reference.bezoutStabilityTarget chamber.squarefree seedBox
  have referenceLocal : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.AllowancesLt reference.entries
      localTarget := chamber.referenceSmall.mono (chamber.target_le_bezout index)
  have nextLocal : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.AllowancesLt
      (state.nextTable epsilon positive).entries localTarget :=
    (state.nextTable_chamberSmall epsilon positive).mono
      (chamber.target_le_bezout index)
  let globalSeparation := reference.robustDerivativeSeparation
    (state.nextTable epsilon positive) chamber.squarefree seedBox
    (state.reference_same_nextTable epsilon positive) referenceLocal nextLocal
  exact globalSeparation.restrict (state.refinesSeed index)
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

/-- Transport the retained owner's winding certificate to the next coefficient reading on the same box.

The original transfer supplies right-side clearance and preserves winding four, retaining a nonzero raw winding state.
-/
def transportedRawStateAt
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (index : chamber.Index) :
    State.Raw.RawWindingState
      (state.nextTable epsilon positive).polynomial
      (state.family.owner index).box where
  box := (state.family.owner index).box
  refinesAmbient := Box.refines_refl _
  proper := (state.family.owner index).proper
  clearance := (state.transferAt epsilon positive index).explicitRightClearance
  rawWinding_ne := by
    intro zero
    have transported := (state.transferAt epsilon positive index).rightWinding_eq
    rw [transported, (state.family.owner index).rawWindingFour] at zero
    exact (show (4 : Int) ≠ 0 by decide) zero
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

/-- Fully explicit Newton extraction for one owner of the next reading. -/
def extractionAt
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (index : chamber.Index) :
    Newton.Extraction.Majorized.Basic.MajorizedSeparatedOutput
      (state.transportedRawStateAt epsilon positive index)
      (state.separationAt epsilon positive index)
      (state.majorantsAt epsilon positive index) epsilon :=
  Newton.Extraction.Majorized.Build.extractSeparatedMajorized
    (state.nextTableDegreeAtLeastTwo epsilon positive)
    (state.transportedRawStateAt epsilon positive index)
    (state.separationAt epsilon positive index)
    (state.majorantsAt epsilon positive index)
    (state.nextElimination epsilon positive) positive
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

/-- The next-reading derivative majorant is exactly the fixed reference-table majorant on the original owner box. -/
@[simp] theorem majorantsAt_derivative
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (index : chamber.Index) :
    (state.majorantsAt epsilon positive index).derivative =
      reference.admittedExtractionDerivative chamber.target
        (state.family.owner index).box := rfl
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

/-- The next-reading Lipschitz majorant is exactly the fixed reference-table majorant on the original owner box. -/
@[simp] theorem majorantsAt_lipschitz
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (index : chamber.Index) :
    (state.majorantsAt epsilon positive index).lipschitz =
      reference.admittedExtractionLipschitz chamber.target
        (state.family.owner index).box := rfl
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

/-- The next-reading Taylor majorant is exactly the fixed reference-table majorant on the original owner box. -/
@[simp] theorem majorantsAt_taylor
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (index : chamber.Index) :
    (state.majorantsAt epsilon positive index).taylor =
      reference.admittedExtractionTaylor chamber.target
        (state.family.owner index).box := rfl
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

/-- The retained next-reading separation margin equals the original reference Bézout margin at its seed owner. -/
@[simp] theorem separationAt_margin
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (index : chamber.Index) :
    (state.separationAt epsilon positive index).margin =
      Dense.Gaussian.Derivative.Separation.Bezout.approximateMargin chamber.squarefree.right
        (chamber.owners.owner index).box := rfl
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

/-- Transport to the next reading retains exactly the original owner box. -/
@[simp] theorem
  transportedRawStateAt_box
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (index : chamber.Index) :
    (state.transportedRawStateAt epsilon positive index).box =
      (state.family.owner index).box := rfl
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

/-- The transported raw state retains exactly the original predicted transport-clearance bound. -/
@[simp] theorem
  transportedRawStateAt_clearance_bound
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (index : chamber.Index) :
    (state.transportedRawStateAt epsilon positive index).clearance.bound =
      state.transportedClearanceBound index :=
  state.transferAt_clearance_bound epsilon positive index
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

/-- The degree-indexed extracted owner family for the next coefficient
reading. -/
def nextFamily
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) :
    Owner.Family.Basic.OwnerFamily (state.nextTable epsilon positive).polynomial
      reference.degree where
  owner index :=
    let output := state.extractionAt epsilon positive index
    { box := output.core.box
      proper := output.core.proper
      clearance := output.clearance
      rawWindingFour := output.core.rawWindingFour }
  pairwiseSeparated := by
    intro left right different
    exact Box.Separated.of_refines
      (state.family.pairwiseSeparated left right different)
      (Box.Refinement.StrictInterior.refines (state.extractionAt epsilon positive left).core.strictCurrent)
      (Box.Refinement.StrictInterior.refines (state.extractionAt epsilon positive right).core.strictCurrent)
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

/-- Every next-reading owner box meets the original positive squared-diagonal accuracy request. -/
theorem nextFamily_accurate
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (index : chamber.Index) :
    ((state.nextFamily epsilon positive).owner index).box.diagonalSq ≤
      epsilon ^ 2 :=
  (state.extractionAt epsilon positive index).core.diagonalSq_le
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

/-- Every next-reading owner box refines its exact original indexed owner box. -/
theorem nextFamily_nested
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (index : chamber.Index) :
    ((state.nextFamily epsilon positive).owner index).box.Refines
      (state.family.owner index).box :=
  (Geometry.Rational.Box.Refinement.StrictInterior.refines (state.extractionAt epsilon positive
      index).core.strictCurrent)
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

/-- Every next-reading owner box lies strictly inside its exact original indexed owner box. -/
theorem nextFamily_strict
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (index : chamber.Index) :
    ((state.nextFamily epsilon positive).owner index).box.StrictInterior
      (state.family.owner index).box :=
  (state.extractionAt epsilon positive index).core.strictCurrent
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

/-- The predicted owner-clearance bound is no larger than the actual retained next-owner clearance.

The comparison specializes the original majorized extraction certificate to the retained separation and reference-table
majorants. -/
theorem predictedOwnerClearance_le_next
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (index : chamber.Index) :
    state.predictedOwnerClearance index epsilon ≤
      ((state.nextFamily epsilon positive).owner index).clearance.bound := by
  have predicted :=
    (state.extractionAt epsilon positive index).predicted_clearance_le
  rw [Dense.Gaussian.Newton.Box.Budget.Majorants.predictedExtractionClearance_eq_data] at predicted
  simpa only [Progressive.Chamber.State.ChamberContinuationState.predictedOwnerClearance,
    separationAt_margin,
    Progressive.Chamber.State.ChamberContinuationState.transferAt_clearance_bound,
      majorantsAt_lipschitz,
      majorantsAt_taylor,
    majorantsAt_derivative,
      transportedRawStateAt_box,
    transportedRawStateAt_clearance_bound,
      nextFamily] using predicted
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

/-- The next reading's refinement evaluation budget is strictly below its retained next-owner clearance.

The common guard target is bounded by the original indexed target, and the unchanged coefficient channels preserve the
quantitative budget. -/
theorem nextFamily_stable
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (index : chamber.Index) :
    (state.nextTable epsilon positive).refinementEvaluationBound
        (state.nextGuardTarget epsilon) (state.family.owner index).box <
      ((state.nextFamily epsilon positive).owner index).clearance.bound := by
  have commonLe := state.nextGuardTarget_le_owner epsilon index
  have scaleNonnegative : 0 ≤ state.table.refinementEvaluationScale
      (state.family.owner index).box :=
    (state.table.refinementEvaluationScale_pos
      (state.family.owner index).box).le
  have commonBudgetLe : state.table.refinementEvaluationBound
      (state.nextGuardTarget epsilon) (state.family.owner index).box ≤
      state.table.refinementEvaluationBound
        (state.nextOwnerGuardTarget index epsilon)
        (state.family.owner index).box := by
    rw [state.table.refinementEvaluationBound_eq_target_mul_scale,
      state.table.refinementEvaluationBound_eq_target_mul_scale]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      commonLe scaleNonnegative
  have localBudget :=
    state.table.refinementEvaluationBound_stabilityTargetForBound_lt
      (state.family.owner index).box
      (state.predictedOwnerClearance_pos index positive)
  have currentStable : state.table.refinementEvaluationBound
      (state.nextGuardTarget epsilon) (state.family.owner index).box <
      ((state.nextFamily epsilon positive).owner index).clearance.bound :=
    commonBudgetLe.trans_lt
      (localBudget.trans_le
        (state.predictedOwnerClearance_le_next epsilon positive index))
  rw [← state.table.refinementEvaluationBound_eq_of_sameChannels
    (state.nextTable epsilon positive) (state.same_nextTable epsilon positive)
    (state.nextGuardTarget epsilon) (state.family.owner index).box]
  exact currentStable
end ChamberContinuationState

end Purelib.RootIsolation.Progressive.Chamber.State

end

