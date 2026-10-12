module
meta import Purelib.Elab.ConstructiveInjectivity

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Relation
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
public import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Transport
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.RootIsolation.Owner.Family.Basic
public import Purelib.RootIsolation.Progressive.Owner.Stability
import Purelib.Tactic.Ring
public import Purelib.RootIsolation.Owner.Family.Refinement
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Bounds
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Refinement
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.RootIsolation.Owner.Local.Basic

open Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table (CoefficientTable)
open Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable (AllowancesLt)
open Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic (SquarefreeCertificate)
open Purelib.RootIsolation.Owner.Family.Basic (OwnerFamily)

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

namespace Purelib.RootIsolation.Progressive.Owner.Transfer
open Purelib.Data.Gaussian

set_option genInjectivity false in
/-- A complete family-level Rouché transfer between two sufficiently
accurate readings of the same progressive coefficient channels. -/
structure GuardedFamilyTransfer
    (left right : CoefficientTable) (target : Fraction.Rational)
    (positive : 0 < target) where
  /-- The two retained coefficient readings come from the same ordered channels. -/ same :
    Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.SameChannels left.entries right.entries
  /-- Every original reading allowance is below the common positive target. -/ leftSmall :
    AllowancesLt left.entries target
  /-- Every later reading allowance is below the same common target. -/ rightSmall :
    AllowancesLt right.entries target
  /-- The original coefficient table has degree at least two. -/ degreeAtLeastTwo : 2 ≤ left.degree
  /-- The original indexed winding-one owner family of the earlier polynomial. -/ family :
    OwnerFamily left.polynomial left.degree
  /-- The common coefficient perturbation bound is below each original owner's retained boundary clearance. -/ stable :
    ∀ index : Fin left.degree,
    left.refinementEvaluationBound target (family.owner index).box <
      (family.owner index).clearance.bound
  /-- The later polynomial has the retained original squarefree certificate. -/ rightSquarefree :
    SquarefreeCertificate right.polynomial

constructive_injectivity GuardedFamilyTransfer

end Purelib.RootIsolation.Progressive.Owner.Transfer

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

namespace Purelib.RootIsolation.Progressive.Owner.Transfer
open Purelib.Data.Gaussian
namespace GuardedFamilyTransfer

/-- Build the complete family transfer at the common coefficient target
computed from every current owner boundary. -/
def ofComputedTarget
    (left right : CoefficientTable)
    (same : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.SameChannels left.entries right.entries)
    (degreeAtLeastTwo : 2 ≤ left.degree)
    (family : OwnerFamily left.polynomial left.degree)
    (leftSmall : AllowancesLt left.entries
      (Progressive.Owner.Stability.ownerFamilyStabilityTarget left family))
    (rightSmall : AllowancesLt right.entries
      (Progressive.Owner.Stability.ownerFamilyStabilityTarget left family))
    (rightSquarefree : SquarefreeCertificate
      right.polynomial) :
    Progressive.Owner.Transfer.GuardedFamilyTransfer left right
      (Progressive.Owner.Stability.ownerFamilyStabilityTarget left family)
      (Progressive.Owner.Stability.ownerFamilyStabilityTarget_pos left family) where
  same := same
  leftSmall := leftSmall
  rightSmall := rightSmall
  degreeAtLeastTwo := degreeAtLeastTwo
  family := family
  stable := by
    intro index
    have commonLe := Progressive.Owner.Stability.ownerFamilyStabilityTarget_le left family index
    have scaleNonnegative :
        0 ≤ left.refinementEvaluationScale (family.owner index).box :=
      (left.refinementEvaluationScale_pos (family.owner index).box).le
    have localBudget := left.refinementEvaluationBound_stabilityTarget_lt
      (family.owner index).box (family.owner index).clearance
    rw [left.refinementEvaluationBound_eq_target_mul_scale] at localBudget ⊢
    exact (Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      commonLe scaleNonnegative).trans_lt localBudget
  rightSquarefree := rightSquarefree
end GuardedFamilyTransfer

end Purelib.RootIsolation.Progressive.Owner.Transfer

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

namespace Purelib.RootIsolation.Progressive.Owner.Transfer
open Purelib.Data.Gaussian
namespace GuardedFamilyTransfer

/-- Read the stable coefficient-channel comparison for the indexed original owner box. -/
def ownerTransferAt
    {left right : CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target}
    (transfer : Progressive.Owner.Transfer.GuardedFamilyTransfer left right target positive)
    (index : Fin left.degree) :
    Dense.Gaussian.Coefficient.Progressive.Transport.StableChannelReadings left right target positive
      (transfer.family.owner index).box where
  same := transfer.same
  leftSmall := transfer.leftSmall
  rightSmall := transfer.rightSmall
  proper := (transfer.family.owner index).proper
  clearance := (transfer.family.owner index).clearance
  budget_lt := transfer.stable index
end GuardedFamilyTransfer

end Purelib.RootIsolation.Progressive.Owner.Transfer

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

namespace Purelib.RootIsolation.Progressive.Owner.Transfer
open Purelib.Data.Gaussian
namespace GuardedFamilyTransfer

/-- The canonical next-reading specialization: request every coefficient at
the family-computed target, with the later allowance and channel proofs
filled by coherence. -/
def refineAtComputedTarget
    (table : CoefficientTable) (degreeAtLeastTwo : 2 ≤ table.degree)
    (family : OwnerFamily table.polynomial table.degree)
    (currentSmall : AllowancesLt table.entries
      (Progressive.Owner.Stability.ownerFamilyStabilityTarget table family))
    (nextSquarefree : SquarefreeCertificate
      (table.refine (Progressive.Owner.Stability.ownerFamilyStabilityTarget table family)
        (Progressive.Owner.Stability.ownerFamilyStabilityTarget_pos table family)).polynomial) :
    Progressive.Owner.Transfer.GuardedFamilyTransfer table
      (table.refine (Progressive.Owner.Stability.ownerFamilyStabilityTarget table family)
        (Progressive.Owner.Stability.ownerFamilyStabilityTarget_pos table family))
      (Progressive.Owner.Stability.ownerFamilyStabilityTarget table family)
      (Progressive.Owner.Stability.ownerFamilyStabilityTarget_pos table family) :=
  Progressive.Owner.Transfer.GuardedFamilyTransfer.ofComputedTarget table
    (table.refine (Progressive.Owner.Stability.ownerFamilyStabilityTarget table family)
      (Progressive.Owner.Stability.ownerFamilyStabilityTarget_pos table family))
    (table.sameChannels_refine (Progressive.Owner.Stability.ownerFamilyStabilityTarget table family)
      (Progressive.Owner.Stability.ownerFamilyStabilityTarget_pos table family))
    degreeAtLeastTwo family currentSmall
    (table.refine_allowances_lt (Progressive.Owner.Stability.ownerFamilyStabilityTarget table family)
      (Progressive.Owner.Stability.ownerFamilyStabilityTarget_pos table family))
    nextSquarefree
end GuardedFamilyTransfer

end Purelib.RootIsolation.Progressive.Owner.Transfer

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

namespace Purelib.RootIsolation.Progressive.Owner.Transfer
open Purelib.Data.Gaussian
namespace GuardedFamilyTransfer

/-- The later same-channel polynomial retains degree at least two. -/
theorem rightDegreeAtLeastTwo
    {left right : CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target}
    (transfer : Progressive.Owner.Transfer.GuardedFamilyTransfer left right target positive) :
    2 ≤ right.polynomial.natDegree := by
  rw [right.polynomial_natDegree,
    ← left.degree_eq_of_sameChannels transfer.same]
  exact transfer.degreeAtLeastTwo
end GuardedFamilyTransfer

end Purelib.RootIsolation.Progressive.Owner.Transfer

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

namespace Purelib.RootIsolation.Progressive.Owner.Transfer
open Purelib.Data.Gaussian
namespace GuardedFamilyTransfer

/-- The same rational owner boxes, now carrying winding and clearance for
the later coefficient reading. -/
def transportedFamily
    {left right : CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target}
    (transfer : Progressive.Owner.Transfer.GuardedFamilyTransfer left right target positive) :
    OwnerFamily right.polynomial left.degree where
  owner index :=
    { box := (transfer.family.owner index).box
      proper := (transfer.family.owner index).proper
      clearance := (transfer.ownerTransferAt index).rightClearance
      rawWindingFour := by
        rw [(transfer.ownerTransferAt index).rightWinding_eq]
        exact (transfer.family.owner index).rawWindingFour }
  pairwiseSeparated := transfer.family.pairwiseSeparated
end GuardedFamilyTransfer

end Purelib.RootIsolation.Progressive.Owner.Transfer

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

namespace Purelib.RootIsolation.Progressive.Owner.Transfer
open Purelib.Data.Gaussian
namespace GuardedFamilyTransfer

/-- Transport all owners and then strictly shrink them for the later exact
rational polynomial. -/
def refinedFamily
    {left right : CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target}
    (transfer : Progressive.Owner.Transfer.GuardedFamilyTransfer left right target positive)
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon) :
    OwnerFamily right.polynomial left.degree :=
  transfer.transportedFamily.refine transfer.rightDegreeAtLeastTwo
    transfer.rightSquarefree epsilon epsilonPositive
end GuardedFamilyTransfer

end Purelib.RootIsolation.Progressive.Owner.Transfer

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

namespace Purelib.RootIsolation.Progressive.Owner.Transfer
open Purelib.Data.Gaussian
namespace GuardedFamilyTransfer

/-- Each transferred and refined owner box meets the supplied positive accuracy target. -/
theorem refinedFamily_accurate
    {left right : CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target}
    (transfer : Progressive.Owner.Transfer.GuardedFamilyTransfer left right target positive)
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon)
    (index : Fin left.degree) :
    ((transfer.refinedFamily epsilon epsilonPositive).owner index).box.diagonalSq ≤
      epsilon ^ 2 :=
  transfer.transportedFamily.refine_accurate transfer.rightDegreeAtLeastTwo
    transfer.rightSquarefree epsilon epsilonPositive index

end GuardedFamilyTransfer

end Purelib.RootIsolation.Progressive.Owner.Transfer

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

namespace Purelib.RootIsolation.Progressive.Owner.Transfer
open Purelib.Data.Gaussian
namespace GuardedFamilyTransfer

/-- Each transferred and refined owner box refines the same original family box. -/
theorem refinedFamily_nested
    {left right : CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target}
    (transfer : Progressive.Owner.Transfer.GuardedFamilyTransfer left right target positive)
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon)
    (index : Fin left.degree) :
    ((transfer.refinedFamily epsilon epsilonPositive).owner index).box.Refines
      (transfer.family.owner index).box :=
  transfer.transportedFamily.refine_nested transfer.rightDegreeAtLeastTwo
    transfer.rightSquarefree epsilon epsilonPositive index
end GuardedFamilyTransfer

end Purelib.RootIsolation.Progressive.Owner.Transfer

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

namespace Purelib.RootIsolation.Progressive.Owner.Transfer
open Purelib.Data.Gaussian
namespace GuardedFamilyTransfer

/-- Each transferred and refined owner box lies strictly inside the same original family box. -/
theorem refinedFamily_strict
    {left right : CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target}
    (transfer : Progressive.Owner.Transfer.GuardedFamilyTransfer left right target positive)
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon)
    (index : Fin left.degree) :
    ((transfer.refinedFamily epsilon epsilonPositive).owner index).box.StrictInterior
      (transfer.family.owner index).box :=
  transfer.transportedFamily.refine_strict transfer.rightDegreeAtLeastTwo
    transfer.rightSquarefree epsilon epsilonPositive index
end GuardedFamilyTransfer

end Purelib.RootIsolation.Progressive.Owner.Transfer

end
