module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Bounds

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Dominance.Basic
import Purelib.Polynomial.Clearance.Box.Dominance.Majorant
public import Purelib.Polynomial.Clearance.Box.Dominance.Uniform
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
public import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Perturbation
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Relation
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
public import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Rouche
import Purelib.Tactic.Ring
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

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

namespace Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Transport.Coarse
open Purelib.Data.Gaussian

/-! ## Transport with a retained coarse evaluation box -/

set_option genInjectivity false in
/-- Rouché transport on `box`, with the coefficient perturbation estimated
on a retained enclosing `budgetBox`.  Keeping that coarse box in the state is
what permits the next allowance target to be chosen before the newly refined
owner box has been calculated. -/
structure CoarseStableChannelReadings
    (left right : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable) (target : Fraction.Rational)
    (positive : 0 < target) (box budgetBox : Box) where
  /-- The two retained coefficient lists read the same original process channels. -/ same :
    Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.SameChannels left.entries right.entries
  /-- Every allowance in the left reading is below the common positive target. -/ leftSmall :
    Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.AllowancesLt left.entries target
  /-- Every allowance in the right reading is below the common positive target. -/ rightSmall :
    Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.AllowancesLt right.entries target
  /-- The winding box has strictly positive width and height. -/ proper : box.Proper
  /-- The winding box refines the retained box on which the perturbation budget is computed. -/ refinesBudget :
    box.Refines budgetBox
  /-- The left reading retains a positive boundary clearance on the winding box. -/ clearance :
    Clearance.Box.Boundary.Basic.BoundaryClearance left.polynomial box
  /-- The uniform perturbation budget on the retained enclosing budget box is smaller than the left clearance. -/
    budget_lt : left.refinementEvaluationBound target budgetBox < clearance.bound

constructive_injectivity CoarseStableChannelReadings

end Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Transport.Coarse

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

namespace Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Transport.Coarse.CoarseStableChannelReadings
open Purelib.Data.Gaussian
section CoarseStableChannelReadings

/-- Read the exact coefficient-difference polynomial between the two retained channel readings. -/
@[expose] def
  perturbation
    {left right : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target} {box budgetBox : Box}
    (_transfer : Dense.Gaussian.Coefficient.Progressive.Transport.Coarse.CoarseStableChannelReadings left right target
      positive box
      budgetBox) : Basic.CanonicalCoefficients.CoefficientPolynomial :=
  Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.readingPerturbation left right
end CoarseStableChannelReadings

end Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Transport.Coarse.CoarseStableChannelReadings

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

namespace Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Transport.Coarse.CoarseStableChannelReadings
open Purelib.Data.Gaussian
section CoarseStableChannelReadings

/-- The right reading's polynomial is the left polynomial plus their exact perturbation. -/
theorem
  rightPolynomial_eq_add
    {left right : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target} {box budgetBox : Box}
    (transfer : Dense.Gaussian.Coefficient.Progressive.Transport.Coarse.CoarseStableChannelReadings left right target
      positive box
      budgetBox) :
    right.polynomial = left.polynomial + transfer.perturbation :=
  (left.polynomial_add_readingPerturbation right).symm
end CoarseStableChannelReadings

end Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Transport.Coarse.CoarseStableChannelReadings

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

namespace Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Transport.Coarse.CoarseStableChannelReadings
open Purelib.Data.Gaussian
section CoarseStableChannelReadings

/-- Construct boundary dominance from the two accurate readings of the same channels.

Their common allowance target bounds the perturbation on the retained enclosing budget box, whose refinement relation
includes every winding-boundary point. -/
@[expose] def
  dominance
    {left right : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target} {box budgetBox : Box}
    (transfer : Dense.Gaussian.Coefficient.Progressive.Transport.Coarse.CoarseStableChannelReadings left right target
      positive box
      budgetBox) :
    Clearance.Box.Dominance.Basic.BoundaryNormDominance left.polynomial
      transfer.perturbation box :=
  Clearance.Box.Dominance.Uniform.boundaryNormDominanceOfUniformBound left.polynomial transfer.perturbation box
    transfer.clearance (left.refinementEvaluationBound target budgetBox)
    transfer.budget_lt (by
      intro point boundary
      have scalarBound := left.readingPerturbation_eval_le_onBox right target positive
        transfer.same transfer.leftSmall transfer.rightSmall budgetBox
        (transfer.refinesBudget.contains boundary.1)
      simpa only [Dense.Gaussian.Coefficient.Progressive.Transport.Coarse.CoarseStableChannelReadings.perturbation,
        Gaussian.Norm.Basic.normSq_eq_canonical,
        Gaussian.Basic.Canonical.normSq, pow_two] using scalarBound)
end CoarseStableChannelReadings

end Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Transport.Coarse.CoarseStableChannelReadings

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

namespace Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Transport.Coarse.CoarseStableChannelReadings
open Purelib.Data.Gaussian
section CoarseStableChannelReadings

/-- Explicit transported clearance whose numerical bound is known before the
right coefficient states are revealed. -/
@[expose] def
  explicitRightClearance
    {left right : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target} {box budgetBox : Box}
    (transfer : Dense.Gaussian.Coefficient.Progressive.Transport.Coarse.CoarseStableChannelReadings left right target
      positive box
      budgetBox) :
    Clearance.Box.Boundary.Basic.BoundaryClearance right.polynomial box where
  bound :=
    (transfer.clearance.bound -
        left.refinementEvaluationBound target budgetBox) ^ 2 /
      (4 * Dense.Gaussian.Bounds.Box.denseEvalNormMajorant
        left.polynomial box)
  positive := by
    exact Purelib.Data.Rat.Fraction.Order.Field.div_pos_direct
      (Purelib.Data.Rat.Fraction.Order.Arithmetic.pow_pos_direct
        (Purelib.Data.Rat.Fraction.Order.Arithmetic.sub_pos_direct transfer.budget_lt) 2)
      (Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_pos_direct (by decide)
        (Dense.Gaussian.Bounds.Box.denseEvalNormMajorant_pos
          left.polynomial box))
  lower := by
    intro point boundary
    rw [transfer.rightPolynomial_eq_add]
    exact
      (Purelib.Polynomial.Clearance.Box.Dominance.Majorant.boundaryClearance_add_of_dominance_with_majorant
        left.polynomial transfer.perturbation box transfer.dominance
        (Dense.Gaussian.Bounds.Box.denseEvalNormMajorant left.polynomial box)
        (Dense.Gaussian.Bounds.Box.denseEvalNormMajorant_pos left.polynomial box)
        (by
          intro z onBoundary
          simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using
            Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormMajorant
            left.polynomial onBoundary.1)).lower point boundary
end CoarseStableChannelReadings

end Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Transport.Coarse.CoarseStableChannelReadings

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

namespace Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Transport.Coarse.CoarseStableChannelReadings
open Purelib.Data.Gaussian
section CoarseStableChannelReadings

/-- Read the transported clearance as the squared remaining margin divided by four times the left polynomial's box
majorant. -/
@[simp] theorem
  explicitRightClearance_bound
    {left right : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target} {box budgetBox : Box}
    (transfer : Dense.Gaussian.Coefficient.Progressive.Transport.Coarse.CoarseStableChannelReadings left right target
      positive box
      budgetBox) :
    transfer.explicitRightClearance.bound =
      (transfer.clearance.bound -
          left.refinementEvaluationBound target budgetBox) ^ 2 /
        (4 * Dense.Gaussian.Bounds.Box.denseEvalNormMajorant
          left.polynomial box) := rfl
end CoarseStableChannelReadings

end Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Transport.Coarse.CoarseStableChannelReadings

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

namespace Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Transport.Coarse.CoarseStableChannelReadings
open Purelib.Data.Gaussian
section CoarseStableChannelReadings

/-- Two certified accurate readings of the same channels have equal raw winding on the retained box. -/
theorem
  rightWinding_eq
    {left right : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target} {box budgetBox : Box}
    (transfer : Dense.Gaussian.Coefficient.Progressive.Transport.Coarse.CoarseStableChannelReadings left right target
      positive box
      budgetBox) :
    Winding.Box.Basic.quadrupledBoxWinding right.polynomial box =
      Winding.Box.Basic.quadrupledBoxWinding left.polynomial box := by
  rw [transfer.rightPolynomial_eq_add]
  exact Winding.Box.Rouche.quadrupledBoxWinding_add_of_boundaryNormDominance
    left.polynomial transfer.perturbation box transfer.proper
      transfer.clearance transfer.dominance

end CoarseStableChannelReadings

end Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Transport.Coarse.CoarseStableChannelReadings

end
