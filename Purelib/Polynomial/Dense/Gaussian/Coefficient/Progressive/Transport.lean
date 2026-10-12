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
public import Purelib.Polynomial.Clearance.Box.Dominance.Sum
import Purelib.Polynomial.Clearance.Box.Dominance.Uniform
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

namespace Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Transport
open Purelib.Data.Gaussian

/-! ## Uniform transport between arbitrary accurate channel readings -/

set_option genInjectivity false in
/-- A root owner guarded against every other reading of the same channels
whose displayed allowances meet the common target. -/
structure StableChannelReadings
    (left right : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable) (target : Fraction.Rational)
    (positive : 0 < target) (box : Box) where
  /-- The two retained coefficient lists read the same original process channels. -/ same :
    Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.SameChannels left.entries right.entries
  /-- Every allowance in the left reading is below the common positive target. -/ leftSmall :
    Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.AllowancesLt left.entries target
  /-- Every allowance in the right reading is below the common positive target. -/ rightSmall :
    Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.AllowancesLt right.entries target
  /-- The winding box has strictly positive width and height. -/ proper : box.Proper
  /-- The left reading retains a positive boundary clearance on the winding box. -/ clearance :
    Clearance.Box.Boundary.Basic.BoundaryClearance left.polynomial box
  /-- The uniform perturbation budget on the winding box is smaller than the left clearance. -/ budget_lt :
    left.refinementEvaluationBound target box < clearance.bound

constructive_injectivity StableChannelReadings

end Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Transport

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

namespace Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Transport.StableChannelReadings
open Purelib.Data.Gaussian
section StableChannelReadings

/-- Read the exact coefficient-difference polynomial between the two retained channel readings. -/
@[expose] def
  perturbation
    {left right : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target} {box : Box}
    (_transfer : Dense.Gaussian.Coefficient.Progressive.Transport.StableChannelReadings left right target positive box)
      :
    Basic.CanonicalCoefficients.CoefficientPolynomial :=
  Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.readingPerturbation left right
end StableChannelReadings

end Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Transport.StableChannelReadings

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

namespace Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Transport.StableChannelReadings
open Purelib.Data.Gaussian
section StableChannelReadings

/-- The right reading's polynomial is the left polynomial plus their exact perturbation. -/
theorem
  rightPolynomial_eq_add
    {left right : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target} {box : Box}
    (transfer : Dense.Gaussian.Coefficient.Progressive.Transport.StableChannelReadings left right target positive box) :
    right.polynomial = left.polynomial + transfer.perturbation :=
  (left.polynomial_add_readingPerturbation right).symm
end StableChannelReadings

end Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Transport.StableChannelReadings

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

namespace Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Transport.StableChannelReadings
open Purelib.Data.Gaussian
section StableChannelReadings

/-- Construct boundary dominance from the two accurate readings of the same channels.

Their common allowance target bounds the perturbation on the winding box against the left reading's retained clearance.
-/
@[expose] def dominance
    {left right : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target} {box : Box}
    (transfer : Dense.Gaussian.Coefficient.Progressive.Transport.StableChannelReadings left right target positive box) :
    Clearance.Box.Dominance.Basic.BoundaryNormDominance left.polynomial
      transfer.perturbation box :=
  Clearance.Box.Dominance.Uniform.boundaryNormDominanceOfUniformBound left.polynomial transfer.perturbation box
    transfer.clearance (left.refinementEvaluationBound target box)
    transfer.budget_lt (by
      intro point boundary
      have scalarBound := left.readingPerturbation_eval_le_onBox right target positive
        transfer.same transfer.leftSmall transfer.rightSmall box boundary.1
      simpa only [Dense.Gaussian.Coefficient.Progressive.Transport.StableChannelReadings.perturbation,
        Gaussian.Norm.Basic.normSq_eq_canonical,
        Gaussian.Basic.Canonical.normSq, pow_two] using scalarBound)
end StableChannelReadings

end Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Transport.StableChannelReadings

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

namespace Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Transport.StableChannelReadings
open Purelib.Data.Gaussian
section StableChannelReadings

/-- The transported clearance with a bound determined entirely by the left
reading, its displayed clearance, the common allowance target, and the box.
Unlike the general homotopy clearance, this formula is available before the
right process states are revealed. -/
@[expose] def
  explicitRightClearance
    {left right : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target} {box : Box}
    (transfer : Dense.Gaussian.Coefficient.Progressive.Transport.StableChannelReadings left right target positive box) :
    Clearance.Box.Boundary.Basic.BoundaryClearance right.polynomial box where
  bound :=
    (transfer.clearance.bound -
        left.refinementEvaluationBound target box) ^ 2 /
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
end StableChannelReadings

end Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Transport.StableChannelReadings

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

namespace Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Transport.StableChannelReadings
open Purelib.Data.Gaussian
section StableChannelReadings

/-- Read the transported clearance as the squared remaining margin divided by four times the left polynomial's box
majorant. -/
@[simp] theorem
  explicitRightClearance_bound
    {left right : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target} {box : Box}
    (transfer : Dense.Gaussian.Coefficient.Progressive.Transport.StableChannelReadings left right target positive box) :
    transfer.explicitRightClearance.bound =
      (transfer.clearance.bound -
          left.refinementEvaluationBound target box) ^ 2 /
        (4 * Dense.Gaussian.Bounds.Box.denseEvalNormMajorant
          left.polynomial box) := by
  rfl
end StableChannelReadings

end Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Transport.StableChannelReadings

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

namespace Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Transport.StableChannelReadings
open Purelib.Data.Gaussian
section StableChannelReadings

/-- Transport the left reading's boundary clearance to the right polynomial.

The retained dominance certificate gives a positive clearance for their exact polynomial sum. -/
@[expose] def
  rightClearance
    {left right : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target} {box : Box}
    (transfer : Dense.Gaussian.Coefficient.Progressive.Transport.StableChannelReadings left right target positive box) :
    Clearance.Box.Boundary.Basic.BoundaryClearance right.polynomial box := by
  rw [transfer.rightPolynomial_eq_add]
  exact Clearance.Box.Dominance.Sum.boundaryClearance_add_of_boundaryNormDominance
    left.polynomial transfer.perturbation box transfer.proper
      transfer.dominance
end StableChannelReadings

end Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Transport.StableChannelReadings

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

namespace Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Transport.StableChannelReadings
open Purelib.Data.Gaussian
section StableChannelReadings

/-- Two certified accurate readings of the same channels have equal raw winding on the retained box. -/
theorem rightWinding_eq
    {left right : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target} {box : Box}
    (transfer : Dense.Gaussian.Coefficient.Progressive.Transport.StableChannelReadings left right target positive box) :
    Winding.Box.Basic.quadrupledBoxWinding right.polynomial box =
      Winding.Box.Basic.quadrupledBoxWinding left.polynomial box := by
  rw [transfer.rightPolynomial_eq_add]
  exact Winding.Box.Rouche.quadrupledBoxWinding_add_of_boundaryNormDominance
    left.polynomial transfer.perturbation box transfer.proper
      transfer.clearance transfer.dominance

end StableChannelReadings

end Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Transport.StableChannelReadings

end
