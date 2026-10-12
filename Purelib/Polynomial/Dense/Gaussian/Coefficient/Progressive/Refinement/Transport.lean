module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Perturbation
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Refinement
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Bounds

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Dominance.Basic
public import Purelib.Polynomial.Clearance.Box.Dominance.Sum
import Purelib.Polynomial.Clearance.Box.Dominance.Uniform
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Relation
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
public import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Rouche
import Purelib.Tactic.Ring
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
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

namespace Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Refinement.Transport
open Purelib.Data.Gaussian

/-! ## One certified progressive-coefficient continuation step -/

set_option genInjectivity false in
/-- Sufficient finite data for transporting one winding box through one
simultaneous coefficient refinement. -/
structure StableRefinement
    (table : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable) (target : Fraction.Rational)
    (positive : 0 < target) (box : Box) where
  /-- Every retained current coefficient allowance is smaller than the common refinement target. -/ currentSmall :
    Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.AllowancesLt table.entries target
  /-- The retained winding box has strictly positive width and height. -/ proper : box.Proper
  /-- The current table's polynomial has the retained positive boundary clearance. -/ clearance :
    Clearance.Box.Boundary.Basic.BoundaryClearance table.polynomial box
  /-- The computed refinement evaluation budget is strictly smaller than the retained clearance. -/ budget_lt :
    table.refinementEvaluationBound target box < clearance.bound

constructive_injectivity StableRefinement

end Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Refinement.Transport

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

namespace Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Refinement.Transport.StableRefinement
open Purelib.Data.Gaussian
section StableRefinement

/-- Refine all retained coefficient channels to the displayed positive target. -/
@[expose] def
  nextTable
    {table : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target} {box : Box}
    (_step : Dense.Gaussian.Coefficient.Progressive.Refinement.Transport.StableRefinement table target positive box) :
      Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable :=
  table.refine target positive
end StableRefinement

end Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Refinement.Transport.StableRefinement

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

namespace Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Refinement.Transport.StableRefinement
open Purelib.Data.Gaussian
section StableRefinement

/-- Read the polynomial difference produced by simultaneous coefficient refinement. -/
@[expose] def
  perturbation
    {table : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target} {box : Box}
    (_step : Dense.Gaussian.Coefficient.Progressive.Refinement.Transport.StableRefinement table target positive box) :
      Basic.CanonicalCoefficients.CoefficientPolynomial :=
  table.refinementPerturbation target positive
end StableRefinement

end Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Refinement.Transport.StableRefinement

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

namespace Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Refinement.Transport.StableRefinement
open Purelib.Data.Gaussian
section StableRefinement

/-- The refined polynomial is the original polynomial plus its exact refinement perturbation. -/
theorem
  polynomial_eq_add
    {table : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target} {box : Box}
    (step : Dense.Gaussian.Coefficient.Progressive.Refinement.Transport.StableRefinement table target positive box) :
    step.nextTable.polynomial = table.polynomial + step.perturbation := by
  exact (table.polynomial_add_refinementPerturbation target positive).symm
end StableRefinement

end Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Refinement.Transport.StableRefinement

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

namespace Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Refinement.Transport.StableRefinement
open Purelib.Data.Gaussian
section StableRefinement

/-- Construct boundary dominance for the simultaneous coefficient refinement.

The uniform evaluation budget and current coefficient allowances certify the perturbation against the original retained
clearance. -/
@[expose] def
  dominance
    {table : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target} {box : Box}
    (step : Dense.Gaussian.Coefficient.Progressive.Refinement.Transport.StableRefinement table target positive box) :
    Clearance.Box.Dominance.Basic.BoundaryNormDominance table.polynomial
      step.perturbation box :=
  Clearance.Box.Dominance.Uniform.boundaryNormDominanceOfUniformBound table.polynomial step.perturbation box
    step.clearance (table.refinementEvaluationBound target box)
    step.budget_lt (by
      intro point boundary
      have scalarBound := table.refinementPerturbation_eval_le_onBox target positive
        step.currentSmall box boundary.1
      simpa only [Dense.Gaussian.Coefficient.Progressive.Refinement.Transport.StableRefinement.perturbation,
        Gaussian.Norm.Basic.normSq_eq_canonical,
        Gaussian.Basic.Canonical.normSq, pow_two] using scalarBound)
end StableRefinement

end Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Refinement.Transport.StableRefinement

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

namespace Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Refinement.Transport.StableRefinement
open Purelib.Data.Gaussian
section StableRefinement

/-- The refined monic polynomial has a computed positive clearance on the
same rational box. -/
@[expose] def
  nextClearance
    {table : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target} {box : Box}
    (step : Dense.Gaussian.Coefficient.Progressive.Refinement.Transport.StableRefinement table target positive box) :
    Clearance.Box.Boundary.Basic.BoundaryClearance step.nextTable.polynomial box := by
  rw [step.polynomial_eq_add]
  exact Clearance.Box.Dominance.Sum.boundaryClearance_add_of_boundaryNormDominance
    table.polynomial step.perturbation box step.proper step.dominance
end StableRefinement

end Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Refinement.Transport.StableRefinement

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

namespace Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Refinement.Transport.StableRefinement
open Purelib.Data.Gaussian
section StableRefinement

/-- Simultaneous coefficient refinement preserves the retained table degree. -/
@[simp] theorem
  next_degree
    {table : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target} {box : Box}
    (step : Dense.Gaussian.Coefficient.Progressive.Refinement.Transport.StableRefinement table target positive box) :
    step.nextTable.degree = table.degree :=
  table.refine_degree target positive

end StableRefinement

end Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Refinement.Transport.StableRefinement

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

namespace Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Refinement.Transport.StableRefinement
open Purelib.Data.Gaussian
section StableRefinement

/-- Exact winding is retained by the newly read progressive polynomial. -/
theorem
  next_winding_eq
    {table : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target} {box : Box}
    (step : Dense.Gaussian.Coefficient.Progressive.Refinement.Transport.StableRefinement table target positive box) :
    Winding.Box.Basic.quadrupledBoxWinding step.nextTable.polynomial box =
      Winding.Box.Basic.quadrupledBoxWinding table.polynomial box := by
  rw [step.polynomial_eq_add]
  exact Winding.Box.Rouche.quadrupledBoxWinding_add_of_boundaryNormDominance
    table.polynomial step.perturbation box step.proper step.clearance
      step.dominance
end StableRefinement

end Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Refinement.Transport.StableRefinement

end
