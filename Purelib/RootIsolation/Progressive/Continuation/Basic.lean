module
meta import Purelib.Elab.ConstructiveInjectivity

import Purelib.Data.Gaussian.Basic
public import Purelib.Geometry.Rational.Box.Bounds
public import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Refinement
public import Purelib.Geometry.Rational.Box.Separation
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
public import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Tactic.Ring
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic

open Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table (CoefficientTable)

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

namespace Purelib.RootIsolation.Progressive.Continuation.Basic
open Purelib.Data.Gaussian

/-! ## Repeatable coefficient/root continuation programs -/

set_option genInjectivity false in
/-- A finite, executable continuation program for all simple root owners of
one progressive monic coefficient table.  A state contains one simultaneous
coefficient reading and one rational owner box for every degree index.  The
single refinement operation advances the coefficient table and every owner
together; the laws state the numerical facts needed by the generic CCL
transducer.

This structure is the exact boundary between the quantitative chamber
argument and the arithmetic output machinery.  In particular, the
`refine_table` field prevents an implementation from silently replacing the
progressive coefficients by an unrelated sequence of rational polynomials. -/
structure RootContinuation (initialTable :
  CoefficientTable) where
  /-- The executable state type carrying a simultaneous coefficient reading and root owners. -/ State : Type
  /-- The retained initial continuation state. -/ initial : State
  /-- Read the actual coefficient table carried by each state. -/ table : State →
    CoefficientTable
  /-- The initial state carries the specified original coefficient table. -/ initial_table : table initial =
    initialTable
  /-- Every state retains the original coefficient degree. -/ table_degree : ∀ state, (table state).degree =
    initialTable.degree
  /-- The original coefficient table has degree at least two. -/ degreeAtLeastTwo : 2 ≤ initialTable.degree
  /-- Read the retained rational owner box for each state and original degree index. -/ box : State → Fin
    initialTable.degree → Box
  /-- Every retained owner box has strictly positive width and height. -/ proper : ∀ state index, (box state
    index).Proper
  /-- Each state polynomial has positive boundary clearance on every retained owner box. -/ clearance : ∀ state index,
    Clearance.Box.Boundary.Basic.BoundaryClearance
      (table state).polynomial (box state index)
  /-- Each retained owner box has raw winding four for its actual state polynomial. -/ rawWindingFour : ∀ state index,
    Winding.Box.Basic.quadrupledBoxWinding
      (table state).polynomial (box state index) = 4
  /-- Every owner box refines the corresponding original indexed owner box. -/ refinesInitial : ∀ state index,
    (box state index).Refines (box initial index)
  /-- Different original degree indices have separated owner boxes in every state. -/ pairwiseSeparated : ∀ state left
    right, left ≠ right →
    (box state left).Separated (box state right)
  /-- Compute the coefficient allowance required for a displayed refinement request. -/ coefficientTarget : State →
    Fraction.Rational → Fraction.Rational
  /-- A positive request gives a positive coefficient allowance target. -/ coefficientTarget_pos : ∀ state {epsilon}, 0
    < epsilon →
    0 < coefficientTarget state epsilon
  /-- Advance the coefficient reading and every indexed owner for a positive accuracy request. -/ refine : (state :
    State) → (epsilon : Fraction.Rational) →
    0 < epsilon → State
  /-- The next state contains exactly the original table's prescribed simultaneous refinement. -/ refine_table : ∀ state
    epsilon positive,
    table (refine state epsilon positive) =
      (table state).refine (coefficientTarget state epsilon)
        (coefficientTarget_pos state positive)
  /-- Each refined owner box refines its corresponding preceding box. -/ nested : ∀ state epsilon positive index,
    (box (refine state epsilon positive) index).Refines (box state index)
  /-- Each refined owner box lies strictly inside its corresponding preceding box. -/ strict : ∀ state epsilon positive
    index,
    (box (refine state epsilon positive) index).StrictInterior
      (box state index)
  /-- Every refined owner's squared diagonal is at most the squared requested accuracy. -/ accurate : ∀ state epsilon
    positive index,
    (box (refine state epsilon positive) index).diagonalSq ≤ epsilon ^ 2

constructive_injectivity RootContinuation

end Purelib.RootIsolation.Progressive.Continuation.Basic

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

namespace Purelib.RootIsolation.Progressive.Continuation.Basic
open Purelib.Data.Gaussian
namespace RootContinuation

open Purelib.RootIsolation in
/-- The finite degree index shared by every retained continuation state. -/
abbrev Index {initialTable :
  CoefficientTable}
    (_continuation : Progressive.Continuation.Basic.RootContinuation initialTable) :=
  Fin initialTable.degree
end RootContinuation

end Purelib.RootIsolation.Progressive.Continuation.Basic

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

namespace Purelib.RootIsolation.Progressive.Continuation.Basic
open Purelib.Data.Gaussian
namespace RootContinuation

open Purelib.RootIsolation in
/-- The initial coefficient table has positive degree. -/
theorem degreePositive
    {initialTable : CoefficientTable}
    (continuation : Progressive.Continuation.Basic.RootContinuation initialTable) :
    0 < initialTable.degree :=
  (by decide : (0 : Nat) < 2).trans_le continuation.degreeAtLeastTwo
end RootContinuation

end Purelib.RootIsolation.Progressive.Continuation.Basic

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

namespace Purelib.RootIsolation.Progressive.Continuation.Basic
open Purelib.Data.Gaussian
namespace RootContinuation

open Purelib.RootIsolation in
/-- Every state's polynomial retains degree at least two. -/
theorem polynomialDegreeAtLeastTwo
    {initialTable : CoefficientTable}
    (continuation : Progressive.Continuation.Basic.RootContinuation initialTable)
    (state : continuation.State) :
    2 ≤ (continuation.table state).polynomial.natDegree := by
  rw [(continuation.table state).polynomial_natDegree,
    continuation.table_degree state]
  exact continuation.degreeAtLeastTwo
end RootContinuation

end Purelib.RootIsolation.Progressive.Continuation.Basic

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

namespace Purelib.RootIsolation.Progressive.Continuation.Basic
open Purelib.Data.Gaussian
namespace RootContinuation

open Purelib.RootIsolation in
/-- Every state's polynomial retains positive degree. -/
theorem polynomialDegreePositive
    {initialTable : CoefficientTable}
    (continuation : Progressive.Continuation.Basic.RootContinuation initialTable)
    (state : continuation.State) :
    0 < (continuation.table state).polynomial.natDegree := by
  rw [(continuation.table state).polynomial_natDegree,
    continuation.table_degree state]
  exact continuation.degreePositive
end RootContinuation

end Purelib.RootIsolation.Progressive.Continuation.Basic

end
