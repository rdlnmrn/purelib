module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.RootIsolation.Progressive.Chamber.Basic
public import Purelib.RootIsolation.Progressive.Closure.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.Tactic.Ring
import Purelib.RootIsolation.Progressive.Continuation.Residual
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Evaluation
import Purelib.RootIsolation.Progressive.Continuation.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table (CoefficientTable)
open Purelib.RootIsolation.Progressive.Chamber.Basic (SimpleRootChamber)

open Purelib.Data

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

namespace Purelib.RootIsolation.Progressive.Closure.Basic
open Purelib.Data.Gaussian
namespace EffectiveAlgebraicClosure

/-- A pairwise-separated reference-polynomial family cannot contain one more track than the reference degree. -/
theorem no_degree_succ_reference_family
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (closure : Progressive.Closure.Basic.EffectiveAlgebraicClosure chamber)
    (family : Fin (reference.degree + 1) →
      Track.Basic.WindingOneTrack reference.polynomial
        (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox reference.polynomial))
    (pairwise : ∀ left right, left ≠ right →
      (family left).initial.box.Separated (family right).initial.box) : False := by
  have impossible := closure.referenceMaximality family pairwise
  omega

end EffectiveAlgebraicClosure

end Purelib.RootIsolation.Progressive.Closure.Basic

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

namespace Purelib.RootIsolation.Progressive.Closure.Basic
open Purelib.Data.Gaussian
namespace EffectiveAlgebraicClosure

/-- The refined owner's anchor residual is bounded by its original-box Lipschitz coefficient times the requested
tolerance squared. -/
theorem refined_anchor_residual_le
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (closure : Progressive.Closure.Basic.EffectiveAlgebraicClosure chamber)
    (history : closure.continuation.State) (index : Fin reference.degree)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    let next := closure.continuation.refine history epsilon positive
    Data.Gaussian.Norm.Basic.normSq
        ((closure.continuation.table next).polynomial.eval
          (closure.continuation.box next index).anchor) ≤
      Dense.Gaussian.Bounds.Box.denseLipschitzBound
          (closure.continuation.table next).polynomial
          (closure.continuation.box closure.continuation.initial index) *
        epsilon ^ 2 :=
  closure.continuation.refinedAnchorResidual_le_requested history index epsilon
    positive
end EffectiveAlgebraicClosure

end Purelib.RootIsolation.Progressive.Closure.Basic

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

namespace Purelib.RootIsolation.Progressive.Closure.Basic
open Purelib.Data.Gaussian
namespace EffectiveAlgebraicClosure

/-- Every refined owner box has squared diagonal at most the requested tolerance squared. -/
theorem refined_boxes_accurate
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (closure : Progressive.Closure.Basic.EffectiveAlgebraicClosure chamber)
    (history : closure.continuation.State) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (index : Fin reference.degree) :
    (closure.continuation.box
      (closure.continuation.refine history epsilon positive) index).diagonalSq ≤
        epsilon ^ 2 :=
  closure.continuation.accurate history epsilon positive index
end EffectiveAlgebraicClosure

end Purelib.RootIsolation.Progressive.Closure.Basic

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

namespace Purelib.RootIsolation.Progressive.Closure.Basic
open Purelib.Data.Gaussian
namespace EffectiveAlgebraicClosure

/-- Distinct original owner indices retain pairwise-separated boxes after refinement. -/
theorem refined_boxes_pairwiseSeparated
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (closure : Progressive.Closure.Basic.EffectiveAlgebraicClosure chamber)
    (history : closure.continuation.State) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (left right : Fin reference.degree)
    (different : left ≠ right) :
    (closure.continuation.box
        (closure.continuation.refine history epsilon positive) left).Separated
      (closure.continuation.box
        (closure.continuation.refine history epsilon positive) right) :=
  closure.continuation.pairwiseSeparated
    (closure.continuation.refine history epsilon positive) left right different
end EffectiveAlgebraicClosure

end Purelib.RootIsolation.Progressive.Closure.Basic

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

namespace Purelib.RootIsolation.Progressive.Closure.Basic
open Purelib.Data.Gaussian
namespace EffectiveAlgebraicClosure

/-- Each refined owner box lies strictly inside its own preceding box. -/
theorem refined_boxes_strict
    {reference : CoefficientTable} {chamber :
      SimpleRootChamber reference}
    (closure : Progressive.Closure.Basic.EffectiveAlgebraicClosure chamber)
    (history : closure.continuation.State) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (index : Fin reference.degree) :
    (closure.continuation.box
        (closure.continuation.refine history epsilon positive) index).StrictInterior
      (closure.continuation.box history index) :=
  closure.continuation.strict history epsilon positive index
end EffectiveAlgebraicClosure

end Purelib.RootIsolation.Progressive.Closure.Basic

end
