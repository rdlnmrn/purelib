module

public import Purelib.Polynomial.Laurent.Toeplitz
public import Purelib.Polynomial.Laurent.Circle.Product
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Additivity of actual Laurent recurrence boundary ledgers

The normalized product receives its own original inventory, winding and
recurrence normal form. Both original input comparisons remain indices;
the signed additivity law compares the three actually constructed ledgers.
-/

public section

namespace Purelib.Polynomial.Laurent.Toeplitz.Product

open Basic (LaurentPolynomial)
open Normalization (Normalized)
open Purelib.RationalFunctions.Curve.Canonical.Circle

variable {left right : LaurentPolynomial} {leftResult : Normalized left} {rightResult : Normalized right}
variable {leftPaths : Boundary.Substitutions leftResult.polynomial}
variable {rightPaths : Boundary.Substitutions rightResult.polynomial}
variable {leftClearance : Boundary.Clearance leftPaths} {rightClearance : Boundary.Clearance rightPaths}

set_option genInjectivity false in
/-- The actual product circle comparison and the recurrence ledger built from that same cached product inventory. -/
structure Comparison (product : Arithmetic.Product left right)
    (first : Toeplitz.Comparison leftResult leftPaths leftClearance)
    (second : Toeplitz.Comparison rightResult rightPaths rightClearance) where
  /-- The actual normalized original product and its independent winding and complete inventory. -/
  circle : Circle.Product.Comparison product first.circle second.circle
  /-- The complete product comparison is the original constructor on the same retained input comparisons. -/
  circle_eq : circle = Circle.Product.Comparison.prepare product first.circle second.circle
  /-- The actual product recurrence boundary ledger reuses this same computed product circle comparison. -/
  result : Toeplitz.Comparison circle.normalized circle.paths circle.clearance
  /-- The complete product ledger consumes the retained circle without replaying its inventory or winding. -/
  result_eq : result = Toeplitz.Comparison.ofCircle circle.result circle.result_eq

constructive_injectivity Comparison

namespace Comparison

variable {product : Arithmetic.Product left right}
variable {first : Toeplitz.Comparison leftResult leftPaths leftClearance}
variable {second : Toeplitz.Comparison rightResult rightPaths rightClearance}

/-- Retain checked original product-circle and actual recurrence caches without rerunning either producer. -/
@[expose] def ofCaches (circle : Circle.Product.Comparison product first.circle second.circle)
    (circleEq : circle = Circle.Product.Comparison.prepare product first.circle second.circle)
    (result : Toeplitz.Comparison circle.normalized circle.paths circle.clearance)
    (resultEq : result = Toeplitz.Comparison.ofCircle circle.result circle.result_eq) :
    Comparison product first second :=
  { circle, circle_eq := circleEq, result, result_eq := resultEq }

/-- Build the actual product comparison and its own recurrence ledger from the same retained input margins. -/
@[expose] def prepare (product : Arithmetic.Product left right)
    (first : Toeplitz.Comparison leftResult leftPaths leftClearance)
    (second : Toeplitz.Comparison rightResult rightPaths rightClearance) : Comparison product first second :=
  let circle := Circle.Product.Comparison.prepare product first.circle second.circle
  let result := Toeplitz.Comparison.ofCircle circle.result circle.result_eq
  ofCaches circle rfl result rfl

/-- The product recurrence result retains exactly the original cached product circle comparison. -/
theorem result_circle (comparison : Comparison product first second) :
    comparison.result.circle = comparison.circle.result :=
  (congrArg (fun result : Toeplitz.Comparison comparison.circle.normalized
    comparison.circle.paths comparison.circle.clearance => result.circle) comparison.result_eq).trans rfl

/-- Actual complementary-target minus kernel coordinates add on the actual normalized product. -/
theorem index_add (comparison : Comparison product first second) :
    comparison.result.index = first.index + second.index := by
  rewrite [comparison.result.index_eq_neg_winding, comparison.result_circle,
    comparison.circle.winding_add, first.index_eq_neg_winding, second.index_eq_neg_winding]
  ring1

/-- Checked complete original product caches recover the same automatic comparison. -/
theorem ofCaches_eq_prepare (circle : Circle.Product.Comparison product first.circle second.circle)
    (circleEq : circle = Circle.Product.Comparison.prepare product first.circle second.circle)
    (result : Toeplitz.Comparison circle.normalized circle.paths circle.clearance)
    (resultEq : result = Toeplitz.Comparison.ofCircle circle.result circle.result_eq) :
    ofCaches circle circleEq result resultEq = prepare product first second := by
  cases circleEq
  cases resultEq
  rfl

/-- The complete retained product result restores its same automatic construction. -/
theorem restore (comparison : Comparison product first second) : comparison = prepare product first second := by
  cases comparison with
  | mk circle circleEq result resultEq => exact ofCaches_eq_prepare circle circleEq result resultEq

end Comparison
end Purelib.Polynomial.Laurent.Toeplitz.Product

end
