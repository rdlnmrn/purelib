module

public import Purelib.Polynomial.Laurent.Toeplitz
public import Purelib.Polynomial.Laurent.Circle.Transport.Locations
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Actual recurrence ledgers under Laurent conjugation, reversal and adjoint

Each transformed original symbol receives its own normalized circle result
and actual recurrence boundary normal form. The fixed orientation compares
these original computations, including support changes and zero roots.
-/

public section

namespace Purelib.Polynomial.Laurent.Toeplitz.Transport

open Basic (LaurentPolynomial)
open Normalization (Normalized)
open Circle.Transport (Orientation)
open Purelib.RationalFunctions.Curve.Canonical.Circle

variable {source : LaurentPolynomial} {normalized : Normalized source}
variable {paths : Boundary.Substitutions normalized.polynomial} {clearance : Boundary.Clearance paths}

set_option genInjectivity false in
/-- The actual transformed symbol's original circle comparison and its own recurrence boundary ledger. -/
structure Comparison (original : Toeplitz.Comparison normalized paths clearance)
    (target : LaurentPolynomial) (orientation : Orientation) where
  /-- The original target normalization, complete margin, inventory and independent winding transport. -/
  circle : Circle.Transport.Comparison original.circle target orientation
  /-- The target's own actual recurrence ledger consumes that same original transformed circle result. -/
  result : Toeplitz.Comparison circle.normalized circle.paths circle.clearance
  /-- The complete target construction reuses its stored circle inventory and winding. -/
  result_eq : result = Toeplitz.Comparison.ofCircle circle.result circle.result_eq

constructive_injectivity Comparison

namespace Comparison

variable {original : Toeplitz.Comparison normalized paths clearance}
variable {target : LaurentPolynomial} {orientation : Orientation}

/-- Retain a checked actual transformed circle and complete recurrence result without replaying either producer. -/
@[expose] def ofCaches (circle : Circle.Transport.Comparison original.circle target orientation)
    (result : Toeplitz.Comparison circle.normalized circle.paths circle.clearance)
    (resultEq : result = Toeplitz.Comparison.ofCircle circle.result circle.result_eq) :
    Comparison original target orientation :=
  { circle, result, result_eq := resultEq }

/-- Construct the actual transformed recurrence ledger from one retained original circle transport. -/
@[expose] def ofTransport (circle : Circle.Transport.Comparison original.circle target orientation) :
    Comparison original target orientation :=
  let result := Toeplitz.Comparison.ofCircle circle.result circle.result_eq
  ofCaches circle result rfl

/-- Construct the actual coefficient-conjugate symbol's circle and recurrence ledger. -/
def conjugate (original : Toeplitz.Comparison normalized paths clearance) :
    Comparison original source.conjugate .preserving :=
  ofTransport (Circle.Transport.Comparison.conjugate original.circle)

/-- Construct the actual exponent-reversed symbol's circle and recurrence ledger. -/
def reverse (original : Toeplitz.Comparison normalized paths clearance) :
    Comparison original source.reverse .reversing :=
  ofTransport (Circle.Transport.Comparison.reverse original.circle)

/-- Construct the actual combined-adjoint symbol's circle and recurrence ledger. -/
def adjoint (original : Toeplitz.Comparison normalized paths clearance) :
    Comparison original source.adjoint .reversing :=
  ofTransport (Circle.Transport.Comparison.adjoint original.circle)

/-- The actual target ledger retains exactly the original transformed circle computation. -/
theorem result_circle (comparison : Comparison original target orientation) :
    comparison.result.circle = comparison.circle.result :=
  (congrArg (fun result : Toeplitz.Comparison comparison.circle.normalized
    comparison.circle.paths comparison.circle.clearance => result.circle) comparison.result_eq).trans rfl

/-- The actual recurrence boundary defect follows the original transport's fixed orientation. -/
theorem index_eq (comparison : Comparison original target orientation) :
    comparison.result.index = orientation.value * original.index := by
  rewrite [comparison.result.index_eq_neg_winding, comparison.result_circle,
    comparison.circle.winding_eq, original.index_eq_neg_winding]
  ring1

/-- Checked transformed caches recover the same actual recurrence extension of the original circle transport. -/
theorem ofCaches_eq_ofTransport (circle : Circle.Transport.Comparison original.circle target orientation)
    (result : Toeplitz.Comparison circle.normalized circle.paths circle.clearance)
    (resultEq : result = Toeplitz.Comparison.ofCircle circle.result circle.result_eq) :
    ofCaches circle result resultEq = ofTransport circle := by
  cases resultEq
  rfl

/-- Restore the same retained transformed-circle recurrence construction without reconstructing the target circle. -/
theorem restore (comparison : Comparison original target orientation) : comparison = ofTransport comparison.circle := by
  cases comparison with
  | mk circle result resultEq => exact ofCaches_eq_ofTransport circle result resultEq

end Comparison
end Purelib.Polynomial.Laurent.Toeplitz.Transport

end
