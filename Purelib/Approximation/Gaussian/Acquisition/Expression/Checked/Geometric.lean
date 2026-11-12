module

public import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Construction
public import Purelib.Approximation.Gaussian.Geometric.Preparation
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Acquisition.Annotated.Basic
import Purelib.Approximation.Gaussian.Provenance.Algebraic
import Purelib.Polynomial.Approximation.Gaussian.Residual.Reciprocal
import Purelib.Data.Gaussian.Norm.Basic
meta import Purelib.Elab.ConstructiveInjectivity

public section

namespace Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Geometric

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Geometric
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Polynomial.Approximation.Gaussian
open Purelib.Data.Gaussian.Norm
open Purelib.Data.Rat.Fraction (Rational)

variable {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}

set_option genInjectivity false in
/-- A checked reciprocal retaining its actual geometric payment and original algebraic denominator.

The geometric program is operationally compared with the unchanged original
child channel. Its all-index lower quadrance pays an actual observation; the
reciprocal then consumes the original residual, not the geometric sample stream.
-/
structure Inverse (child : Completed environment expression) where
  /-- The actual retained geometric sample program of the denominator. -/
  source : GeometricApproximation
  /-- The original numerical child agrees operationally with this sample program. -/
  equivalent : NamedEquivalent child.channel.name source.toApproximation.toNamed
  /-- The retained original starting state of this same sample program. -/
  initial : Preparation.State source
  /-- The retained positive all-index sample lower quadrance. -/
  lowerSq : Rational
  /-- The lower quadrance is strictly positive. -/
  positive : 0 < lowerSq
  /-- Every actual source sample satisfies the retained lower quadrance. -/
  lower : ∀ index, lowerSq ≤ Basic.normSq (source.sample index)
  /-- The actual computed payment, observation and original-channel preparation. -/
  paid : Preparation.Paid source child.channel equivalent initial lowerSq
  /-- The retained payment is exactly the original lower-bound preparation. -/
  paid_eq : paid = Preparation.fromLower source child.channel equivalent initial lowerSq positive lower
  /-- The cached reciprocal consumes the exact original child residual. -/
  cache : Residual.Reciprocal child.sidecar.residual paid.prepared
  /-- The cached reciprocal is the original preparation-directed construction. -/
  cache_eq : cache = Residual.Reciprocal.ofPrepared child.sidecar.residual paid.prepared
  /-- The actual result sidecar retains the original denominator and reciprocal cache. -/
  result : Algebraic.Sidecar (paid.prepared.quotient (CoherentNamed.Coherence.exact 1))
  /-- The result consumes exactly the retained original reciprocal cache. -/
  result_eq : result = child.sidecar.reciprocalFromCache cache
  /-- The complete original checked inverse, including its original child. -/
  completed : Completed environment (.inverse expression)
  /-- The checked inverse consumes exactly the same payment, residual cache and result. -/
  completed_eq : completed = child.inverse paid.prepared cache result result_eq

constructive_injectivity Inverse

/-- Pay the actual geometric observation and construct a reciprocal of the unchanged original checked child.

The bound is a mathematical input to this constructor. Spatial clients derive
it from their retained enclosures; it is not an input to admitted-fragment
completion. Every downstream constructor consumes the once stored caches.
-/
@[expose] def fromLower (child : Completed environment expression) (source : GeometricApproximation)
    (equivalent : NamedEquivalent child.channel.name source.toApproximation.toNamed)
    (initial : Preparation.State source) (lowerSq : Rational) (positive : 0 < lowerSq)
    (lower : ∀ index, lowerSq ≤ Basic.normSq (source.sample index)) : Inverse child :=
  let paid := Preparation.fromLower source child.channel equivalent initial lowerSq positive lower
  let cache := Residual.Reciprocal.ofPrepared child.sidecar.residual paid.prepared
  let result := child.sidecar.reciprocalFromCache cache
  let completed := child.inverse paid.prepared cache result rfl
  ⟨source, equivalent, initial, lowerSq, positive, lower, paid, rfl, cache, rfl, result, rfl, completed, rfl⟩

/-- The complete reciprocal output uses the quotient channel of its exact retained payment. -/
theorem Inverse.channel {child : Completed environment expression} (inverse : Inverse child) :
    inverse.completed.channel = inverse.paid.prepared.quotient (CoherentNamed.Coherence.exact 1) := by
  rewrite [inverse.completed_eq]
  rfl

/-- The complete reciprocal output retains the same result sidecar and its actual original-child cache. -/
theorem Inverse.sidecar {child : Completed environment expression} (inverse : Inverse child) :
    inverse.completed.sidecar = inverse.channel.symm ▸ inverse.result := by
  cases inverse with
  | mk source equivalent initial lowerSq positive lower paid paidEq cache cacheEq result resultEq
      completed completedEq =>
      cases completedEq
      rfl

end Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Geometric

end
