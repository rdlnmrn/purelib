module

public import Purelib.Polynomial.Laurent.Circle
public import Purelib.RootIsolation.Multiplicity.Circle.Recurrence
public import Purelib.RootIsolation.Multiplicity.Circle.Roots.Recurrence.Observation
public import Purelib.RootIsolation.Multiplicity.Circle.Roots.Recurrence.Combination
public import Purelib.RootIsolation.Multiplicity.Circle.Roots.Recurrence.Recovery
public import Purelib.RootIsolation.Multiplicity.Circle.Roots.Recurrence.Selection
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Original Laurent symbols and their actual recurrence boundary index

The original complete polynomial inventory and independent quotient winding
remain cached in the circle comparison. Its same inventory and sufficient
argument data construct the constant or positive recurrence ledger once.
The returned integer reads that ledger's actual boundary normal form.
-/

public section

namespace Purelib.Polynomial.Laurent.Toeplitz

open Basic (LaurentPolynomial)
open Normalization (Normalized)
open Purelib.RationalFunctions.Curve.Canonical.Circle
open Purelib.RootIsolation.Multiplicity.Circle renaming Recurrence → RootRecurrence

namespace Comparison

/-- The actual recurrence-owner type for this same retained original circle comparison. -/
@[expose] def Ledger {source : LaurentPolynomial} {normalized : Normalized source}
    {paths : Boundary.Substitutions normalized.polynomial} {clearance : Boundary.Clearance paths}
    (circle : Circle.Comparison normalized paths clearance) : Type 1 :=
  RootRecurrence circle.polynomial.inventory circle.polynomial.argument normalized.poleOrder

/-- Construct the actual ledger from the same circle caches and the source-derived positive-pole constant unit. -/
@[expose] def prepareLedger {source : LaurentPolynomial} {normalized : Normalized source}
    {paths : Boundary.Substitutions normalized.polynomial} {clearance : Boundary.Clearance paths}
    (circle : Circle.Comparison normalized paths clearance) : Ledger circle :=
  RootRecurrence.prepare circle.polynomial.inventory circle.polynomial.argument normalized.poleOrder
    normalized.polynomial_eval_zero_nonzero

end Comparison

set_option genInjectivity false in
/-- An original normalized Laurent symbol's independent winding and actual recurrence boundary ledger.

The same original inventory supplies the argument data, formal characteristic
modes and geometrically selected boundary. Complete producer equalities retain
the actual cached constructions. No roots, rank, basis, sufficient search
budget or index identity are caller inputs.
-/
structure Comparison {source : LaurentPolynomial} (normalized : Normalized source)
    (paths : Boundary.Substitutions normalized.polynomial) (clearance : Boundary.Clearance paths) where
  /-- The retained original inventory and independently computed quotient winding. -/
  circle : Circle.Comparison normalized paths clearance
  /-- The circle comparison is the original automatic constructor on these exact inputs. -/
  circle_eq : circle = Circle.Comparison.prepare normalized paths clearance
  /-- The actual recurrence ledger consumes this same retained circle inventory and argument data. -/
  recurrence : Comparison.Ledger circle
  /-- The complete ledger is the same automatic recurrence construction from the cached circle. -/
  recurrence_eq : recurrence = Comparison.prepareLedger circle

constructive_injectivity Comparison

namespace Comparison

variable {source : LaurentPolynomial} {normalized : Normalized source}
variable {paths : Boundary.Substitutions normalized.polynomial} {clearance : Boundary.Clearance paths}

/-- Retain checked complete original circle and recurrence caches without rerunning either producer. -/
@[expose] def ofCaches (circle : Circle.Comparison normalized paths clearance)
    (circleEq : circle = Circle.Comparison.prepare normalized paths clearance)
    (recurrence : Ledger circle) (recurrenceEq : recurrence = prepareLedger circle) :
    Comparison normalized paths clearance :=
  { circle, circle_eq := circleEq, recurrence, recurrence_eq := recurrenceEq }

/-- Add the actual recurrence ledger to one already retained original circle comparison. -/
@[expose] def ofCircle (circle : Circle.Comparison normalized paths clearance)
    (circleEq : circle = Circle.Comparison.prepare normalized paths clearance) :
    Comparison normalized paths clearance :=
  let recurrence := prepareLedger circle
  ofCaches circle circleEq recurrence rfl

/-- Construct the original scalar index comparison from the normalized symbol and finite boundary certificate. -/
@[expose] def prepare (normalized : Normalized source) (paths : Boundary.Substitutions normalized.polynomial)
    (clearance : Boundary.Clearance paths) : Comparison normalized paths clearance :=
  let circle := Circle.Comparison.prepare normalized paths clearance
  ofCircle circle rfl

/-- Read the signed index from the actual retained recurrence boundary normal form. -/
@[expose] def index (comparison : Comparison normalized paths clearance) : Int :=
  RootRecurrence.defect comparison.recurrence

/-- The actual recurrence defect equals the minimal pole order minus independently counted inside multiplicity. -/
theorem index_eq (comparison : Comparison normalized paths clearance) :
    comparison.index = (normalized.poleOrder : Int) - (comparison.circle.polynomial.inventory.insideCount : Int) :=
  RootRecurrence.defect_eq comparison.recurrence

/-- The actual recurrence boundary index is the negative of the independent original Laurent winding. -/
theorem index_eq_neg_winding (comparison : Comparison normalized paths clearance) :
    comparison.index = -comparison.circle.reading.winding :=
  comparison.index_eq.trans comparison.circle.index_eq_neg_winding

/-- Checked complete original caches recover the same automatic scalar comparison. -/
theorem ofCaches_eq_prepare (circle : Circle.Comparison normalized paths clearance)
    (circleEq : circle = Circle.Comparison.prepare normalized paths clearance)
    (recurrence : Ledger circle) (recurrenceEq : recurrence = prepareLedger circle) :
    ofCaches circle circleEq recurrence recurrenceEq = prepare normalized paths clearance := by
  cases circleEq
  cases recurrenceEq
  rfl

/-- The complete retained comparison restores its original automatic construction. -/
theorem restore (comparison : Comparison normalized paths clearance) :
    comparison = prepare normalized paths clearance := by
  cases comparison with
  | mk circle circleEq recurrence recurrenceEq => exact ofCaches_eq_prepare circle circleEq recurrence recurrenceEq

end Comparison
end Purelib.Polynomial.Laurent.Toeplitz

end
