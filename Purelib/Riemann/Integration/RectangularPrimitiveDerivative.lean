module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns

import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Polynomial.Dense.Derivative
import Purelib.Topology.Grid.Signs
public import Purelib.Riemann.Normalization.InverseModelPrimitiveBounds
public import Purelib.Riemann.Integration.RectangularSharedPrimitives
public import Purelib.Data.Vector.Dependent
import Purelib.Tactic.Ring
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Polynomial.Dense.Gaussian.Primitive.DerivativeBound

open Purelib.Riemann.Normalization.InverseRootPolynomial

@[expose] public section

/-!
# Fixed Taylor bounds for the actual oriented rectangular primitive banks

The original models determine derivative ceilings before any Newton index
or fine spatial mesh is chosen. Arbitrary retained gauge signs preserve
these bounds. They apply to the supplied primitive data, not to a newly
integrated replacement polynomial.
-/

namespace Purelib.Riemann.Integration.RectangularPrimitiveDerivative

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Polynomial.Dense.Derivative (derivative)
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance PrimitiveOverlapBounds)
open Purelib.Riemann.Normalization.InverseModelDerivativeBounds (DerivativeBounds)
open Purelib.Riemann.Normalization.InverseModelPrimitiveBounds (PrimitiveDerivativeBounds)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank Transitions)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (ModelTriangle OwnedTriangulation)
open Purelib.Riemann.Branches.RectangularSheetGauge (signedValue)

section
open Purelib.Algebra
/-- A finite sum of nonnegative rational values is nonnegative. -/
private theorem sum_nonnegative {count : Nat} (values : Fin count → Coordinate) (nonnegative : ∀ index, 0 ≤ values
  index) :
    0 ≤ FiniteSum.Fin.sumFin values := by
  have estimate := FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ => 0) values nonnegative
  simpa only [FiniteSum.Fin.sumFin_zero] using estimate

/-- Each nonnegative rational entry is bounded by the finite sum. -/
private theorem entry_le_sum {count : Nat} (values : Fin count → Coordinate)
    (nonnegative : ∀ index, 0 ≤ values index) (index : Fin count) : values index ≤ FiniteSum.Fin.sumFin values := by
  rw [← FiniteSum.Fin.sumFin_ite_eq index values]
  apply FiniteSum.Rational.Order.Positivity.sumFin_mono
  intro entry
  if equal : entry = index then rw [if_pos equal]
  else rw [if_neg equal]; exact nonnegative entry

end

open Purelib.Data in
open Purelib.Polynomial in
/-- A sign-oriented coefficient retains the original inverse-model derivative bound.

The evaluation identity links the coefficient to the numerator times the refined model, with either gauge sign,
throughout the original box. -/
private theorem signed_derivative_bound {polynomial numerator : Polynomial} {box : Box}
    {clearance : RegionClearance polynomial box} {initial : Model polynomial box}
    {root : DerivativeBounds clearance initial} (bounds : PrimitiveDerivativeBounds root numerator)
    (stage : Nat) (flip : Bool) (coefficient : Polynomial)
    (equal : ∀ point, coefficient.eval point = numerator.eval point * signedValue flip ((initial.refine
      stage).value.eval point))
    {point : Gaussian} (inside : box.Contains point) : normSq ((Dense.Derivative.derivative coefficient).eval point) ≤
      bounds.bound := by
  cases flip with
  | false => exact bounds.coefficient_derivative_le stage coefficient equal inside
  | true =>
      have unsigned : ∀ point, (-coefficient).eval point = numerator.eval point * (initial.refine stage).value.eval
        point := by
        intro point
        rw [Dense.Basic.DensePolynomial.eval_neg, equal]
        change -(numerator.eval point * -((initial.refine stage).value.eval point)) = _
        ring1
      have estimate := bounds.coefficient_derivative_le stage (-coefficient) unsigned inside
      rw [Dense.Derivative.eval_derivative_neg, Gaussian.Basic.Canonical.normSq_neg] at estimate
      exact estimate

variable {polynomial numerator : Polynomial} {ambient : Box} {columns rows : Nat} {geometry : Geometry columns rows}
  {bank : Bank polynomial geometry} {clearance : RegionClearance polynomial ambient}

open Purelib.Data in
set_option genInjectivity false in
/-- Cached inverse-root derivative bounds on the original rectangular model bank.

The dependent vectors preserve each local model and its refinement into the common cleared ambient region, independently
of future model indices. -/
structure DerivativeBank (clearance : RegionClearance polynomial ambient) (bank : Bank polynomial geometry) where
  /-- Every local model box refines the common ambient box. -/ refines : ∀ column row, (geometry.box column row).Refines
    ambient
  /-- The dependent grid of derivative bounds for the original local models. -/ roots : Vector.DependentVector (fun
    column => Vector.DependentVector (fun row =>
    DerivativeBounds (clearance.restrict (refines column row)) (bank.ready column row).model))

constructive_injectivity DerivativeBank

namespace DerivativeBank

open Purelib.Data in
/-- Compute a dependent grid of derivative bounds using the retained ambient restrictions. -/
def build (clearance : RegionClearance polynomial ambient) (bank : Bank polynomial geometry)
    (refines : ∀ column row, (geometry.box column row).Refines ambient) : DerivativeBank clearance bank :=
  ⟨refines, Vector.DependentVector.ofFn fun column => Vector.DependentVector.ofFn fun row =>
    DerivativeBounds.build (clearance.restrict (refines column row)) (bank.ready column row).model⟩

open Purelib.Algebra in
open Purelib.Data in
set_option genInjectivity false in
/-- A numerator-specific derivative bank with a cached total ceiling.

Its dependent entries reuse the exact root bounds at each grid location and retain the finite sum defining the total. -/
structure Numerator (roots : DerivativeBank clearance bank) (numerator : Polynomial) where
  /-- The dependent grid of primitive derivative bounds for this numerator. -/ entries : Vector.DependentVector (fun
    column => Vector.DependentVector (fun row =>
    PrimitiveDerivativeBounds ((roots.roots.get column).get row) numerator))
  /-- The cached total derivative ceiling. -/ total : Coordinate
  /-- The total is the double finite sum of the retained derivative bounds. -/ total_eq : total = FiniteSum.Fin.sumFin
    (fun column => FiniteSum.Fin.sumFin (fun row => ((entries.get column).get row).bound))

constructive_injectivity Numerator

open Purelib.Algebra in
open Purelib.Data in
/-- Build numerator-specific derivative bounds from the existing root bank and cache their sum. -/
def forNumerator (roots : DerivativeBank clearance bank) (numerator : Polynomial) : Numerator roots numerator :=
  let entries := Vector.DependentVector.ofFn fun column => Vector.DependentVector.ofFn fun row =>
    PrimitiveDerivativeBounds.build ((roots.roots.get column).get row) numerator
  ⟨entries, FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (fun row => ((entries.get column).get row).bound)),
    rfl⟩

namespace Numerator

variable {roots : DerivativeBank clearance bank} {stage : Nat}
  {transitions : Transitions (bank.refine stage)} {gauge : Purelib.Topology.Grid.Signs.Gauge transitions.flatGrid}
  {primitives : Primitives (Purelib.Riemann.Branches.RectangularSheetGauge.Transitions.oriented transitions gauge)
    numerator}

/-- The retained derivative total is nonnegative. -/
theorem total_nonnegative (bounds : Numerator roots numerator) : 0 ≤ bounds.total := by
  rw [bounds.total_eq]
  exact sum_nonnegative _ (fun _ => sum_nonnegative _ (fun _ => PrimitiveDerivativeBounds.bound_nonnegative _))

/-- Each local derivative bound is at most the cached grid total. -/
theorem entry_le_total (bounds : Numerator roots numerator) (column : Fin (columns + 1)) (row : Fin (rows + 1)) :
    ((bounds.entries.get column).get row).bound ≤ bounds.total := by
  rw [bounds.total_eq]
  exact (entry_le_sum _ (fun _ => PrimitiveDerivativeBounds.bound_nonnegative _) row).trans
    (entry_le_sum _ (fun _ => sum_nonnegative _ (fun _ => PrimitiveDerivativeBounds.bound_nonnegative _)) column)

open Purelib.Riemann in
open Purelib.Polynomial in
/-- Bound the derivative of an actual oriented primitive coefficient by its retained local ceiling.

The gauge sign leaves the norm bound unchanged, so the original derivative bank applies at every refinement stage. -/
theorem coefficient_derivative_le (bounds : Numerator roots numerator)
    (primitives : Primitives (Branches.RectangularSheetGauge.Transitions.oriented transitions gauge) numerator)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) {point : Gaussian}
    (inside : (geometry.box column row).Contains point) :
    normSq ((Dense.Derivative.derivative (primitives.cells column row).coefficient).eval point) ≤ ((bounds.entries.get
      column).get row).bound := by
  apply signed_derivative_bound ((bounds.entries.get column).get row) stage (gauge.values column row) _ ?_ inside
  intro point
  rw [primitives.coefficient_eq, Branches.RectangularSheetGauge.Transitions.oriented,
    Branches.RectangularSheetGauge.Bank.orient_value, Integration.RectangularRefinementSigns.Bank.refine_model bank]

open Purelib.Riemann in
open Purelib.Data in
/-- Bound a local primitive's Taylor increment error using its original derivative ceiling.

Both endpoints lie in the same model box; the squared error is at most four times the ceiling times squared movement
squared. -/
theorem increment_bound (bounds : Numerator roots numerator)
    (primitives : Primitives (Branches.RectangularSheetGauge.Transitions.oriented transitions gauge) numerator)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) {start finish : Gaussian}
    (startInside : (geometry.box column row).Contains start) (finishInside : (geometry.box column row).Contains finish)
      :
    normSq (primitives.value column row finish - primitives.value column row start -
      (primitives.cells column row).coefficient.eval start * (finish - start)) ≤
        4 * ((bounds.entries.get column).get row).bound * normSq (finish - start) ^ 2 := by
  have estimate := (primitives.dense column row).increment_bound_of_derivative startInside finishInside
    ((bounds.entries.get column).get row).bound ((bounds.entries.get column).get row).bound_nonnegative
    (fun _ inside => by
      rw [Gaussian.Norm.Basic.normSq_eq_canonical]
      exact bounds.coefficient_derivative_le primitives column row inside)
  simpa only [Primitives.dense, Primitives.value, Gaussian.Norm.Basic.normSq_eq_canonical] using estimate

open Purelib.Riemann in
open Purelib.Data in
open Purelib.LinearAlgebra in
/-- Bound a shared primitive increment using its model-owner discrepancy and fixed Taylor ceiling.

At the request's model index, both vertices lie in the selected local box. The bound combines thirty-two global overlap
charges with eight local derivative charges times squared movement squared. -/
theorem shared_increment_bound (bounds : Numerator roots numerator)
    {overlap : PrimitiveOverlapBounds clearance numerator} {target : Coordinate}
    (request : GridPrimitiveAccuracy overlap columns target) (stage_eq : stage = request.index)
    {anchors : PrimitiveAnchors primitives} {offsets : LinearAlgebra.Grid.Offsets anchors.edges}
    {triangles : List (ModelTriangle geometry)} {surface : OwnedTriangulation triangles}
    (readings : SharedPrimitiveValues anchors offsets surface)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) (first last : Fin surface.mesh.vertices.length)
    (firstInside : (geometry.box column row).Contains (surface.mesh.coordinate first))
    (lastInside : (geometry.box column row).Contains (surface.mesh.coordinate last)) :
    normSq (readings.values last - readings.values first -
      (primitives.cells column row).coefficient.eval (surface.mesh.coordinate first) *
        (surface.mesh.coordinate last - surface.mesh.coordinate first)) ≤
      32 * request.globalBound + 8 * ((bounds.entries.get column).get row).bound *
        normSq (surface.mesh.coordinate last - surface.mesh.coordinate first) ^ 2 := by
  subst stage
  have endpoints := Integration.RectangularSharedPrimitives.GridPrimitiveAccuracy.shared_local_increment_bound request
    readings roots.refines column row first last firstInside lastInside
  have taylor := bounds.increment_bound primitives column row firstInside lastInside
  let endpointError := (readings.values last - readings.values first) -
    (primitives.value column row (surface.mesh.coordinate last) - primitives.value column row (surface.mesh.coordinate
      first))
  let localError := primitives.value column row (surface.mesh.coordinate last) - primitives.value column row
    (surface.mesh.coordinate first) -
    (primitives.cells column row).coefficient.eval (surface.mesh.coordinate first) * (surface.mesh.coordinate last -
      surface.mesh.coordinate first)
  have equal : readings.values last - readings.values first -
      (primitives.cells column row).coefficient.eval (surface.mesh.coordinate first) *
        (surface.mesh.coordinate last - surface.mesh.coordinate first) = endpointError + localError := by
    dsimp only [endpointError, localError]; ring1
  rw [equal]
  have scalarEstimate := Gaussian.Norm.Bounds.normSq_add_le_two endpointError localError
  simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at scalarEstimate
  exact scalarEstimate.trans
    ((Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add endpoints taylor) (by decide)).trans_eq
      (by ring1))

end Numerator
end DerivativeBank

end Purelib.Riemann.Integration.RectangularPrimitiveDerivative
