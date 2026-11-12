module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Coefficient.Allocation.Rows
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Cells.Refinement
public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling.Stages
import Purelib.Tactic.Ring

/-! # One actual later curved cofactor retaining all six old row observations

The actual old Models may have different requests, states and readings.
Their finite maximum index is computed before one requestAfter on the SAME
original cofactor certificate. One later observation constructs all six new
original Models, each retaining its old-index order witness. Nothing equates
or discards the six old values, and no old radius is assigned a new request.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Cells.Model

namespace CoefficientRefined

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Curves.Legendre.Periods
open Purelib.Riemann.RootContinuation
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Coefficient

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {span : Interval.Bounds} {inside : FixedRootBoxPath.Inside span.lower}
variable {source : Transport.Reading actual span.lower inside} {anchor : Parameter.Anchor source.lift}
variable {data : (index : Fin 6) →
  Waist.Differential.Bounds.Data site parameter (Jets.Specification.Table.forms parameter index)}
variable (rows : Allocation.Rows (anchor := anchor) data)
variable {accuracies : Fin 6 → AccuracyRequest}
variable (models : Data.Vector.DependentVector (fun index => Model (data index) source (accuracies index)))
variable (widthPositive : 0 < span.width) (target : AccuracyRequest)

/-- The chosen request pays both the actual positive fourth width and all six old-source coefficient costs. -/
def request : AccuracyRequest :=
  ((models.get 0).fourthRequest widthPositive).minimum (rows.sourceRequest target)

/-- The finite maximum of the SAME six old observed indices precedes the single new cofactor request. -/
@[expose] def current : Nat := models.maximum (fun _ model => model.sample.comparison.leftIndex)

/-- The exact original selected-observation type retains its actual request and old-index maximum payment. -/
@[expose] def Later (request : AccuracyRequest) :=
  { sample : CertifiedSquareRoot.Sampling.ResidualObservation source.lift.unitRoot request //
      current models ≤ sample.comparison.leftIndex }

/-- Each retained original row index lies before the exact finite maximum of these SAME old Models. -/
theorem current_le (index : Fin 6) : (models.get index).sample.comparison.leftIndex ≤ current models :=
  models.get_le_maximum (fun _ model => model.sample.comparison.leftIndex) index

/-- Construct original Refined Models from the SAME actual new sample, preserving every different old Model. -/
@[expose] def refineRows {request : AccuracyRequest} (later : Later models request) :
    Data.Vector.DependentVector (fun index => Refined (models.get index) request) :=
  Data.Vector.DependentVector.ofFn (fun index =>
    ⟨ofSample (data index) source (models.get index).regular request later.val,
      (current_le models index).trans later.property⟩)

/-- The newly retained sample is the original requestAfter result at the SAME six-old-index maximum. -/
@[irreducible, expose] def LaterCache (request : AccuracyRequest) (later : Later models request) : Prop :=
  later = CertifiedSquareRoot.Sampling.requestAfter source.lift.unitRoot request (current models)

/-- All stored new row Models are the original complete once-built reweighting of that actual shared sample. -/
@[irreducible, expose] def RowsCache {request : AccuracyRequest} (later : Later models request)
    (refined : Data.Vector.DependentVector (fun index => Refined (models.get index) request)) : Prop :=
  refined = refineRows models later

/-- The actual chosen request, complete later observation and six independent old/new Model comparisons. -/
@[expose] def Selected :=
  Σ selected : { value : AccuracyRequest // value = request rows models widthPositive target },
    Σ later : { value : Later models selected.val // LaterCache models selected.val value },
      { refined : Data.Vector.DependentVector (fun index => Refined (models.get index) selected.val) //
        RowsCache models later.val refined }

namespace Selected

open Purelib.Data.Rat.Fraction.Order

/-- Store the whole completed request, observation and actual six-row comparison factories unchanged. -/
@[expose] def ofCompleted (selected : AccuracyRequest)
    (selected_eq : selected = request rows models widthPositive target)
    (later : Later models selected) (later_eq : LaterCache models selected later)
    (refined : Data.Vector.DependentVector (fun index => Refined (models.get index) selected))
    (refined_eq : RowsCache models later refined) : Selected rows models widthPositive target :=
  ⟨⟨selected, selected_eq⟩, ⟨⟨later, later_eq⟩, ⟨refined, refined_eq⟩⟩⟩

/-- Choose both residual payments, request one later sample after ALL old indices, then store six new Models once. -/
def build : Selected rows models widthPositive target :=
  let selected := request rows models widthPositive target
  let later := CertifiedSquareRoot.Sampling.requestAfter source.lift.unitRoot selected (current models)
  let refined := refineRows models later
  ofCompleted rows models widthPositive target selected rfl later (by unfold LaterCache; rfl)
    refined (by unfold RowsCache; rfl)

variable {rows models widthPositive target}
variable (selected : Selected rows models widthPositive target)

/-- Read the SAME actual newly chosen request, before which the old Models and their indices already existed. -/
@[expose] def accuracy : AccuracyRequest := selected.1.val

/-- Read the identical complete newly observed sample together with its actual maximum-index payment. -/
@[expose] def later : Later models selected.accuracy := selected.2.1.val

/-- Read one SAME stored original old/new Model comparison without another sample or numerical Model factory. -/
@[expose] def refined (index : Fin 6) : Refined (models.get index) selected.accuracy := selected.2.2.val.get index

/-- Read the actual original new Model of one differential row; its different old Model remains retained separately. -/
@[expose] def row (index : Fin 6) : Model (data index) source selected.accuracy := (selected.refined index).val

/-- The actual chosen request is the original positive minimum computed before the new observation. -/
theorem accuracy_eq : selected.accuracy = request rows models widthPositive target := selected.1.property

/-- The whole actual later cache retains the exact original requestAfter factory and all six old-index inputs. -/
theorem later_eq : selected.later =
    CertifiedSquareRoot.Sampling.requestAfter source.lift.unitRoot selected.accuracy (current models) := by
  have kept := selected.2.1.property
  unfold LaterCache at kept
  exact kept

/-- Every stored row retains its exact original ofSample factory on the SAME actual later observation. -/
theorem row_eq (index : Fin 6) : selected.row index =
    ofSample (data index) source (models.get index).regular selected.accuracy selected.later.val := by
  have kept := selected.2.2.property
  unfold RowsCache at kept
  have reading := congrArg (fun refined => (refined.get index).val) kept
  have entry := Data.Vector.DependentVector.ofFn_get
    (fun position : Fin 6 => (⟨ofSample (data position) source (models.get position).regular
      selected.accuracy selected.later.val, (current_le models position).trans selected.later.property⟩ :
        Refined (models.get position) selected.accuracy)) index
  exact reading.trans
    (congrArg (fun refined : Refined (models.get index) selected.accuracy => refined.val) entry)

/-- All six new rows retain the SAME whole actual later observation, without identifying the six distinct old ones. -/
theorem row_sample_eq (index : Fin 6) : (selected.row index).sample = selected.later.val :=
  congrArg Model.sample (selected.row_eq index)

/-- The actual later residual request is no larger than the original exact positive fourth-width request. -/
theorem fourth_le : selected.accuracy.tolerance ≤ span.width ^ 4 := by
  rewrite [selected.accuracy_eq]
  exact ((models.get 0).fourthRequest widthPositive).minimum_le_left (rows.sourceRequest target)

/-- Every original row's old-source coefficient term is paid using the SAME genuinely new cofactor request. -/
theorem source_payment (index : Fin 6) :
    4 * (Allocation.sourceCoefficient (rows.get index) * selected.accuracy.tolerance) ≤ target.tolerance := by
  have chosen : selected.accuracy.tolerance ≤ (rows.sourceRequest target).tolerance := by
    rewrite [selected.accuracy_eq]
    exact ((models.get 0).fourthRequest widthPositive).minimum_le_right (rows.sourceRequest target)
  have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct chosen
    (Arithmetic.mul_nonneg_direct (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 4)
      (Allocation.coefficients_nonnegative (rows.get index)).1)
  exact (show 4 * (Allocation.sourceCoefficient (rows.get index) * selected.accuracy.tolerance) =
    (4 * Allocation.sourceCoefficient (rows.get index)) * selected.accuracy.tolerance by ring1).trans_le
    (scaled.trans ((show (4 * Allocation.sourceCoefficient (rows.get index)) *
      (rows.sourceRequest target).tolerance =
        4 * (Allocation.sourceCoefficient (rows.get index) * (rows.sourceRequest target).tolerance) by
          ring1).trans_le (rows.source_payment target index)))

/-- Every actual new-versus-old integral payment preserves that row's OWN old request and coefficient cache. -/
theorem integral_error_le (index : Fin 6) :
    Norm.Basic.normSq ((selected.row index).cell.integralSample - (models.get index).cell.integralSample) ≤
      span.width ^ 2 * (Bounds.residualSlope (data index) * (span.width ^ 4 + (accuracies index).tolerance)) := by
  have paid := (selected.refined index).integral_error_le
  unfold errorBound at paid
  have requestPaid := Arithmetic.add_le_add_direct selected.fourth_le
    (Fraction.Order.Basic.le_refl (accuracies index).tolerance)
  have coefficient := Arithmetic.mul_le_mul_of_nonneg_left_direct requestPaid
    (Bounds.signed_slopes_nonnegative (data index) (models.get index).regular).2
  exact paid.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct coefficient
    (Arithmetic.sq_nonneg_direct span.width))

end Selected

end CoefficientRefined

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Cells.Model

end
