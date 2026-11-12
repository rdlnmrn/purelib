module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Bank.Quarter.Realization
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Entry.Quarter
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Spine
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Tactic.Ring

/-! # One old curved bank on the same literal paid-quarter primitive spine

The retained old bank and complete old paid spine keep their independent
requests and observations. The source and finish comparisons derive their
full-cubic agreements from that actual paid quarter. Original Bank.Cells
pays its actual model sample; the two endpoint comparisons pay the same
old boundary against the literal old paid-spine increment.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Bank.Quarter

namespace Paid

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Curves.Legendre.Periods.Jets.Source (Row)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement (Piece)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.Branches.ClearSheetContinuation (Subdivision)
open Purelib.Riemann.Meshes
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)

variable {site : Fin 2} {parameter : Canonical} {unitQuarter : UnitCircuitQuarter}
variable {positive : (0 : Rational) < 2} {actual : Transport.Quarter site parameter 2 unitQuarter positive}
variable {regular : parameter ≠ criticalValue site} {row : Row}
variable {specification : OddPower.Derivative.Specification (Paths.polynomial parameter) (row.form parameter)}
variable {data : Waist.Differential.Bounds.Data site parameter specification.differential}
variable {initialAccuracy : AccuracyRequest} {initial : Piece data actual initialAccuracy}
variable {whole : initial.span = Differential.Circuit.span} {depth : Nat}
variable {current : Subdivision.Endpoint} {reading : ReadingAt actual current}
variable {originalOwner sourceOwner : OwnerAt site parameter unitQuarter positive current}
variable {original : Steps.Quarter actual regular current reading originalOwner}
variable {agreement : Steps.Acquisition.InitialAgreement current reading sourceOwner}
variable (paid : Steps.Acquisition.Quarter original sourceOwner agreement)
variable (bank : Realization (specification := specification) initial whole depth)
variable {accuracy : AccuracyRequest}
variable (observed : OwnerPath.Primitive.Spine (row.expression parameter) accuracy paid.receipt.trace)

/-- Both endpoint caches compare the same old bank Entries and literal old paid-quarter vertices at their old radii. -/
abbrev Compared (first : current = UniformPrimitiveMesh.firstEndpoint) :=
  Entry.Quarter.Compared paid bank.endpoints.first bank.endpoints.last observed
    (OwnerPath.Primitive.tailRequest accuracy) (OwnerPath.Primitive.tailRequest accuracy) first

/-- Derive both signed endpoint comparisons once from the actual quarter, keeping the complete old input caches. -/
def compare (first : current = UniformPrimitiveMesh.firstEndpoint) : Compared paid bank observed first :=
  Entry.Quarter.Compared.build paid bank.endpoints.first bank.endpoints.last observed
    (OwnerPath.Primitive.tailRequest accuracy) (OwnerPath.Primitive.tailRequest accuracy) first

variable {first : current = UniformPrimitiveMesh.firstEndpoint}
variable (compared : Compared paid bank observed first)

/-- The unchanged original bank and vertex request allocations pay exactly the endpoint increment coefficient. -/
private theorem endpoint_payment (bankAccuracy vertexAccuracy : Rational) :
    2 * ((16 * (bankAccuracy / 16 + vertexAccuracy / ((64 : Nat) : Rational)) +
        4 * (vertexAccuracy / 8)) +
      (16 * (bankAccuracy / 16 + vertexAccuracy / ((64 : Nat) : Rational)) +
        4 * (vertexAccuracy / 8))) = 4 * bankAccuracy + 3 * vertexAccuracy := by
  have first : (4 : Rational) * 16 * (16 : Rational)⁻¹ = 4 := of_decide_eq_true rfl
  have last : (4 : Rational) * (16 * ((64 : Nat) : Rational)⁻¹ + 4 * (8 : Rational)⁻¹) = 3 := by
    rewrite [Cast.natCast_eq_fromInt 64]
    decide +kernel
  rewrite [Field.div_eq_mul_inv_direct, Field.div_eq_mul_inv_direct, Field.div_eq_mul_inv_direct]
  calc
    _ = bankAccuracy * (4 * 16 * (16 : Rational)⁻¹) +
        vertexAccuracy * (4 * (16 * ((64 : Nat) : Rational)⁻¹ + 4 * (8 : Rational)⁻¹)) := by ring1
    _ = _ := by rewrite [first, last]; ring1

include compared in
/-- Both actual endpoint comparisons pay the old bank boundary minus this same old paid-spine increment. -/
theorem boundary_error_le :
    Norm.Basic.normSq ((bank.endpoints.last.value - bank.endpoints.first.value) -
      (observed.last.value - observed.first.value)) ≤
      4 * (request depth).tolerance + 3 * accuracy.tolerance := by
  have retained := compared.boundary_error_lt
  change Norm.Basic.normSq ((bank.endpoints.last.value - bank.endpoints.first.value) -
      (observed.last.value - observed.first.value)) <
    2 * ((16 * ((request depth).tolerance / 16 + accuracy.tolerance / ((64 : Nat) : Rational)) +
        4 * (accuracy.tolerance / 8)) +
      (16 * ((request depth).tolerance / 16 + accuracy.tolerance / ((64 : Nat) : Rational)) +
        4 * (accuracy.tolerance / 8))) at retained
  exact retained.le.trans_eq (endpoint_payment _ _)

/-- The actual stored old model sample is compared to the literal old paid-spine increment. -/
@[expose] def residual : Canonical :=
  bank.layer.val.model.integralSample - (observed.last.value - observed.first.value)

include compared in
/-- Original cell and endpoint certificates derive the entire retained quarter residual bound internally.

The original cell ceiling and dyadic radius pay the Taylor/integral error.
Both old request contributions remain explicit: bank request rho squared
and the actual old Spine accuracy. No aggregate residual is admitted.
-/
theorem residual_le : Norm.Basic.normSq (residual paid bank observed) ≤
    2 * cellCeiling specification initial * Geometric.Basic.quarterRadius 1 depth +
      8 * (request depth).tolerance + 6 * accuracy.tolerance := by
  have cells := bank.endpoints.boundary_error_le bank.cells
  have endpoints := boundary_error_le paid bank observed compared
  have difference (boundary sample increment : Canonical) :
      sample - increment = -(boundary - sample) + (boundary - increment) := by ring1
  unfold residual
  rewrite [difference (bank.endpoints.last.value - bank.endpoints.first.value)
    bank.layer.val.model.integralSample (observed.last.value - observed.first.value)]
  calc
    _ ≤ 2 * (Norm.Basic.normSq (-(bank.endpoints.last.value - bank.endpoints.first.value -
          bank.layer.val.model.integralSample)) +
        Norm.Basic.normSq ((bank.endpoints.last.value - bank.endpoints.first.value) -
          (observed.last.value - observed.first.value))) := Norm.Bounds.normSq_add_le_two _ _
    _ = 2 * (Norm.Basic.normSq (bank.endpoints.last.value - bank.endpoints.first.value -
          bank.layer.val.model.integralSample) +
        Norm.Basic.normSq ((bank.endpoints.last.value - bank.endpoints.first.value) -
          (observed.last.value - observed.first.value))) := by rewrite [Norm.Basic.normSq_neg]; rfl
    _ ≤ 2 * (cellCeiling specification initial * Geometric.Basic.quarterRadius 1 depth +
        (4 * (request depth).tolerance + 3 * accuracy.tolerance)) :=
      Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Order.Arithmetic.add_le_add_direct cells endpoints) (of_decide_eq_true rfl : (0 : Rational) ≤ 2)
    _ = _ := by ring1

end Paid

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Bank.Quarter

end
