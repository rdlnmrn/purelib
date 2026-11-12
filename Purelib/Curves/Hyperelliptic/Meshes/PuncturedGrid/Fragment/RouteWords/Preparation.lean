module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.Words
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedReadings
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Nat.Order
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Tactic.Ring

/-! # Common mesh readings after an original whole-word contact request

The original request is fixed before its common numerical stage. Both
original stage floors are paid, and the same retained word comparisons and
route readings supply the actual total bound, with all old charges intact.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.RouteRequest

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords (LiftedFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums
  (WordPreparation wordEndpoints_mem modelSum)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Gaussian.Norm.Sum
open Purelib.Data.Gaussian.Norm
open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open Purelib.Approximation.Rational.Budget
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames RootEdgeBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)

variable {genus : Nat} {curve : HyperellipticCurve genus} {source : Differential genus}
variable {branches : BranchIsolation.Data curve} {higher : 1 < curve.polynomial.natDegree}
variable {base : FramedPuncturedGrid curve branches higher} {frames : RootFrames base.bank.grid}
variable {vertices : VertexBank base.bank.grid} {edges : RootEdgeBank frames}
variable {mesh : LiftedMesh vertices edges base.faces} {axes : PrimitiveAxes base.bank.grid}
variable {domains : FaceDomainBank frames base.faces.regulars} {count : Nat} {target : Rational}
variable {pieces : List (LiftedFragment axes domains mesh source count target)} {allowance : Rational}

/-- The original common word bank and cached route readings after the SAME retained request's sufficient floor.

Readings alone does not own the required mesh or numerical preparation.
This exact Sigma retains those complete existing results and their whole
factory equations; the supplied original RouteRequest remains its index.
-/
@[expose] def Prepared (request : RouteRequest pieces allowance)
    (tolerance : Rational) (positive : 0 < tolerance) : Type 1 :=
  Σ common : {value : WordPreparation pieces tolerance positive request.index //
    value = WordPreparation.build pieces tolerance positive request.index},
  {value : Readings request common.val.shared // value = RouteRequest.readings request common.val.shared
    (Data.Nat.Order.le_max_right _ _) (wordEndpoints_mem pieces)}

namespace Prepared

variable (request : RouteRequest pieces allowance) (tolerance : Rational) (positive : 0 < tolerance)

/-- Build one common numerical bank above the original mesh and contact floors, then cache its original route total.

The request and every fragment remain supplied values. No contact, query,
Point, Entry, domain or source factory runs again in this operation.
-/
def build : Prepared request tolerance positive :=
  let common := WordPreparation.build pieces tolerance positive request.index
  let readings := RouteRequest.readings request common.shared common.minimum_le (wordEndpoints_mem pieces)
  ⟨⟨common, rfl⟩, ⟨readings, rfl⟩⟩

variable {request tolerance positive}
variable (prepared : Prepared request tolerance positive)

/-- Read the whole original common bank, including its actual numerical stage, anchors and offsets. -/
def common : WordPreparation pieces tolerance positive request.index := prepared.1.val

/-- Read the original cached route values and total on this SAME common bank. -/
def readings : Readings request prepared.common.shared := prepared.2.val

/-- The common bank is its complete original factory at the retained request floor. -/
theorem common_eq : prepared.common = WordPreparation.build pieces tolerance positive request.index :=
  prepared.1.property

/-- The route values, total and paid bound are the complete original factory on that same bank. -/
theorem readings_eq : prepared.readings = RouteRequest.readings request prepared.common.shared
    (Data.Nat.Order.le_max_right _ _) (wordEndpoints_mem pieces) := prepared.2.property

/-- The actual common stage pays the complete original contact request before any route reading. -/
theorem later : request.index ≤ max prepared.common.budgets.index request.index := prepared.common.minimum_le

/-- Sum the actual materialized original fragment comparisons in their literal word order. -/
def value : Canonical := sumFin (fun position : Fin pieces.length => (prepared.common.reading position).value)

/-- The retained total payment keeps the actual word count and every original inner-piece bound. -/
def modelBound : Rational := (pieces.length : Rational) *
  sumFin (fun position : Fin pieces.length => (prepared.common.reading position).bound)

/-- The materialized comparison sum is the SAME original assigned-face word increment on the common bank. -/
theorem value_eq : prepared.value = gaussianSum (pieces.map (fun piece => piece.value prepared.common.shared)) :=
  (sumFin_congr (fun position : Fin pieces.length =>
    LiftedReadings.ClearGrid.RegularPrimitiveFragment.SheetEntry.BankReading.value_eq_lifted
      (prepared.common.reading position) (pieces[position.val]'position.isLt).occurrence)).trans
        (Indexed.sumFin_map pieces (fun piece => piece.value prepared.common.shared))

/-- The materialized assigned-face total and the actual retained route total satisfy the original whole-word bound. -/
theorem accurate : normSq (prepared.value - prepared.readings.sum) < allowance :=
  (congrArg (fun value => normSq (value - prepared.readings.sum)) prepared.value_eq).trans_lt
    prepared.readings.accurate

/-- The same retained comparison vector pays its actual original polynomial-model total. -/
theorem model_accurate : normSq (prepared.value - modelSum pieces) ≤ prepared.modelBound :=
  prepared.common.sum_accurate

/-- The actual route total and old polynomial-model total are compared with both literal payments retained.

Only the contact allowance is paid by the new request floor. The original
model bounds retain every actual piece count, residual and old radius.
-/
theorem route_model_le : normSq (prepared.readings.sum - modelSum pieces) ≤
    2 * (prepared.modelBound + allowance) := by
  have scalar : (prepared.value - modelSum pieces) - (prepared.value - prepared.readings.sum) =
      prepared.readings.sum - modelSum pieces := by ring1
  have triangle := Bounds.normSq_sub_le_two
    (prepared.value - modelSum pieces) (prepared.value - prepared.readings.sum)
  have paid := Arithmetic.add_le_add_direct
    prepared.model_accurate prepared.accurate.1
  exact (congrArg normSq scalar).symm.trans_le (triangle.trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct paid
      (by decide +kernel : (0 : Rational) ≤ 2)))

end Prepared

/-- A complete original canonical contact request and its retained paid common numerical preparation.

The request is genuinely new work: each actual canonical route, start
Owner, common path and contact budget is constructed before the common
stage. This does not identify an old Point with a newly queried Owner.
-/
@[expose] def CanonicalPrepared (pieces : List (LiftedFragment axes domains mesh source count target))
    (allowance : Rational) (allowancePositive : 0 < allowance)
    (tolerance : Rational) (positive : 0 < tolerance) : Type 2 :=
  Σ request : {value : RouteRequest pieces allowance //
    value = RouteRequest.build pieces canonicalRoute allowance allowancePositive},
  {value : Prepared request.val tolerance positive // value = Prepared.build request.val tolerance positive}

namespace CanonicalPrepared

variable (pieces : List (LiftedFragment axes domains mesh source count target))
variable (allowance : Rational) (allowancePositive : 0 < allowance)
variable (tolerance : Rational) (positive : 0 < tolerance)

/-- Build all original canonical contacts once BEFORE their single paid common stage and cached route total. -/
def build : CanonicalPrepared pieces allowance allowancePositive tolerance positive :=
  let request := RouteRequest.build pieces canonicalRoute allowance allowancePositive
  let prepared := Prepared.build request tolerance positive
  ⟨⟨request, rfl⟩, ⟨prepared, rfl⟩⟩

variable {pieces allowance allowancePositive tolerance positive}
variable (retained : CanonicalPrepared pieces allowance allowancePositive tolerance positive)

/-- Read the complete original contact request with its actual ordered word and cached sufficient floor. -/
def request : RouteRequest pieces allowance := retained.1.val

/-- Read the same retained common bank and original route readings after that exact request. -/
def prepared : Prepared retained.request tolerance positive := retained.2.val

/-- The whole request is the original canonical-route constructor, including all contacts and their budgets. -/
theorem request_eq : retained.request = RouteRequest.build pieces canonicalRoute allowance allowancePositive :=
  retained.1.property

/-- The whole preparation is its cached-input constructor on that exact retained request. -/
theorem prepared_eq : retained.prepared = Prepared.build retained.request tolerance positive := retained.2.property

/-- The stored route-value list preserves every original canonical-route occurrence and orientation. -/
theorem values_eq : retained.prepared.readings.values = pieces.map (fun piece =>
    RouteContacts.routeValue piece (canonicalRoute piece) retained.prepared.common.shared) := by
  have requested := congrArg (fun value : RouteRequest pieces allowance =>
    value.requests.values retained.prepared.common.shared) retained.request_eq
  exact retained.prepared.readings.values_eq.trans (requested.trans
    (RouteRequests.build_values (Aggregate.perTerm allowance pieces.length)
      (Aggregate.perTerm_positive allowancePositive pieces.length) canonicalRoute pieces
      retained.prepared.common.shared))

/-- The actual cached route total is the original canonical-route word sum, without another route lookup. -/
theorem sum_eq : retained.prepared.readings.sum = gaussianSum (pieces.map (fun piece =>
    RouteContacts.routeValue piece (canonicalRoute piece) retained.prepared.common.shared)) :=
  retained.prepared.readings.sum_eq.trans (congrArg gaussianSum retained.values_eq)

/-- The actual canonical-route word total has the paid original all-contact comparison to the same materialized bank. -/
theorem accurate : normSq (retained.prepared.value - gaussianSum (pieces.map (fun piece =>
    RouteContacts.routeValue piece (canonicalRoute piece) retained.prepared.common.shared))) < allowance :=
  (congrArg (fun value => normSq (retained.prepared.value - value)) retained.sum_eq).symm.trans_lt
    (Prepared.accurate retained.prepared)

end CanonicalPrepared
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.RouteRequest

end
