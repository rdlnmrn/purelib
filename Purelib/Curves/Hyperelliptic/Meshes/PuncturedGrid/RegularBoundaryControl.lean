module
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Data.List.Flatten
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Components.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularEnergyCompletion
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalAreaComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentClosure

public section

/-!
# Requested regular exterior period and energy control

Exact root-thread closure makes the full cached cap total zero. The actual
shared triangle integral therefore meets the original period request. One
positive energy allowance selects both squared area tolerances and the cap
energy tolerance; the signed exterior loss follows from the computed cap.
The surface polygon retains its internal segment-area correction.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
open Purelib.Data.Gaussian.Norm
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Integration.Path

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation (SampledEntry
  Request)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularEnergyCompletion (RegularEnergyPlan)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularEnergyCompletion.Request (RegularEnergyAcquisition
  acquireRegularEnergy)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Gaussian.Basic.Canonical

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Riemann.Meshes.LiftedPuncturedGrid base} {differential :
    Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {domains : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
    base.faces.regulars}
  {index depth readingIndex : Nat} {box : Purelib.Geometry.Rational.Box}
  {sample : Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {shared : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains}
  {localTarget localArea target areaTarget : Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

namespace RegularBoundaryControl

/-- Exact original regular root closure makes the total of all retained cap paths zero. -/
private theorem groups_total_zero
    (groups : List (ComponentSamples.SampledComponent (regular := regular) sample shared depth readingIndex localTarget
      localArea floor))
    (degree : curve.polynomial.natDegree = 2 * genus + 2) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (((groups.map SampledComponent.values).flatten).map
      (fun value => value.evaluated.capPath)).flatten = 0 := by
  induction groups with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, List.flatten_cons, Data.List.Map.map_append, Data.List.Flatten.flatten_append, -eq_self,
        -iff_self]
      rw [IncrementArea.sum_append, ← head.cap.total_eq, head.total_zero degree, ih, Data.Gaussian.Basic.add_zero]

end RegularBoundaryControl

section SampledComponent

namespace RegularBoundaryControl.SampledComponent

/-- The sum of actual retained source-minus-cap increment errors is the difference of the original two increment sums.
-/
private theorem errors_sum
    (values : List (AllSurfacePreparation.SampledEntry (regular := regular) sample shared depth readingIndex localTarget
      localArea floor)) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (values.map (fun value => value.increment -
      value.evaluated.right.total)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (values.map SampledEntry.increment) -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (values.map (fun value => value.evaluated.right.total)) := by
  induction values with
  | nil => change (0 : InverseRootPolynomial.Gaussian) = 0 - 0; ring1
  | cons head tail ih =>
    simp only [List.map_cons, Data.Gaussian.Norm.Sum.Basic.gaussianSum, ih, -eq_self, -iff_self]; ring1

end RegularBoundaryControl.SampledComponent

namespace Exterior.ComponentSamples.SampledComponent

/-- The actual original component source and cap totals differ by at most its squared retained occurrence count times
the local target. -/
theorem
  integral_close
    (group : ComponentSamples.SampledComponent (regular := regular) sample shared depth readingIndex localTarget
      localArea floor) :
    Data.Gaussian.Norm.Basic.normSq (group.surface.total - group.cap.total) ≤
      (group.values.length : InverseRootPolynomial.Coordinate) * ((group.values.length :
        InverseRootPolynomial.Coordinate) * localTarget) := by
  have estimate := Data.Gaussian.Norm.Sum.Bounds.normSq_sum_le
    (group.values.map (fun value => value.increment - value.evaluated.right.total)) localTarget (by
      intro value member
      obtain ⟨original, _, equal⟩ := Map.mem_map.mp member
      rw [← equal]
      exact original.integral_close.le)
  rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularBoundaryControl.SampledComponent.errors_sum,
    Data.List.Map.length_map, ← group.surface.total_eq] at estimate
  have totals : Data.Gaussian.Norm.Sum.Basic.gaussianSum (group.values.map (fun value =>
    value.evaluated.right.total)) = group.cap.total := by
    rw [group.cap.total_eq, IncrementArea.sum_flatten, Data.List.Map.map_map]
    apply congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum
    apply Map.map_congr_left
    intro value _
    exact value.evaluated.right.total_eq
  rw [totals] at estimate
  exact estimate

/-- Read the same component integral through its assigned triangle edges. The component's occurrence certificate retains
the original exterior word. -/
theorem
  triangle_integral
    (group : ComponentSamples.SampledComponent (regular := regular) sample shared depth readingIndex localTarget
      localArea floor)
    (readings : TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh) :
    group.surface.total = Data.Gaussian.Norm.Sum.Basic.gaussianSum ((group.values.map SampledEntry.entry).map
      (fun entry => entry.occurrence.placement.location.sourceEdge.increment readings.values)) := by
  rw [group.surface.total_eq, SampledEntry.increment_list_eq group.values readings]

/-- Every original component's retained occurrence count is bounded by the complete flattened component bank length. -/
theorem
  length_le_groups
    (groups : List (ComponentSamples.SampledComponent (regular := regular) sample shared depth readingIndex localTarget
      localArea floor)) :
    ∀ group ∈ groups, group.values.length ≤ (groups.map SampledComponent.values).flatten.length := by
  induction groups with
  | nil => intro group member; cases member
  | cons head tail ih =>
      intro group member
      simp only [List.map_cons, List.flatten_cons, Data.List.Append.length_append, -eq_self, -iff_self]
      rcases Data.List.Membership.mem_cons.mp member with rfl | member
      · exact Nat.le_add_right _ _
      · exact (ih group member).trans (Nat.le_add_left _ _)

end Exterior.ComponentSamples.SampledComponent

end SampledComponent

section AllSurfacePreparation
namespace Exterior.SurfaceRequests.AllSurfacePreparation.Request.Evaluation

variable {prepared :
  Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential}
  {request : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request prepared
    target areaTarget floor}

/-- The exact component partition and its original root closures cancel only the total. No area is asserted to vanish.
-/
theorem
  cap_total_zero
  (evaluated : AllSurfacePreparation.Request.Evaluation request sample shared depth readingIndex)
    (degree : curve.polynomial.natDegree = 2 * genus + 2) : evaluated.cap.total = 0 := by
  rw [evaluated.cap.total_eq, evaluated.pairs_eq, Data.List.Map.map_map]
  change Data.Gaussian.Norm.Sum.Basic.gaussianSum (evaluated.samples.values.map (fun value =>
    value.evaluated.capPath)).flatten = 0
  have same := congrArg (fun values : List (AllSurfacePreparation.SampledEntry (regular := regular) sample shared depth
    readingIndex
      request.localTarget request.budget.areaTarget floor) =>
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (values.map (fun value => value.evaluated.capPath)).flatten)
      evaluated.components.values_eq
  exact same.symm.trans (Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularBoundaryControl.groups_total_zero
    evaluated.components.groups degree)

/-- The original requested period tolerance bounds the actual complete source integral after exact cap-total
cancellation. -/
theorem
  integral_small
  (evaluated : AllSurfacePreparation.Request.Evaluation request sample shared depth readingIndex)
    (degree : curve.polynomial.natDegree = 2 * genus + 2) : Data.Gaussian.Norm.Basic.normSq evaluated.integral
      < target := by
  have bound := evaluated.integral_close
  rw [evaluated.cap_total_zero degree, Data.Gaussian.Basic.sub_zero] at bound
  exact bound

/-- The vanishing estimate applies to the exact edge readings used by the surface, in its certified exterior occurrence
order. -/
theorem
  triangle_integral_small
  (evaluated : AllSurfacePreparation.Request.Evaluation request sample shared depth readingIndex)
    (degree : curve.polynomial.natDegree = 2 * genus + 2) (readings : TrianglePrimitiveReadings.TriangleReadings shared
      lifted.mesh) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (request.entries.map
      (fun entry => entry.occurrence.placement.location.sourceEdge.increment readings.values))) < target := by
  rw [← evaluated.triangle_integral readings]
  exact evaluated.integral_small degree

/-- The original request pays the full error count of each retained component. -/
theorem
  component_error_paid
  (evaluated : AllSurfacePreparation.Request.Evaluation request sample shared depth readingIndex)
    (grouped : ComponentSamples sample shared depth readingIndex request.localTarget
      request.budget.areaTarget floor
      prepared.components evaluated.samples.values) :
    ∀ group ∈ grouped.groups, (group.values.length : InverseRootPolynomial.Coordinate) * ((group.values.length :
      InverseRootPolynomial.Coordinate) * request.localTarget) < target := by
  intro group member
  have lengthLe := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.SampledComponent.length_le_groups
    grouped.groups group member
  rw [grouped.values_eq] at lengthLe
  have lengthEq : evaluated.samples.values.length = request.count := by
    rw [← Data.List.Map.length_map (values := evaluated.samples.values) SampledEntry.entry,
      evaluated.samples.entries_eq, request.count_entries]
  rw [lengthEq] at lengthLe
  have countLe := Fraction.Cast.Order.natCast_le_direct lengthLe
  have countNonnegative := Fraction.Cast.Order.natCast_le_direct (Nat.zero_le group.values.length)
  have inner := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct countLe request.positive.le
  have scale := Fraction.Order.Arithmetic.mul_le_mul_direct countLe inner
    (Fraction.Order.Arithmetic.mul_nonneg_direct countNonnegative request.positive.le)
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le request.count))
  exact scale.trans_lt request.total_paid

/-- Every original component meets the period allowance separately, using its own root closure and the paid count of the
original sample bank. -/
theorem
  component_integral_small
  (evaluated : AllSurfacePreparation.Request.Evaluation request sample shared depth readingIndex)
    (degree : curve.polynomial.natDegree = 2 * genus + 2)
    (grouped : ComponentSamples sample shared depth readingIndex request.localTarget
      request.budget.areaTarget floor
      prepared.components evaluated.samples.values) :
    ∀ group ∈ grouped.groups, Data.Gaussian.Norm.Basic.normSq group.surface.total < target := by
  intro group member
  have bounded := group.integral_close
  rw [group.total_zero degree, Data.Gaussian.Basic.sub_zero] at bounded
  exact bounded.trans_lt (evaluated.component_error_paid grouped group member)

end Exterior.SurfaceRequests.AllSurfacePreparation.Request.Evaluation

namespace RegularBoundaryControl.AllSurfacePreparation

/-- A paid original boundary-plus-energy discrepancy and signed energy lower bound give the retained strict boundary
loss bound. -/
theorem boundary_loss {boundary energy : InverseRootPolynomial.Gaussian}
  {loss : InverseRootPolynomial.Coordinate}
    (positive : 0 < loss) (close : Data.Gaussian.Norm.Basic.normSq (boundary + energy) < 2 * (loss ^ 2 + loss ^
      2))
    (lower : -(loss / 2) < energy.im / 4) : boundary.im / 4 < loss := by
  have radiusPositive : 0 < 2 * loss := Fraction.Order.Arithmetic.mul_pos_direct (by decide) positive
  have squareClose : Data.Gaussian.Norm.Basic.normSq (boundary + energy) < (2 * loss) ^ 2 := close.trans_eq (by
    ring1)
  have signed := (Components.Bounds.imaginary_bounds_of_normSq_lt_sq radiusPositive squareClose).2
  have divided : (boundary + energy).im / 4 < (2 * loss) / 4 := by
    apply (Fraction.Order.Field.div_lt_iff_pos (by decide : (0 : InverseRootPolynomial.Coordinate) < 4)).2
    rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide : (4 : InverseRootPolynomial.Coordinate) ≠ 0)]
    exact signed
  have added := Fraction.Order.Arithmetic.add_lt_add_direct divided (Fraction.Order.Arithmetic.neg_lt_neg_direct lower)
  have left : (boundary + energy).im / 4 + -(energy.im / 4) = boundary.im / 4 := by
    rw [Data.Gaussian.Basic.add_im]
    simp only [Fraction.Field.div_eq_mul_inv_direct, -eq_self, -iff_self]
    ring1
  have half : loss / 2 * 2 = loss := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  have quarter : (2 * loss) / 4 * 4 = 2 * loss := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  have right : (2 * loss) / 4 + -(-(loss / 2)) = loss := by
    rw [neg_neg]
    apply Fraction.Field.mul_right_cancel_of_ne (by decide : (4 : InverseRootPolynomial.Coordinate) ≠ 0)
    calc
      ((2 * loss) / 4 + loss / 2) * 4 = (2 * loss) / 4 * 4 + (loss / 2 * 2) * 2 := by ring1
      _ = loss * 4 := by rw [quarter, half]; ring1
  exact left.symm.trans_lt (added.trans_eq right)

end RegularBoundaryControl.AllSurfacePreparation

set_option genInjectivity false in
/-- One acquisition controls the physical period correction and the signed energy loss. Every tolerance and refinement
is derived from the two positive requests; all original source, cap and energy caches remain available. -/
structure RegularBoundaryControl (prepared :
  ExteriorProgram.AllSurfacePreparation regular domains differential)
    (periodTarget loss : InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The original joint source request paying the period target and squared energy loss. -/ request :
    AllSurfacePreparation.Request prepared periodTarget (loss ^ 2) floor
  /-- The actual original source and regular cap energy acquisition at the retained area and half-loss targets. -/
    acquired : RegularEnergyCompletion.Request.RegularEnergyAcquisition request (loss ^ 2) (loss / 2)
  /-- The complete original component partition of those same acquired source occurrences. -/ components :
    Exterior.ComponentSamples acquired.sample acquired.shared acquired.plan.fine request.readingIndex
    request.localTarget request.budget.areaTarget floor prepared.components acquired.evaluated.source.samples.values
  /-- Every retained original component integral meets the supplied period target. -/ component_integrals_small : ∀
    group ∈ components.groups, Data.Gaussian.Norm.Basic.normSq group.surface.total < periodTarget
  /-- The actual retained complete cap increment total is zero. -/ cap_total_zero : acquired.evaluated.source.cap.total
    = 0
  /-- The squared norm of the actual original complete source integral meets the period target. -/ integral_small :
    Data.Gaussian.Norm.Basic.normSq acquired.evaluated.source.integral < periodTarget
  /-- The actual original complete source area satisfies the retained signed energy loss bound. -/ source_upper :
    acquired.evaluated.source.source.area.im / 4 < loss
  /-- The actual original surface polygon area plus its retained internal-area correction satisfies the signed loss
    bound. -/ surface_upper : (acquired.evaluated.source.surface.area + acquired.evaluated.source.internalArea).im / 4 <
    loss

constructive_injectivity RegularBoundaryControl

namespace RegularBoundaryControl

/-- Evaluate a prepared regular request on the existing common bank. -/
@[expose] def evaluate {prepared : ExteriorProgram.AllSurfacePreparation regular domains differential}
    {periodTarget loss : InverseRootPolynomial.Coordinate} {floor : Nat}
    (request : AllSurfacePreparation.Request prepared periodTarget (loss ^ 2) floor)
    (degree : curve.polynomial.natDegree = 2 * genus + 2) (lossPositive : 0 < loss)
    {index : Nat} (sample : Primitives.Sample cap differential index collar.box)
    (shared : PrimitiveData.FacePrimitiveBank differential index domains) (later : request.index ≤ index) :
    RegularBoundaryControl
      prepared periodTarget loss floor := by
  have squarePositive : 0 < loss ^ 2 := by
    rw [pow_two]
    exact Fraction.Order.Arithmetic.mul_pos_direct lossPositive lossPositive
  have halfPositive : 0 < loss / 2 := Fraction.Order.Field.div_pos_direct lossPositive (by decide)
  let acquired := RegularEnergyCompletion.Request.acquireRegularEnergy request degree (loss ^ 2) (loss / 2)
    squarePositive halfPositive sample shared later
  let components := acquired.evaluated.source.components
  exact ⟨request, acquired, components, acquired.evaluated.source.component_integral_small degree components,
    acquired.evaluated.source.cap_total_zero degree,
    acquired.evaluated.source.integral_small degree,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularBoundaryControl.AllSurfacePreparation.boundary_loss lossPositive
      acquired.evaluated.source_energy_close acquired.evaluated.energy.lower,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularBoundaryControl.AllSurfacePreparation.boundary_loss lossPositive
      acquired.evaluated.surface_energy_close acquired.evaluated.energy.lower⟩

/-- Standalone construction uses the same shared-bank evaluation path. -/
@[expose] def build (prepared : ExteriorProgram.AllSurfacePreparation regular domains differential)
    (degree : curve.polynomial.natDegree = 2 * genus + 2)
    (periodTarget loss : InverseRootPolynomial.Coordinate) (periodPositive : 0 < periodTarget) (lossPositive : 0 < loss)
    (floor : Nat) :
      RegularBoundaryControl
      prepared periodTarget loss floor := by
  have squarePositive : 0 < loss ^ 2 := by
    rw [pow_two]
    exact Fraction.Order.Arithmetic.mul_pos_direct lossPositive lossPositive
  let request := AllSurfacePreparation.Request.build prepared periodTarget (loss ^ 2) periodPositive squarePositive
    floor
  exact
    evaluate
    request degree lossPositive
    (Primitives.Sample.build cap differential request.index collar.box)
    (FacePrimitiveBank.build differential request.index domains) (Nat.le_refl _)

end RegularBoundaryControl
end AllSurfacePreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
