module
import Purelib.Data.List.Membership
public import Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Periods.PreparedRootClosedPeriodBank
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Paths.PreparedPrimitivePaths
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedOwnerClosedBridges
import Purelib.Riemann.Integration.PreparedOwnerClosedSchedules
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.State.WindingOne.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Riemann.Branches.ContainedPreparedPolynomialSheets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodReadback

public section

/-!
# Ambient containment of the actual standard period parents

The four original banks retain their own ambient certificates. Their bounds
embed in the fixed curve ambient, and the existing root-subedge ancestry
carries those bounds to every actual scheduler stage.
-/

namespace Purelib.Riemann.Periods.StandardPeriodAmbient.EndpointsIn

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation (EndpointsIn)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedgeRefinement RootSubedgeBlock)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {source :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {box larger : Purelib.Geometry.Rational.Box}

/-- Concatenating two parent lists preserves their common endpoint containment. -/
theorem append {first last : List (CenteredEdge curve source)}
    (a : EndpointsIn box first) (b : EndpointsIn box last) : EndpointsIn box (first ++ last) := by
  induction first with
  | nil => exact b
  | cons head tail ih => exact ⟨a.1, a.2.1, ih a.2.2⟩

/-- Enlarge the ambient box of all retained parent endpoints along the supplied refinement. -/
theorem enlarge (refines : box.Refines larger) : ∀ {parents : List (CenteredEdge curve source)},
    EndpointsIn box parents → EndpointsIn larger parents
  | [], _ => trivial
  | _ :: _, inside => ⟨refines.contains inside.1, refines.contains inside.2.1, enlarge refines inside.2.2⟩

/-- Every member of a contained parent list has both endpoints in the same box. -/
theorem member {parents : List (CenteredEdge curve source)} (inside : EndpointsIn box parents)
    {parent : CenteredEdge curve source} (present : parent ∈ parents) :
    box.Contains (parent.edge.point 0) ∧ box.Contains (parent.edge.point 1) := by
  induction parents with
  | nil => exact (List.not_mem_nil present).elim
  | cons head tail ih =>
      rcases Purelib.Data.List.Membership.mem_cons.mp present with rfl | present
      · exact ⟨inside.1, inside.2.1⟩
      · exact ih inside.2.2 present

open Purelib.Curves in
/-- Changing the differential preserves the original parent endpoint containment. -/
theorem recast (target : Hyperelliptic.Differentials.Basic.Differential genus) : ∀ {parents : List (CenteredEdge curve
  source)},
    EndpointsIn box parents → EndpointsIn box (parents.map (recastCenteredEdge target))
  | [], _ => trivial
  | _ :: _, inside => ⟨inside.1, inside.2.1, recast target inside.2.2⟩

open Purelib.Riemann in
open Purelib.Data in
/-- Every retained child in a root-subedge block stays between its original parent endpoints. -/
private theorem block {parent : CenteredEdge curve source}
    (first : box.Contains (parent.edge.point 0)) (last : box.Contains (parent.edge.point 1)) :
    ∀ {children : List (CenteredEdge curve source)}, RootSubedgeBlock parent children → EndpointsIn box children
  | _, .nil => trivial
  | _, .cons head tail => by
      have query (fraction : Rat.Fraction.Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1) :
          box.Contains (parent.edge.point (head.location fraction inside).fraction) :=
        Paths.PreparedPrimitivePaths.point_inside_of_endpoints parent box first last (head.location fraction
          inside).inside
      exact ⟨(head.location 0 (by decide)).point_eq ▸ query 0 (by decide),
        (head.location 1 (by decide)).point_eq ▸ query 1 (by decide), block first last tail⟩

/-- Transport endpoint containment through the actual root-subedge ancestry.

Each child's original fraction witness identifies its physical endpoints inside the same parent box. -/
theorem refinement : ∀ {parents children : List (CenteredEdge curve source)},
    RootSubedgeRefinement parents children → EndpointsIn box parents → EndpointsIn box children
  | _, _, .nil, _ => trivial
  | _, _, .cons _ roots tail, inside => append (block inside.1 inside.2.1 roots) (refinement tail inside.2.2)

end Purelib.Riemann.Periods.StandardPeriodAmbient.EndpointsIn

namespace Purelib.Riemann.Periods.StandardPeriodAmbient.ClosedBoundaryDoublePath

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation (EndpointsIn)
open Purelib.Riemann.Branches.ContainedPreparedPolynomialSheets.PreparedPolynomialSheetPropagation (prepared_endpoints)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Paths.PreparedClearPathModels.PreparedPath (DyadicBank)
open Purelib.Riemann.Readings.PreparedBoundaryClosure (ClosedBoundaryDoublePath)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Readings.PreparedBoundaryClosure.ClosedBoundaryDoublePath (total checkReturn_joined)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Data in
open Purelib.Polynomial in
open Purelib.Geometry in
/-- Every original dyadic bank supplies endpoint containment in its own retained ambient box. -/
private theorem bank_endpoints (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (source :
  Hyperelliptic.Differentials.Basic.Differential genus) (sheet : Fin 2)
    {depth : Nat} {diameter : Rat.Fraction.Rational} {positive : 0 < diameter}
    {ambient : Rational.Box} {start finish : Gaussian.Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)}
    (bank : DyadicBank depth diameter positive path owner) :
    EndpointsIn ambient (CenteredPathChain.ofDyadicBank curve source sheet bank).parents := by
  cases bank with
  | safe checked => exact prepared_endpoints curve source sheet checked.prepared
  | executed within prepared success => exact prepared_endpoints curve source sheet prepared
  | executedCertified checked =>
      rw [CenteredPathChain.ofDyadicBank, CenteredPathChain.ofExecutedCheckedDyadic_parents_eq_ofPreparedPath]
      exact prepared_endpoints curve source sheet checked.prepared
  | certified certificate => exact prepared_endpoints curve source sheet certificate.prepared

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Geometry in
/-- Embed the four original closed-tour banks into one supplied ambient box.

The connector and both boundary-box refinements transport their retained endpoint certificates through the exact initial
schedule concatenation. -/
theorem initial_endpoints (tour : ClosedBoundaryDoublePath curve) (source :
  Hyperelliptic.Differentials.Basic.Differential genus)
    (box : Rational.Box) (connector : tour.joined.data.connectorAmbient.Refines box)
    (left : tour.joined.data.leftState.box.Refines box) (right : tour.joined.data.rightState.box.Refines box) :
    EndpointsIn box (Topology.PreparedRootSafeCycleStates.ClosedBoundaryDoublePath.rootClosedInitial tour
      source).state.parents := by
  change EndpointsIn box (Integration.PreparedOwnerClosedSchedules.ClosedBoundaryDoublePath.schedule tour
    source).toDifferential.initial.parents
  rw [Integration.PreparedOwnerClosedSchedules.ClosedBoundaryDoublePath.schedule_initial_parents]
  exact Periods.StandardPeriodAmbient.EndpointsIn.append
    (Periods.StandardPeriodAmbient.EndpointsIn.append
      (Periods.StandardPeriodAmbient.EndpointsIn.append
        (Periods.StandardPeriodAmbient.EndpointsIn.enlarge connector
          (bank_endpoints curve source 0 tour.joined.data.forwardChecked))
        (Periods.StandardPeriodAmbient.EndpointsIn.enlarge right
          (bank_endpoints curve source 0 tour.joined.data.rightBoundaryChecked)))
      (Periods.StandardPeriodAmbient.EndpointsIn.enlarge connector
        (bank_endpoints curve source 1 tour.joined.data.backwardChecked)))
    (Periods.StandardPeriodAmbient.EndpointsIn.enlarge left
      (bank_endpoints curve source 1 tour.joined.data.leftBoundaryChecked))

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Polynomial in
open Purelib.Geometry in
open Purelib.RootIsolation in
/-- Preserve ambient containment through the total checked root-return construction.

Both an accepted return and the traced fallback retain the supplied connector and boundary geometry in their original
initial parent banks. -/
theorem total_initial_endpoints {leftAmbient rightAmbient connectorAmbient : Rational.Box}
    (leftState : State.WindingOne.Basic.WindingOneState curve.polynomial leftAmbient)
    (rightState : State.WindingOne.Basic.WindingOneState curve.polynomial rightAmbient)
    (connector : Polynomial.Geometry.ClearPath curve.polynomial connectorAmbient leftState.box.anchor
      rightState.box.anchor)
    (within : connector.WithinAmbient)
    (owner : Owner (curve.polynomial.eval leftState.box.anchor))
    (source : Hyperelliptic.Differentials.Basic.Differential genus) (box : Rational.Box)
    (connectorInside : connectorAmbient.Refines box)
    (leftInside : leftState.box.Refines box) (rightInside : rightState.box.Refines box) :
    EndpointsIn box (Topology.PreparedRootSafeCycleStates.ClosedBoundaryDoublePath.rootClosedInitial
      (total leftState rightState connector within owner) source).state.parents := by
  unfold total
  dsimp only
  split
  · rename_i closed accepted
    apply initial_endpoints
    · rw [checkReturn_joined _ closed accepted]
      exact connectorInside
    · rw [checkReturn_joined _ closed accepted]
      exact leftInside
    · rw [checkReturn_joined _ closed accepted]
      exact rightInside
  · exact initial_endpoints _ source box connectorInside leftInside rightInside

end Purelib.Riemann.Periods.StandardPeriodAmbient.ClosedBoundaryDoublePath

namespace Purelib.Riemann.Periods.StandardPeriodAmbient.IntersectionRow

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation (EndpointsIn)
open Purelib.Riemann.Integration.PreparedRefinementProgramCore (standardDifferentials)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection (IntersectionRow)
open Purelib.Riemann.Periods.PreparedRootClosedPeriodBank

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}
  {base : FramedPuncturedGrid curve (Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve
    branches).branches higher}
  {lifted : LiftedPuncturedGrid base}
  {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}
  {index : Fin genus} (row : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionRow
    lifted integral index)

section
open Purelib.Riemann
open Purelib.Curves
open Purelib.Geometry
open Purelib.RootIsolation
/-- The original standard A-period initial parents lie in the fixed curve ambient. -/
theorem a_initial_ambient : EndpointsIn (Hyperelliptic.Branches.Cuts.Ambient curve) row.period.aInitial.state.parents :=
  by
  have toursEq : row.period.tours = Integration.PreparedOwnerClosedBridges.OwnerClosedCyclePair.ofData curve branches
    index := by
    have equal := congrArg (fun period : PreparedCycleModels.RootClosedPeriodRow curve => period.tours) row.period_eq
    rw [PreparedCycleModels.RootClosedPeriodBank.ofData_row] at equal
    exact equal
  rw [row.period.aInitial_eq, PreparedCycleModels.OwnerClosedCyclePair.aInitial_state]
  rw [toursEq]
  apply Periods.StandardPeriodAmbient.ClosedBoundaryDoublePath.total_initial_endpoints
  · exact Rational.Box.refines_refl _
  · exact State.WindingOne.Basic.WindingOneState.refinesAmbient _
  · exact State.WindingOne.Basic.WindingOneState.refinesAmbient _

/-- The original standard B-period initial parents lie in the fixed curve ambient. -/
theorem b_initial_ambient : EndpointsIn (Hyperelliptic.Branches.Cuts.Ambient curve) row.period.bInitial.state.parents :=
  by
  have toursEq : row.period.tours = Integration.PreparedOwnerClosedBridges.OwnerClosedCyclePair.ofData curve branches
    index := by
    have equal := congrArg (fun period : PreparedCycleModels.RootClosedPeriodRow curve => period.tours) row.period_eq
    rw [PreparedCycleModels.RootClosedPeriodBank.ofData_row] at equal
    exact equal
  rw [row.period.bInitial_eq, PreparedCycleModels.OwnerClosedCyclePair.bInitial_state]
  rw [toursEq]
  apply Periods.StandardPeriodAmbient.ClosedBoundaryDoublePath.total_initial_endpoints
  · exact Rational.Box.refines_refl _
  · exact State.WindingOne.Basic.WindingOneState.refinesAmbient _
  · exact State.WindingOne.Basic.WindingOneState.refinesAmbient _

end

open Purelib.Riemann
open Purelib.Curves
/-- Every actual A-period schedule stage inherits the original fixed ambient containment. -/
theorem a_stage_ambient (stage : Nat) : EndpointsIn (Hyperelliptic.Branches.Cuts.Ambient curve) (row.period.aState
  stage).state.parents :=
  Periods.StandardPeriodAmbient.EndpointsIn.refinement (row.period.aInitial.statesSubedges (standardDifferentials genus)
    stage) (a_initial_ambient row)

/-- Every actual B-period schedule stage inherits the original fixed ambient containment. -/
theorem b_stage_ambient (stage : Nat) : EndpointsIn (Hyperelliptic.Branches.Cuts.Ambient curve) (row.period.bState
  stage).state.parents :=
  Periods.StandardPeriodAmbient.EndpointsIn.refinement (row.period.bInitial.statesSubedges (standardDifferentials genus)
    stage) (b_initial_ambient row)

end Purelib.Riemann.Periods.StandardPeriodAmbient.IntersectionRow
