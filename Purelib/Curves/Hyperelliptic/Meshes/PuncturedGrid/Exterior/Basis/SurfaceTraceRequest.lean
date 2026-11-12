module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledTraceRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Integration.PreparedWeightedCoefficientBudget
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedWeightedTraceAllocation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonScheduledTrace
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Topology.PreparedBankRootChains

open Purelib.Approximation.Rational.Budget

open Purelib.Data.Rat.Fraction.Order

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledTraceRequest

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data.Rat

open Purelib.Riemann

public section

/-! Shared trace tolerances selected from the retained component covers. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceTraceRequest

open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)

open Purelib.Riemann.Normalization

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Differentials.Basic.Differential genus}
  {collar : Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {bounds : Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}

set_option genInjectivity false in
/-- A component's covers are retained before choosing the common source
coefficient tolerance and depth floor. -/
structure TraceComponent where
  /-- The original prepared surface component. -/ component :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent
    regular domains differential
  /-- The common parent preparation on this exact original component. -/ retained :
    Preparation.CommonBasisPreparation component.prepared

constructive_injectivity TraceComponent

namespace TraceComponent

/-- Retain the original surface component together with its common parent preparation. -/
@[expose] def build (component :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent
  regular domains differential) :
    TraceComponent (regular := regular) (domains
      := domains) (differential := differential) :=
  ⟨component, Preparation.CommonBasisPreparation.build
    component.prepared⟩

/-- The basis coefficient bound makes the displayed common origin bound nonnegative. -/
theorem originBound_nonnegative (basis : Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds)
  :
    0 ≤ (2 : Coordinate) + 8 * basis.coefficient := by
  simpa only [-eq_self, -iff_self, Fraction.Field.zero_add] using Arithmetic.add_le_add_direct (by
      decide : (0 : Coordinate) ≤ 2)
    (Arithmetic.mul_nonneg_direct (by decide : (0 : Coordinate) ≤ 8)
      (Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds.coefficient_nonnegative basis))

variable (basis : Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds)
  (errorTarget : Coordinate) (positive : 0 < errorTarget)

set_option genInjectivity false in
/-- Keep each allocation, including its finite depth computation, as data. -/
structure Allocated where
  /-- The original component and common source-cover preparation. -/ owner :
    TraceComponent (regular := regular) (domains
    := domains) (differential := differential)
  /-- The retained trace allocation for the original source bound, origin bound and resampling scale. -/ allocation :
    Paths.PreparedWeightedTraceAllocation.WeightedTraceAllocation errorTarget
    (Samples.traceSourceBound owner.retained.sources)
    (2 + 8 * basis.coefficient)
    (Samples.traceResamplingScale
      owner.retained.anchors owner.retained.sources)
  /-- The retained allocation is exactly the finite allocation computed from these original covers. -/ allocation_eq :
    allocation = Samples.traceAllocation
    owner.retained.anchors owner.retained.sources errorTarget
    (2 + 8 * basis.coefficient) positive
    (TraceComponent.originBound_nonnegative basis)

constructive_injectivity Allocated

/-- Compute and retain the trace allocation on this exact component's original source covers. -/
@[expose] def allocate (owner : TraceComponent
  (regular := regular) (domains := domains) (differential := differential)) :
    Allocated (domains := domains)
      (differential := differential) basis errorTarget positive :=
  ⟨owner, Samples.traceAllocation
    owner.retained.anchors owner.retained.sources errorTarget
    (2 + 8 * basis.coefficient) positive
    (TraceComponent.originBound_nonnegative
      basis), rfl⟩

namespace Allocated

variable {basis errorTarget positive}

/-- Compute the coefficient tolerance paid by the retained trace allocation's half allowance. -/
@[expose] def coefficient (entry :
  Allocated (domains := domains)
  (differential := differential) basis errorTarget positive) : Coordinate :=
  Integration.PreparedWeightedCoefficientBudget.coefficientTolerance
    entry.owner.component.program.period.initial entry.allocation.half

/-- The retained half allowance gives a strictly positive coefficient tolerance. -/
theorem coefficient_positive (entry :
  Allocated (domains := domains)
  (differential := differential) basis errorTarget positive) :
    0 < entry.coefficient :=
  Integration.PreparedWeightedCoefficientBudget.coefficientTolerance_positive _ entry.allocation.half_positive

/-- Compute the minimum retained coefficient tolerance, capped by one for an empty list. -/
@[expose] def commonCoefficient : List
  (Allocated (domains := domains)
  (differential := differential) basis errorTarget positive) → Coordinate
  | [] => 1
  | head :: tail => min head.coefficient
    (commonCoefficient
    tail)

/-- Compute the maximum retained component cover floor, with zero for an empty list. -/
@[expose] def commonFloor : List
  (Allocated (domains := domains)
  (differential := differential) basis errorTarget positive) → Nat
  | [] => 0
  | head :: tail => max head.allocation.coverFloor
    (commonFloor
    tail)

/-- The common finite minimum of retained coefficient tolerances is strictly positive. -/
theorem common_positive : (entries : List
  (Allocated (domains := domains)
  (differential := differential) basis errorTarget positive)) →
    0 < Allocated.commonCoefficient
      entries
  | [] => by change (0 : Coordinate) < 1; decide
  | head :: tail => Basic.lt_min head.coefficient_positive
    (common_positive
    tail)

/-- The common coefficient tolerance fits every original member's retained coefficient allowance. -/
theorem coefficient_le : (entries : List
  (Allocated (domains := domains)
  (differential := differential) basis errorTarget positive)) →
    ∀ entry ∈ entries,
      Allocated.commonCoefficient
      entries ≤ entry.coefficient
  | [], _, member => False.elim (List.not_mem_nil member)
  | head :: tail, entry, member => by
      rcases Purelib.Data.List.Membership.mem_cons.mp member with same | later
      · subst entry; exact Basic.min_le_left _ _
      · exact (Basic.min_le_right _ _).trans
          (coefficient_le
          tail entry later)

/-- Every original member's retained cover floor is paid by the common maximum. -/
theorem floor_le : (entries : List
  (Allocated (domains := domains)
  (differential := differential) basis errorTarget positive)) →
    ∀ entry ∈ entries, entry.allocation.coverFloor ≤
      Allocated.commonFloor entries
  | [], _, member => False.elim (List.not_mem_nil member)
  | head :: tail, entry, member => by
      rcases Purelib.Data.List.Membership.mem_cons.mp member with same | later
      · subst entry; exact Data.Nat.Order.le_max_left _ _
      · exact
          (floor_le
          tail entry later).trans (Data.Nat.Order.le_max_right _ _)

/-- Acquisition consumes the exact covers used for the allocation. -/
@[expose] def prepare (entry :
  Allocated (domains := domains)
  (differential := differential) basis errorTarget positive)
    (target coefficientTarget : Coordinate) (targetPositive : 0 < target)
      (coefficientPositive : 0 < coefficientTarget)
    (coverFloor floor : Nat) : SurfaceRequest.Entry (domains :=
      domains) (differential := differential) basis target coefficientTarget coverFloor floor :=
  ⟨entry.owner.component, entry.owner.retained,
    Preparation.CommonBasisRequest.build entry.owner.retained basis
      target coefficientTarget targetPositive coefficientPositive coverFloor floor⟩

end Allocated
end TraceComponent

set_option genInjectivity false in
/-- A complete-surface request with internally selected source tolerances.
The squared component count pays the norm-squared error of their sum. -/
structure ScheduledRequest (prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential)
    (basis : Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds)
    (target errorTarget : Coordinate) (floor : Nat) where
  /-- The common local trace error allowance. -/ localError : Coordinate
  /-- The retained local trace allowance is strictly positive. -/ positive : 0 < localError
  /-- The squared original component count pays the sum's complete trace-error target. -/ paid :
    (prepared.components.length : Coordinate)^2 * localError ≤ errorTarget
  /-- The retained component allocations on their original source covers. -/ allocations : List
    (TraceComponent.Allocated (domains := domains)
    (differential := differential) basis localError positive)
  /-- The common retained coefficient tolerance. -/ coefficientTarget : Coordinate
  /-- The retained coefficient tolerance is exactly the minimum computed from the allocations. -/ coefficient_eq :
    coefficientTarget =
    TraceComponent.Allocated.commonCoefficient
    allocations
  /-- The shared coefficient tolerance is strictly positive. -/ coefficientPositive : 0 < coefficientTarget
  /-- The common retained source-cover depth floor. -/ coverFloor : Nat
  /-- The retained cover floor is exactly the maximum computed from the allocations. -/ cover_eq : coverFloor =
    TraceComponent.Allocated.commonFloor
    allocations
  /-- The original complete-surface request using these common tolerances and depth floors. -/ request :
    SurfaceRequest.Request prepared basis target coefficientTarget
    coverFloor floor
  /-- The request entries are exactly those prepared from the retained allocation list. -/ entries_eq : request.entries
    = allocations.map (fun entry =>
    entry.prepare request.localTarget coefficientTarget request.positive coefficientPositive coverFloor floor)
  /-- Every original request entry is paid by the shared coefficient tolerance and cover floor. -/ compatible : ∀ entry
    ∈ request.entries,
    coefficientTarget ≤ Integration.PreparedWeightedCoefficientBudget.coefficientTolerance
      entry.component.program.period.initial
        (Samples.traceAllocation entry.retained.anchors
        entry.retained.sources localError
        (2 + 8 * basis.coefficient) positive
        (TraceComponent.originBound_nonnegative
          basis)).half ∧
    (Samples.traceAllocation entry.retained.anchors
      entry.retained.sources localError
      (2 + 8 * basis.coefficient) positive
      (TraceComponent.originBound_nonnegative
        basis)).coverFloor ≤ coverFloor

constructive_injectivity ScheduledRequest

namespace ScheduledRequest

/-- Allocate and prepare a complete surface trace request on the original component covers.

The squared component count pays the shared local error, and finite minima and maxima choose common coefficient and
depth requirements. -/
@[expose] def build (prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential)
    (basis : Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds)
    (target errorTarget : Coordinate) (targetPositive : 0 < target) (errorPositive :
      0 < errorTarget)
    (floor : Nat) : ScheduledRequest prepared
      basis target errorTarget floor := open Purelib in by
  let localError := Weighted.allowance errorTarget ((prepared.components.length :
    Coordinate)^2)
  have errorPositive' : 0 < localError := Weighted.allowance_positive errorPositive
    (Arithmetic.sq_nonneg_direct _)
  let owners := prepared.components.map
    TraceComponent.build
  let allocated := owners.map
    (TraceComponent.allocate basis localError
    errorPositive')
  let coefficient :=
    TraceComponent.Allocated.commonCoefficient
    allocated
  have coefficientPositive :=
    TraceComponent.Allocated.common_positive
    allocated
  let coverFloor :=
    TraceComponent.Allocated.commonFloor allocated
  let localTarget := Weighted.allowance target (4 * (prepared.components.length :
    Coordinate))
  have localPositive : 0 < localTarget := Weighted.allowance_positive targetPositive
    (Arithmetic.mul_nonneg_direct (by decide : (0 : Coordinate) ≤ 4)
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)))
  let entries := allocated.map (fun entry => entry.prepare localTarget coefficient localPositive coefficientPositive
    coverFloor floor)
  have same : entries.map SurfaceRequest.Entry.component =
    prepared.components := by
    change (((prepared.components.map
      TraceComponent.build).map
      (TraceComponent.allocate basis localError
        errorPositive')).map
      (fun entry => entry.prepare localTarget coefficient localPositive coefficientPositive coverFloor floor)).map
        SurfaceRequest.Entry.component = _
    induction prepared.components with
    | nil => rfl
    | cons head tail ih => exact congrArg (List.cons head) ih
  let request : SurfaceRequest.Request prepared basis target
    coefficient coverFloor floor :=
    ⟨localTarget, rfl, localPositive,
      Weighted.mul_allowance_le targetPositive.le
        (Arithmetic.mul_nonneg_direct (by decide : (0 : Coordinate) ≤
          4) (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _))),
      entries, same, SurfaceRequest.Entry.maximum entries, rfl⟩
  refine ⟨localError, errorPositive', Weighted.mul_allowance_le errorPositive.le
    (Arithmetic.sq_nonneg_direct _),
    allocated, coefficient, rfl, coefficientPositive, coverFloor, rfl, request, rfl, ?_⟩
  intro entry member
  obtain ⟨owner, owned, equal⟩ := Data.List.Map.mem_map.mp member
  subst entry
  have cap :=
    TraceComponent.Allocated.coefficient_le
    allocated owner owned
  have depth := TraceComponent.Allocated.floor_le
    allocated owner owned
  change coefficient ≤ Integration.PreparedWeightedCoefficientBudget.coefficientTolerance
    owner.owner.component.program.period.initial
      (Samples.traceAllocation
      owner.owner.retained.anchors owner.owner.retained.sources localError
      (2 + 8 * basis.coefficient) errorPositive'
      (TraceComponent.originBound_nonnegative
        basis)).half ∧
    (Samples.traceAllocation
      owner.owner.retained.anchors owner.owner.retained.sources localError
      (2 + 8 * basis.coefficient) errorPositive'
      (TraceComponent.originBound_nonnegative
        basis)).coverFloor ≤ coverFloor
  rw [← owner.allocation_eq]
  exact ⟨cap, depth⟩

end ScheduledRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceTraceRequest
