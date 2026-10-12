module
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceTraceRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSurfaceRequest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSourceBudget
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces

open Purelib.Curves

open Purelib.Geometry

open Purelib

open Purelib.Data.Rat

open Purelib.Riemann

@[expose] public section

/-! Pay every root-restoration cost before scheduling the complete surface. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSourceSurface

open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSourceBudget.CommonBasisRequest.Sampled
  (rootSourceTarget rootSourceTarget_positive rootSourceCost_paid)

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {bounds : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}

variable {basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {target coefficientTarget : Normalization.InverseRootPolynomial.Coordinate} {coverFloor floor index minimum
    readingIndex : Nat}
  {box : Rational.Box} {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap
    differential index box}
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}

variable {energyFloor radialDepth : Nat}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

open Purelib.Data.Gaussian.Basic.Canonical

/-- Choose the root-restoration target on the original surface components. -/
def sourceSurfaceTarget (rootAllowance : Normalization.InverseRootPolynomial.Coordinate) : List
  (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent
  regular domains differential) → Normalization.InverseRootPolynomial.Coordinate
  | [] => 1
  | head :: tail => min
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSourceBudget.CommonBasisRequest.Sampled.rootSourceTarget
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation.build head.prepared)
    rootAllowance)
      (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSourceSurface.sourceSurfaceTarget
        rootAllowance tail)

/-- A positive root allowance gives a positive common source target on the original component list. -/
theorem sourceSurfaceTarget_positive {rootAllowance : Normalization.InverseRootPolynomial.Coordinate} (positive : 0 <
  rootAllowance) :
    (components : List
      (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent
      regular domains differential)) → 0 <
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSourceSurface.sourceSurfaceTarget rootAllowance components
  | [] => by change (0 : Normalization.InverseRootPolynomial.Coordinate) < 1; decide
  | head :: tail => Fraction.Order.Basic.lt_min
    (RootSourceBudget.CommonBasisRequest.Sampled.rootSourceTarget_positive
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation.build head.prepared) positive)
      (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSourceSurface.sourceSurfaceTarget_positive
        positive tail)

/-- The common surface source target is no greater than each original component fixed-cover target. -/
theorem sourceSurfaceTarget_le (rootAllowance : Normalization.InverseRootPolynomial.Coordinate) :
    (components : List
      (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent
      regular domains differential)) → ∀ component ∈ components,
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSourceSurface.sourceSurfaceTarget rootAllowance components ≤
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSourceBudget.CommonBasisRequest.Sampled.rootSourceTarget
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation.build component.prepared)
      rootAllowance
  | [], _, member => False.elim (List.not_mem_nil member)
  | _ :: tail, component, member => by
      cases member with
      | head => exact Fraction.Order.Basic.min_le_left ..
      | tail _ later =>
          exact (Fraction.Order.Basic.min_le_right ..).trans
            (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSourceSurface.sourceSurfaceTarget_le
              rootAllowance tail component later)

namespace Plans.Samples

/-- Numerical plans inherit payments established entirely from their original covers. -/
theorem rootSourcePayments_of_targets {rootAllowance : Normalization.InverseRootPolynomial.Coordinate} (positive : 0 <
  target) :
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor)) →
    (plans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans capSample polynomials minimum entries)
      →
    (∀ entry ∈ entries, target ≤
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSourceBudget.CommonBasisRequest.Sampled.rootSourceTarget
      entry.retained rootAllowance) →
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSurfaceRequest.Plans.Samples.RootSourcePayments rootAllowance
      entries plans
  | [], _, _ => True.intro
  | head :: tail, plans, paid =>
      ⟨rootSourceCost_paid (request := head.request) (inputs := plans.1.inputs) positive (paid head (List.mem_cons_self
        ..)),

          rootSourcePayments_of_targets
          positive tail plans.2 (fun entry member => paid entry (List.mem_cons_of_mem head member))⟩

end Plans.Samples

namespace ScheduledRequest
variable {prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential} {errorTarget rootAllowance : Normalization.InverseRootPolynomial.Coordinate}
  (positive : 0 < target) (errorPositive : 0 < errorTarget)
  (scheduled : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceTraceRequest.ScheduledRequest prepared basis
    target errorTarget floor)
  (canonical : scheduled = Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceTraceRequest.ScheduledRequest.build
    prepared basis target errorTarget positive errorPositive floor)
  (targetPaid : target ≤
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSourceSurface.sourceSurfaceTarget rootAllowance
    prepared.components)

include canonical targetPaid

/-- The existing canonical scheduler preserves precisely the covers used to
choose the root-restoration ceiling. -/
theorem entry_source_target (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry (domains :=
  domains) (differential := differential) basis
    scheduled.request.localTarget scheduled.coefficientTarget scheduled.coverFloor floor)
    (member : entry ∈ scheduled.request.entries) :
    scheduled.request.localTarget ≤
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSourceBudget.CommonBasisRequest.Sampled.rootSourceTarget
      entry.retained rootAllowance := open Purelib.Data.Rat in by
  subst scheduled
  let scheduled := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceTraceRequest.ScheduledRequest.build prepared
    basis target errorTarget positive errorPositive floor
  rw [scheduled.entries_eq] at member
  obtain ⟨allocated, owned, rfl⟩ := Data.List.Map.mem_map.mp member
  change allocated ∈ (prepared.components.map
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceTraceRequest.TraceComponent.build).map
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceTraceRequest.TraceComponent.allocate basis
      scheduled.localError scheduled.positive) at owned
  obtain ⟨owner, present, rfl⟩ := Data.List.Map.mem_map.mp owned
  obtain ⟨component, componentPresent, rfl⟩ := Data.List.Map.mem_map.mp present
  have weightNN : 0 ≤ 4 * (prepared.components.length : Normalization.InverseRootPolynomial.Coordinate) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _))
  have denominatorPositive : 0 < 4 * (prepared.components.length : Normalization.InverseRootPolynomial.Coordinate) + 1
    :=
    Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct weightNN (by decide)
  have product := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (show 1 ≤ 4 * (prepared.components.length : Normalization.InverseRootPolynomial.Coordinate) + 1 from
      (Fraction.zero_add (1 : Normalization.InverseRootPolynomial.Coordinate)).symm.trans_le
      (Fraction.Order.Arithmetic.add_le_add_direct weightNN (Fraction.Order.Basic.le_refl _)))
    scheduled.request.positive.le
  rw [Fraction.Field.mul_one_direct] at product
  have localLe : scheduled.request.localTarget ≤ target := by
    rw [scheduled.request.local_eq] at product
    exact product.trans_eq (Fraction.Field.div_mul_cancel_of_ne _ _ denominatorPositive.ne')
  exact localLe.trans (targetPaid.trans
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSourceSurface.sourceSurfaceTarget_le rootAllowance
    prepared.components component componentPresent))

/-- All numerical stages satisfy the pre-acquisition source payment. -/
theorem root_sources_paid (plans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans capSample
  polynomials minimum scheduled.request.entries) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSurfaceRequest.Plans.Samples.RootSourcePayments rootAllowance
      scheduled.request.entries plans :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSourceSurface.Plans.Samples.rootSourcePayments_of_targets
    scheduled.request.positive scheduled.request.entries plans
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSourceSurface.ScheduledRequest.entry_source_target positive
      errorPositive scheduled canonical targetPaid)

end ScheduledRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSourceSurface
