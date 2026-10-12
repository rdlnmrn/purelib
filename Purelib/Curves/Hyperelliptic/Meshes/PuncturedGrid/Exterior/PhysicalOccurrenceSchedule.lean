module
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSourceRequest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOwnerRequest
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOwnerRequest

open Purelib.Data.Rat

open Purelib.Data.Vector

open Purelib.Riemann.Paths

public section

/-! Select physical owner queries, source refinements and a common sampling
schedule, in that order, without evaluating either primitive bank. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOwnerRequest (PhysicalOwnerBudget)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement (sourceRunDensity
  sourceRunRefinement)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior (SourceRunRefinement)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan
  (ParentEvaluation)
open Purelib.Riemann.Normalization
open Purelib.Data.Rat.Fraction.Compatibility
variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {differential other :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains differential} {target : Purelib.Data.Rat.Fraction.Rational} {minimum floor : Nat}

namespace PhysicalOccurrenceSchedule

set_option genInjectivity false in
/-- The piece count comes from the physical mesh's selected perimeter side. Query selection precedes source refinement;
no fine values enter this data. -/
structure PhysicalOccurrencePreparation (request : PhysicalSourceRequest prepared other target
  minimum floor)
    (i : Fin prepared.occurrences.length) (count : Nat) where
  /-- The original physical-piece count budget allocated one eighth of the occurrence allowance. -/ budget :
    PhysicalOwnerRequest.PhysicalOwnerBudget (request.plans.get i) count (request.allowance / 8)
  /-- The cached original paired source plan refined to pay its retained query requirements. -/ sources :
    budget.Prepared
  /-- The source-run refinement requirement at the retained parent count and density. -/ refinement :
    SourceRunRefinement sources.plan.parents.plans.length
    (SourceRunRefinement.sourceRunDensity sources.plan) (request.allowance / 8) floor

constructive_injectivity PhysicalOccurrencePreparation

end PhysicalOccurrenceSchedule

namespace PhysicalOccurrenceSchedule.PhysicalOccurrencePreparation

/-- Prepare the original physical owner budget, query-refined source plan and source-run refinement in their dependency
order. -/
@[expose] def build (request : PhysicalSourceRequest prepared other target minimum floor)
    (i : Fin prepared.occurrences.length) (count : Nat) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOccurrenceSchedule.PhysicalOccurrencePreparation
      request i count :=
  let positive := Fraction.Order.Field.div_pos_direct request.positive (by decide : (0 : Fraction.Rational) < 8)
  let budget := PhysicalOwnerBudget.build (request.plans.get i) count (request.allowance / 8) positive
  let sources := budget.prepare
  ⟨budget, sources, SourceRunRefinement.sourceRunRefinement sources.plan (request.allowance / 8) positive floor⟩

end PhysicalOccurrenceSchedule.PhysicalOccurrencePreparation

namespace PhysicalOccurrenceSchedule

/-- The complete dependent bank of original occurrence preparations at their actual physical piece counts. -/
@[expose] def PhysicalOccurrencePreparations (request : PhysicalSourceRequest prepared other
  target minimum floor)
    (counts : Fin prepared.occurrences.length → Nat) :=
  Data.Vector.DependentVector (fun i =>
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOccurrenceSchedule.PhysicalOccurrencePreparation request
    i (counts i))

/-- The complete retained owner-request bank at one common physical trace depth. -/
@[expose] def PhysicalOccurrenceOwners {request : PhysicalSourceRequest prepared other target
  minimum floor}
    {counts : Fin prepared.occurrences.length → Nat}
    (entries :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOccurrenceSchedule.PhysicalOccurrencePreparations
      request counts) (physicalDepth : Nat) :=
  Data.Vector.DependentVector (fun i => (entries.get i).budget.Owners
    (RectangularDyadicPairedTrace.dyadicCount physicalDepth))

end PhysicalOccurrenceSchedule

set_option genInjectivity false in
/-- All occurrences use one physical depth and numerical stage. The cap arc depth additionally includes each retained
source partition's initial depth. -/
structure PhysicalOccurrenceSchedule (request : PhysicalSourceRequest prepared other target
  minimum floor)
    (counts : Fin prepared.occurrences.length → Nat) where
  /-- The cached original occurrence preparations and their exact dependent piece counts. -/ entries :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOccurrenceSchedule.PhysicalOccurrencePreparations request
    counts
  /-- The common physical trace depth paying all original occurrence refinements. -/ physicalDepth : Nat
  /-- The requested physical floor is paid by the common physical depth. -/ physicalFloor_le : floor ≤ physicalDepth
  /-- Every original occurrence refinement is paid at the common physical depth. -/ physical_ge : ∀ i, (entries.get
    i).refinement.depth ≤ physicalDepth
  /-- The cached complete bank of original piece and junction owner requests at that physical depth. -/ owners :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOccurrenceSchedule.PhysicalOccurrenceOwners entries
    physicalDepth
  /-- The common numerical stage paying the original request, source plans and owner banks. -/ index : Nat
  /-- The common numerical stage equals the maximum of its retained original requirements. -/ index_eq : index = max
    request.index (entries.maximum fun i entry =>
    max entry.sources.plan.index (owners.get i).index)
  /-- Every original query-refined source plan is paid at the common numerical stage. -/ source_ge : ∀ i, (entries.get
    i).sources.plan.index ≤ index
  /-- Every original physical owner request is paid at the common numerical stage. -/ owner_ge : ∀ i, (owners.get
    i).index ≤ index
  /-- The common cap-arc depth including each original occurrence's source partition depth. -/ depth : Nat
  /-- The cap depth is exactly the maximum of the floor and all original occurrence depth requirements. -/ depth_eq :
    depth = max floor (entries.maximum fun i entry =>
    (prepared.occurrences[i.val]'i.isLt).piece.mesh.depth +
      max entry.sources.plan.parents.depth entry.refinement.depth)
  /-- The common cap depth pays each original partition depth and its larger source or refinement requirement. -/
    depth_ge : ∀ i, (prepared.occurrences[i.val]'i.isLt).piece.mesh.depth +
    max (entries.get i).sources.plan.parents.depth (entries.get i).refinement.depth ≤ depth

constructive_injectivity PhysicalOccurrenceSchedule

namespace PhysicalOccurrenceSchedule

/-- Cache all original occurrence preparations and owner requests with common paid physical, numerical and cap-depth
schedules. -/
@[expose] def build (request : PhysicalSourceRequest prepared other target minimum floor)
    (counts : Fin prepared.occurrences.length → Nat) :
      PhysicalOccurrenceSchedule request
      counts := by
  let entries :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOccurrenceSchedule.PhysicalOccurrencePreparations request
    counts :=
    DependentVector.ofFn fun i =>
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOccurrenceSchedule.PhysicalOccurrencePreparation.build
      request i (counts i)
  let physicalDepth := max floor (entries.maximum fun _ entry => entry.refinement.depth)
  let owners : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOccurrenceSchedule.PhysicalOccurrenceOwners
    entries physicalDepth :=
    DependentVector.ofFn fun i => (entries.get i).budget.owners
      (RectangularDyadicPairedTrace.dyadicCount physicalDepth)
  let index := max request.index (entries.maximum fun i entry =>
    max entry.sources.plan.index (owners.get i).index)
  let depth := max floor (entries.maximum fun i entry =>
    (prepared.occurrences[i.val]'i.isLt).piece.mesh.depth +
      max entry.sources.plan.parents.depth entry.refinement.depth)
  refine ⟨entries, physicalDepth, Data.Nat.Order.le_max_left _ _, ?_, owners, index, rfl, ?_, ?_, depth, rfl, ?_⟩
  · intro i
    exact (entries.get_le_maximum (fun _ entry => entry.refinement.depth) i).trans (Data.Nat.Order.le_max_right _ _)
  · intro i
    exact (Data.Nat.Order.le_max_left _ _).trans ((entries.get_le_maximum (fun i entry =>
      max entry.sources.plan.index (owners.get i).index) i).trans (Data.Nat.Order.le_max_right _ _))
  · intro i
    exact (Data.Nat.Order.le_max_right _ _).trans ((entries.get_le_maximum (fun i entry =>
      max entry.sources.plan.index (owners.get i).index) i).trans (Data.Nat.Order.le_max_right _ _))
  · intro i
    exact (entries.get_le_maximum (fun i entry =>
      (prepared.occurrences[i.val]'i.isLt).piece.mesh.depth +
        max entry.sources.plan.parents.depth entry.refinement.depth) i).trans (Data.Nat.Order.le_max_right _ _)

variable {request :
  PhysicalSourceRequest prepared other
  target minimum floor}
  {counts : Fin prepared.occurrences.length → Nat} (schedule :
    PhysicalOccurrenceSchedule
    request counts)

/-- Synchronize with a later complete-surface mesh before acquiring numerical banks. Retain the query-refined source
plans and recompute only the owner requests that depend on the physical trace's number of edges. -/
@[expose] def atPhysicalDepth (physicalDepth : Nat) (later : schedule.physicalDepth ≤ physicalDepth) :
    PhysicalOccurrenceSchedule request
      counts := by
  let owners : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOccurrenceSchedule.PhysicalOccurrenceOwners
    schedule.entries physicalDepth :=
    DependentVector.ofFn fun i => (schedule.entries.get i).budget.owners
      (RectangularDyadicPairedTrace.dyadicCount physicalDepth)
  let index := max request.index (schedule.entries.maximum fun i entry =>
    max entry.sources.plan.index (owners.get i).index)
  refine ⟨schedule.entries, physicalDepth, schedule.physicalFloor_le.trans later,
    fun i => (schedule.physical_ge i).trans later, owners, index, rfl, ?_, ?_,
    schedule.depth, schedule.depth_eq, schedule.depth_ge⟩
  · intro i
    exact (Data.Nat.Order.le_max_left _ _).trans ((schedule.entries.get_le_maximum (fun i entry =>
      max entry.sources.plan.index (owners.get i).index) i).trans (Data.Nat.Order.le_max_right _ _))
  · intro i
    exact (Data.Nat.Order.le_max_right _ _).trans ((schedule.entries.get_le_maximum (fun i entry =>
      max entry.sources.plan.index (owners.get i).index) i).trans (Data.Nat.Order.le_max_right _ _))

/-- The additional source depth after removing the original occurrence and retained parent partition depths. -/
@[expose] def fine (depth : Nat) (i : Fin prepared.occurrences.length) : Nat :=
  depth - ((prepared.occurrences[i.val]'i.isLt).piece.mesh.depth + (schedule.entries.get i).sources.plan.parents.depth)

/-- The original occurrence, parent and additional source depths sum to the selected common cap depth. -/
theorem arc_depth {depth : Nat} (later : schedule.depth ≤ depth) (i : Fin prepared.occurrences.length) :
    (prepared.occurrences[i.val]'i.isLt).piece.mesh.depth +
      ((schedule.entries.get i).sources.plan.parents.depth + schedule.fine depth i) = depth := by
  have bound := (Nat.add_le_add_left (Data.Nat.Order.le_max_left (schedule.entries.get i).sources.plan.parents.depth
    (schedule.entries.get i).refinement.depth) (prepared.occurrences[i.val]'i.isLt).piece.mesh.depth).trans
      ((schedule.depth_ge i).trans later)
  rw [← Nat.add_assoc]
  exact Data.Nat.Subtraction.add_sub_of_le bound

/-- A later common cap depth pays the original source-refinement depth after removing the occurrence partition depth. -/
theorem source_refined {depth : Nat} (later : schedule.depth ≤ depth) (i : Fin prepared.occurrences.length) :
    (schedule.entries.get i).refinement.depth ≤
      (schedule.entries.get i).sources.plan.parents.depth + schedule.fine depth i := by
  have bound := (Nat.add_le_add_left (Data.Nat.Order.le_max_right (schedule.entries.get i).sources.plan.parents.depth
    (schedule.entries.get i).refinement.depth) (prepared.occurrences[i.val]'i.isLt).piece.mesh.depth).trans
      ((schedule.depth_ge i).trans later)
  rw [← schedule.arc_depth later i] at bound
  omega0

/-- The selected physical mesh pays every retained source width cap. -/
theorem physical_refined (i : Fin prepared.occurrences.length) :
    (1 / 2 : Fraction.Rational)^schedule.physicalDepth ≤ (schedule.entries.get i).refinement.width := by
  have later := schedule.physical_ge i
  let extra := schedule.physicalDepth - (schedule.entries.get i).refinement.depth
  have same : schedule.physicalDepth = (schedule.entries.get i).refinement.depth + extra :=
    (Data.Nat.Subtraction.add_sub_of_le later).symm
  rw [(schedule.entries.get i).refinement.width_eq, same, pow_add]
  have bounded := Fraction.Order.Arithmetic.pow_le_pow_direct (by decide : (0 : Fraction.Rational) ≤ 1 / 2)
    (by decide : (1 / 2 : Fraction.Rational) ≤ 1) extra
  rw [one_pow] at bounded
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bounded
    (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) _)).trans_eq (mul_one _)

variable {stage depth : Nat} {box otherBox : Purelib.Geometry.Rational.Box}
  (sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box)
  (otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox)

/-- The complete dependent bank evaluating the exact retained source plans at their scheduled additional depths. -/
@[expose] def Evaluations := Data.Vector.DependentVector (fun i : Fin prepared.occurrences.length =>
  PairedSourcePlan.ParentEvaluation (schedule.entries.get i).sources.plan sample otherSample (schedule.fine depth i))

/-- Evaluate the query-refined owners themselves, at one later cap stage. -/
@[expose] def evaluate (chart : HyperellipticReciprocal.originOrder curve = 0)
    (later : schedule.index ≤ stage) :
      Evaluations
      (depth := depth) schedule sample otherSample :=
  DependentVector.ofFn fun i => (schedule.entries.get i).sources.plan.parents.evaluate
    sample otherSample chart ((Data.Nat.Order.le_max_left _ _).trans ((schedule.source_ge i).trans later))
    (schedule.fine depth i)

end PhysicalOccurrenceSchedule
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
