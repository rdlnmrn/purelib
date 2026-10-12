module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapAccuracy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularArcPlans
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalAreaComparison
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ArcError

public section

/-!
# Automatic regular exterior comparison with the retained cap energy

The original surface request chooses the shared polynomial stage. Cached
polynomial bounds then choose sufficient common subdivisions for every arc
and the cap mesh. All local error obligations are discharged internally.
The same original source and cap evaluation supplies the full-area cache.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularEnergyCompletion

open Purelib
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapAccuracy
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularArcPlans
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularArcPlans.AllSurfacePreparation
open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation (Request)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularArcPlans.AllSurfacePreparation (ArcPlans)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation (CapAttachment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment
  (ReciprocalGeometry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapAccuracy (RequestedRegularEnergy)
open Purelib.Approximation.Rational.Budget.Aggregate (perTerm perTerm_positive)
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
  {index : Nat} {box : Purelib.Geometry.Rational.Box}
  {sample : Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box} {shared :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains}
  {prepared :
    Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains differential} {target areaTarget : Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor :
    Nat}
  {request : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request prepared
    target areaTarget floor}

set_option genInjectivity false in
/-- Select both shared subdivision thresholds once from the actual request entries and the already acquired polynomial
bounds. -/
structure RegularEnergyPlan (request : AllSurfacePreparation.Request prepared target areaTarget floor)
    (sample : Primitives.Sample cap differential index box) (errorTarget : InverseRootPolynomial.Coordinate) where
  /-- The original curve polynomial has the retained even hyperelliptic degree. -/ degree : curve.polynomial.natDegree =
    2 * genus + 2
  /-- The original complete cap comparison tolerance is strictly positive. -/ positive : 0 < errorTarget
  /-- The cached polynomial energy bounds of the actual supplied cap sample. -/
  bounds : Charts.Reciprocal.Cap.EnergyBounds
    sample
  /-- The cached per-occurrence arc error allowance. -/ localTarget : InverseRootPolynomial.Coordinate
  /-- The local allowance is exactly the aggregate target divided according to the original occurrence count. -/
    localTarget_eq : localTarget = Aggregate.perTerm errorTarget request.count
  /-- The actual retained local arc allowance is strictly positive. -/ local_positive : 0 < localTarget
  /-- The complete original arc request bank on the exact retained surface entries. -/ plans :
    AllSurfacePreparation.ArcPlans sample localTarget request.entries
  /-- The cached common fine subdivision required by all original arc plans. -/ fine : Nat
  /-- The fine subdivision equals the complete retained arc-plan maximum. -/ fine_eq : fine = plans.fineMaximum
  /-- The cached common energy subdivision floor for the actual selected fine depth. -/ energyMinimum : Nat
  /-- The energy floor equals the complete original arc-plan maximum at the retained fine depth. -/ energyMinimum_eq :
    energyMinimum = plans.energyMaximum fine

constructive_injectivity RegularEnergyPlan

namespace RegularEnergyPlan

variable {errorTarget : Riemann.Normalization.InverseRootPolynomial.Coordinate}

/-- Prepare all original arc comparisons from the supplied cached energy bounds and retain their exact common
subdivision thresholds. -/
@[expose] def build (request : AllSurfacePreparation.Request prepared target areaTarget floor)
    (degree : curve.polynomial.natDegree = 2 * genus + 2) (bounds : Charts.Reciprocal.Cap.EnergyBounds sample)
    (errorTarget : InverseRootPolynomial.Coordinate) (positive : 0 < errorTarget) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularEnergyCompletion.RegularEnergyPlan request sample errorTarget :=
  let localTarget := Aggregate.perTerm errorTarget request.count
  let localPositive := Aggregate.perTerm_positive positive request.count
  let plans := ArcPlans.build degree bounds localTarget localPositive request.entries
  let fine := plans.fineMaximum
  ⟨degree, positive, bounds, localTarget, rfl, localPositive, plans, fine, rfl, plans.energyMaximum fine, rfl⟩

variable {attached : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment
  prepared} {geometry :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry
  attached}

set_option genInjectivity false in
/-- Certified success retains the original full source/cap evaluation and one actual cap energy at its sufficient common
depth. No analytic comparison or successful finite scan remains as a constructor input. -/
structure Evaluation (plan : Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularEnergyCompletion.RegularEnergyPlan request
  sample errorTarget)
    (shared : PrimitiveData.FacePrimitiveBank differential index domains)
    (geometry : CapAttachment.ReciprocalGeometry attached) (energyTarget : InverseRootPolynomial.Coordinate) where
  /-- The actual full source/cap evaluation on the original request and shared primitive bank. -/ source :
    AllSurfacePreparation.Request.Evaluation request sample shared plan.fine request.readingIndex
  /-- The actual requested cap energy acquisition at the retained sufficient energy depth. -/ energy :
    CapAccuracy.RequestedRegularEnergy geometry sample energyTarget plan.energyMinimum
  /-- The actual original cap area and retained cap energy satisfy the complete requested comparison tolerance. -/
    cap_energy_close : Data.Gaussian.Norm.Basic.normSq (source.cap.area + energy.evaluated.area) < errorTarget

constructive_injectivity Evaluation

/-- Evaluate the original surface once, acquire the retained requested cap energy and discharge all local arc errors
from the paid plan. -/
@[expose] def evaluate (plan : Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularEnergyCompletion.RegularEnergyPlan
  request sample errorTarget)
    (shared : PrimitiveData.FacePrimitiveBank differential index domains) (later : request.index ≤ index)
    (geometry : CapAttachment.ReciprocalGeometry attached) (energyTarget : InverseRootPolynomial.Coordinate) (positive :
      0 < energyTarget) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularEnergyCompletion.RegularEnergyPlan.Evaluation plan shared geometry
      energyTarget := by
  let source := request.evaluate sample shared plan.fine request.readingIndex later le_rfl
  let energy := RequestedRegularEnergy.build geometry sample plan.bounds plan.degree energyTarget positive
    plan.energyMinimum
  have fineLater : plan.plans.fineMaximum ≤ plan.fine := plan.fine_eq ▸ le_rfl
  have energyLater : plan.plans.energyMaximum plan.fine ≤ energy.request.depth := by
    rw [← plan.energyMinimum_eq]
    exact energy.request.minimum_le
  have localBounds := plan.plans.local_errors source.samples energy.request.depth fineLater energyLater
  rw [plan.localTarget_eq] at localBounds
  exact ⟨source, energy, source.cap_energy_error_requested plan.degree energy.evaluated errorTarget plan.positive
    localBounds⟩

namespace Evaluation

variable {plan : Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularEnergyCompletion.RegularEnergyPlan request sample
  errorTarget} {energyTarget : Riemann.Normalization.InverseRootPolynomial.Coordinate}

/-- The original prepared source path is compared with the same energy, with both finite area allowances retained in the
bound. -/
theorem source_energy_close (evaluated :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularEnergyCompletion.RegularEnergyPlan.Evaluation plan shared geometry
  energyTarget) :
    Data.Gaussian.Norm.Basic.normSq (evaluated.source.source.area + evaluated.energy.evaluated.area) < 2 *
      (areaTarget + errorTarget) := by
  have decomposition : evaluated.source.source.area + evaluated.energy.evaluated.area =
      (evaluated.source.source.area - evaluated.source.cap.area) +
        (evaluated.source.cap.area + evaluated.energy.evaluated.area) := by ring1
  rw [decomposition]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : InverseRootPolynomial.Coordinate) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct evaluated.source.area_close evaluated.cap_energy_close))

/-- The polygon used by the shared triangle readings keeps its internal segment-area correction, exactly as in the
original surface comparison. -/
theorem surface_energy_close (evaluated :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularEnergyCompletion.RegularEnergyPlan.Evaluation plan shared geometry
  energyTarget) :
    Data.Gaussian.Norm.Basic.normSq (evaluated.source.surface.area + evaluated.source.internalArea +
      evaluated.energy.evaluated.area) <
      2 * (areaTarget + errorTarget) := by
  have decomposition : evaluated.source.surface.area + evaluated.source.internalArea + evaluated.energy.evaluated.area =
      (evaluated.source.surface.area + evaluated.source.internalArea - evaluated.source.cap.area) +
        (evaluated.source.cap.area + evaluated.energy.evaluated.area) := by ring1
  rw [decomposition]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : InverseRootPolynomial.Coordinate) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct evaluated.source.surface_area_close evaluated.cap_energy_close))

end Evaluation
end RegularEnergyPlan

namespace Request

set_option genInjectivity false in
/-- Retain a supplied shared sample and face bank, then derive every additional subdivision from their cached data. -/
structure RegularEnergyAcquisition (request : AllSurfacePreparation.Request prepared target areaTarget floor)
  (errorTarget energyTarget : InverseRootPolynomial.Coordinate) where
  /-- The retained common polynomial stage of the supplied original sample and primitive bank. -/ index : Nat
  /-- The actual shared stage pays the original surface request. -/ later : request.index ≤ index
  /-- The original supplied cap polynomial sample at the retained common stage. -/ sample : Primitives.Sample cap
    differential index collar.box
  /-- The original supplied face primitive bank at that same actual stage. -/ shared : PrimitiveData.FacePrimitiveBank
    differential index domains
  /-- The retained original arc and energy subdivision plan tied to the supplied cap sample. -/ plan :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularEnergyCompletion.RegularEnergyPlan request sample errorTarget
  /-- The original cap attachment on the actual prepared exterior surface. -/ attached :
    AllSurfacePreparation.CapAttachment prepared
  /-- The reciprocal geometry of that exact retained cap attachment. -/ geometry : CapAttachment.ReciprocalGeometry
    attached
  /-- The actual complete source/cap and cap-energy acquisition on the retained original plan. -/ evaluated :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularEnergyCompletion.RegularEnergyPlan.Evaluation plan shared geometry
    energyTarget

constructive_injectivity RegularEnergyAcquisition

/-- Reuse the supplied original polynomial sample and primitive bank, derive sufficient subdivisions from cached bounds
and retain the complete requested energy comparison. -/
@[expose] def acquireRegularEnergy (request : AllSurfacePreparation.Request prepared target areaTarget floor)
    (degree : curve.polynomial.natDegree = 2 * genus + 2) (errorTarget energyTarget : InverseRootPolynomial.Coordinate)
    (errorPositive : 0 < errorTarget) (energyPositive : 0 < energyTarget) {index : Nat}
    (sample : Primitives.Sample cap differential index collar.box)
    (shared : PrimitiveData.FacePrimitiveBank differential index domains) (later : request.index ≤ index) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularEnergyCompletion.Request.RegularEnergyAcquisition request
      errorTarget energyTarget :=
  let bounds := EnergyBounds.build sample
  let plan := Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularEnergyCompletion.RegularEnergyPlan.build request degree
    bounds errorTarget errorPositive
  let attached := CapAttachment.build prepared
  let geometry := ReciprocalGeometry.build attached
  ⟨index, later, sample, shared, plan, attached, geometry, plan.evaluate shared later geometry energyTarget
    energyPositive⟩

end Request
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularEnergyCompletion
