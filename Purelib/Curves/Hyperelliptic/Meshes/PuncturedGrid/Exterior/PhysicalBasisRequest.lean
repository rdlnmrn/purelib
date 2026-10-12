module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalArcAggregation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOccurrenceSchedule
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSourceRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisSamples
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.CenteredBilinearPath
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisSamples

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOccurrenceSchedule

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSourceRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Data.Rat

open Purelib.Data.Vector

open Purelib.Riemann.Periods

public section

/-! Synchronize all physical basis-pair source owners before common cap sampling. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest (BasisArcPreparations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisSamples (PhysicalBasisArcSample
  PhysicalBasisArcSamples PhysicalOccurrenceValues PhysicalOccurrenceSamples)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalArcAggregation (physicalArcError)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Riemann.Meshes.LiftedPuncturedGrid base} {differential other :
    Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}

namespace PhysicalBasisRequest

/-- The complete dependent matrix of original paired physical-source requests for the retained basis preparations. -/
@[expose] def PhysicalBasisRequests (preparations : BasisArcRequest.BasisArcPreparations regular domains) (target :
  Fraction.Rational) (minimum floor : Nat) :=
  Data.Vector.DependentVector (fun first : Fin genus => Data.Vector.DependentVector (fun second : Fin genus =>
    PhysicalSourceRequest (preparations.get first) (PeriodMatrix.standardDifferential second)
      target minimum floor))

/-- The actual physical piece counts for each original basis pair and surface occurrence. -/
@[expose] def PhysicalBasisPieceCounts (preparations : BasisArcRequest.BasisArcPreparations regular domains) :=
  (first second : Fin genus) → Fin (preparations.get first).occurrences.length → Nat

/-- The complete dependent matrix of retained occurrence schedules for the exact requests and physical piece counts. -/
@[expose] def PhysicalBasisSchedules {preparations : BasisArcRequest.BasisArcPreparations regular domains}
    {target : Fraction.Rational} {minimum floor : Nat}
    (entries : PhysicalBasisRequests
      preparations target minimum floor)
    (counts : PhysicalBasisPieceCounts
      preparations) :=
  Data.Vector.DependentVector (fun first : Fin genus => Data.Vector.DependentVector (fun second : Fin genus =>
    PhysicalOccurrenceSchedule ((entries.get first).get second) (counts first second)))

end PhysicalBasisRequest

set_option genInjectivity false in
/-- All basis pairs retain their query-refined source owners and use one physical depth, one cap depth and one numerical
stage. -/
structure PhysicalBasisRequest (regular : RegularBounds.Data cap)
    (domains : DomainBanks.FaceDomainBank lifted.frames base.faces.regulars) (target : Fraction.Rational) (minimum
      depthFloor : Nat) where
  /-- The original complete exterior preparation for every basis differential. -/ preparations :
    BasisArcRequest.BasisArcPreparations regular domains
  /-- The cached original physical-source request for every basis pair. -/ entries :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisRequest.PhysicalBasisRequests preparations target
    minimum depthFloor
  /-- The actual retained physical piece counts for every basis pair and occurrence. -/ pieceCounts :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisRequest.PhysicalBasisPieceCounts preparations
  /-- The cached original occurrence schedules synchronized to the common physical depth. -/ schedules :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisRequest.PhysicalBasisSchedules entries pieceCounts
  /-- The common physical trace depth retained by every original basis-pair schedule. -/ physicalDepth : Nat
  /-- Every retained basis-pair schedule uses exactly the common physical depth. -/ physicalDepth_eq : ∀ first second,
    ((schedules.get first).get second).physicalDepth = physicalDepth
  /-- The common numerical stage paying all original basis-pair schedules and the requested minimum. -/ index : Nat
  /-- The common numerical stage is exactly the maximum of the minimum and retained schedule indices. -/ index_eq :
    index = max minimum (schedules.maximum fun _ row => row.maximum fun _ schedule => schedule.index)
  /-- The requested numerical minimum is paid at the common stage. -/ minimum_le : minimum ≤ index
  /-- Every original basis-pair schedule is paid at the common numerical stage. -/ index_ge : ∀ first second,
    ((schedules.get first).get second).index ≤ index
  /-- The common cap depth paying all original basis-pair spatial requirements. -/ depth : Nat
  /-- The common cap depth is exactly the maximum of the requested floor and retained schedule depths. -/ depth_eq :
    depth = max depthFloor (schedules.maximum fun _ row => row.maximum fun _ schedule => schedule.depth)
  /-- The requested cap-depth floor is paid at the common depth. -/ depthFloor_le : depthFloor ≤ depth
  /-- Every original basis-pair schedule is paid at the common cap depth. -/ depth_ge : ∀ first second, ((schedules.get
    first).get second).depth ≤ depth

constructive_injectivity PhysicalBasisRequest

namespace PhysicalBasisRequest

/-- The maxima depend only on the finite requests, before the common cap polynomials or any fine source paths are
sampled. -/
@[expose] def build (preparations : BasisArcRequest.BasisArcPreparations regular domains)
    (pieceCounts : PhysicalBasisPieceCounts
      preparations)
    (target : Fraction.Rational) (positive : 0 < target) (minimum depthFloor physicalFloor : Nat) :
    PhysicalBasisRequest regular domains target
      minimum depthFloor := by
  let entries : PhysicalBasisRequests
    preparations target minimum depthFloor := DependentVector.ofFn fun first =>
    DependentVector.ofFn fun second =>
      PhysicalSourceRequest.build (preparations.get first) (PeriodMatrix.standardDifferential second) target positive
        minimum depthFloor
  let initial : PhysicalBasisSchedules entries
    pieceCounts := DependentVector.ofFn fun first =>
    DependentVector.ofFn fun second =>
      PhysicalOccurrenceSchedule.build ((entries.get first).get second) (pieceCounts first second)
  let physicalDepth := max physicalFloor (initial.maximum fun _ row => row.maximum fun _ schedule =>
    schedule.physicalDepth)
  have physicalLe (first second : Fin genus) : ((initial.get first).get second).physicalDepth ≤ physicalDepth :=
    ((initial.get first).get_le_maximum (fun _ schedule => schedule.physicalDepth) second).trans
      ((initial.get_le_maximum (fun _ row => row.maximum fun _ schedule => schedule.physicalDepth) first).trans
        (Data.Nat.Order.le_max_right _ _))
  let schedules : PhysicalBasisSchedules entries
    pieceCounts := DependentVector.ofFn fun first =>
    DependentVector.ofFn fun second =>
      ((initial.get first).get second).atPhysicalDepth physicalDepth (physicalLe first second)
  let index := max minimum (schedules.maximum fun _ row => row.maximum fun _ schedule => schedule.index)
  let depth := max depthFloor (schedules.maximum fun _ row => row.maximum fun _ schedule => schedule.depth)
  refine ⟨preparations, entries, pieceCounts, schedules, physicalDepth, ?_, index, rfl,
    Data.Nat.Order.le_max_left _ _, ?_, depth, rfl, Data.Nat.Order.le_max_left _ _, ?_⟩
  · intro first second
    have outer := DependentVector.ofFn_get (fun first =>
      DependentVector.ofFn fun second =>
        ((initial.get first).get second).atPhysicalDepth physicalDepth (physicalLe first second)) first
    have row := congrArg (fun row => (row.get second).physicalDepth) outer
    have inner := DependentVector.ofFn_get (fun second =>
      ((initial.get first).get second).atPhysicalDepth physicalDepth (physicalLe first second)) second
    exact row.trans (congrArg (fun schedule => schedule.physicalDepth) inner)
  · intro first second
    exact ((schedules.get first).get_le_maximum (fun _ schedule => schedule.index) second).trans
      ((schedules.get_le_maximum (fun _ row => row.maximum fun _ schedule => schedule.index) first).trans
        (Data.Nat.Order.le_max_right _ _))
  · intro first second
    exact ((schedules.get first).get_le_maximum (fun _ schedule => schedule.depth) second).trans
      ((schedules.get_le_maximum (fun _ row => row.maximum fun _ schedule => schedule.depth) first).trans
        (Data.Nat.Order.le_max_right _ _))

/-- Retain a complete-surface spatial lower bound while selecting exterior owners. -/
theorem build_physicalFloor_le (preparations : BasisArcRequest.BasisArcPreparations regular domains)
    (pieceCounts : PhysicalBasisPieceCounts
      preparations)
    (target : Fraction.Rational) (positive : 0 < target) (minimum depthFloor physicalFloor : Nat) :
    physicalFloor ≤ (build
      preparations pieceCounts target positive minimum depthFloor physicalFloor).physicalDepth :=
  Data.Nat.Order.le_max_left _ _

variable {target : Data.Rat.Fraction.Rational} {minimum depthFloor stage depth : Nat} {box :
  Geometry.Rational.Box}

/-- The entries retain every pair's actual source evaluations at the shared stage and depth, including their
per-occurrence refinement certificates. -/
@[expose] def Evaluations (request :
  PhysicalBasisRequest regular domains target
  minimum depthFloor)
    (polynomials : CapBasisEnergy.RegularBasisPolynomials cap stage box) (depth : Nat) :=
  Data.Vector.DependentVector (fun first : Fin genus => Data.Vector.DependentVector (fun second : Fin genus =>
    ((request.schedules.get first).get second).Evaluations (depth := depth)
      (polynomials.get first) (polynomials.get second)))

/-- Evaluate every retained query-refined basis-pair source owner once using the shared original polynomial bank at a
paid common stage. -/
@[expose] def evaluate (request :
  PhysicalBasisRequest regular domains target
  minimum depthFloor)
    (polynomials : CapBasisEnergy.RegularBasisPolynomials cap stage box)
    (chart : HyperellipticReciprocal.originOrder curve = 0)
    (later : request.index ≤ stage) :
    request.Evaluations polynomials depth :=
  DependentVector.ofFn fun first => DependentVector.ofFn fun second =>
    let pair := (request.schedules.get first).get second
    pair.evaluate (polynomials.get first) (polynomials.get second) chart
      ((request.index_ge first second).trans later)

/-- Later common cap depths pay each pair's source-run refinement requirement. -/
theorem source_refined (request :
  PhysicalBasisRequest regular domains target
  minimum depthFloor)
    {depth : Nat} (spatial : request.depth ≤ depth) (first second : Fin genus)
    (i : Fin (request.preparations.get first).occurrences.length) :
    let pair := (request.schedules.get first).get second
    (pair.entries.get i).refinement.depth ≤ (pair.entries.get i).sources.plan.parents.depth + pair.fine depth i :=
  ((request.schedules.get first).get second).source_refined ((request.depth_ge first second).trans spatial) i

/-- Counts and vertex values belong to the retained physical side samples. -/
@[expose] def Counts (request :
  PhysicalBasisRequest regular domains target
  minimum depthFloor) :=
  (first second : Fin genus) → Fin (request.preparations.get first).occurrences.length → Nat

/-- The exact original physical vertex values for every basis pair and retained occurrence count. -/
@[expose] def Values (request :
  PhysicalBasisRequest regular domains target
  minimum depthFloor) (counts : request.Counts) :=
  (first second : Fin genus) → PhysicalBasisSamples.PhysicalOccurrenceValues (request.preparations.get first) (counts
    first second)

/-- The complete dependent matrix of cached conjugate centered samples on those original physical values. -/
@[expose] def Samples (request :
  PhysicalBasisRequest regular domains target
  minimum depthFloor)
    {counts : request.Counts} (values : request.Values counts) :=
  Data.Vector.DependentVector (fun first : Fin genus => Data.Vector.DependentVector (fun second : Fin genus =>
    PhysicalBasisSamples.PhysicalOccurrenceSamples (values first second)))

/-- Every original physical occurrence sample meets its exact basis-pair arc-error allowance at the supplied common cap
depth. -/
@[expose] def Accurate (request :
  PhysicalBasisRequest regular domains target
  minimum depthFloor)
    (polynomials : CapBasisEnergy.RegularBasisPolynomials cap stage box) (depth : Nat)
    {counts : request.Counts} {values : request.Values counts} (samples : request.Samples values) : Prop :=
  ∀ first second i, Data.Gaussian.Norm.Basic.normSq (PhysicalArcAggregation.physicalArcError
    ((request.preparations.get first).occurrences[i.val]'i.isLt)
    (polynomials.get first) (polynomials.get second) depth
    ((((samples.get first).get second).get i).centeredArea)) <
      ((request.entries.get first).get second).allowance

/-- Assemble the physical basis matrix from existing sample banks and their side-comparison certificates. Source
evaluations and physical samples are reused. -/
@[expose] def assemble (request :
  PhysicalBasisRequest regular domains target
  minimum depthFloor)
    (polynomials : CapBasisEnergy.RegularBasisPolynomials cap stage box)
    (evaluated : request.Evaluations polynomials depth)
    (spatial : request.depth ≤ depth)
    (counts : request.Counts) (values : request.Values counts) (samples : request.Samples values)
    (accurate : request.Accurate polynomials depth samples) :
    PhysicalBasisSamples.PhysicalBasisArcSamples (regular := regular) (domains := domains) polynomials target minimum
      depthFloor depth :=
  DependentVector.ofFn fun first => DependentVector.ofFn fun second =>
    PhysicalBasisArcSample.ofSamples (request.preparations.get first) ((request.entries.get first).get second)
      (request.pieceCounts first second) ((request.schedules.get first).get second)
      ((evaluated.get first).get second) ((request.depth_ge first second).trans spatial) (counts first second) (values
        first second)
      ((samples.get first).get second) (accurate first second)

end PhysicalBasisRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
