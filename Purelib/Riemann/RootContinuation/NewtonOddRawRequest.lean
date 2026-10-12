module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.CoercivitySchedule
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
public import Purelib.Riemann.RootContinuation.NewtonOddCoercivityPreparation
import Purelib.Riemann.RootContinuation.NewtonRawEnergyGrid
public import Purelib.Riemann.Periods.NewtonRawPeriodSchedule
public import Purelib.Riemann.RootContinuation.NewtonRawOddExteriorSchedule
public import Purelib.Riemann.Periods.NewtonRawPeriodGeometry
public import Purelib.Riemann.RootContinuation.NewtonOriginalEnergyComparison
import Purelib.Riemann.RootContinuation.NewtonOddSourcePreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest
import Purelib.Riemann.Periods.NewtonCanonicalPeriodReadback
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.RootContinuation.NewtonHomogeneousAnnularRequest
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PartitionBankCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Riemann.RootContinuation.NewtonRawEnergyBudget
import Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousCutRequest
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRawOddEnergyBudget
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Topology.NewtonRawSewingSchedule
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Riemann.Topology.NewtonObservationSurfaceLower
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Riemann.RootContinuation.NewtonCanonicalMatrixRequest
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.Topology.NewtonOddSurfaceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Polynomial.Dense.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.QuotientFreeOmega

public section

/-! A computed common tail for odd raw coercivity on the original corrected period owner. -/
namespace Purelib.Riemann.RootContinuation.NewtonOddRawRequest

open Purelib

open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Riemann.Normalization
open Purelib.Riemann.RootContinuation.NewtonRawEnergyGrid (RawEnergyGrid)
open Purelib.Riemann.Topology.NewtonOddSurfaceGeometry (OddSurfaceGeometry)
open Purelib.Riemann.RootContinuation.NewtonOddSourcePreparation (OddSourcePreparation)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis (CoercivitySchedule)
open Purelib.Riemann.RootContinuation.NewtonRawEnergyBudget (rawEnergyAllowance)
open Purelib.Riemann.Periods.NewtonRawPeriodSchedule (RawPeriodSchedule)
open Purelib.Riemann.RootContinuation.NewtonOriginalEnergyComparison (OriginalEnergyComparison)
open Purelib.Riemann.Periods.NewtonRawPeriodGeometry (periodGeometry)
open Purelib.Riemann.Periods.NewtonCanonicalPeriodReadback (canonicalPeriodSheet)
open Purelib.Riemann.Topology.NewtonRawSewingSchedule (SewingSchedule)
open Purelib.Riemann.RootContinuation.NewtonRawOddExteriorSchedule (OddExteriorSchedule)
open Purelib.Riemann.RootContinuation.NewtonOddCoercivityPreparation.OddSourcePreparation (ownerLengths coercivity)
open Purelib.Riemann.Topology.NewtonObservationSurfaceLower (surfaceLowerConstant surfaceLowerConstant_positive)

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin
    2}
  {ordered : Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank
    sheet} {paired : Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered}
  (prepared : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
  (observations : ProtectedObservations base.bank.toBranchCellBank)
  (preparation : NewtonPreparation base.bank.toBranchCellBank) (radius : Data.Rat.Fraction.Rational)
  {collar : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  (regular : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap)

namespace OddRawRequestTypes

variable {observations preparation radius regular}
  (grid : RawEnergyGrid observations preparation radius)

/-- Odd surface geometry over the exact retained raw-energy grid. -/
@[expose] def Geometry := OddSurfaceGeometry observations grid.partitions regular grid.domains

/-- Odd source preparation indexed by the retained geometry, basis and floor. -/
@[expose] def Source (geometry : Geometry (regular := regular) grid) (first : Fin genus) (floor : Nat) :=
  OddSourcePreparation observations grid.partitions regular grid.domains geometry first floor

open Purelib.Curves.Hyperelliptic in
/-- Coercivity schedule retaining the original grid and source acquisition.

Keeps the exact owner lengths, excision, compatible partitions and raw-energy allowance with both original numerical
floors. -/
@[expose] def Coercivity {geometry : Geometry (regular := regular) grid} {first : Fin genus} {floor : Nat}
    (source : Source grid geometry first floor) :=
  Curves.Hyperelliptic.Meshes.Newton.Basis.CoercivitySchedule geometry.shared source.acquired
    (ownerLengths source) floor floor grid.excision grid.compatible
    (rawEnergyAllowance observations)

/-- Numerical index of the retained odd coercivity schedule. -/
@[expose] def stage {geometry : Geometry (regular := regular) grid} {first : Fin genus} {floor : Nat}
    {source : Source grid geometry first floor} (schedule : Coercivity grid source) : Nat := schedule.index

end OddRawRequestTypes

open Purelib.Curves.Hyperelliptic in
set_option genInjectivity false in
/-- Synchronized raw-energy request for an odd-degree curve.

Retains the degree and ramification certificates, actual grid, geometry and source, sewing and period requests, selected
refined sheet, exterior joining, coercivity and original-energy comparison. -/
structure OddRawRequest (first : Fin genus) (floor : Nat) where
  /-- The original polynomial has degree twice the genus plus one. -/ degree : curve.polynomial.natDegree = 2 * genus +
    1
  /-- The reciprocal origin has ramification order one. -/ branch :
    Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1
  /-- Actual retained raw-energy grid. -/ grid : RawEnergyGrid observations preparation radius
  /-- Shared odd surface geometry on that exact grid. -/ geometry : OddRawRequestTypes.Geometry (regular := regular)
    grid
  /-- Original odd source preparation at the selected basis and floor. -/ source : OddRawRequestTypes.Source grid
    geometry first floor
  /-- Sewing and annular requests for the retained grid. -/ sewing : SewingSchedule grid floor
  /-- Selected sheet of the refined period geometry. -/ newSheet : Fin 2
  /-- The selected sheet is exactly the canonical period sheet. -/ sheet_eq : newSheet = canonicalPeriodSheet (lifted :=
    lifted) (sheet := sheet) (periodGeometry grid)
  /-- Physical period and cut requests retaining the selected sheet. -/ period : RawPeriodSchedule prepared sewing
    newSheet floor floor
  /-- Odd exterior joining schedule retaining the sewing data. -/ joining : OddExteriorSchedule grid sewing floor
  /-- Actual source coercivity schedule for the retained grid. -/ coercivity : OddRawRequestTypes.Coercivity grid source
  /-- Original-energy comparison at half the protected surface lower constant. -/ comparison : OriginalEnergyComparison
    prepared (periodGeometry grid) (surfaceLowerConstant observations / 2) floor
  /-- Common numerical index for the retained request families. -/ index : Nat
  /-- Exact nested maximum of period, joining, coercivity and comparison indices. -/ index_eq : index = max
    period.cut.index (max joining.index (max (OddRawRequestTypes.stage grid coercivity) comparison.request.index))

constructive_injectivity OddRawRequest

namespace OddRawRequest

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- Assemble the odd raw-energy request on a retained grid.

Derives origin order one from the odd degree, constructs each dependent request using the same grid owners, and records
the exact maximum of their numerical indices. -/
@[expose] def build (grid : RawEnergyGrid observations preparation radius) (first : Fin genus) (floor : Nat)
    (degree : curve.polynomial.natDegree = 2 * genus + 1) :
    OddRawRequest prepared observations preparation radius regular first floor := by
  have branch : Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1 := by
    have balance := Charts.Reciprocal.HyperellipticReciprocal.degree_balance curve
    rw [degree] at balance
    omega
  let geometry := OddSurfaceGeometry.build observations grid.partitions regular grid.domains
  let source := OddSourcePreparation.build observations grid.partitions regular grid.domains geometry first floor
  let sewing := SewingSchedule.build grid floor
  let newSheet := canonicalPeriodSheet (lifted := lifted) (sheet := sheet) (periodGeometry grid)
  let period := RawPeriodSchedule.build prepared sewing newSheet floor floor
  let joining := OddExteriorSchedule.build grid sewing floor
  let coercivity := NewtonOddCoercivityPreparation.OddSourcePreparation.coercivity
    source grid.excision grid.compatible floor branch
  let comparison := OriginalEnergyComparison.build prepared (periodGeometry grid) (surfaceLowerConstant observations /
    2)
    (Fraction.Order.Field.div_pos_direct (surfaceLowerConstant_positive observations) (by decide)) floor
  exact ⟨degree, branch, grid, geometry, source, sewing, newSheet, rfl, period, joining, coercivity, comparison,
    max period.cut.index (max joining.index (max (OddRawRequestTypes.stage grid coercivity) comparison.request.index)),
      rfl⟩

variable {prepared observations preparation radius regular} {first : Fin genus} {floor : Nat}
  (request : OddRawRequest prepared observations preparation radius regular first floor)

/-- The retained period cut index lies below the raw request index. -/
theorem period_le : request.period.cut.index ≤ request.index := by
  rw [request.index_eq]
  exact Data.Nat.Order.le_max_left _ _

/-- The exterior joining schedule index lies below the raw request index. -/
theorem joining_le : request.joining.index ≤ request.index := by
  rw [request.index_eq]
  exact (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_right _ _)

/-- The retained coercivity stage lies below the raw request index. -/
theorem coercivity_le : OddRawRequestTypes.stage request.grid request.coercivity ≤ request.index := by
  rw [request.index_eq]
  exact (Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _
    _))

/-- The original-energy matrix comparison index lies below the raw request index. -/
theorem comparison_le : request.comparison.request.index ≤ request.index := by
  rw [request.index_eq]
  exact (Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _
    _))

/-- The actual sewing request index lies below the raw request index. -/
theorem sewing_le : request.sewing.sewing.index ≤ request.index :=
  request.sewing.sewing_le.trans ((request.joining.sewing_le request.grid request.sewing).trans request.joining_le)

/-- The actual annular request index lies below the raw request index. -/
theorem annular_le : request.sewing.annular.index ≤ request.index :=
  request.sewing.annular_le.trans ((request.joining.sewing_le request.grid request.sewing).trans request.joining_le)

/-- The odd raw request respects its requested floor. -/
theorem floor_le : floor ≤ request.index := request.coercivity.floor_le.trans request.coercivity_le

end OddRawRequest
end Purelib.Riemann.RootContinuation.NewtonOddRawRequest
