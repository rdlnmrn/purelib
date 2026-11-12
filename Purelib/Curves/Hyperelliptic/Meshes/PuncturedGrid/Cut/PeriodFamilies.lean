module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison
public import Purelib.Data.Vector.Dependent
import Purelib.Approximation.Budget.PreparedPrimitiveBatchBudget
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.SynchronizedPrimitives
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Data.Vector

open Purelib.Data.Rat

open Purelib.Curves

open Purelib

open Purelib.Riemann

public section

/-!
# One numerical primitive bank across a finite family of actual periods

Heterogeneous preparations and budgets are materialized before selecting one
common polynomial index. A surface floor can be included before constructing
any numerical data. Every requested period retains that very same bank, not
an independently constructed bank at merely the same index.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {source : Differentials.Basic.Differential genus} {count :
    Nat}
  {periods : Data.Vector (CyclePrograms.CutCycleProgram lifted
    source) count}
  {domains : Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
    {differential : Fin genus}

set_option genInjectivity false in
/-- All geometric and comparison entries are stored dependent data.
Reading another cycle never reconstructs its preparation or comparison. -/
structure PrimitiveFamily (periods : Data.Vector
  (CyclePrograms.CutCycleProgram lifted source) count)
    (domains : Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
      (differential : Fin genus) where
  /-- The original dependent face bank of every retained period. -/ banks : DependentVector (fun index =>
    FaceBanks.FaceBank (periods index))
  /-- The original primitive comparison prepared for each exact retained face bank. -/ comparisons :
    DependentVector (fun index =>
    PeriodPrimitiveComparison.PrimitiveBank (banks.get index) differential)
  /-- Every retained comparison uses the original common domain bank. -/ domains_eq : ∀ index, (comparisons.get
    index).domains = domains

constructive_injectivity PrimitiveFamily

namespace PrimitiveFamily

/-- Prepare a primitive comparison for each original period bank using the same retained domains and differential. -/
@[expose] def ofBanks (banks : DependentVector (fun index =>
  FaceBanks.FaceBank (periods index)))
    (domains : Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
      (differential : Fin genus) :
    PrimitiveFamily periods domains differential :=
  let comparisons := DependentVector.ofFn fun index =>
    PeriodPrimitiveComparison.PrimitiveBank.build (banks.get index) domains
    differential
  ⟨banks, comparisons, fun index => by rw [DependentVector.ofFn_get]; rfl⟩

/-- A generated segment bank is used literally; no canonical root cover or
subdivision is required before building the finite comparison family. -/
@[expose] def ofSegments (segments : DependentVector (fun index =>
  PeriodSegmentBanks.SegmentBank (periods index).period))
    (domains : Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
      (differential : Fin genus) :
    PrimitiveFamily periods domains differential :=
  PrimitiveFamily.ofBanks (DependentVector.ofFn fun
    index => FaceBanks.FaceBank.ofSegments (periods index) (segments.get index))
    domains differential

/-- The family built from original segment banks retains the exact corresponding face bank at each index. -/
theorem ofSegments_bank (segments : DependentVector (fun index =>
  PeriodSegmentBanks.SegmentBank (periods index).period))
    (domains : Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
      (differential : Fin genus) (index : Fin count) :
    (PrimitiveFamily.ofSegments segments domains
      differential).banks.get index = FaceBanks.FaceBank.ofSegments (periods
      index) (segments.get index) :=
  DependentVector.ofFn_get _ index

variable (family : PrimitiveFamily periods domains
  differential)

set_option genInjectivity false in
/-- Select scalar tolerances for every cycle before sampling any primitive.
The maximum includes an independent surface floor and handles empty banks. -/
structure Budget (targets : Data.Vector Readings.PreparedPrimitiveChargeBounds.Coordinate count)
  (surfaceFloor : Nat) where
  /-- The original dependent scalar request for every period and its own positive target. -/ requests :
    DependentVector (fun index =>
    PeriodPrimitiveComparison.PrimitiveBank.ScalarRequest (family.comparisons.get
    index) (targets index))
  /-- The retained maximum of all original scalar-request stage floors. -/ maximum : Nat
  /-- The retained maximum equals the actual dependent request-bank maximum. -/ maximum_eq : maximum = requests.maximum
    (fun _ request => request.minimum)
  /-- The shared polynomial stage including the original surface floor. -/ index : Nat
  /-- The shared stage is exactly the maximum of surface floor and retained request maximum. -/ index_eq : index = max
    surfaceFloor maximum

constructive_injectivity Budget

namespace Budget

variable {family : PrimitiveFamily periods domains
  differential} {targets : Data.Vector Readings.PreparedPrimitiveChargeBounds.Coordinate count}
  {surfaceFloor : Nat}

section
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily.Budget
/-- Prepare every original scalar request before taking its maximum together with the supplied surface floor. -/
@[expose] def build (family : PrimitiveFamily periods domains
  differential) (targets : Data.Vector Readings.PreparedPrimitiveChargeBounds.Coordinate count)
    (positive : ∀ index, 0 < targets index) (surfaceFloor : Nat) :
      Budget family targets surfaceFloor :=
  let requests := DependentVector.ofFn fun index =>
    PeriodPrimitiveComparison.PrimitiveBank.ScalarRequest.build
    (family.comparisons.get index) (targets index) (positive index)
  let maximum := requests.maximum (fun _ request => request.minimum)
  ⟨requests, maximum, rfl, max surfaceFloor maximum, rfl⟩

/-- Each retained scalar comparison is ready at the original common budget stage. -/
theorem later (budget : Budget family targets
  surfaceFloor) (index : Fin count) :
    (budget.requests.get index).minimum ≤ budget.index := by
  rw [budget.index_eq, budget.maximum_eq]
  exact (budget.requests.get_le_maximum (fun _ request => request.minimum) index).trans (Data.Nat.Order.le_max_right _
    _)

end

/-- The retained common stage is at least the supplied surface floor. -/
theorem surface_later (budget : Budget family
  targets surfaceFloor) : surfaceFloor ≤ budget.index := by
  rw [budget.index_eq]
  exact Data.Nat.Order.le_max_left _ _

end Budget

/-- Transport the original numerical primitive bank along an equality of its domain owners. -/
@[expose] def castNumerics {first last : Face.DomainBanks.FaceDomainBank
  lifted.frames base.faces.regulars} {index : Nat}
    (equal : first = last) (numerics : Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) index first) :
    Face.PrimitiveData.FacePrimitiveBank (Periods.PeriodMatrix.standardDifferential
      differential) index last := by
  cases equal
  exact numerics

/-- Transport the original numerical primitive bank to an equal retained domain owner. -/
@[expose] def castNumerics_for_request {first last : Face.DomainBanks.FaceDomainBank
  lifted.frames base.faces.regulars} {index : Nat}
    (equal : first = last) (numerics : Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) index first) :
    Face.PrimitiveData.FacePrimitiveBank (Periods.PeriodMatrix.standardDifferential
      differential) index last := by
  cases equal
  exact numerics

/-- Transport along a domain equality retains the original numerical bank heterogeneously. -/
private theorem castNumerics_heq {first last : Face.DomainBanks.FaceDomainBank
  lifted.frames base.faces.regulars} {index : Nat}
    (equal : first = last) (numerics : Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) index first) :
    HEq (PrimitiveFamily.castNumerics equal numerics) numerics :=
      by
  cases equal
  rfl

/-- The request-oriented domain transport preserves the exact original numerical bank. -/
theorem castNumerics_heq_for_request {first last : Face.DomainBanks.FaceDomainBank
  lifted.frames base.faces.regulars} {index : Nat}
    (equal : first = last) (numerics : Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) index first) :
    HEq (PrimitiveFamily.castNumerics_for_request equal numerics)
      numerics := by
  cases equal
  rfl

variable {family : PrimitiveFamily periods domains
  differential} {targets : Data.Vector Readings.PreparedPrimitiveChargeBounds.Coordinate count}
  {surfaceFloor : Nat}

set_option genInjectivity false in
/-- A family of requested periods retaining one actual shared numerical primitive bank.

Each original period keeps its own requested stage floor together with exact common-index and heterogeneous cache
identities. -/
structure Requested (budget : Budget family
  targets surfaceFloor) (minimumStages : Data.Vector Nat count) where
  /-- The one actual numerical primitive bank shared across the entire original family. -/ numerics :
    Face.PrimitiveData.FacePrimitiveBank (Periods.PeriodMatrix.standardDifferential
    differential) budget.index domains
  /-- The retained dependent bank of period comparisons at their individual targets and minimum stages. -/ periods :
    DependentVector (fun index =>
    PeriodPrimitiveComparison.PrimitiveBank.RequestedPeriod
    (family.comparisons.get index) (targets index) (minimumStages index))
  /-- Every original period comparison uses the retained common numerical stage. -/ indices_eq : ∀ index, (periods.get
    index).locals.index = budget.index
  /-- Every period retains the very same original numerical bank after dependent owner transport. -/ numerics_eq : ∀
    index, HEq (periods.get index).locals.numerics numerics

constructive_injectivity Requested

/-- Independent producers can supply the one checked bank. Numeric caches
are only read here; acquisition constructs the actual per-cycle requests. -/
@[expose] def Budget.requestWith (budget : Budget
  family targets surfaceFloor)
    (numerics : Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) budget.index domains)
    (minimumStages : Data.Vector Nat count) :
      Requested budget minimumStages :=
  let periods := DependentVector.ofFn fun index => (budget.requests.get index).requestWith (budget.later
    index)
    (PrimitiveFamily.castNumerics (family.domains_eq index).symm
      numerics) (minimumStages index)
  { numerics := numerics
    periods := periods
    indices_eq := fun index => by rw [DependentVector.ofFn_get]; rfl
    numerics_eq := fun index => by
      rw [DependentVector.ofFn_get]
      exact HEq.trans ((budget.requests.get index).requestWith_numerics _ _ _)
        (PrimitiveFamily.castNumerics_heq_for_request _ numerics)
        }

/-- Build one numerical primitive bank at the retained shared stage and use it for every original requested period. -/
@[expose] def Budget.request (budget : Budget
  family targets surfaceFloor) (minimumStages : Data.Vector Nat count) :
  Requested budget minimumStages :=
  budget.requestWith (Face.PrimitiveData.FacePrimitiveBank.build
    (Periods.PeriodMatrix.standardDifferential differential) budget.index domains) minimumStages

/-- Requesting periods with a supplied numerical bank retains that exact bank. -/
theorem Budget.requestWith_numerics (budget :
  Budget family targets surfaceFloor)
    (numerics : Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) budget.index domains)
    (minimumStages : Data.Vector Nat count) : (budget.requestWith numerics minimumStages).numerics =
      numerics := rfl

end PrimitiveFamily
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies
