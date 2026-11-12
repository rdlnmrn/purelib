module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Selection
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.PointBanks
public import Purelib.Riemann.Readings.RectangularPointReadings.SharedMesh
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Readings.RectangularPrimitiveBoundary
import Purelib.Geometry.Rectangle.Partition.RectangularUniformGeometry

/-! # Original fragment endpoint views on a given shared primitive mesh

The two literal endpoint slots index the old shared mesh and its old
primitive values. Containment and genuine point-bank membership produce
both lookups. No primitive, anchor, offset, root, scalar observation or
mesh is prepared by this view; repeated coordinates keep both slots.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings.EndpointReadings

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
  (DomainMeshBudget DomainMeshReadings FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
  (DomainPrimitives FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
  (RegularPrimitiveFragment RegularPrimitiveFragments)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment (SheetEntry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Vector (DependentVector)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions (Interval)
open Purelib.Geometry.Rectangle.Partition.RectangularUniformGeometry (Located)
open Purelib.Riemann.Integration.PreparedParentSplitting.Geometry (allCells_mem)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Integration.RectangularSharedPrimitives
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)
open Purelib.Topology.Mesh.CoordinateTriangulation (VertexLookup)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
variable {frames : RootFrames base.bank.grid} {source : Differential genus} {axes : PrimitiveAxes base.bank.grid}
variable {parent : CenteredEdge curve source} {domains : FaceDomainBank frames base.faces.regulars}
variable {target tolerance : Rational} {request : LocalRequest parent count target}
variable {points : List Canonical} {index : Nat}
variable {numerator : CoefficientPolynomial}

section Fragment

variable {cuts : List Rational} {partition : AxisPartition 0 1 cuts} {interval : Interval}
variable {fragment : RegularPrimitiveFragment axes parent partition interval}

/-- The literal first and last endpoint slots, with separate indices even when their coordinates agree. -/
@[expose] def point (fragment : RegularPrimitiveFragment axes parent partition interval) : Fin 2 → Canonical :=
  Fin.cases fragment.located.first (fun _ => fragment.located.last)

/-- Both literal endpoints belong to the same original selected regular face. -/
theorem point_inside (fragment : RegularPrimitiveFragment axes parent partition interval) (slot : Fin 2) :
    fragment.face.located.face.cell.box.Contains (point fragment slot) := by
  refine Fin.cases ?_ (fun _ => ?_) slot
  · change fragment.face.located.face.cell.box.Contains fragment.located.first
    rewrite [fragment.face.located.cell_eq]
    exact fragment.first_inside
  · change fragment.face.located.face.cell.box.Contains fragment.located.last
    rewrite [fragment.face.located.cell_eq]
    exact fragment.last_inside

variable (assigned : SheetEntry fragment domains request)

/-- Actual split-point inclusion supplies both outer endpoints without any outside-list fallback. -/
theorem point_mem (included : ∀ value ∈ assigned.split.points, value ∈ points) (slot : Fin 2) :
    point fragment slot ∈ points :=
  Fin.cases (included _ assigned.split.first_mem_points)
    (fun _ => included _ assigned.split.last_mem_points) slot

/-- The two actual containing-cell locations on the unchanged original domain axes. -/
@[expose] def Locations := DependentVector fun slot : Fin 2 => Located assigned.domain.geometry (point fragment slot)

/-- Locate each literal endpoint once on the original retained domain geometry. -/
def locationBank : Locations assigned :=
  DependentVector.ofFn fun slot => PeriodDomain.locate assigned.domain (point fragment slot)
    (point_inside fragment slot)

/-- The two genuine lookup results on the supplied old common mesh. -/
@[expose] def Lookups (budget : DomainMeshBudget assigned.domain source points tolerance (numerator := numerator)) :=
  DependentVector fun slot : Fin 2 => VertexLookup budget.mesh.surface.mesh.vertices (point fragment slot)

/-- Look up both literal endpoints using their actual original cell locations and point-bank membership. -/
def lookupBank (budget : DomainMeshBudget assigned.domain source points tolerance (numerator := numerator))
    (locations : Locations assigned) (included : ∀ value ∈ assigned.split.points, value ∈ points) :
    Lookups assigned budget :=
  budget.lookupPoints (point fragment) locations (point_mem assigned included)

/-- The endpoint lookup vector keeps its original whole factory, ordering and actual argument expressions. -/
theorem lookupBank_factory
    (budget : DomainMeshBudget assigned.domain source points tolerance (numerator := numerator))
    (locations : Locations assigned) (included : ∀ value ∈ assigned.split.points, value ∈ points) :
    lookupBank assigned budget locations included =
      DependentVector.ofFn fun slot => budget.mesh.lookup (point fragment slot) (point_mem assigned included slot)
        (locations.get slot).column (locations.get slot).row
        (allCells_mem assigned.domain.geometry (locations.get slot).column (locations.get slot).row)
        (locations.get slot).inside := by
  unfold lookupBank
  exact DomainMeshBudget.lookupPoints_factory budget (point fragment) locations (point_mem assigned included)

variable {numerics : FacePrimitiveBank source index (numerator := numerator) domains}
variable {budgets : FaceMeshBudgets source points tolerance (numerator := numerator) domains}
variable (shared : FaceSharedMeshes (numerator := numerator) budgets numerics)
variable (included : ∀ value ∈ assigned.split.points, value ∈ points)

/-- The actual old numerical slice, mesh budget and values, two lookups and exact endpoint view.

Every computed component retains its whole factory. The heterogeneous
mesh-reading equation preserves the given old slice through the exact
face, sheet and domain transports; it introduces no new numerical bank.
-/
abbrev Cache :=
  (data : {value : DomainPrimitives assigned.domain source index (numerator := numerator) //
    value = SharedComparison.sharedPrimitives assigned numerics}) ×
  (budget : {value : DomainMeshBudget assigned.domain source points tolerance (numerator := numerator) //
    value = BankReadings.meshBudget assigned budgets}) ×
  (readings : {value : DomainMeshReadings budget.val data.val //
    HEq value (BankReadings.meshReadings assigned shared)}) ×
  (locations : {value : Locations assigned // value = locationBank assigned}) ×
  (lookups : {value : Lookups assigned budget.val //
    value = lookupBank assigned budget.val locations.val included}) ×
  {value : PointReadings data.val.anchors data.val.offsets (point fragment) //
    value = PointReadings.ofShared readings.val.readings (fun slot => (lookups.val.get slot).index)
      (point fragment) (fun slot => (lookups.val.get slot).coordinate_eq)}

/-- Finish the numerical view on the given original cache prefix and the exact retained geometric locations. -/
private def onCaches
    (data : {value : DomainPrimitives assigned.domain source index (numerator := numerator) //
      value = SharedComparison.sharedPrimitives assigned numerics})
    (budget : {value : DomainMeshBudget assigned.domain source points tolerance (numerator := numerator) //
      value = BankReadings.meshBudget assigned budgets})
    (readings : {value : DomainMeshReadings budget.val data.val //
      HEq value (BankReadings.meshReadings assigned shared)})
    (locations : {value : Locations assigned // value = locationBank assigned}) : Cache assigned shared included :=
  let lookups : {value : Lookups assigned budget.val //
      value = lookupBank assigned budget.val locations.val included} :=
    ⟨lookupBank assigned budget.val locations.val included, rfl⟩
  let reading := PointReadings.ofShared readings.val.readings (fun slot => (lookups.val.get slot).index)
    (point fragment) (fun slot => (lookups.val.get slot).coordinate_eq)
  ⟨data, budget, readings, locations, lookups, ⟨reading, rfl⟩⟩

/-- Read the old face/sheet caches once, then locate and index each endpoint without numerical reevaluation. -/
def build : Cache assigned shared included :=
  let data : {value : DomainPrimitives assigned.domain source index (numerator := numerator) //
      value = SharedComparison.sharedPrimitives assigned numerics} :=
    ⟨SharedComparison.sharedPrimitives assigned numerics, rfl⟩
  let budget : {value : DomainMeshBudget assigned.domain source points tolerance (numerator := numerator) //
      value = BankReadings.meshBudget assigned budgets} :=
    ⟨BankReadings.meshBudget assigned budgets, rfl⟩
  let readings : {value : DomainMeshReadings budget.val data.val //
      HEq value (BankReadings.meshReadings assigned shared)} :=
    ⟨BankReadings.meshReadings assigned shared, HEq.rfl⟩
  let locations : {value : Locations assigned // value = locationBank assigned} :=
    ⟨locationBank assigned, rfl⟩
  onCaches assigned shared included data budget readings locations

/-- Index the actual numerator values using the supplied SAME geometric endpoint locations.

The given locations retain their entire original factory. Only the genuine
lookups on this supplied numerical mesh and its two-slot reading view are
prepared. No Finish, Point, Query, domain, root or geometry is rebuilt.
-/
def fromLocations (locations : {value : Locations assigned // value = locationBank assigned}) :
    Cache assigned shared included :=
  let data : {value : DomainPrimitives assigned.domain source index (numerator := numerator) //
      value = SharedComparison.sharedPrimitives assigned numerics} :=
    ⟨SharedComparison.sharedPrimitives assigned numerics, rfl⟩
  let budget : {value : DomainMeshBudget assigned.domain source points tolerance (numerator := numerator) //
      value = BankReadings.meshBudget assigned budgets} :=
    ⟨BankReadings.meshBudget assigned budgets, rfl⟩
  let readings : {value : DomainMeshReadings budget.val data.val //
      HEq value (BankReadings.meshReadings assigned shared)} :=
    ⟨BankReadings.meshReadings assigned shared, HEq.rfl⟩
  onCaches assigned shared included data budget readings locations

/-- The given-location view agrees with the original complete numerical-view factory without running it for data. -/
theorem fromLocations_eq_build
    (locations : {value : Locations assigned // value = locationBank assigned}) :
    fromLocations assigned shared included locations = build assigned shared included := by
  rcases locations with ⟨locations, factory⟩
  cases factory
  unfold fromLocations build
  rfl

variable {assigned shared included} (cached : Cache assigned shared included)

/-- Read the exact old primitive polynomials, anchors, offsets and stage. -/
@[expose] def data : DomainPrimitives assigned.domain source index (numerator := numerator) := cached.1.val

/-- Read the exact old budget and unchanged common mesh. -/
@[expose] def budget : DomainMeshBudget assigned.domain source points tolerance
        (numerator := numerator) := cached.2.1.val

/-- Read the actual old shared value cache on that mesh and those same numerical primitives. -/
@[expose] def meshValues : DomainMeshReadings (budget cached) (data cached) := cached.2.2.1.val

/-- Read the two retained original cell locations. -/
@[expose] def locations : Locations assigned := cached.2.2.2.1.val

/-- Read both retained actual lookup results. -/
@[expose] def lookups : Lookups assigned (budget cached) := cached.2.2.2.2.1.val

/-- Read the two-slot view of the old primitive readings. -/
@[expose] def reading : PointReadings (data cached).anchors (data cached).offsets (point fragment) :=
  cached.2.2.2.2.2.val

/-- The numerical slice is the original whole getter result. -/
theorem data_eq : data cached = SharedComparison.sharedPrimitives assigned numerics := cached.1.property

/-- The budget is the original whole getter result. -/
theorem budget_eq : budget cached = BankReadings.meshBudget assigned budgets := cached.2.1.property

/-- The complete mesh-reading value is the original old bank read, with its actual dependent indices. -/
theorem meshValues_heq : HEq (meshValues cached) (BankReadings.meshReadings assigned shared) :=
  cached.2.2.1.property

/-- The complete two-slot geometric cache retains its whole original location factory. -/
theorem locations_eq : locations cached = locationBank assigned := cached.2.2.2.1.property

/-- Each location is the exact original endpoint-location factory result. -/
theorem location_eq (slot : Fin 2) : (locations cached).get slot =
    PeriodDomain.locate assigned.domain (point fragment slot) (point_inside fragment slot) :=
  (congrArg (fun values : Locations assigned => values.get slot) cached.2.2.2.1.property).trans
    (DependentVector.ofFn_get _ slot)

/-- Each lookup is the exact checked common-mesh factory on its retained original location. -/
theorem lookup_eq (slot : Fin 2) : (lookups cached).get slot =
    (budget cached).mesh.lookup (point fragment slot) (point_mem assigned included slot)
      ((locations cached).get slot).column ((locations cached).get slot).row
      (allCells_mem assigned.domain.geometry ((locations cached).get slot).column
        ((locations cached).get slot).row) ((locations cached).get slot).inside :=
  (congrArg (fun values : Lookups assigned (budget cached) => values.get slot)
    cached.2.2.2.2.1.property).trans
      ((congrArg (fun values : Lookups assigned (budget cached) => values.get slot)
        (lookupBank_factory assigned (budget cached) (locations cached) included)).trans
        (DependentVector.ofFn_get _ slot))

/-- The endpoint view is the original ofShared operation on these same stored lookup and value caches. -/
theorem reading_eq : reading cached = PointReadings.ofShared (meshValues cached).readings
    (fun slot => ((lookups cached).get slot).index) (point fragment)
    (fun slot => ((lookups cached).get slot).coordinate_eq) := cached.2.2.2.2.2.property

/-- Supplied geometric locations remain the same whole cache in the actual new numerical view. -/
theorem fromLocations_locations
    (keptLocations : {value : Locations assigned // value = locationBank assigned}) :
    locations (fromLocations assigned shared included keptLocations) = keptLocations.val := by
  unfold fromLocations onCaches locations
  rfl

/-- Every literal endpoint slot retains the complete original numerical mesh cell owner. -/
theorem owner_eq (slot : Fin 2) : (reading cached).owners slot =
    (budget cached).mesh.surface.owners ((lookups cached).get slot).index :=
  (congrArg (fun value : PointReadings (data cached).anchors (data cached).offsets (point fragment) =>
    value.owners slot) (reading_eq cached)).trans (PointReadings.ofShared_owner _ _ _ _ slot)

/-- Whole mesh-budget transport preserves the complete cell owner selected by the same endpoint lookup. -/
private theorem owner_lookup_congr
    {firstBudget lastBudget : DomainMeshBudget assigned.domain source points tolerance (numerator := numerator)}
    (equal : firstBudget = lastBudget) (keptLocations : Locations assigned)
    (keptIncluded : ∀ value ∈ assigned.split.points, value ∈ points) (slot : Fin 2) :
    firstBudget.mesh.surface.owners ((lookupBank assigned firstBudget keptLocations keptIncluded).get slot).index =
      lastBudget.mesh.surface.owners ((lookupBank assigned lastBudget keptLocations keptIncluded).get slot).index := by
  cases equal
  rfl

/-- Each slot's whole cell owner is the original old mesh owner at its exact checked endpoint lookup. -/
theorem owner_eq_old (slot : Fin 2) : (reading cached).owners slot =
    (BankReadings.meshBudget assigned budgets).mesh.surface.owners
      ((lookupBank assigned (BankReadings.meshBudget assigned budgets) (locations cached) included).get slot).index :=
  (owner_eq cached slot).trans
    ((congrArg (fun values : Lookups assigned (budget cached) =>
      (budget cached).mesh.surface.owners (values.get slot).index) cached.2.2.2.2.1.property).trans
      (owner_lookup_congr (assigned := assigned) (budget_eq cached) (locations cached) included slot))

/-- Every literal endpoint slot reads the actual old shared scalar cache at its genuine lookup index. -/
theorem value_eq (slot : Fin 2) : (reading cached).values slot =
    (meshValues cached).readings.values ((lookups cached).get slot).index :=
  (congrArg (fun value : PointReadings (data cached).anchors (data cached).offsets (point fragment) =>
    value.values slot) (reading_eq cached)).trans (PointReadings.ofShared_value _ _ _ _ slot)

/-- The endpoint view equals the old atPoint reading by actual mesh membership, including coincident slots. -/
theorem value_eq_atPoint (slot : Fin 2) : (reading cached).values slot =
    SharedPrimitiveValues.atPoint (meshValues cached).readings (point fragment slot) :=
  (value_eq cached slot).trans
    ((SharedPrimitiveValues.atPoint_coordinate (meshValues cached).readings
      ((lookups cached).get slot).index).symm.trans
      (congrArg (SharedPrimitiveValues.atPoint (meshValues cached).readings)
        ((lookups cached).get slot).coordinate_eq))

/-- The two-slot values equal the given old bank's original endpoint reads through the whole cached transports. -/
theorem value_eq_old_atPoint (slot : Fin 2) : (reading cached).values slot =
    SharedPrimitiveValues.atPoint (BankReadings.meshReadings assigned shared).readings (point fragment slot) :=
  (value_eq_atPoint cached slot).trans
    (DomainMeshReadings.atPoint_congr (domain := assigned.domain) (data_eq cached) (budget_eq cached)
      (meshValues_heq cached) (point fragment slot))

end Fragment

section Selected

variable {partition : AxisPartition 0 1 (axes.parameters parent)}
variable {fragments : RegularPrimitiveFragments axes parent partition partition.intervals}
variable {entries : FragmentSheets domains request fragments} {chosen : Interval}
variable {member : chosen ∈ partition.intervals}
variable (selected : FragmentSheets.Selected entries chosen member)

/-- A selected stored occurrence inherits inclusion from the original whole parent point bank. -/
theorem selected_points_mem (globalIncluded : ∀ value ∈
    PointBanks.RegularPrimitiveFragments.SheetEntries.points entries, value ∈ points)
    (value : Canonical) (present : value ∈ selected.assigned.split.points) : value ∈ points := by
  have sameRead : value ∈ (entries.at selected.position).2.split.points :=
    Eq.mp (congrArg (fun retained : Σ fragment : RegularPrimitiveFragment axes parent partition selected.interval,
      SheetEntry fragment domains request => value ∈ retained.2.split.points) selected.read_eq) present
  exact globalIncluded value
    (PointBanks.RegularPrimitiveFragments.SheetEntries.at_points_mem entries selected.position value sameRead)

/-- Index the old common numerical bank for an actual retained selected occurrence.

The only inclusion input is the same original whole point-bank inclusion
used by the parent shared-sum consumer. Actual occurrence membership and
both endpoint memberships are derived without running the selector again.
-/
def fromSelected {numerics : FacePrimitiveBank source index (numerator := numerator) domains}
    {budgets : FaceMeshBudgets source points tolerance
        (numerator := numerator) domains} (shared : FaceSharedMeshes (numerator := numerator) budgets numerics)
    (globalIncluded : ∀ value ∈ PointBanks.RegularPrimitiveFragments.SheetEntries.points entries, value ∈ points) :
    Cache selected.assigned shared (selected_points_mem selected globalIncluded) :=
  build selected.assigned shared (selected_points_mem selected globalIncluded)

end Selected

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings.EndpointReadings
