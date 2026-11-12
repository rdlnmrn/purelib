module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings.Endpoints
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Endpoints.Primitives
public import Purelib.Data.List.DependentProduct
import Purelib.Data.Vector.Dependent
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-! # Retained original fragment occurrences and their actual internal gaps

Each literal occurrence keeps one finish Point/Query cache and one old
shared-mesh endpoint view. Boundary selection reindexes the whole stored
occurrence. Internal joins consume those same values in parameter order.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.FragmentSheets

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.PointBanks
open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
  (RegularPrimitiveFragment RegularPrimitiveFragments)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment
  (SheetEntry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment.SheetEntry
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Vector (DependentVector)
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions (Interval)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_succ sumFin_congr)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
variable {frames : RootFrames base.bank.grid} {source : Differential genus} {axes : PrimitiveAxes base.bank.grid}
variable {parent : CenteredEdge curve source} {domains : FaceDomainBank frames base.faces.regulars}
variable {target tolerance : Rational} {request : LocalRequest parent count target}
variable {points : List Canonical} {index : Nat}
variable {numerator : CoefficientPolynomial}
variable {budgets : FaceMeshBudgets source points tolerance (numerator := numerator) domains}
variable {numerics : Face.PrimitiveData.FacePrimitiveBank source index (numerator := numerator) domains}
variable (shared : FaceSharedMeshes (numerator := numerator) budgets numerics)
variable {partition : AxisPartition 0 1 (axes.parameters parent)}

/-- The original fragment and whole SheetEntry at one literal parameter interval. -/
abbrev OccurrencePair (interval : Interval) :=
  Σ fragment : RegularPrimitiveFragment axes parent partition interval, SheetEntry fragment domains request

/-- One actual original finish and old numerical endpoint view, with their complete factory equations. -/
abbrev Occurrence {interval : Interval} {fragment : RegularPrimitiveFragment axes parent partition interval}
    (assigned : SheetEntry fragment domains request) :=
  (included : {_value : Unit // ∀ value ∈ assigned.split.points, value ∈ points}) ×
  {value : Finish assigned // value = Finish.build assigned} ×
  {value : EndpointReadings.Cache assigned shared included.property //
    value = EndpointReadings.build assigned shared included.property}

namespace Occurrence

variable {shared} {interval : Interval} {fragment : RegularPrimitiveFragment axes parent partition interval}
variable {assigned : SheetEntry fragment domains request}

/-- Acquire the actual finish once and index the old shared readings once, retaining both original factories. -/
def build (assigned : SheetEntry fragment domains request)
    (included : ∀ value ∈ assigned.split.points, value ∈ points) : Occurrence shared assigned :=
  let member : {_value : Unit // ∀ value ∈ assigned.split.points, value ∈ points} := ⟨(), included⟩
  let finish : {value : Finish assigned // value = Finish.build assigned} := ⟨Finish.build assigned, rfl⟩
  let view : {value : EndpointReadings.Cache assigned shared member.property //
      value = EndpointReadings.build assigned shared member.property} :=
    ⟨EndpointReadings.build assigned shared member.property, rfl⟩
  ⟨member, finish, view⟩

variable (kept : Occurrence shared assigned)

include kept in
/-- Read the same actual membership certificate used for the old mesh lookups. -/
theorem included : ∀ value ∈ assigned.split.points, value ∈ points := kept.1.property

/-- Read the sole retained finish Point, Query, Entry and original root comparison. -/
@[expose] def finish : Finish assigned := kept.2.1.val

/-- Read the sole old numerical endpoint view. -/
@[expose] def view : EndpointReadings.Cache assigned shared kept.included := kept.2.2.val

/-- Read the old numerical primitive slice, retaining its nominal domain and actual stage. -/
@[expose] def data : DomainPrimitives assigned.domain source index
        (numerator := numerator) := EndpointReadings.data kept.view

/-- Read the same two old endpoint reading slots and complete numerical owners. -/
@[expose] def reading : PointReadings kept.data.anchors kept.data.offsets (EndpointReadings.point fragment) :=
  EndpointReadings.reading kept.view

/-- Read the literal old incoming value. -/
@[expose] def initial : Canonical := kept.reading.values 0

/-- Read the separate literal old finish value. -/
@[expose] def terminal : Canonical := kept.reading.values 1

/-- The finish is the complete original factory on this actual SheetEntry. -/
theorem finish_eq : kept.finish = Finish.build assigned := kept.2.1.property

/-- The endpoint view is the complete original factory on the same assigned entry and old banks. -/
theorem view_eq : kept.view = EndpointReadings.build assigned shared kept.included := kept.2.2.property

/-- Abstract certified occurrence fields retain the same complete original occurrence factory. -/
private theorem fromCaches_eq_build
    (member : {_value : Unit // ∀ value ∈ assigned.split.points, value ∈ points})
    (finish : {value : Finish assigned // value = Finish.build assigned})
    (view : {value : EndpointReadings.Cache assigned shared member.property //
      value = EndpointReadings.build assigned shared member.property}) :
    (⟨member, finish, view⟩ : Occurrence shared assigned) =
      build (shared := shared) assigned member.property := by
  rcases member with ⟨token, included⟩
  cases token
  have finishEq : finish = ⟨Finish.build assigned, rfl⟩ := Subtype.ext finish.property
  have viewEq : view = ⟨EndpointReadings.build assigned shared included, rfl⟩ := Subtype.ext view.property
  cases finishEq
  cases viewEq
  unfold build
  rfl

section Numerator

variable {newNumerator : CoefficientPolynomial} {newIndex : Nat} {newTolerance : Rational}
variable {newBudgets : FaceMeshBudgets source points newTolerance (numerator := newNumerator) domains}
variable {newNumerics : Face.PrimitiveData.FacePrimitiveBank source newIndex
  (numerator := newNumerator) domains}
variable (newShared : FaceSharedMeshes (numerator := newNumerator) newBudgets newNumerics)

/-- Prepare true new-numerator values on the SAME given physical occurrence and retained endpoint locations.

The entire old finish subtype is forwarded unchanged. The original location
cache is supplied to the existing endpoint-view worker; only real lookups
and readings of the new numerical bank are computed. The old occurrence
is an input cache, never a request to execute its producer again.
-/
def revalue : Occurrence newShared assigned :=
  let member := kept.1
  let finish := kept.2.1
  let view : {value : EndpointReadings.Cache assigned newShared member.property //
      value = EndpointReadings.build assigned newShared member.property} :=
    ⟨EndpointReadings.fromLocations assigned newShared member.property kept.view.2.2.2.1,
      EndpointReadings.fromLocations_eq_build assigned newShared member.property kept.view.2.2.2.1⟩
  ⟨member, finish, view⟩

/-- The new numerical occurrence forwards the exact complete original Finish cache. -/
theorem revalue_finish : (kept.revalue newShared).finish = kept.finish := by
  unfold revalue finish
  rfl

/-- The new numerical view retains the exact complete original two-slot geometric location cache. -/
theorem revalue_locations : EndpointReadings.locations (kept.revalue newShared).view =
    EndpointReadings.locations kept.view := by
  unfold revalue view
  exact EndpointReadings.fromLocations_locations (assigned := assigned) (shared := newShared)
    (included := kept.1.property) kept.view.2.2.2.1

/-- The new occurrence's whole factory is derived from its retained field factories, without running the factory. -/
theorem revalue_eq_build : kept.revalue newShared = build (shared := newShared) assigned kept.included := by
  unfold revalue
  exact fromCaches_eq_build (shared := newShared) kept.1 kept.2.1 _

end Numerator

/-- Transport a whole cached occurrence along equality of its complete original fragment/Entry pair. -/
def castPair {interval : Interval}
    {first last : OccurrencePair (axes := axes) (partition := partition)
      (domains := domains) (request := request) interval}
    (equal : first = last) (kept : Occurrence shared first.2) : Occurrence shared last.2 := by
  cases equal
  exact kept

/-- Whole-pair transport preserves the entire cached finish and numerical view. -/
theorem castPair_heq {interval : Interval}
    {first last : OccurrencePair (axes := axes) (partition := partition)
      (domains := domains) (request := request) interval}
    (equal : first = last) (kept : Occurrence shared first.2) : HEq (castPair equal kept) kept := by
  cases equal
  rfl

/-- Whole-pair transport preserves the actual original incoming scalar. -/
theorem castPair_initial {interval : Interval}
    {first last : OccurrencePair (axes := axes) (partition := partition)
      (domains := domains) (request := request) interval}
    (equal : first = last) (kept : Occurrence shared first.2) : (castPair equal kept).initial = kept.initial := by
  cases equal
  rfl

/-- Whole-pair transport preserves the actual original finish scalar. -/
theorem castPair_terminal {interval : Interval}
    {first last : OccurrencePair (axes := axes) (partition := partition)
      (domains := domains) (request := request) interval}
    (equal : first = last) (kept : Occurrence shared first.2) : (castPair equal kept).terminal = kept.terminal := by
  cases equal
  rfl

end Occurrence

variable {intervals : List Interval} {fragments : RegularPrimitiveFragments axes parent partition intervals}
variable (entries : FragmentSheets domains request fragments)

/-- Actual source-read equality transports the original whole point inclusion to this retained pair. -/
private theorem includedAt (included : ∀ value ∈
    RegularPrimitiveFragments.SheetEntries.points entries, value ∈ points)
    (position : Fin intervals.length) (kept : {value : OccurrencePair (request := request)
      (intervals[position.val]'position.isLt) // value = entries.at position})
    (value : Canonical) (member : value ∈ kept.val.2.split.points) : value ∈ points := by
  have present : value ∈ (entries.at position).2.split.points :=
    Eq.mp (congrArg (fun pair : OccurrencePair (request := request) (intervals[position.val]'position.isLt) =>
      value ∈ pair.2.split.points) kept.property) member
  exact included value
    (RegularPrimitiveFragments.SheetEntries.at_points_mem entries position value present)

/-- An actual bounded occurrence read and its complete cached finish/numerical product. -/
abbrev Leaf (position : Fin intervals.length) :=
  Σ kept : {value : OccurrencePair (request := request) (intervals[position.val]'position.isLt) //
      value = entries.at position}, Occurrence shared kept.val.2

/-- The original interval-indexed product retains one actual leaf per fragment occurrence. -/
abbrev Leaves := DependentProduct intervals (Leaf shared entries)

/-- Materialize the one original bounded leaf at its actual retained interval position. -/
def buildLeaf (included : ∀ value ∈ RegularPrimitiveFragments.SheetEntries.points entries,
    value ∈ points) (position : Fin intervals.length) : Leaf shared entries position :=
  let kept : {value : OccurrencePair (request := request) (intervals[position.val]'position.isLt) //
      value = entries.at position} := ⟨entries.at position, rfl⟩
  let occurrence := Occurrence.build (shared := shared) kept.val.2 (includedAt entries included position kept)
  ⟨kept, occurrence⟩

/-- Materialize each actual read, finish and old endpoint view once in original interval order. -/
def buildLeaves (included : ∀ value ∈ RegularPrimitiveFragments.SheetEntries.points entries,
    value ∈ points) : Leaves shared entries :=
  DependentProduct.ofFn intervals (buildLeaf shared entries included)

namespace Leaf

variable {shared entries} {position : Fin intervals.length} (leaf : Leaf shared entries position)

/-- Read the actual retained whole original fragment/Entry pair. -/
@[expose] def pair : OccurrencePair (axes := axes) (partition := partition) (domains := domains) (request := request)
    (intervals[position.val]'position.isLt) := leaf.1.val

/-- Read the same complete original cached occurrence. -/
@[expose] def occurrence : Occurrence shared leaf.pair.2 := leaf.2

/-- The complete pair is its actual original bounded source read. -/
theorem pair_eq : leaf.pair = entries.at position := leaf.1.property

section Numerator

variable {newNumerator : CoefficientPolynomial} {newIndex : Nat} {newTolerance : Rational}
variable {newBudgets : FaceMeshBudgets source points newTolerance (numerator := newNumerator) domains}
variable {newNumerics : Face.PrimitiveData.FacePrimitiveBank source newIndex
  (numerator := newNumerator) domains}
variable (newShared : FaceSharedMeshes (numerator := newNumerator) newBudgets newNumerics)

/-- Reuse the same retained whole fragment/Entry pair and physical Finish for the genuine new numerical bank. -/
def revalue : Leaf newShared entries position := ⟨leaf.1, leaf.2.revalue newShared⟩

/-- The actual complete fragment/Entry pair is forwarded unchanged to the new numerator view. -/
theorem revalue_pair : (leaf.revalue newShared).pair = leaf.pair := by
  unfold revalue pair
  rfl

/-- The retained physical Finish keeps its entire original query, Point, Entry, comparison and factory. -/
theorem revalue_finish : HEq (leaf.revalue newShared).occurrence.finish leaf.occurrence.finish :=
  heq_of_eq (Occurrence.revalue_finish leaf.2 newShared)

/-- The revalued cache's factory follows its original whole source read and retained field factories. -/
theorem revalue_eq_buildLeaf
    (included : ∀ value ∈ RegularPrimitiveFragments.SheetEntries.points entries, value ∈ points) :
    leaf.revalue newShared = buildLeaf newShared entries included position := by
  rcases leaf with ⟨⟨pair, factory⟩, occurrence⟩
  cases factory
  unfold revalue buildLeaf
  exact congrArg
    (fun value : Occurrence newShared (entries.at position).2 =>
      (⟨⟨entries.at position, rfl⟩, value⟩ : Leaf newShared entries position))
    (Occurrence.revalue_eq_build occurrence newShared)

end Numerator

end Leaf

section NumeratorLeaves

variable {newNumerator : CoefficientPolynomial} {newIndex : Nat} {newTolerance : Rational}
variable {newBudgets : FaceMeshBudgets source points newTolerance (numerator := newNumerator) domains}
variable {newNumerics : Face.PrimitiveData.FacePrimitiveBank source newIndex
  (numerator := newNumerator) domains}
variable (newShared : FaceSharedMeshes (numerator := newNumerator) newBudgets newNumerics)

/-- Materialize the true new numerical leaves from the GIVEN physical product, without another source read or Finish.

The original certified finite-product operation consumes each actual
retained leaf and its derived factory. The old whole product remains an
input cache; only the real new numerical endpoint views are prepared.
-/
def revalueLeaves (bank : Leaves shared entries)
    (included : ∀ value ∈ RegularPrimitiveFragments.SheetEntries.points entries, value ∈ points) :
    {value : Leaves newShared entries // value = buildLeaves newShared entries included} :=
  Id.run (DependentProduct.ofFnM (m := Id) intervals (buildLeaf newShared entries included)
    (fun position =>
      let original := DependentProduct.get intervals bank position
      pure ⟨original.revalue newShared, original.revalue_eq_buildLeaf newShared included⟩))

end NumeratorLeaves

/-- Read an actual cached leaf without running its read, finish or view producer again. -/
@[expose] def leafAt (bank : Leaves shared entries) (position : Fin intervals.length) : Leaf shared entries position :=
  DependentProduct.get intervals bank position

section Boundaries

variable {fragments : RegularPrimitiveFragments axes parent partition partition.intervals}
variable {entries : FragmentSheets domains request fragments}
variable (bank : Leaves shared entries)
variable {chosen : Interval} {member : chosen ∈ partition.intervals}
variable (selected : Selected entries chosen member)

/-- The selected metadata and actual stored leaf retain the same complete original pair. -/
theorem leaf_selected_eq : (leafAt shared entries bank selected.position).pair =
    (⟨selected.fragment, selected.assigned⟩ : OccurrencePair (request := request) selected.interval) :=
  (Leaf.pair_eq (leafAt shared entries bank selected.position)).trans selected.read_eq.symm

/-- Project and transport the whole original selected occurrence, preserving its actual caches. -/
def selectedOccurrence : Occurrence shared selected.assigned :=
  Occurrence.castPair (shared := shared) (leaf_selected_eq shared bank selected)
    (leafAt shared entries bank selected.position).occurrence

/-- Boundary projection preserves the complete cached leaf occurrence. -/
theorem selectedOccurrence_heq : HEq (selectedOccurrence shared bank selected)
    (leafAt shared entries bank selected.position).occurrence :=
  Occurrence.castPair_heq (shared := shared) (leaf_selected_eq shared bank selected)
    (leafAt shared entries bank selected.position).occurrence

/-- Boundary projection preserves the exact original incoming reading. -/
theorem selectedOccurrence_initial : (selectedOccurrence shared bank selected).initial =
    (leafAt shared entries bank selected.position).occurrence.initial :=
  Occurrence.castPair_initial (shared := shared) (leaf_selected_eq shared bank selected)
    (leafAt shared entries bank selected.position).occurrence

/-- Boundary projection preserves the exact original finish reading. -/
theorem selectedOccurrence_terminal : (selectedOccurrence shared bank selected).terminal =
    (leafAt shared entries bank selected.position).occurrence.terminal :=
  Occurrence.castPair_terminal (shared := shared) (leaf_selected_eq shared bank selected)
    (leafAt shared entries bank selected.position).occurrence

/-- The actual first boundary selector has literal interval position zero. -/
theorem first_position (first : First entries) : first.selected.position.val = 0 := by
  cases positionEq : first.selected.position.val with
  | zero => rfl
  | succ previous =>
      have later : previous + 1 < partition.intervals.length := by
        exact Eq.mp (congrArg (fun value => value < partition.intervals.length) positionEq)
          first.selected.position.isLt
      have seam := partition.consecutive previous later
      have member : (partition.intervals[previous]'(Nat.lt_trans (Nat.lt_succ_self _) later)) ∈
          partition.intervals := List.getElem_mem (Nat.lt_trans (Nat.lt_succ_self _) later)
      have bounds := partition.interval_bounds member
      have selected : (partition.intervals[previous + 1]'later).lower = 0 := by
        have indexEq : first.selected.position = ⟨previous + 1, later⟩ := Fin.ext positionEq
        exact (congrArg (fun index : Fin partition.intervals.length =>
          (partition.intervals[index.val]'index.isLt).lower) indexEq).symm.trans first.lower_eq
      have impossible := (partition.intervals[previous]'
        (Nat.lt_trans (Nat.lt_succ_self _) later)).ordered
      exact False.elim ((not_lt_of_ge bounds.1) (impossible.trans_eq (seam.trans selected)))

/-- The final bounded position has no next occurrence. -/
private theorem final_index (position length : Nat) (bound : position < length)
    (noNext : ¬position + 1 < length) : position + 1 = length := by omega0

/-- The actual last boundary selector has the literal final interval position. -/
theorem last_position (last : Last entries) : last.selected.position.val + 1 = partition.intervals.length := by
  have bound := last.selected.position.isLt
  have noNext : ¬last.selected.position.val + 1 < partition.intervals.length := by
    intro later
    have seam := partition.consecutive last.selected.position.val later
    have member : (partition.intervals[last.selected.position.val + 1]'later) ∈ partition.intervals :=
      List.getElem_mem later
    have bounds := partition.interval_bounds member
    have before := (partition.intervals[last.selected.position.val + 1]'later).ordered
    have selected : (partition.intervals[last.selected.position.val]'
        (Nat.lt_trans (Nat.lt_succ_self _) later)).upper = 1 := last.upper_eq
    exact (not_lt_of_ge bounds.2) ((selected.symm.trans seam).trans_lt before)
  exact final_index _ _ bound noNext

end Boundaries

section Internal

variable {fragments : RegularPrimitiveFragments axes parent partition partition.intervals}
variable {entries : FragmentSheets domains request fragments}
variable (bank : Leaves shared entries) (position : Fin (partition.intervals.length - 1))

/-- The actual preceding original cached leaf of an internal partition seam. -/
@[expose] def previousLeaf := leafAt shared entries bank (partition.previousIndex position)

/-- The actual following original cached leaf of the same internal partition seam. -/
@[expose] def followingLeaf := leafAt shared entries bank (partition.nextIndex position)

/-- The exact original consecutive Point/Entry/OwnerJoin type on these two retained leaves. -/
abbrev InternalSeam := AtSeam (previousLeaf shared bank position).occurrence.finish
  (followingLeaf shared bank position).pair.2
  (partition.consecutive position.val (partition.nextIndex position).isLt)

/-- The exact existing same-parent numerical jump and its factory on one already retained physical seam. -/
abbrev InternalJump (seam : InternalSeam shared bank position) :=
  {value : AtSeam.PrimitiveJump seam
      (previousLeaf shared bank position).occurrence.data (followingLeaf shared bank position).occurrence.data
      (previousLeaf shared bank position).occurrence.reading (followingLeaf shared bank position).occurrence.reading
      1 0 rfl rfl //
    value = AtSeam.primitiveJump seam
      (previousLeaf shared bank position).occurrence.data (followingLeaf shared bank position).occurrence.data
      (previousLeaf shared bank position).occurrence.reading (followingLeaf shared bank position).occurrence.reading
      1 0 rfl rfl}

/-- One actual consecutive physical join and the existing cached old-primitive jump on the same two views. -/
abbrev InternalGap :=
  Σ seam : {value : InternalSeam shared bank position //
    value = consecutive position.val (partition.nextIndex position).isLt
      (previousLeaf shared bank position).occurrence.finish (followingLeaf shared bank position).pair.2},
  InternalJump shared bank position seam.val

/-- Compute the actual numerical jump on the GIVEN complete physical seam and its original factory. -/
def internalGapFrom
    (seam : {value : InternalSeam shared bank position //
      value = consecutive position.val (partition.nextIndex position).isLt
        (previousLeaf shared bank position).occurrence.finish (followingLeaf shared bank position).pair.2}) :
    InternalGap shared bank position :=
  let jump : InternalJump shared bank position seam.val :=
    ⟨AtSeam.primitiveJump seam.val
      (previousLeaf shared bank position).occurrence.data (followingLeaf shared bank position).occurrence.data
      (previousLeaf shared bank position).occurrence.reading (followingLeaf shared bank position).occurrence.reading
      1 0 rfl rfl, rfl⟩
  ⟨seam, jump⟩

/-- Prepare the one internal physical seam and one original attempt/readGap using only the same actual leaf caches. -/
def internalGap : InternalGap shared bank position :=
  let seam : {value : InternalSeam shared bank position //
      value = consecutive position.val (partition.nextIndex position).isLt
        (previousLeaf shared bank position).occurrence.finish (followingLeaf shared bank position).pair.2} :=
    ⟨consecutive position.val (partition.nextIndex position).isLt
      (previousLeaf shared bank position).occurrence.finish (followingLeaf shared bank position).pair.2, rfl⟩
  internalGapFrom shared bank position seam

/-- The given physical seam yields the same whole internal cache without running the physical seam producer. -/
theorem internalGapFrom_eq
    (seam : {value : InternalSeam shared bank position //
      value = consecutive position.val (partition.nextIndex position).isLt
        (previousLeaf shared bank position).occurrence.finish (followingLeaf shared bank position).pair.2}) :
    internalGapFrom shared bank position seam = internalGap shared bank position := by
  have same : seam = ⟨consecutive position.val (partition.nextIndex position).isLt
      (previousLeaf shared bank position).occurrence.finish (followingLeaf shared bank position).pair.2, rfl⟩ :=
    Subtype.ext seam.property
  cases same
  unfold internalGap internalGapFrom
  rfl

namespace InternalGap

variable {shared bank position} (kept : InternalGap shared bank position)

/-- Read the same real consecutive physical comparison cache. -/
@[expose] def seam : InternalSeam shared bank position := kept.1.val

/-- Read the existing old-bank jump cache without a second attempt or gap read. -/
@[expose] def jump := kept.2.val

/-- Read the actual signed old finish-minus-next-incoming gap. -/
@[expose] def value : Canonical := AtSeam.PrimitiveJump.gap kept.jump

/-- The signed scalar is the difference of the same two original leaf endpoint readings. -/
theorem value_eq : kept.value = (previousLeaf shared bank position).occurrence.terminal -
    (followingLeaf shared bank position).occurrence.initial := AtSeam.PrimitiveJump.gap_eq kept.jump

end InternalGap

section NumeratorInternal

variable {newNumerator : CoefficientPolynomial} {newIndex : Nat} {newTolerance : Rational}
variable {newBudgets : FaceMeshBudgets source points newTolerance (numerator := newNumerator) domains}
variable {newNumerics : Face.PrimitiveData.FacePrimitiveBank source newIndex
  (numerator := newNumerator) domains}
variable (newShared : FaceSharedMeshes (numerator := newNumerator) newBudgets newNumerics)

/-- Whole original source-pair equality transports the complete given physical seam and changes no cache value. -/
private def transportInternalSeam
    {firstInterval lastInterval : Interval} {same : firstInterval.upper = lastInterval.lower}
    {first nextFirst : OccurrencePair (axes := axes) (partition := partition)
      (domains := domains) (request := request) firstInterval}
    {last nextLast : OccurrencePair (axes := axes) (partition := partition)
      (domains := domains) (request := request) lastInterval}
    {finish : Finish first.2} {nextFinish : Finish nextFirst.2}
    (firstEq : first = nextFirst) (lastEq : last = nextLast) (finishEq : HEq finish nextFinish)
    (seam : AtSeam finish last.2 same) : AtSeam nextFinish nextLast.2 same := by
  cases firstEq
  cases lastEq
  cases finishEq
  exact seam

/-- The transported physical cache keeps its original full producer equation at the same actual seam. -/
private theorem transportInternalSeam_factory
    {firstInterval lastInterval : Interval} {same : firstInterval.upper = lastInterval.lower}
    {first nextFirst : OccurrencePair (axes := axes) (partition := partition)
      (domains := domains) (request := request) firstInterval}
    {last nextLast : OccurrencePair (axes := axes) (partition := partition)
      (domains := domains) (request := request) lastInterval}
    {finish : Finish first.2} {nextFinish : Finish nextFirst.2}
    (firstEq : first = nextFirst) (lastEq : last = nextLast) (finishEq : HEq finish nextFinish)
    (seam : AtSeam finish last.2 same)
    (factory : seam = atSeam finish last.2 same) :
    transportInternalSeam firstEq lastEq finishEq seam = atSeam nextFinish nextLast.2 same := by
  cases firstEq
  cases lastEq
  cases finishEq
  unfold transportInternalSeam
  exact factory

/-- Equal whole source pairs identify the complete retained Finish values through their original factories. -/
private theorem finishesOfPair
    {interval : Interval}
    {first next : OccurrencePair (axes := axes) (partition := partition)
      (domains := domains) (request := request) interval}
    (oldOccurrence : Occurrence shared first.2) (newOccurrence : Occurrence newShared next.2)
    (pairEq : first = next) : HEq oldOccurrence.finish newOccurrence.finish := by
  cases pairEq
  exact heq_of_eq (oldOccurrence.finish_eq.trans newOccurrence.finish_eq.symm)

/-- Reuse the GIVEN actual internal Point/Entry/OwnerJoin cache for one true new-numerator jump.

Whole retained source-pair and Finish factories supply the index transports.
The physical cache is transported as a complete value. Only the genuine new
numerical attempt and readGap are executed, preserving both actual offsets.
-/
def revalueInternalGap (newBank : Leaves newShared entries) (oldGap : InternalGap shared bank position) :
    {value : InternalGap newShared newBank position // value = internalGap newShared newBank position} :=
  let oldFirst := previousLeaf shared bank position
  let oldLast := followingLeaf shared bank position
  let newFirst := previousLeaf newShared newBank position
  let newLast := followingLeaf newShared newBank position
  have firstEq : oldFirst.pair = newFirst.pair := oldFirst.pair_eq.trans newFirst.pair_eq.symm
  have lastEq : oldLast.pair = newLast.pair := oldLast.pair_eq.trans newLast.pair_eq.symm
  have finishEq : HEq oldFirst.occurrence.finish newFirst.occurrence.finish :=
    finishesOfPair (shared := shared) (newShared := newShared) oldFirst.occurrence newFirst.occurrence firstEq
  let original := oldGap.seam
  let transported : InternalSeam newShared newBank position :=
    transportInternalSeam firstEq lastEq finishEq original
  have oldFactory : original = atSeam oldFirst.occurrence.finish oldLast.pair.2
      (partition.consecutive position.val (partition.nextIndex position).isLt) :=
    oldGap.1.property.trans
      (consecutive_eq_atSeam position.val (partition.nextIndex position).isLt
        oldFirst.occurrence.finish oldLast.pair.2)
  have newFactory : transported = consecutive position.val (partition.nextIndex position).isLt
      newFirst.occurrence.finish newLast.pair.2 :=
    (transportInternalSeam_factory firstEq lastEq finishEq original oldFactory).trans
      (consecutive_eq_atSeam position.val (partition.nextIndex position).isLt
        newFirst.occurrence.finish newLast.pair.2).symm
  let seam : {value : InternalSeam newShared newBank position //
      value = consecutive position.val (partition.nextIndex position).isLt
        newFirst.occurrence.finish newLast.pair.2} := ⟨transported, newFactory⟩
  ⟨internalGapFrom newShared newBank position seam, internalGapFrom_eq newShared newBank position seam⟩

end NumeratorInternal

/-- The ordered actual internal joins retain all original consecutive partition positions. -/
abbrev Internals := DependentVector fun position : Fin (partition.intervals.length - 1) =>
  InternalGap shared bank position

/-- Materialize each internal physical and old-bank comparison once in original parameter order. -/
def buildInternals : Internals shared bank := DependentVector.ofFn fun position => internalGap shared bank position

section NumeratorInternals

variable {newNumerator : CoefficientPolynomial} {newIndex : Nat} {newTolerance : Rational}
variable {newBudgets : FaceMeshBudgets source points newTolerance (numerator := newNumerator) domains}
variable {newNumerics : Face.PrimitiveData.FacePrimitiveBank source newIndex
  (numerator := newNumerator) domains}
variable (newShared : FaceSharedMeshes (numerator := newNumerator) newBudgets newNumerics)

/-- Retain all actual original internal physical seams and prepare exactly one true new-numerator jump at each slot. -/
def revalueInternals (newBank : Leaves newShared entries) (oldInternals : Internals shared bank) :
    {value : Internals newShared newBank // value = buildInternals newShared newBank} :=
  let loaded := fun position : Fin (partition.intervals.length - 1) =>
    revalueInternalGap (shared := shared) (bank := bank) (position := position) (newShared := newShared)
      newBank (oldInternals.get position)
  let values := DependentVector.ofFn fun position => (loaded position).val
  ⟨values, DependentVector.ofFn_congr _ _ (fun position => (loaded position).property)⟩

end NumeratorInternals

end Internal

section Word

variable {fragments : RegularPrimitiveFragments axes parent partition partition.intervals}
variable (entries : FragmentSheets domains request fragments)
variable (included : ∀ value ∈ RegularPrimitiveFragments.SheetEntries.points entries, value ∈ points)

/-- One original parent word with its actual occurrence bank, boundary projections and ordered internal comparisons. -/
abbrev Word :=
  Σ bank : {value : Leaves shared entries // value = buildLeaves shared entries included},
  Σ first : {value : First entries // value = FragmentSheets.first entries},
  Σ last : {value : Last entries // value = FragmentSheets.last entries},
  {value : Occurrence shared first.val.selected.assigned //
    value = selectedOccurrence shared bank.val first.val.selected} ×
  {value : Occurrence shared last.val.selected.assigned //
    value = selectedOccurrence shared bank.val last.val.selected} ×
  {value : Internals shared bank.val // value = buildInternals shared bank.val}

/-- Retain each occurrence once, select both boundary metadata once, then build the actual internal seams. -/
def word : Word shared entries included :=
  let bank : {value : Leaves shared entries // value = buildLeaves shared entries included} :=
    ⟨buildLeaves shared entries included, rfl⟩
  let first : {value : First entries // value = FragmentSheets.first entries} :=
    ⟨FragmentSheets.first entries, rfl⟩
  let last : {value : Last entries // value = FragmentSheets.last entries} :=
    ⟨FragmentSheets.last entries, rfl⟩
  let initial := selectedOccurrence shared bank.val first.val.selected
  let terminal := selectedOccurrence shared bank.val last.val.selected
  let internal := buildInternals shared bank.val
  ⟨bank, first, last, ⟨initial, rfl⟩, ⟨terminal, rfl⟩, ⟨internal, rfl⟩⟩

namespace Word

variable {shared entries included} (kept : Word shared entries included)

/-- Read the same retained original occurrence product. -/
@[expose] def leaves : Leaves shared entries := kept.1.val

/-- Read the original first boundary selection. -/
@[expose] def first : First entries := kept.2.1.val

/-- Read the original last boundary selection. -/
@[expose] def last : Last entries := kept.2.2.1.val

/-- Read the whole transported initial occurrence, retaining its actual Finish and old numerical view. -/
@[expose] def initial : Occurrence shared kept.first.selected.assigned := kept.2.2.2.1.val

/-- Read the SAME transported terminal occurrence used for both outgoing and literal closing work. -/
@[expose] def terminal : Occurrence shared kept.last.selected.assigned := kept.2.2.2.2.1.val

/-- Read the stored actual consecutive physical/numerical caches. -/
@[expose] def internal : Internals shared kept.leaves := kept.2.2.2.2.2.val

/-- The complete occurrence product retains its original single materialization factory. -/
theorem leaves_eq : kept.leaves = buildLeaves shared entries included := kept.1.property

/-- The first boundary metadata is the exact original selector result. -/
theorem first_eq : kept.first = FragmentSheets.first entries := kept.2.1.property

/-- The last boundary metadata is the exact original selector result. -/
theorem last_eq : kept.last = FragmentSheets.last entries := kept.2.2.1.property

/-- Every internal cache is its exact ordered materialization on these same retained leaves. -/
theorem internal_eq : kept.internal = buildInternals shared kept.leaves := kept.2.2.2.2.2.property

/-- The complete initial occurrence is its original whole-leaf transport. -/
theorem initial_eq : kept.initial = selectedOccurrence shared kept.leaves kept.first.selected :=
  kept.2.2.2.1.property

/-- The complete terminal occurrence is its original whole-leaf transport. -/
theorem terminal_eq : kept.terminal = selectedOccurrence shared kept.leaves kept.last.selected :=
  kept.2.2.2.2.1.property

/-- Read the actual ordered fragment increments without acquiring or evaluating an endpoint again. -/
@[expose] def increments : List Canonical := List.ofFn fun position : Fin partition.intervals.length =>
  (leafAt shared entries kept.leaves position).occurrence.terminal -
    (leafAt shared entries kept.leaves position).occurrence.initial

/-- Read the actual ordered internal gap scalars from their retained original caches. -/
@[expose] def gaps : List Canonical := List.ofFn fun position : Fin (partition.intervals.length - 1) =>
  InternalGap.value (kept.internal.get position)

/-- The original word retains exactly one increment per actual fragment occurrence. -/
theorem increments_length : kept.increments.length = partition.intervals.length :=
  Data.List.OfFn.Basic.length_ofFn

/-- The original internal bank retains exactly one gap for each consecutive pair, including a zero-length bank. -/
theorem gaps_length : kept.gaps.length = partition.intervals.length - 1 := Data.List.OfFn.Basic.length_ofFn

/-- All complete retained field factories identify their same exact canonical parent word. -/
private theorem eq_materialized : kept = word shared entries included := by
  rcases kept with ⟨bank, first, last, initial, terminal, internal⟩
  have bankEq : bank = ⟨buildLeaves shared entries included, rfl⟩ := Subtype.ext bank.property
  cases bankEq
  have firstEq : first = ⟨FragmentSheets.first entries, rfl⟩ := Subtype.ext first.property
  cases firstEq
  have lastEq : last = ⟨FragmentSheets.last entries, rfl⟩ := Subtype.ext last.property
  cases lastEq
  have initialEq : initial = ⟨selectedOccurrence shared (buildLeaves shared entries included)
      (FragmentSheets.first entries).selected, rfl⟩ := Subtype.ext initial.property
  cases initialEq
  have terminalEq : terminal = ⟨selectedOccurrence shared (buildLeaves shared entries included)
      (FragmentSheets.last entries).selected, rfl⟩ := Subtype.ext terminal.property
  cases terminalEq
  have internalEq : internal = ⟨buildInternals shared (buildLeaves shared entries included), rfl⟩ :=
    Subtype.ext internal.property
  cases internalEq
  unfold word
  rfl

section Numerator

variable {newNumerator : CoefficientPolynomial} {newIndex : Nat} {newTolerance : Rational}
variable {newBudgets : FaceMeshBudgets source points newTolerance (numerator := newNumerator) domains}
variable {newNumerics : Face.PrimitiveData.FacePrimitiveBank source newIndex
  (numerator := newNumerator) domains}
variable (newShared : FaceSharedMeshes (numerator := newNumerator) newBudgets newNumerics)

/-- Prepare the true new-numerator parent word on the SAME complete retained physical occurrence and seam caches.

The original first/last metadata and actual Finish values survive. The
existing finite products retain the new numerical endpoint views and one
new attempt/readGap per original internal slot. No source read, Point,
Query, geometric word or physical seam constructor is executed again.
-/
def revalue : {value : Word newShared entries included // value = word newShared entries included} :=
  let bank := revalueLeaves (entries := entries) (shared := shared) (newShared := newShared) kept.leaves included
  let first := kept.2.1
  let last := kept.2.2.1
  let initial := selectedOccurrence newShared bank.val first.val.selected
  let terminal := selectedOccurrence newShared bank.val last.val.selected
  let internal := revalueInternals (shared := shared) (bank := kept.leaves) (newShared := newShared)
    bank.val kept.internal
  let actual : Word newShared entries included :=
    ⟨bank, first, last, ⟨initial, rfl⟩, ⟨terminal, rfl⟩, internal⟩
  ⟨actual, eq_materialized actual⟩

/-- The original whole first boundary metadata is retained verbatim. -/
theorem revalue_first : (kept.revalue newShared).val.first = kept.first := by
  unfold revalue first
  rfl

/-- The original whole last boundary metadata is retained verbatim. -/
theorem revalue_last : (kept.revalue newShared).val.last = kept.last := by
  unfold revalue last
  rfl

/-- Equal whole first metadata compares the same original physical Finish factories across numerator banks. -/
private theorem initialFinish_heq {first next : First entries}
    (same : first = next)
    (left : Occurrence newShared first.selected.assigned) (right : Occurrence shared next.selected.assigned) :
    HEq left.finish right.finish := by
  cases same
  exact heq_of_eq (left.finish_eq.trans right.finish_eq.symm)

/-- Equal whole last metadata compares the same original physical Finish factories across numerator banks. -/
theorem terminalFinish_heq {last next : Last entries}
    (same : last = next)
    (left : Occurrence newShared last.selected.assigned) (right : Occurrence shared next.selected.assigned) :
    HEq left.finish right.finish := by
  cases same
  exact heq_of_eq (left.finish_eq.trans right.finish_eq.symm)

/-- The entire original initial physical Finish is preserved, with no owner identity inferred from coordinates. -/
theorem revalue_initial_finish : HEq (kept.revalue newShared).val.initial.finish kept.initial.finish :=
  initialFinish_heq (shared := shared) (newShared := newShared) (kept.revalue_first newShared)
    (kept.revalue newShared).val.initial kept.initial

/-- The SAME original terminal physical Finish remains the value used by outgoing and closing work. -/
theorem revalue_terminal_finish : HEq (kept.revalue newShared).val.terminal.finish kept.terminal.finish :=
  terminalFinish_heq (shared := shared) (newShared := newShared) (kept.revalue_last newShared)
    (kept.revalue newShared).val.terminal kept.terminal

/-- The complete new-numerator word retains its actual original producer equation derived from its input caches. -/
theorem revalue_eq_word : (kept.revalue newShared).val = word newShared entries included :=
  (kept.revalue newShared).property

end Numerator

end Word

/-- The original ordered Gaussian list sum equals its finite indexed scalar sum. -/
private theorem sum_ofFn {size : Nat} (values : Fin size → Canonical) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn values) = sumFin values := by
  induction size with
  | zero => rfl
  | succ size previous =>
      rewrite [Data.List.OfFn.Basic.ofFn_succ, sumFin_succ]
      change values 0 + Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn (fun i => values i.succ)) = _
      exact congrArg (fun value => values 0 + value) (previous (fun i => values i.succ))

/-- A literal finite endpoint table telescopes through its actual consecutive differences. -/
private theorem scalar_open {size : Nat} (initial terminal : Fin (size + 1) → Canonical) :
    sumFin (fun i => terminal i - initial i) =
      sumFin (fun i : Fin size => terminal i.castSucc - initial i.succ) +
        (terminal (Fin.last size) - initial 0) := by
  induction size with
  | zero =>
      rewrite [sumFin_succ]
      change terminal 0 - initial 0 + 0 = 0 + (terminal 0 - initial 0)
      ring1
  | succ size previous =>
      have whole := sumFin_succ (fun i : Fin (size + 2) => terminal i - initial i)
      have adjacent := sumFin_succ
        (fun i : Fin (size + 1) => terminal i.castSucc - initial i.succ)
      have following := previous (fun i => initial i.succ) (fun i => terminal i.succ)
      rewrite [whole, adjacent, following]
      change terminal 0 - initial 0 +
        (sumFin (fun i : Fin size => terminal i.succ.castSucc - initial i.succ.succ) +
          (terminal (Fin.last (size + 1)) - initial (Fin.succ 0))) =
        terminal 0 - initial (Fin.succ 0) +
          sumFin (fun i : Fin size => terminal i.succ.castSucc - initial i.succ.succ) +
            (terminal (Fin.last (size + 1)) - initial 0)
      ring1

/-- Exact bounded positions transport the same scalar telescope without function equality. -/
private theorem scalar_open_indices {size : Nat} (initial terminal : Fin size → Canonical)
    (first last : Fin size) (previous next : Fin (size - 1) → Fin size)
    (firstEq : first.val = 0) (lastEq : last.val + 1 = size)
    (previousEq : ∀ i, (previous i).val = i.val) (nextEq : ∀ i, (next i).val = i.val + 1) :
    sumFin (fun i => terminal i - initial i) =
      sumFin (fun i => terminal (previous i) - initial (next i)) + (terminal last - initial first) := by
  cases size with
  | zero => exact Fin.elim0 first
  | succ size =>
      have firstSame : first = 0 := Fin.ext firstEq
      have lastSame : last = Fin.last size := Fin.ext (Nat.succ.inj lastEq)
      have adjacent : sumFin (fun i : Fin size => terminal i.castSucc - initial i.succ) =
          sumFin (fun i => terminal (previous i) - initial (next i)) :=
        sumFin_congr fun i => congrArg₂ (fun left right : Canonical => left - right)
          (congrArg terminal (Fin.ext (previousEq i)).symm)
          (congrArg initial (Fin.ext (nextEq i)).symm)
      exact (scalar_open initial terminal).trans
        (congrArg₂ (fun left right : Canonical => left + right) adjacent
          (congrArg₂ (fun left right : Canonical => left - right)
            (congrArg terminal lastSame.symm) (congrArg initial firstSame.symm)))

namespace Word

variable {shared entries included} (kept : Word shared entries included)

/-- The actual original word's increments telescope through its stored internal gaps and literal boundary readings. -/
theorem telescope : Data.Gaussian.Norm.Sum.Basic.gaussianSum kept.increments =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum kept.gaps + (kept.terminal.terminal - kept.initial.initial) := by
  have opening := scalar_open_indices
    (fun i => (leafAt shared entries kept.leaves i).occurrence.initial)
    (fun i => (leafAt shared entries kept.leaves i).occurrence.terminal)
    kept.first.selected.position kept.last.selected.position
    partition.previousIndex partition.nextIndex (first_position kept.first) (last_position kept.last)
    (fun _ => rfl) (fun _ => rfl)
  have gaps : sumFin (fun i => (leafAt shared entries kept.leaves (partition.previousIndex i)).occurrence.terminal -
      (leafAt shared entries kept.leaves (partition.nextIndex i)).occurrence.initial) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum kept.gaps :=
    (sumFin_congr (fun i => (InternalGap.value_eq (kept.internal.get i)).symm)).trans (sum_ofFn _).symm
  have initial : (leafAt shared entries kept.leaves kept.first.selected.position).occurrence.initial =
      kept.initial.initial :=
    (selectedOccurrence_initial shared kept.leaves kept.first.selected).symm.trans
      (congrArg (fun value : Occurrence shared kept.first.selected.assigned => value.initial) kept.initial_eq).symm
  have terminal : (leafAt shared entries kept.leaves kept.last.selected.position).occurrence.terminal =
      kept.terminal.terminal :=
    (selectedOccurrence_terminal shared kept.leaves kept.last.selected).symm.trans
      (congrArg (fun value : Occurrence shared kept.last.selected.assigned => value.terminal) kept.terminal_eq).symm
  exact (sum_ofFn _).trans (opening.trans
    (congrArg₂ (fun left right : Canonical => left + right) gaps
      (congrArg₂ (fun left right : Canonical => left - right) terminal initial)))

end Word

end Word

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.FragmentSheets
