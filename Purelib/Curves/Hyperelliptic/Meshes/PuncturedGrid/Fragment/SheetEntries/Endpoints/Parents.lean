module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Selection
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Endpoints
public import Purelib.Riemann.Topology.PreparedBankRootChains
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Comparison
import Purelib.Riemann.Normalization.ContinuedInverseRoot.Point.Transport
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Approximation.Gaussian.Equivalence

/-! # Actual adjacent-parent and literal closing fragment joins

The same original parent root and geometric chains supply independent
signed comparison and physical incidence. Original last/first occurrence
caches supply the actual Points and Entries. Only whole point/Owner index
transports and one genuine finite-tail OwnerJoin are constructed.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.FragmentSheets

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveFragments)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment
  (SheetEntry domainCache)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment.SheetEntry
  (Finish)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.OwnerTraceReadings (OwnerJoin)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Riemann.Topology.PreparedBankRootChains.RootChain (castChildren)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus leftCount rightCount : Nat} {curve : HyperellipticCurve genus}
variable {branches : BranchIsolation.Data curve} {higher : 1 < curve.polynomial.natDegree}
variable {base : FramedPuncturedGrid curve branches higher} {frames : RootFrames base.bank.grid}
variable {source : Differential genus} {axes : PrimitiveAxes base.bank.grid}
variable {leftParent rightParent : CenteredEdge curve source}
variable {leftPartition : AxisPartition 0 1 (axes.parameters leftParent)}
variable {rightPartition : AxisPartition 0 1 (axes.parameters rightParent)}
variable {leftFragments : RegularPrimitiveFragments axes leftParent leftPartition leftPartition.intervals}
variable {rightFragments : RegularPrimitiveFragments axes rightParent rightPartition rightPartition.intervals}
variable {domains : FaceDomainBank frames base.faces.regulars} {leftTarget rightTarget : Rational}
variable {leftRequest : LocalRequest leftParent leftCount leftTarget}
variable {rightRequest : LocalRequest rightParent rightCount rightTarget}
variable {leftEntries : FragmentSheets domains leftRequest leftFragments}
variable {rightEntries : FragmentSheets domains rightRequest rightFragments}
variable (leftEnd : Last leftEntries) (rightEnd : First rightEntries)
variable (finish : Finish leftEnd.selected.assigned)

/-- Reindex the SAME original first Point of the next parent at the actual preceding finish coordinate. -/
def rightPoint (pointEq : leftEnd.selected.fragment.located.last = rightEnd.selected.fragment.located.first) :
    ContinuedNeighborhood.Point rightRequest.neighborhood leftEnd.selected.fragment.located.last :=
  ContinuedNeighborhood.Point.castPoint pointEq rightEnd.selected.assigned.sample

/-- Exact physical index transport retains the complete right incoming Point. -/
theorem rightPoint_heq
    (pointEq : leftEnd.selected.fragment.located.last = rightEnd.selected.fragment.located.first) :
    HEq (rightPoint leftEnd rightEnd pointEq) rightEnd.selected.assigned.sample := by
  unfold rightPoint
  exact ContinuedNeighborhood.Point.castPoint_heq pointEq rightEnd.selected.assigned.sample

/-- The SAME cast incoming Point retains its whole original Owner; no independent Owners are identified. -/
theorem rightOwner_heq
    (pointEq : leftEnd.selected.fragment.located.last = rightEnd.selected.fragment.located.first) :
    HEq rightEnd.selected.assigned.sample.owner (rightPoint leftEnd rightEnd pointEq).owner := by
  unfold rightPoint
  have castOwner {first last : Canonical} (same : first = last)
      (sample : ContinuedNeighborhood.Point rightRequest.neighborhood last) :
      HEq sample.owner (ContinuedNeighborhood.Point.castPoint same sample).owner := by
    cases same
    rfl
  exact castOwner pointEq rightEnd.selected.assigned.sample

/-- Reindex the whole original right-face Entry with its actual Point and whole Owner identities. -/
def rightEntry (pointEq : leftEnd.selected.fragment.located.last = rightEnd.selected.fragment.located.first) :
    Entry (domainCache rightEnd.selected.fragment domains).models leftEnd.selected.fragment.located.last
      (rightPoint leftEnd rightEnd pointEq).owner :=
  rightEnd.selected.assigned.entry.castPoint pointEq.symm (rightOwner_heq leftEnd rightEnd pointEq)

/-- The complete right Entry remains the original actual incoming Entry. -/
theorem rightEntry_heq
    (pointEq : leftEnd.selected.fragment.located.last = rightEnd.selected.fragment.located.first) :
    HEq (rightEntry leftEnd rightEnd pointEq) rightEnd.selected.assigned.entry := by
  unfold rightEntry
  exact rightEnd.selected.assigned.entry.castPoint_heq pointEq.symm (rightOwner_heq leftEnd rightEnd pointEq)

/-- The right domain's original actual sheet is unchanged by the whole Point/Entry transport. -/
theorem rightEntry_sheet
    (pointEq : leftEnd.selected.fragment.located.last = rightEnd.selected.fragment.located.first) :
    (rightEntry leftEnd rightEnd pointEq).sheet = rightEnd.selected.assigned.entry.sheet := by
  unfold rightEntry
  exact rightEnd.selected.assigned.entry.castPoint_sheet pointEq.symm (rightOwner_heq leftEnd rightEnd pointEq)

/-- Transport an actual supplied root comparison to the SAME reindexed incoming Point name. -/
def pointEquivalent
    (pointEq : leftEnd.selected.fragment.located.last = rightEnd.selected.fragment.located.first)
    (comparison : NamedEquivalent finish.sample.certificate.value.name
      rightEnd.selected.assigned.sample.certificate.value.name) :
    NamedEquivalent finish.sample.certificate.value.name
      (rightPoint leftEnd rightEnd pointEq).certificate.value.name := by
  unfold rightPoint
  exact NamedEquivalent.transport rfl
    (ContinuedNeighborhood.Point.castPoint_name pointEq rightEnd.selected.assigned.sample).symm comparison

/-- Actual retained endpoints, signed comparison and OwnerJoin with their complete original input and field factories.

The comparison is an index of this cache type. The public adjacent and
closing producers below derive that actual data from their original
RootChain; no desired comparison is a producer input.
-/
@[expose] def Joined
    (pointEq : leftEnd.selected.fragment.located.last = rightEnd.selected.fragment.located.first)
    (comparison : NamedEquivalent finish.sample.certificate.value.name
      rightEnd.selected.assigned.sample.certificate.value.name)
    :=
  {value : Last leftEntries × First rightEntries × Finish leftEnd.selected.assigned ×
      NamedEquivalent finish.sample.certificate.value.name rightEnd.selected.assigned.sample.certificate.value.name //
    value = (leftEnd, rightEnd, finish, comparison)} ×
  {values : (sample : ContinuedNeighborhood.Point rightRequest.neighborhood leftEnd.selected.fragment.located.last) ×
      Entry (domainCache rightEnd.selected.fragment domains).models
        leftEnd.selected.fragment.located.last sample.owner ×
      NamedEquivalent finish.sample.certificate.value.name sample.certificate.value.name ×
      OwnerJoin finish.sample.owner sample.owner //
    values.1 = rightPoint leftEnd rightEnd pointEq ∧
    HEq values.2.1 (rightEntry leftEnd rightEnd pointEq) ∧
    values.2.1.sheet = rightEnd.selected.assigned.entry.sheet ∧
    HEq values.2.2.1 (pointEquivalent leftEnd rightEnd finish pointEq comparison) ∧
    values.2.2.2 = OwnerJoin.acquire finish.sample.owner values.1.owner values.2.2.1}

section

attribute [local irreducible] rightPoint rightEntry pointEquivalent

/-- Pack one actual derived root comparison into the two retained original endpoint Owners and their finite join. -/
private def joinGiven
    (pointEq : leftEnd.selected.fragment.located.last = rightEnd.selected.fragment.located.first)
    (comparison : NamedEquivalent finish.sample.certificate.value.name
      rightEnd.selected.assigned.sample.certificate.value.name)
    : Joined leftEnd rightEnd finish pointEq comparison := by
  let sample : ContinuedNeighborhood.Point rightRequest.neighborhood leftEnd.selected.fragment.located.last :=
    rightPoint leftEnd rightEnd pointEq
  let entry : Entry (domainCache rightEnd.selected.fragment domains).models leftEnd.selected.fragment.located.last
      sample.owner := rightEntry leftEnd rightEnd pointEq
  let equivalent : NamedEquivalent finish.sample.certificate.value.name sample.certificate.value.name :=
    pointEquivalent leftEnd rightEnd finish pointEq comparison
  let joined : OwnerJoin finish.sample.owner sample.owner :=
    OwnerJoin.acquire finish.sample.owner sample.owner equivalent
  exact (⟨(leftEnd, rightEnd, finish, comparison), rfl⟩,
    ⟨⟨sample, entry, equivalent, joined⟩, rfl, HEq.rfl,
      rightEntry_sheet leftEnd rightEnd pointEq, HEq.rfl, rfl⟩)

end

namespace Joined

variable {leftEnd rightEnd finish}
variable {pointEq : leftEnd.selected.fragment.located.last = rightEnd.selected.fragment.located.first}
variable {comparison : NamedEquivalent finish.sample.certificate.value.name
  rightEnd.selected.assigned.sample.certificate.value.name}
variable (retained : Joined leftEnd rightEnd finish pointEq comparison)

/-- Read the original right incoming Point at the identical left finish index. -/
@[expose] def sample : ContinuedNeighborhood.Point rightRequest.neighborhood leftEnd.selected.fragment.located.last :=
  retained.2.val.1

/-- Read the SAME whole original right-face Entry. -/
@[expose] def entry : Entry (domainCache rightEnd.selected.fragment domains).models
    leftEnd.selected.fragment.located.last retained.sample.owner := retained.2.val.2.1

/-- Read the actual two-Owner signed comparison used by the join. -/
@[expose] def equivalent : NamedEquivalent finish.sample.certificate.value.name
    retained.sample.certificate.value.name :=
  retained.2.val.2.2.1

/-- Read the complete actual finite-tail OwnerJoin. -/
@[expose] def joined : OwnerJoin finish.sample.owner retained.sample.owner := retained.2.val.2.2.2

/-- The complete original endpoint-role and comparison inputs are retained. -/
theorem originals_eq : retained.1.val = (leftEnd, rightEnd, finish, comparison) := retained.1.property

/-- The actual incoming Point is the original whole Point transport. -/
theorem sample_eq : retained.sample = rightPoint leftEnd rightEnd pointEq := retained.2.property.1

/-- The complete original incoming Point is retained before its dependent coordinate reindexing. -/
theorem sample_heq : HEq retained.sample rightEnd.selected.assigned.sample :=
  (heq_of_eq retained.sample_eq).trans (rightPoint_heq leftEnd rightEnd pointEq)

/-- The actual comparison is the exact original comparison transported to the SAME reindexed Point name. -/
theorem equivalent_heq : HEq retained.equivalent (pointEquivalent leftEnd rightEnd finish pointEq comparison) :=
  retained.2.property.2.2.2.1

/-- The full original right Entry is preserved heterogeneously. -/
theorem entry_heq : HEq retained.entry rightEnd.selected.assigned.entry :=
  retained.2.property.2.1.trans (rightEntry_heq leftEnd rightEnd pointEq)

/-- The actual incoming Entry keeps its original domain sheet. -/
theorem entry_sheet : retained.entry.sheet = rightEnd.selected.assigned.entry.sheet := retained.2.property.2.2.1

/-- The entire join is its actual two-Owner factory using the SAME signed comparison. -/
theorem joined_eq : retained.joined = OwnerJoin.acquire finish.sample.owner retained.sample.owner retained.equivalent :=
  retained.2.property.2.2.2.2

end Joined

section Adjacent

variable {remaining : List (CenteredEdge curve source)} {initial terminal : Named}
variable {start finishPoint : LiftedPoint 2}

/-- The actual parent chain derives physical incidence of the retained last and first fragment roles. -/
theorem next_point (geometry : CenteredPathChain (leftParent :: rightParent :: remaining)
    (start := start) (finish := finishPoint)) :
    leftEnd.selected.fragment.located.last = rightEnd.selected.fragment.located.first := by
  have common := congrArg (fun point : LiftedPoint 2 => point.coordinate) geometry.remaining.start_eq
  have endpoints : leftParent.edge.point 1 = rightParent.edge.point 0 :=
    leftParent.edge.point_one.trans (common.symm.trans rightParent.edge.point_zero.symm)
  exact leftEnd.selected.fragment.located.last_eq.trans
    ((congrArg leftParent.edge.point leftEnd.upper_eq).trans
      (endpoints.trans ((congrArg rightParent.edge.point rightEnd.lower_eq).symm.trans
        rightEnd.selected.fragment.located.first_eq.symm)))

/-- Derive the actual finish-to-incoming root comparison from the retained adjacent original parent comparisons. -/
def nextEquivalent (roots : RootChain (leftParent :: rightParent :: remaining) initial terminal) :
    NamedEquivalent finish.sample.certificate.value.name rightEnd.selected.assigned.sample.certificate.value.name :=
  let lastNames := leftParent.edge.rootName_eq (firstInside := leftEnd.selected.fragment.located.upper_inside)
    (lastInside := by decide) leftEnd.upper_eq
  let firstNames := rightParent.edge.rootName_eq (firstInside := rightEnd.selected.assigned.fractionInside)
    (lastInside := rightParent.edge.baseInside) rightEnd.lower_eq
  let last := NamedEquivalent.transport lastNames rfl finish.original
  let first := NamedEquivalent.transport firstNames rfl rightEnd.selected.assigned.original
  last.symm.trans ((RootChain.nextEquivalent roots).trans first)

/-- The same whole original chains and boundary caches, the actual adjacent comparison, and their real Point join. -/
@[expose] def Next
    (geometry : CenteredPathChain (leftParent :: rightParent :: remaining) (start := start) (finish := finishPoint))
    (roots : RootChain (leftParent :: rightParent :: remaining) initial terminal) :=
  {value : CenteredPathChain (leftParent :: rightParent :: remaining) (start := start) (finish := finishPoint) ×
      RootChain (leftParent :: rightParent :: remaining) initial terminal ×
      FragmentSheets domains leftRequest leftFragments × FragmentSheets domains rightRequest rightFragments //
    value = (geometry, roots, leftEntries, rightEntries)} ×
  (Σ comparison : {value : NamedEquivalent finish.sample.certificate.value.name
      rightEnd.selected.assigned.sample.certificate.value.name // value = nextEquivalent leftEnd rightEnd finish roots},
    Joined leftEnd rightEnd finish (next_point leftEnd rightEnd geometry) comparison.val)

/-- Build the genuine cross-parent join from the SAME geometric/root chains and supplied endpoint caches. -/
def next
    (geometry : CenteredPathChain (leftParent :: rightParent :: remaining) (start := start) (finish := finishPoint))
    (roots : RootChain (leftParent :: rightParent :: remaining) initial terminal) :
    Next leftEnd rightEnd finish geometry roots :=
  let comparison : {value : NamedEquivalent finish.sample.certificate.value.name
      rightEnd.selected.assigned.sample.certificate.value.name //
    value = nextEquivalent leftEnd rightEnd finish roots} :=
    ⟨nextEquivalent leftEnd rightEnd finish roots, rfl⟩
  let retained := joinGiven leftEnd rightEnd finish (next_point leftEnd rightEnd geometry) comparison.val
  (⟨(geometry, roots, leftEntries, rightEntries), rfl⟩, ⟨comparison, retained⟩)

namespace Next

variable {leftEnd rightEnd finish}
variable {geometry : CenteredPathChain (leftParent :: rightParent :: remaining)
  (start := start) (finish := finishPoint)}
variable {roots : RootChain (leftParent :: rightParent :: remaining) initial terminal}
variable (retained : Next leftEnd rightEnd finish geometry roots)

/-- Read the SAME actual cross-parent root comparison. -/
@[expose] def comparison : NamedEquivalent finish.sample.certificate.value.name
    rightEnd.selected.assigned.sample.certificate.value.name := retained.2.1.val

/-- Read the actual Point, Entry and OwnerJoin cache on that SAME derived comparison. -/
@[expose] def joined : Joined leftEnd rightEnd finish (next_point leftEnd rightEnd geometry) retained.comparison :=
  retained.2.2

/-- The whole geometric/root chains and complete original parent entry banks are retained. -/
theorem originals_eq : retained.1.val = (geometry, roots, leftEntries, rightEntries) := retained.1.property

/-- The comparison is its exact original adjacent RootChain/Point factory. -/
theorem comparison_eq : retained.comparison = nextEquivalent leftEnd rightEnd finish roots := retained.2.1.property

end Next

end Adjacent

section Closing

variable (before after : List (CenteredEdge curve source))
variable (firstEq : before ++ [leftParent] = rightParent :: after) {root : Named} {point : LiftedPoint 2}

include firstEq in
/-- The SAME closed chain derives physical return from its actual final and first parents, including a singleton. -/
theorem closing_point
    (geometry : CenteredPathChain (before ++ [leftParent]) (start := point) (finish := point)) :
    leftEnd.selected.fragment.located.last = rightEnd.selected.fragment.located.first := by
  have last := congrArg (fun value : LiftedPoint 2 => value.coordinate) (geometry.last_eq before)
  have first := congrArg (fun value : LiftedPoint 2 => value.coordinate) (geometry.castParents firstEq).start_eq
  have endpoints : leftParent.edge.point 1 = rightParent.edge.point 0 :=
    leftParent.edge.point_one.trans (last.trans (first.symm.trans rightParent.edge.point_zero.symm))
  exact leftEnd.selected.fragment.located.last_eq.trans
    ((congrArg leftParent.edge.point leftEnd.upper_eq).trans
      (endpoints.trans ((congrArg rightParent.edge.point rightEnd.lower_eq).symm.trans
        rightEnd.selected.fragment.located.first_eq.symm)))

/-- Read the literal last and first actual root comparisons to derive final-to-first Point agreement. -/
def closingEquivalent (roots : RootChain (before ++ [leftParent]) root root) :
    NamedEquivalent finish.sample.certificate.value.name rightEnd.selected.assigned.sample.certificate.value.name :=
  let lastNames := leftParent.edge.rootName_eq (firstInside := leftEnd.selected.fragment.located.upper_inside)
    (lastInside := by decide) leftEnd.upper_eq
  let firstNames := rightParent.edge.rootName_eq (firstInside := rightEnd.selected.assigned.fractionInside)
    (lastInside := rightParent.edge.baseInside) rightEnd.lower_eq
  let last := NamedEquivalent.transport lastNames rfl finish.original
  let first := NamedEquivalent.transport firstNames rfl rightEnd.selected.assigned.original
  last.symm.trans ((RootChain.lastEquivalent before roots).trans
    ((RootChain.firstEquivalent (castChildren firstEq roots)).trans first))

/-- Original nonempty closed parent lists, their boundary caches and the literal retained return comparison and join. -/
@[expose] def Closing
    (geometry : CenteredPathChain (before ++ [leftParent]) (start := point) (finish := point))
    (roots : RootChain (before ++ [leftParent]) root root) :=
  {value : CenteredPathChain (before ++ [leftParent]) (start := point) (finish := point) ×
      RootChain (before ++ [leftParent]) root root × FragmentSheets domains leftRequest leftFragments ×
      FragmentSheets domains rightRequest rightFragments × List (CenteredEdge curve source) ×
      List (CenteredEdge curve source) // value = (geometry, roots, leftEntries, rightEntries, before, after)} ×
  (Σ comparison : {value : NamedEquivalent finish.sample.certificate.value.name
      rightEnd.selected.assigned.sample.certificate.value.name //
    value = closingEquivalent leftEnd rightEnd finish before after firstEq roots},
    Joined leftEnd rightEnd finish (closing_point leftEnd rightEnd before after firstEq geometry) comparison.val)

/-- Retain the actual literal closing join, using existing last/first root data and the same old endpoint roles. -/
def close
    (geometry : CenteredPathChain (before ++ [leftParent]) (start := point) (finish := point))
    (roots : RootChain (before ++ [leftParent]) root root) :
    Closing leftEnd rightEnd finish before after firstEq geometry roots :=
  let comparison : {value : NamedEquivalent finish.sample.certificate.value.name
      rightEnd.selected.assigned.sample.certificate.value.name //
    value = closingEquivalent leftEnd rightEnd finish before after firstEq roots} :=
    ⟨closingEquivalent leftEnd rightEnd finish before after firstEq roots, rfl⟩
  let retained := joinGiven leftEnd rightEnd finish
    (closing_point leftEnd rightEnd before after firstEq geometry) comparison.val
  (⟨(geometry, roots, leftEntries, rightEntries, before, after), rfl⟩, ⟨comparison, retained⟩)

namespace Closing

variable {leftEnd rightEnd finish before after firstEq}
variable {geometry : CenteredPathChain (before ++ [leftParent]) (start := point) (finish := point)}
variable {roots : RootChain (before ++ [leftParent]) root root}
variable (retained : Closing leftEnd rightEnd finish before after firstEq geometry roots)

/-- Read the SAME literal final-to-first operational root comparison. -/
@[expose] def comparison : NamedEquivalent finish.sample.certificate.value.name
    rightEnd.selected.assigned.sample.certificate.value.name := retained.2.1.val

/-- Read the complete actual closing Point, Entry and OwnerJoin cache. -/
@[expose] def joined : Joined leftEnd rightEnd finish
    (closing_point leftEnd rightEnd before after firstEq geometry) retained.comparison := retained.2.2

/-- The whole original closed chains, entry banks and literal parent prefixes are retained. -/
theorem originals_eq : retained.1.val = (geometry, roots, leftEntries, rightEntries, before, after) :=
  retained.1.property

/-- The closing comparison is the actual last/first RootChain factory, preserving the literal final contribution. -/
theorem comparison_eq : retained.comparison = closingEquivalent leftEnd rightEnd finish before after firstEq roots :=
  retained.2.1.property

end Closing

end Closing

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.FragmentSheets

end
