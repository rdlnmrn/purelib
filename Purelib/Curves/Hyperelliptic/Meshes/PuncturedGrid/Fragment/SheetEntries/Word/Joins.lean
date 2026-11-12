module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Endpoints.Parents
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.Junction.Gap

/-! # Original numerical gaps on retained adjacent and closing Point joins

A given physical Joined cache supplies the real root comparison. Both old
endpoint views retain their own numerical owners, constants and stages.
Their actual point incidences derive seam-only selected-cell coverage.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.FragmentSheets

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveFragments)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment (domainCache)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment.SheetEntry
  (Finish)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
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
variable {domains : FaceDomainBank frames base.faces.regulars} {leftTarget rightTarget tolerance : Rational}
variable {leftRequest : LocalRequest leftParent leftCount leftTarget}
variable {rightRequest : LocalRequest rightParent rightCount rightTarget}
variable {leftEntries : FragmentSheets domains leftRequest leftFragments}
variable {rightEntries : FragmentSheets domains rightRequest rightFragments}
variable {points : List Canonical} {index : Nat}
variable {numerator : CoefficientPolynomial}
variable {budgets : FaceMeshBudgets source points tolerance (numerator := numerator) domains}
variable {numerics : Face.PrimitiveData.FacePrimitiveBank source index (numerator := numerator) domains}
variable {shared : FaceSharedMeshes (numerator := numerator) budgets numerics}
variable {leftEnd : Last leftEntries} {rightEnd : First rightEntries}
variable (left : Occurrence shared leftEnd.selected.assigned) (right : Occurrence shared rightEnd.selected.assigned)
variable {pointEq : leftEnd.selected.fragment.located.last = rightEnd.selected.fragment.located.first}
variable {comparison : NamedEquivalent left.finish.sample.certificate.value.name
  rightEnd.selected.assigned.sample.certificate.value.name}
variable (joined : Joined leftEnd rightEnd left.finish pointEq comparison)

namespace Joined

/-- Spell the same actual incoming Entry at its retained old domain sheet, preserving its complete value. -/
@[expose] def primitiveEntry : Entry (domainCache rightEnd.selected.fragment domains).models
    leftEnd.selected.fragment.located.last joined.sample.owner :=
  joined.entry.withSheet rightEnd.selected.assigned.entry.sheet joined.entry_sheet

/-- The spelling changes no actual incoming Entry or reachability data. -/
theorem primitiveEntry_eq : primitiveEntry left joined = joined.entry :=
  joined.entry.withSheet_eq rightEnd.selected.assigned.entry.sheet joined.entry_sheet

include pointEq in
/-- Both selected original numerical cells contain the same actual physical seam point. -/
theorem covered : Junction.EndInside left.data right.data left.reading right.reading 1 0
    (finish := leftEnd.selected.fragment.located.last) :=
  ⟨left.data.readingCell_inside left.reading 1 rfl,
    right.data.readingCell_inside right.reading 0 pointEq.symm⟩

/-- The exact original covered junction cache on the given physical join and unchanged endpoint views. -/
abbrev NumericalGap :=
  {value : Junction.CachedGap left.finish.sample joined.sample
      (leftEnd.selected.fragment.located.request_endpoints leftRequest).2
      left.finish.primitiveEntry (primitiveEntry left joined) joined.joined left.data right.data
      left.reading right.reading 1 0 rfl pointEq.symm
      (finish := leftEnd.selected.fragment.located.last) //
    value = Junction.cacheGap left.finish.sample joined.sample
      (leftEnd.selected.fragment.located.request_endpoints leftRequest).2
      left.finish.primitiveEntry (primitiveEntry left joined) joined.joined left.data right.data
      left.reading right.reading 1 0 rfl pointEq.symm (covered left right (pointEq := pointEq))
      (finish := leftEnd.selected.fragment.located.last)}

/-- Execute one original attempt/readGap on this actual retained adjacent or literal closing join. -/
def readingsGap : NumericalGap left right joined :=
  ⟨Junction.cacheGap left.finish.sample joined.sample
    (leftEnd.selected.fragment.located.request_endpoints leftRequest).2
    left.finish.primitiveEntry (primitiveEntry left joined) joined.joined left.data right.data
    left.reading right.reading 1 0 rfl pointEq.symm (covered left right (pointEq := pointEq))
    (finish := leftEnd.selected.fragment.located.last), rfl⟩

namespace NumericalGap

variable {left right joined} (kept : NumericalGap left right joined)

/-- Read the same actual cached signed old-bank scalar. -/
@[expose] def value : Canonical := Junction.CachedGap.value kept.val

/-- The scalar uses the two literal old endpoint slots, with both original constants preserved. -/
theorem value_eq : kept.value = left.terminal - right.initial := Junction.CachedGap.value_eq kept.val

/-- The actual original attempt/reading/preparation cache is retained with its exact whole factory. -/
theorem cache_eq : kept.val = Junction.cacheGap left.finish.sample joined.sample
    (leftEnd.selected.fragment.located.request_endpoints leftRequest).2
    left.finish.primitiveEntry (primitiveEntry left joined) joined.joined left.data right.data
    left.reading right.reading 1 0 rfl pointEq.symm (covered left right (pointEq := pointEq))
    (finish := leftEnd.selected.fragment.located.last) := kept.property

end NumericalGap
end Joined

section AdjacentWords

open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)

variable {leftIncluded : ∀ value ∈ PointBanks.RegularPrimitiveFragments.SheetEntries.points leftEntries,
  value ∈ points}
variable {rightIncluded : ∀ value ∈ PointBanks.RegularPrimitiveFragments.SheetEntries.points rightEntries,
  value ∈ points}
variable (leftWord : Word shared leftEntries leftIncluded) (rightWord : Word shared rightEntries rightIncluded)
variable {remaining : List (CenteredEdge curve source)} {start finish : LiftedPoint 2} {initial terminal : Named}
variable (geometry : CenteredPathChain (leftParent :: rightParent :: remaining) (start := start) (finish := finish))
variable (roots : RootChain (leftParent :: rightParent :: remaining) initial terminal)

namespace Word

/-- One actual adjacent-parent physical join and its old numerical gap, preserving both whole factories. -/
abbrev Adjacent :=
  Σ physical : {value : Next leftWord.last rightWord.first leftWord.terminal.finish geometry roots //
    value = FragmentSheets.next leftWord.last rightWord.first leftWord.terminal.finish geometry roots},
  {value : Joined.NumericalGap leftWord.terminal rightWord.initial physical.val.joined //
    value = Joined.readingsGap leftWord.terminal rightWord.initial physical.val.joined}

/-- Compute the numerical adjacent gap on the GIVEN original physical Next cache and its whole factory. -/
def joinNextFrom
    (physical : {value : Next leftWord.last rightWord.first leftWord.terminal.finish geometry roots //
      value = FragmentSheets.next leftWord.last rightWord.first leftWord.terminal.finish geometry roots}) :
    Adjacent leftWord rightWord geometry roots :=
  let gap := Joined.readingsGap leftWord.terminal rightWord.initial physical.val.joined
  ⟨physical, ⟨gap, rfl⟩⟩

/-- Join the same two original parent words once, then cache one covered original numerical attempt/readGap. -/
def joinNext : Adjacent leftWord rightWord geometry roots :=
  let physical : {value : Next leftWord.last rightWord.first leftWord.terminal.finish geometry roots //
      value = FragmentSheets.next leftWord.last rightWord.first leftWord.terminal.finish geometry roots} :=
    ⟨FragmentSheets.next leftWord.last rightWord.first leftWord.terminal.finish geometry roots, rfl⟩
  joinNextFrom leftWord rightWord geometry roots physical

/-- The given adjacent physical cache retains the entire original constructor without executing it for data. -/
theorem joinNextFrom_eq
    (physical : {value : Next leftWord.last rightWord.first leftWord.terminal.finish geometry roots //
      value = FragmentSheets.next leftWord.last rightWord.first leftWord.terminal.finish geometry roots}) :
    joinNextFrom leftWord rightWord geometry roots physical = joinNext leftWord rightWord geometry roots := by
  have same : physical =
      ⟨FragmentSheets.next leftWord.last rightWord.first leftWord.terminal.finish geometry roots, rfl⟩ :=
    Subtype.ext physical.property
  cases same
  unfold joinNext joinNextFrom
  rfl

namespace Adjacent

variable {leftWord rightWord geometry roots} (kept : Adjacent leftWord rightWord geometry roots)

/-- Read the same complete adjacent physical comparison and Point/Entry/join cache. -/
@[expose] def physical : Next leftWord.last rightWord.first leftWord.terminal.finish geometry roots := kept.1.val

/-- Read the same complete old-bank numerical attempt and its actual gap cache. -/
@[expose] def numerical : Joined.NumericalGap leftWord.terminal rightWord.initial kept.physical.joined :=
  kept.2.val

/-- Read the actual signed original adjacent-parent gap. -/
@[expose] def value : Canonical := Joined.NumericalGap.value kept.numerical

/-- The complete physical cache is its original same-boundary adjacent constructor. -/
theorem physical_eq : kept.physical = FragmentSheets.next leftWord.last rightWord.first
    leftWord.terminal.finish geometry roots := kept.1.property

/-- The complete numerical cache is its original constructor on that same physical join. -/
theorem numerical_eq : kept.numerical = Joined.readingsGap leftWord.terminal rightWord.initial kept.physical.joined :=
  kept.2.property

/-- The adjacent scalar is the original left finish minus original right incoming reading. -/
theorem value_eq : kept.value = leftWord.terminal.terminal - rightWord.initial.initial :=
  Joined.NumericalGap.value_eq kept.numerical

section Numerator

variable {newNumerator : CoefficientPolynomial} {newIndex : Nat} {newTolerance : Rational}
variable {newBudgets : FaceMeshBudgets source points newTolerance (numerator := newNumerator) domains}
variable {newNumerics : Face.PrimitiveData.FacePrimitiveBank source newIndex
  (numerator := newNumerator) domains}
variable (newShared : FaceSharedMeshes (numerator := newNumerator) newBudgets newNumerics)

/-- Transport the entire GIVEN actual adjacent root cache along whole boundary and Finish identities. -/
private def transportPhysical
    {last nextLast : Last leftEntries} {first nextFirst : First rightEntries}
    {finish : Finish last.selected.assigned} {nextFinish : Finish nextLast.selected.assigned}
    (lastEq : last = nextLast) (firstEq : first = nextFirst) (finishEq : HEq finish nextFinish)
    (physical : Next last first finish geometry roots) : Next nextLast nextFirst nextFinish geometry roots := by
  cases lastEq
  cases firstEq
  cases finishEq
  exact physical

/-- The whole adjacent producer equation survives that exact input transport. -/
private theorem transportPhysical_factory
    {last nextLast : Last leftEntries} {first nextFirst : First rightEntries}
    {finish : Finish last.selected.assigned} {nextFinish : Finish nextLast.selected.assigned}
    (lastEq : last = nextLast) (firstEq : first = nextFirst) (finishEq : HEq finish nextFinish)
    (physical : Next last first finish geometry roots)
    (factory : physical = FragmentSheets.next last first finish geometry roots) :
    transportPhysical lastEq firstEq finishEq physical =
      FragmentSheets.next nextLast nextFirst nextFinish geometry roots := by
  cases lastEq
  cases firstEq
  cases finishEq
  unfold transportPhysical
  exact factory

/-- Reuse the literal original cross-parent Point/Entry/OwnerJoin cache for one actual new-numerator gap.

Both new words contain the same original first/last source metadata and
whole Finish factories. These genuine identities transport the physical
cache; no RootChain query/comparison or physical join is executed again.
-/
def revalue
    (newLeft : Word newShared leftEntries leftIncluded) (newRight : Word newShared rightEntries rightIncluded) :
    {value : Adjacent newLeft newRight geometry roots // value = joinNext newLeft newRight geometry roots} :=
  have lastEq : leftWord.last = newLeft.last := leftWord.last_eq.trans newLeft.last_eq.symm
  have firstEq : rightWord.first = newRight.first := rightWord.first_eq.trans newRight.first_eq.symm
  have finishEq : HEq leftWord.terminal.finish newLeft.terminal.finish :=
    (Word.terminalFinish_heq (shared := shared) (newShared := newShared) lastEq.symm
      newLeft.terminal leftWord.terminal).symm
  let physical : {value : Next newLeft.last newRight.first newLeft.terminal.finish geometry roots //
      value = FragmentSheets.next newLeft.last newRight.first newLeft.terminal.finish geometry roots} :=
    ⟨transportPhysical lastEq firstEq finishEq kept.physical,
      transportPhysical_factory lastEq firstEq finishEq kept.physical kept.physical_eq⟩
  ⟨joinNextFrom newLeft newRight geometry roots physical, joinNextFrom_eq newLeft newRight geometry roots physical⟩

end Numerator

end Adjacent
end Word
end AdjacentWords

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.FragmentSheets
