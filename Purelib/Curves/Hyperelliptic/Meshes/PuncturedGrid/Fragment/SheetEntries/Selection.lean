module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
public import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Position
import Purelib.Polynomial.Geometry.Grid.AxisNeighbors
import Purelib.Data.Rat.Fraction

/-! # Original first and last sheet-entry occurrences

The original partition selectors and interval-position reader locate an
already retained occurrence. The sheet-spine reader returns that SAME
geometric fragment and Entry. Selection never prepares or observes a root,
face, Point, Query, domain or split.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.FragmentSheets

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
  (RegularPrimitiveFragment RegularPrimitiveFragments)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment (SheetEntry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions (Interval)
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
variable {frames : RootFrames base.bank.grid} {source : Differential genus} {axes : PrimitiveAxes base.bank.grid}
variable {parent : CenteredEdge curve source} {partition : AxisPartition 0 1 (axes.parameters parent)}
variable {domains : FaceDomainBank frames base.faces.regulars} {target : Rational}
variable {request : LocalRequest parent count target}
variable {fragments : RegularPrimitiveFragments axes parent partition partition.intervals}
variable (entries : FragmentSheets domains request fragments)

/-- The original interval-position result and SAME indexed fragment/Entry read, each with its complete factory. -/
@[expose] def Selected (chosen : Interval) (member : chosen ∈ partition.intervals) :=
  Σ found : {value : {position : Fin partition.intervals.length //
      partition.intervals[position.val]'position.isLt = chosen} //
    value = Interval.position chosen partition.intervals member},
  {value : Σ fragment : RegularPrimitiveFragment axes parent partition
        (partition.intervals[found.val.val.val]'found.val.val.isLt),
      SheetEntry fragment domains request // value = entries.at found.val.val}

/-- Locate the already selected original interval once and read its actual sheet-entry occurrence once. -/
def select (chosen : Interval) (member : chosen ∈ partition.intervals) : Selected entries chosen member :=
  let found : {value : {position : Fin partition.intervals.length //
      partition.intervals[position.val]'position.isLt = chosen} //
    value = Interval.position chosen partition.intervals member} :=
    ⟨Interval.position chosen partition.intervals member, rfl⟩
  let retained := entries.at found.val.val
  ⟨found, ⟨retained, rfl⟩⟩

namespace Selected

variable {entries} {chosen : Interval} {member : chosen ∈ partition.intervals}
variable (selected : Selected entries chosen member)

/-- Read the whole original interval-position result. -/
@[expose] def index : {position : Fin partition.intervals.length //
    partition.intervals[position.val]'position.isLt = chosen} := selected.1.val

/-- Read the literal bounded occurrence index. -/
@[expose] def position : Fin partition.intervals.length := selected.index.val

/-- Read the actual original interval at the retained occurrence. -/
@[expose] def interval : Interval := partition.intervals[selected.position.val]'selected.position.isLt

/-- Read the actual retained geometric fragment at that same interval occurrence. -/
@[expose] def fragment : RegularPrimitiveFragment axes parent partition selected.interval := selected.2.val.1

/-- Read the actual original SheetEntry, preserving its complete Point, root comparison, domain and split. -/
@[expose] def assigned : SheetEntry selected.fragment domains request := selected.2.val.2

/-- The whole index is the original finite metadata-position factory result. -/
theorem index_eq : selected.index = Interval.position chosen partition.intervals member := selected.1.property

/-- The retained whole interval is the supplied original selected payload. -/
theorem interval_eq : selected.interval = chosen := selected.index.property

/-- The complete fragment/Entry pair is the SAME original sheet-spine read. -/
theorem read_eq : (⟨selected.fragment, selected.assigned⟩ :
    Σ fragment : RegularPrimitiveFragment axes parent partition selected.interval,
      SheetEntry fragment domains request) =
    entries.at selected.position := selected.2.property

end Selected

/-- The original following selector at zero and its actual first fragment/Entry read. -/
@[expose] def First :=
  Σ selected : {value : AxisNeighbors.AtEndpoint partition.intervals (0 : Rational) false //
    value = partition.following 0 partition.lower_mem partition.proper},
    Selected entries selected.val.interval selected.val.member

/-- Select the original zero-endpoint occurrence and retain its complete original metadata/read factories. -/
def first : First entries :=
  let selected : {value : AxisNeighbors.AtEndpoint partition.intervals (0 : Rational) false //
    value = partition.following 0 partition.lower_mem partition.proper} :=
    ⟨partition.following 0 partition.lower_mem partition.proper, rfl⟩
  let retained := select entries selected.val.interval selected.val.member
  ⟨selected, retained⟩

namespace First

variable {entries} (retained : First entries)

/-- Read the original following-interval selector, without another neighbor scan. -/
@[expose] def selection : AxisNeighbors.AtEndpoint partition.intervals (0 : Rational) false := retained.1.val

/-- Read the actual original first fragment and SheetEntry cache. -/
@[expose] def selected : Selected entries retained.selection.interval retained.selection.member := retained.2

/-- The whole following selector retains its original partition factory. -/
theorem selection_eq : retained.selection = partition.following 0 partition.lower_mem partition.proper :=
  retained.1.property

/-- The literal retained first interval starts at the original zero parameter. -/
theorem lower_eq : retained.selected.interval.lower = 0 :=
  (congrArg (fun value : Interval => value.lower) retained.selected.interval_eq).trans retained.selection.endpoint_eq

end First

/-- The original final-endpoint selector and its actual last fragment/Entry read. -/
@[expose] def Last :=
  Σ selected : {value : AxisPartition.Endpoint partition (1 : Rational) //
    value = partition.endpoint 1 partition.upper_mem},
    Selected entries selected.val.interval selected.val.member

/-- Select the original final-endpoint occurrence and retain the same metadata/read factories. -/
def last : Last entries :=
  let selected : {value : AxisPartition.Endpoint partition (1 : Rational) //
    value = partition.endpoint 1 partition.upper_mem} := ⟨partition.endpoint 1 partition.upper_mem, rfl⟩
  let retained := select entries selected.val.interval selected.val.member
  ⟨selected, retained⟩

namespace Last

variable {entries} (retained : Last entries)

/-- Read the original final-endpoint selector without another neighbor scan. -/
@[expose] def selection : AxisPartition.Endpoint partition (1 : Rational) := retained.1.val

/-- Read the actual original last fragment and SheetEntry cache. -/
@[expose] def selected : Selected entries retained.selection.interval retained.selection.member := retained.2

/-- The whole final-endpoint selector retains its original partition factory. -/
theorem selection_eq : retained.selection = partition.endpoint 1 partition.upper_mem := retained.1.property

/-- The literal retained last interval finishes at the original one parameter. -/
theorem upper_eq : retained.selected.interval.upper = 1 :=
  (congrArg (fun value : Interval => value.upper) retained.selected.interval_eq).trans
    (AxisPartition.Endpoint.upper_eq retained.selection)

end Last

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.FragmentSheets

end
