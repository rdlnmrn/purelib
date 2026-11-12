module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Joint
public import Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.Vertices
import Purelib.Data.List.DependentProduct
import Purelib.Curves.Legendre.Paths
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.RootContinuation.FixedRootBoxBudget
import Purelib.Riemann.RootContinuation.FixedRootBoxPath
import Purelib.Riemann.Topology.SquareRootContinuationChain

/-! # Shared signed Owners on the actual paid strip grid

The given joint grid is retained whole. Its two original endpoint lists are
bound once, and one original budget Owner is bound at every shared vertex.
Nested original DependentProducts preserve bounded vertex occurrences and
their complete factories. Adjacent cells project the same stored values.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.FixedRootBoxPath (Inside PathData)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}
    (range : Range patch) (budget : FixedRootBoxBudget.Budget patch.base.seed.owner)
    (factory : budget = range.seedBudget)
    {ambient : Box} {start finish : Canonical}
    (segment : ClearSegment (Paths.polynomial parameter) ambient start finish)
    (firstInside : patch.box.Contains start) (lastInside : patch.box.Contains finish)
    (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ range.stripBound)

namespace JointGrid

/-- The actual strip radicand at two retained endpoint occurrences.

Its value is not a fixed-fibre spatial path or an interpolation of roots.
-/
@[expose] def radicand (time fraction : Endpoint) : Canonical :=
  (Paths.polynomial (parameter + (⟨time.parameter, 0⟩ : Canonical) * increment)).eval
    (segment.pointAt fraction.parameter)

/-- One original budget Owner at every shared bounded endpoint pair, with each complete ownerAt factory. -/
@[expose] def OwnerTable (timeFirst : Endpoint) (timeTargets : List Endpoint)
    (spaceFirst : Endpoint) (spaceTargets : List Endpoint) :=
  DependentProduct (timeFirst :: timeTargets) (fun timeIndex =>
    DependentProduct (spaceFirst :: spaceTargets) (fun spaceIndex =>
      let time := (timeFirst :: timeTargets)[timeIndex.val]'timeIndex.isLt
      let fraction := (spaceFirst :: spaceTargets)[spaceIndex.val]'spaceIndex.isLt
      { value : Owner (radicand (segment := segment) increment time fraction) //
        value = budget.ownerAt
          (range.rectangle_nonzero segment firstInside lastInside increment admitted
            time.parameter fraction.parameter time.inside fraction.inside)
          (range.rectangle_movement budget factory segment firstInside lastInside increment admitted
            time.parameter fraction.parameter time.inside fraction.inside) }))

namespace OwnerTable

/-- Bind each actual signed reference Owner once in the original nested occurrence products. -/
def build (timeFirst : Endpoint) (timeTargets : List Endpoint)
    (spaceFirst : Endpoint) (spaceTargets : List Endpoint) :
    OwnerTable range budget factory segment firstInside lastInside increment admitted
      timeFirst timeTargets spaceFirst spaceTargets :=
  DependentProduct.ofFn (timeFirst :: timeTargets) (fun timeIndex =>
    let time := (timeFirst :: timeTargets)[timeIndex.val]'timeIndex.isLt
    DependentProduct.ofFn (spaceFirst :: spaceTargets) (fun spaceIndex =>
      let fraction := (spaceFirst :: spaceTargets)[spaceIndex.val]'spaceIndex.isLt
      let point := radicand (segment := segment) increment time fraction
      let owner := budget.ownerAt (target := point)
        (range.rectangle_nonzero segment firstInside lastInside increment admitted
          time.parameter fraction.parameter time.inside fraction.inside)
        (range.rectangle_movement budget factory segment firstInside lastInside increment admitted
          time.parameter fraction.parameter time.inside fraction.inside)
      ⟨owner, rfl⟩))

variable {range budget factory segment firstInside lastInside increment admitted}
    {timeFirst spaceFirst : Endpoint} {timeTargets spaceTargets : List Endpoint}
    (table : OwnerTable range budget factory segment firstInside lastInside increment admitted
      timeFirst timeTargets spaceFirst spaceTargets)

/-- Read the SAME stored original Owner at its two unchanged bounded vertex indices. -/
@[expose] def owner (timeIndex : Fin (timeFirst :: timeTargets).length)
    (spaceIndex : Fin (spaceFirst :: spaceTargets).length) :
    Owner (radicand (segment := segment) increment
      ((timeFirst :: timeTargets)[timeIndex.val]'timeIndex.isLt)
      ((spaceFirst :: spaceTargets)[spaceIndex.val]'spaceIndex.isLt)) :=
  (DependentProduct.get (spaceFirst :: spaceTargets)
    (DependentProduct.get (timeFirst :: timeTargets) table timeIndex) spaceIndex).val

/-- The stored Owner keeps the complete original budget.ownerAt factory at that exact endpoint pair. -/
theorem owner_eq (timeIndex : Fin (timeFirst :: timeTargets).length)
    (spaceIndex : Fin (spaceFirst :: spaceTargets).length) :
    table.owner timeIndex spaceIndex = budget.ownerAt
      (range.rectangle_nonzero segment firstInside lastInside increment admitted
        ((timeFirst :: timeTargets)[timeIndex.val]'timeIndex.isLt).parameter
        ((spaceFirst :: spaceTargets)[spaceIndex.val]'spaceIndex.isLt).parameter
        ((timeFirst :: timeTargets)[timeIndex.val]'timeIndex.isLt).inside
        ((spaceFirst :: spaceTargets)[spaceIndex.val]'spaceIndex.isLt).inside)
      (range.rectangle_movement budget factory segment firstInside lastInside increment admitted
        ((timeFirst :: timeTargets)[timeIndex.val]'timeIndex.isLt).parameter
        ((spaceFirst :: spaceTargets)[spaceIndex.val]'spaceIndex.isLt).parameter
        ((timeFirst :: timeTargets)[timeIndex.val]'timeIndex.isLt).inside
        ((spaceFirst :: spaceTargets)[spaceIndex.val]'spaceIndex.isLt).inside) :=
  (DependentProduct.get (spaceFirst :: spaceTargets)
    (DependentProduct.get (timeFirst :: timeTargets) table timeIndex) spaceIndex).property

/-- Each SAME cached vertex Owner retains exactly the original signed seed box. -/
theorem owner_box (timeIndex : Fin (timeFirst :: timeTargets).length)
    (spaceIndex : Fin (spaceFirst :: spaceTargets).length) :
    (table.owner timeIndex spaceIndex).track.initial.box = patch.base.seed.owner.track.initial.box :=
  (congrArg (fun value : Owner _ => value.track.initial.box) (table.owner_eq timeIndex spaceIndex)).trans
    (FixedRootBoxBudget.Budget.ownerAt_box _ _ _)

/-- Each SAME cached vertex Owner retains exactly the paid common target clearance. -/
theorem owner_clearance (timeIndex : Fin (timeFirst :: timeTargets).length)
    (spaceIndex : Fin (spaceFirst :: spaceTargets).length) :
    (table.owner timeIndex spaceIndex).track.initial.clearance.bound = budget.clearance :=
  (congrArg (fun value : Owner _ => value.track.initial.clearance.bound) (table.owner_eq timeIndex spaceIndex)).trans
    (FixedRootBoxBudget.Budget.ownerAt_clearance _ _ _)

/-- Equality of the actual bounded occurrence indices transports the SAME whole cached vertex Owner. -/
theorem owner_index_heq {firstTime lastTime : Fin (timeFirst :: timeTargets).length}
    {firstSpace lastSpace : Fin (spaceFirst :: spaceTargets).length}
    (timeEq : firstTime = lastTime) (spaceEq : firstSpace = lastSpace) :
    HEq (table.owner firstTime firstSpace) (table.owner lastTime lastSpace) := by
  cases timeEq
  cases spaceEq
  rfl

end OwnerTable

variable (firstPath lastPath : PathData budget budget)
    {firstDepth lastDepth : Nat} {left right : Endpoint}
    (grid : JointGrid (range := range) (budget := budget) increment firstPath lastPath
      firstDepth lastDepth left right)

/-- The SAME whole paid grid, two original target lists and all shared signed vertex Owners.

The exact output keeps the original grid and both list factories as data.
OwnerTable stores one complete original Owner per bounded vertex; it is not
a function which reconstructs owners when neighboring cells query it.
-/
@[expose] def Vertices :=
  (original : { value : JointGrid (range := range) (budget := budget) increment firstPath lastPath
      firstDepth lastDepth left right // value = grid }) ×
  (times : { value : List Endpoint // value = dyadicTargets original.val.selection.stage left right }) ×
  (spaces : { value : List Endpoint //
      value = dyadicTargets (firstDepth + (lastDepth + original.val.selection.stage)) left right }) ×
    { owners : OwnerTable range budget factory segment firstInside lastInside increment admitted
        left times.val left spaces.val //
      owners = OwnerTable.build range budget factory segment firstInside lastInside increment admitted
        left times.val left spaces.val }

/-- Bind both target words once, then bind each shared signed Owner once after the GIVEN grid's paid selection. -/
def vertices :
    Vertices range budget factory segment firstInside lastInside increment admitted firstPath lastPath grid :=
  let times := dyadicTargets grid.selection.stage left right
  let spaces := dyadicTargets (firstDepth + (lastDepth + grid.selection.stage)) left right
  let owners := OwnerTable.build range budget factory segment firstInside lastInside increment admitted
    left times left spaces
  ⟨⟨grid, rfl⟩, ⟨times, rfl⟩, ⟨spaces, rfl⟩, ⟨owners, rfl⟩⟩

namespace Vertices

variable {range budget factory segment firstInside lastInside increment admitted firstPath lastPath grid}
    (cached : Vertices range budget factory segment firstInside lastInside increment admitted firstPath lastPath grid)

/-- Read the SAME original joint grid, retaining its selected floor and both original child-occurrence tables. -/
@[expose] def original : JointGrid (range := range) (budget := budget) increment firstPath lastPath
    firstDepth lastDepth left right := cached.1.val

/-- The entire original joint grid is the GIVEN value, without a second selection or table construction. -/
theorem original_eq : cached.original = grid := cached.1.property

/-- Read the SAME retained time-target endpoint word. -/
@[expose] def times : List Endpoint := cached.2.1.val

/-- The complete time word retains its original dyadicTargets factory. -/
theorem times_eq : cached.times = dyadicTargets cached.original.selection.stage left right := cached.2.1.property

/-- Read the SAME retained spatial-target endpoint word. -/
@[expose] def spaces : List Endpoint := cached.2.2.1.val

/-- The complete spatial word retains its actual common-depth dyadicTargets factory. -/
theorem spaces_eq : cached.spaces =
    dyadicTargets (firstDepth + (lastDepth + cached.original.selection.stage)) left right := cached.2.2.1.property

/-- Read the SAME original nested table of complete shared vertex Owners. -/
@[expose] def owners : OwnerTable range budget factory segment firstInside lastInside increment admitted
    left cached.times left cached.spaces := cached.2.2.2.val

/-- The complete owner table retains its original one-pass materialization factory. -/
theorem owners_eq : cached.owners =
    OwnerTable.build range budget factory segment firstInside lastInside increment admitted
      left cached.times left cached.spaces := cached.2.2.2.property

/-- Read one shared vertex Owner using its actual original bounded row and column occurrences. -/
@[expose] def owner (timeIndex : Fin (left :: cached.times).length)
    (spaceIndex : Fin (left :: cached.spaces).length) :
    Owner (radicand (segment := segment) increment
      ((left :: cached.times)[timeIndex.val]'timeIndex.isLt)
      ((left :: cached.spaces)[spaceIndex.val]'spaceIndex.isLt)) := cached.owners.owner timeIndex spaceIndex

/-- The actual shared vertex Owner keeps its original signed box. -/
theorem owner_box (timeIndex : Fin (left :: cached.times).length)
    (spaceIndex : Fin (left :: cached.spaces).length) :
    (cached.owner timeIndex spaceIndex).track.initial.box = patch.base.seed.owner.track.initial.box :=
  cached.owners.owner_box timeIndex spaceIndex

/-- The actual shared vertex Owner keeps its exact original paid clearance. -/
theorem owner_clearance (timeIndex : Fin (left :: cached.times).length)
    (spaceIndex : Fin (left :: cached.spaces).length) :
    (cached.owner timeIndex spaceIndex).track.initial.clearance.bound = budget.clearance :=
  cached.owners.owner_clearance timeIndex spaceIndex

/-- Equal bounded vertex occurrences read the SAME whole stored Owner, independently of coordinate coincidences. -/
theorem owner_index_heq {firstTime lastTime : Fin (left :: cached.times).length}
    {firstSpace lastSpace : Fin (left :: cached.spaces).length}
    (timeEq : firstTime = lastTime) (spaceEq : firstSpace = lastSpace) :
    HEq (cached.owner firstTime firstSpace) (cached.owner lastTime lastSpace) :=
  cached.owners.owner_index_heq timeEq spaceEq

end Vertices

end JointGrid

end Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range

end
