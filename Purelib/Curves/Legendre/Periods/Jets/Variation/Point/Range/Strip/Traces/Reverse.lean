module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Traces.Shared
public import Purelib.Riemann.Paths.OwnerTracePath.Box.Reverse
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Traces
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Traces.Links
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Traces.Corners
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Traces.Realizations
import Purelib.Riemann.Paths.OwnerTracePath.Reverse
import Purelib.Riemann.Paths.OwnerTracePath.Dyadic
import Purelib.Riemann.Paths.OwnerTracePath.Pullback
import Purelib.Data.List.DependentProduct
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Vertices
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Edges
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.RootContinuation.FixedRootBoxBudget
import Purelib.Riemann.RootContinuation.FixedRootBoxPath
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Joint
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Spatial
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTracePath.Between

/-! # Actual reverse strip traces on the same complete native reading bank

Each reverse consumer uses the retained whole cache and checked forward
edges. The original Range variation and selected dyadic payment derive
reverse movement. No Owner, request, comparison selector or native sample
is executed, and no reverse trace is inferred from forward Small alone.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.JointGrid.Vertices.Edges

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.FixedRootBoxPath (Inside PathData)
open Purelib.Riemann.Paths.OwnerTracePath
open OwnerPath.Dyadic (LinkPreparation)
open Purelib.Riemann.Paths.OwnerTraceReadings
open Links.Requirements (Readings)

attribute [local irreducible] timePolynomial spacePolynomial
attribute [local irreducible] Links Links.Requirements Links.Requirements.Demands
attribute [local irreducible] Links.Requirements.Targets Readings Shared

variable {parameter : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}
    {range : Range patch} {budget : FixedRootBoxBudget.Budget patch.base.seed.owner}
    {factory : budget = range.seedBudget}
    {ambient : Box} {start finish : Canonical}
    {segment : ClearSegment (Paths.polynomial parameter) ambient start finish}
    {firstInside : patch.box.Contains start} {lastInside : patch.box.Contains finish}
    {increment : Canonical} {admitted : Norm.Basic.normSq increment ≤ range.stripBound}
    {firstPath lastPath : PathData budget budget}
    {firstDepth lastDepth : Nat} {left right : Endpoint}
    {grid : JointGrid (range := range) (budget := budget) increment firstPath lastPath
      firstDepth lastDepth left right}
    {cached : Vertices range budget factory segment firstInside lastInside increment admitted firstPath lastPath grid}
    {ordered : left.parameter ≤ right.parameter} {zeroInside : Inside 0} {oneInside : Inside 1}
    {firstFactory : firstPath =
      range.spatialPath budget factory segment firstInside lastInside increment admitted 0 zeroInside}
    {lastFactory : lastPath =
      range.spatialPath budget factory segment firstInside lastInside increment admitted 1 oneInside}
    {retained : Edges cached ordered zeroInside oneInside firstFactory lastFactory}

namespace Shared

variable (shared : Shared retained)

/-- The retained Time reversal keeps its original link and trace factories on the given native bank. -/
@[expose] def TimeReverse (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin (left :: retained.original.spaces).length) :=
  LinkPreparation.ReverseTrace
    (cached := (Links.time (linked := shared.links) timeIndex spaceIndex).2.2)
    (Readings.timeFirst (linked := shared.links) (required := shared.required)
        (demanded := shared.demanded) (targeted := shared.targeted) (observed := shared.observed) timeIndex spaceIndex)
    (Readings.timeLast (linked := shared.links) (required := shared.required)
        (demanded := shared.demanded) (targeted := shared.targeted) (observed := shared.observed) timeIndex spaceIndex)
    (Readings.time_first_later (linked := shared.links) (required := shared.required)
        (demanded := shared.demanded) (targeted := shared.targeted) (observed := shared.observed) timeIndex spaceIndex)
    (Readings.time_last_later (linked := shared.links) (required := shared.required)
        (demanded := shared.demanded) (targeted := shared.targeted) (observed := shared.observed) timeIndex spaceIndex)
    (shared.time timeIndex spaceIndex).val

/-- Reverse one given Time trace through its retained link preparation and complete native readings. -/
def reverseTime (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin (left :: retained.original.spaces).length) : TimeReverse shared timeIndex spaceIndex :=
  LinkPreparation.reverseTrace
    (cached := (Links.time (linked := shared.links) timeIndex spaceIndex).2.2)
    (Readings.timeFirst (linked := shared.links) (required := shared.required)
        (demanded := shared.demanded) (targeted := shared.targeted) (observed := shared.observed) timeIndex spaceIndex)
    (Readings.timeLast (linked := shared.links) (required := shared.required)
        (demanded := shared.demanded) (targeted := shared.targeted) (observed := shared.observed) timeIndex spaceIndex)
    (Readings.time_first_later (linked := shared.links) (required := shared.required)
        (demanded := shared.demanded) (targeted := shared.targeted) (observed := shared.observed) timeIndex spaceIndex)
    (Readings.time_last_later (linked := shared.links) (required := shared.required)
        (demanded := shared.demanded) (targeted := shared.targeted) (observed := shared.observed) timeIndex spaceIndex)
    (shared.time timeIndex spaceIndex).val

/-- The retained Space reversal keeps its original link and trace factories on the given native bank. -/
@[expose] def SpaceReverse (timeIndex : Fin (left :: retained.original.times).length)
    (spaceIndex : Fin retained.original.spaces.length) :=
  LinkPreparation.ReverseTrace
    (cached := (Links.space (linked := shared.links) timeIndex spaceIndex).2.2)
    (Readings.spaceFirst (linked := shared.links) (required := shared.required)
        (demanded := shared.demanded) (targeted := shared.targeted) (observed := shared.observed) timeIndex spaceIndex)
    (Readings.spaceLast (linked := shared.links) (required := shared.required)
        (demanded := shared.demanded) (targeted := shared.targeted) (observed := shared.observed) timeIndex spaceIndex)
    (Readings.space_first_later (linked := shared.links) (required := shared.required)
        (demanded := shared.demanded) (targeted := shared.targeted) (observed := shared.observed) timeIndex spaceIndex)
    (Readings.space_last_later (linked := shared.links) (required := shared.required)
        (demanded := shared.demanded) (targeted := shared.targeted) (observed := shared.observed) timeIndex spaceIndex)
    (shared.space timeIndex spaceIndex).val

/-- Reverse one given Space trace through its retained link preparation and complete native readings. -/
def reverseSpace (timeIndex : Fin (left :: retained.original.times).length)
    (spaceIndex : Fin retained.original.spaces.length) : SpaceReverse shared timeIndex spaceIndex :=
  LinkPreparation.reverseTrace
    (cached := (Links.space (linked := shared.links) timeIndex spaceIndex).2.2)
    (Readings.spaceFirst (linked := shared.links) (required := shared.required)
        (demanded := shared.demanded) (targeted := shared.targeted) (observed := shared.observed) timeIndex spaceIndex)
    (Readings.spaceLast (linked := shared.links) (required := shared.required)
        (demanded := shared.demanded) (targeted := shared.targeted) (observed := shared.observed) timeIndex spaceIndex)
    (Readings.space_first_later (linked := shared.links) (required := shared.required)
        (demanded := shared.demanded) (targeted := shared.targeted) (observed := shared.observed) timeIndex spaceIndex)
    (Readings.space_last_later (linked := shared.links) (required := shared.required)
        (demanded := shared.demanded) (targeted := shared.targeted) (observed := shared.observed) timeIndex spaceIndex)
    (shared.space timeIndex spaceIndex).val

/-- One reverse temporal trace per original unique edge occurrence, with its complete construction factory. -/
@[expose] def TimeReverses := DependentProduct retained.original.times (fun timeIndex =>
  DependentProduct (left :: retained.original.spaces) (fun spaceIndex =>
    { value : TimeReverse shared timeIndex spaceIndex // value = shared.reverseTime timeIndex spaceIndex }))

/-- One reverse spatial trace per original unique edge occurrence, with its complete construction factory. -/
@[expose] def SpaceReverses := DependentProduct (left :: retained.original.times) (fun timeIndex =>
  DependentProduct retained.original.spaces (fun spaceIndex =>
    { value : SpaceReverse shared timeIndex spaceIndex // value = shared.reverseSpace timeIndex spaceIndex }))

/-- Both actual reverse tables retain the same complete given forward/corner cache as data. -/
@[expose] def Reversed :=
  (_original : { value : Shared retained // value = shared }) × TimeReverses shared × SpaceReverses shared

/-- Construct both reverse tables once from the GIVEN shared corner/interior bank, without any observation. -/
def reverse : Reversed shared :=
  let times := DependentProduct.ofFn retained.original.times (fun timeIndex =>
    DependentProduct.ofFn (left :: retained.original.spaces) (fun spaceIndex =>
      let value := shared.reverseTime timeIndex spaceIndex
      ⟨value, rfl⟩))
  let spaces := DependentProduct.ofFn (left :: retained.original.times) (fun timeIndex =>
    DependentProduct.ofFn retained.original.spaces (fun spaceIndex =>
      let value := shared.reverseSpace timeIndex spaceIndex
      ⟨value, rfl⟩))
  ⟨⟨shared, rfl⟩, times, spaces⟩

namespace Reversed

variable {shared} (reversed : Reversed shared)

/-- Project the SAME actual reverse temporal cache at its original bounded occurrence. -/
@[expose] def time (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin (left :: retained.original.spaces).length) : TimeReverse shared timeIndex spaceIndex :=
  (DependentProduct.get (left :: retained.original.spaces)
    (DependentProduct.get retained.original.times reversed.2.1 timeIndex) spaceIndex).val

/-- Project the SAME actual reverse spatial cache at its original bounded occurrence. -/
@[expose] def space (timeIndex : Fin (left :: retained.original.times).length)
    (spaceIndex : Fin retained.original.spaces.length) : SpaceReverse shared timeIndex spaceIndex :=
  (DependentProduct.get retained.original.spaces
    (DependentProduct.get (left :: retained.original.times) reversed.2.2 timeIndex) spaceIndex).val

/-- The temporal reverse starts at the exact same complete coarse-corner reading as the forward trace's end. -/
theorem time_first_eq (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin (left :: retained.original.spaces).length) :
    (reversed.time timeIndex spaceIndex).2.val.realization.first =
      Readings.timeLast (linked := shared.links)
          (required := shared.required)
          (demanded := shared.demanded) (targeted := shared.targeted)
          (observed := shared.observed) timeIndex spaceIndex :=
  (reversed.time timeIndex spaceIndex).2.val.first_eq

/-- The temporal reverse finishes at the exact same complete coarse-corner reading as the forward trace's start. -/
theorem time_last_eq (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin (left :: retained.original.spaces).length) :
    (reversed.time timeIndex spaceIndex).2.val.realization.last =
      Readings.timeFirst (linked := shared.links)
          (required := shared.required)
          (demanded := shared.demanded) (targeted := shared.targeted)
          (observed := shared.observed) timeIndex spaceIndex :=
  (reversed.time timeIndex spaceIndex).2.val.last_eq

/-- The spatial reverse starts at the same complete transported coarse-corner reading as the forward trace's end. -/
theorem space_first_eq (timeIndex : Fin (left :: retained.original.times).length)
    (spaceIndex : Fin retained.original.spaces.length) :
    (reversed.space timeIndex spaceIndex).2.val.realization.first =
      Readings.spaceLast (linked := shared.links)
          (required := shared.required)
          (demanded := shared.demanded) (targeted := shared.targeted)
          (observed := shared.observed) timeIndex spaceIndex :=
  (reversed.space timeIndex spaceIndex).2.val.first_eq

/-- The spatial reverse finishes at the same complete transported coarse-corner reading as the forward trace's start. -/
theorem space_last_eq (timeIndex : Fin (left :: retained.original.times).length)
    (spaceIndex : Fin retained.original.spaces.length) :
    (reversed.space timeIndex spaceIndex).2.val.realization.last =
      Readings.spaceFirst (linked := shared.links)
          (required := shared.required)
          (demanded := shared.demanded) (targeted := shared.targeted)
          (observed := shared.observed) timeIndex spaceIndex :=
  (reversed.space timeIndex spaceIndex).2.val.last_eq

/-- The temporal reverse starts at the complete SAME incoming native corner object under exact Owner transport. -/
theorem time_first_heq (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin (left :: retained.original.spaces).length) :
    HEq (reversed.time timeIndex spaceIndex).2.val.realization.first
      (Readings.sample (linked := shared.links)
          (required := shared.required)
          (demanded := shared.demanded) (targeted := shared.targeted)
          (observed := shared.observed) timeIndex.succ spaceIndex) :=
  (heq_of_eq (reversed.time_first_eq timeIndex spaceIndex)).trans (OwnerReading.castParameter_heq _ _)

/-- The temporal reverse finishes at the complete SAME incoming native corner object under exact Owner transport. -/
theorem time_last_heq (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin (left :: retained.original.spaces).length) :
    HEq (reversed.time timeIndex spaceIndex).2.val.realization.last
      (Readings.sample (linked := shared.links)
          (required := shared.required)
          (demanded := shared.demanded) (targeted := shared.targeted)
          (observed := shared.observed) timeIndex.castSucc spaceIndex) :=
  (heq_of_eq (reversed.time_last_eq timeIndex spaceIndex)).trans (OwnerReading.castParameter_heq _ _)

/-- The spatial reverse starts at the complete SAME incoming native corner object under exact Owner transport. -/
theorem space_first_heq (timeIndex : Fin (left :: retained.original.times).length)
    (spaceIndex : Fin retained.original.spaces.length) :
    HEq (reversed.space timeIndex spaceIndex).2.val.realization.first
      (Readings.sample (linked := shared.links)
          (required := shared.required)
          (demanded := shared.demanded) (targeted := shared.targeted)
          (observed := shared.observed) timeIndex spaceIndex.succ) :=
  (heq_of_eq (reversed.space_first_eq timeIndex spaceIndex)).trans (OwnerReading.castParameter_heq _ _)

/-- The spatial reverse finishes at the complete SAME incoming native corner object under exact Owner transport. -/
theorem space_last_heq (timeIndex : Fin (left :: retained.original.times).length)
    (spaceIndex : Fin retained.original.spaces.length) :
    HEq (reversed.space timeIndex spaceIndex).2.val.realization.last
      (Readings.sample (linked := shared.links)
          (required := shared.required)
          (demanded := shared.demanded) (targeted := shared.targeted)
          (observed := shared.observed) timeIndex spaceIndex.castSucc) :=
  (heq_of_eq (reversed.space_last_eq timeIndex spaceIndex)).trans (OwnerReading.castParameter_heq _ _)

/-- The complete temporal root word reverses, retaining every stationary occurrence. -/
theorem time_root_word (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin (left :: retained.original.spaces).length) :
    (Readings.timeLast (linked := shared.links)
          (required := shared.required)
          (demanded := shared.demanded) (targeted := shared.targeted)
          (observed := shared.observed) timeIndex spaceIndex).value ::
        (reversed.time timeIndex spaceIndex).2.val.realization.roots =
      ((Readings.timeFirst (linked := shared.links)
          (required := shared.required)
          (demanded := shared.demanded) (targeted := shared.targeted)
          (observed := shared.observed) timeIndex spaceIndex).value ::
        (shared.time timeIndex spaceIndex).val.realization.roots).reverse :=
  (reversed.time timeIndex spaceIndex).2.val.root_word

/-- The complete spatial root word reverses, retaining every stationary occurrence. -/
theorem space_root_word (timeIndex : Fin (left :: retained.original.times).length)
    (spaceIndex : Fin retained.original.spaces.length) :
    (Readings.spaceLast (linked := shared.links)
          (required := shared.required)
          (demanded := shared.demanded) (targeted := shared.targeted)
          (observed := shared.observed) timeIndex spaceIndex).value ::
        (reversed.space timeIndex spaceIndex).2.val.realization.roots =
      ((Readings.spaceFirst (linked := shared.links)
          (required := shared.required)
          (demanded := shared.demanded) (targeted := shared.targeted)
          (observed := shared.observed) timeIndex spaceIndex).value ::
        (shared.space timeIndex spaceIndex).val.realization.roots).reverse :=
  (reversed.space timeIndex spaceIndex).2.val.root_word

/-- The temporal reverse keeps the exact complete original base word in reverse occurrence order. -/
theorem time_base_word (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin (left :: retained.original.spaces).length) :
    Cast.Path.ofCoordinate OwnerPath.Dyadic.last.parameter ::
        (OwnerPath.reversePath
          (Time.Links.whole (linked := Links.time (linked := shared.links) timeIndex spaceIndex))
          (reversed.time timeIndex spaceIndex).1.val.2).vertices =
      (Cast.Path.ofCoordinate OwnerPath.Dyadic.first.parameter ::
        (Time.Links.whole (linked := Links.time (linked := shared.links) timeIndex spaceIndex)).vertices).reverse :=
  OwnerPath.reversePath_vertices _ _

/-- The spatial reverse keeps its SAME complete composeLine base word in reverse occurrence order. -/
theorem space_base_word (timeIndex : Fin (left :: retained.original.times).length)
    (spaceIndex : Fin retained.original.spaces.length) :
    Cast.Path.ofCoordinate OwnerPath.Dyadic.last.parameter ::
        (OwnerPath.reversePath
          (Space.Links.whole (linked := Links.space (linked := shared.links) timeIndex spaceIndex))
          (reversed.space timeIndex spaceIndex).1.val.2).vertices =
      (Cast.Path.ofCoordinate OwnerPath.Dyadic.first.parameter ::
        (Space.Links.whole (linked := Links.space (linked := shared.links) timeIndex spaceIndex)).vertices).reverse :=
  OwnerPath.reversePath_vertices _ _

end Reversed

namespace SpaceReverse

variable {shared} {timeIndex : Fin (left :: retained.original.times).length}
    {spaceIndex : Fin retained.original.spaces.length} (trace : SpaceReverse shared timeIndex spaceIndex)

/-- The exact physical-fibre realization of the given reversed spatial trace, with its original path and indices. -/
@[expose] def FibreRealization : Type :=
  LinkPreparation.ReverseTrace.AffineRealization
    (cached := (Links.space (linked := shared.links) timeIndex spaceIndex).2.2)
    (incoming := Readings.spaceFirst (linked := shared.links) (required := shared.required)
      (demanded := shared.demanded) (targeted := shared.targeted)
      (observed := shared.observed) timeIndex spaceIndex)
    (outgoing := Readings.spaceLast (linked := shared.links) (required := shared.required)
      (demanded := shared.demanded) (targeted := shared.targeted)
      (observed := shared.observed) timeIndex spaceIndex)
    (firstLater := Readings.space_first_later (linked := shared.links) (required := shared.required)
      (demanded := shared.demanded) (targeted := shared.targeted)
      (observed := shared.observed) timeIndex spaceIndex)
    (lastLater := Readings.space_last_later (linked := shared.links) (required := shared.required)
      (demanded := shared.demanded) (targeted := shared.targeted)
      (observed := shared.observed) timeIndex spaceIndex)
    (forward := (shared.space timeIndex spaceIndex).val) trace
    (Paths.polynomial
      (parameter + (⟨((left :: retained.original.times)[timeIndex.val]'timeIndex.isLt).parameter, 0⟩ : Canonical) *
        increment))
    (segment.pointAt (spaceFirst retained.original spaceIndex).parameter)
    (segment.pointAt (spaceLast retained.original spaceIndex).parameter -
      segment.pointAt (spaceFirst retained.original spaceIndex).parameter)
    (Space.polynomial_eq retained.original timeIndex spaceIndex)

/-- Transport the SAME checked reverse spatial trace to its actual fixed fibre without observing or reversing it again.

The original composeLine equation supplies the exact affine polynomial
factory. Temporal radicand traces are not retyped through this operation.
-/
def spatialRealization : FibreRealization trace :=
  LinkPreparation.ReverseTrace.affineImage
    (cached := (Links.space (linked := shared.links) timeIndex spaceIndex).2.2)
    (incoming := Readings.spaceFirst (linked := shared.links) (required := shared.required)
      (demanded := shared.demanded) (targeted := shared.targeted)
      (observed := shared.observed) timeIndex spaceIndex)
    (outgoing := Readings.spaceLast (linked := shared.links) (required := shared.required)
      (demanded := shared.demanded) (targeted := shared.targeted)
      (observed := shared.observed) timeIndex spaceIndex)
    (firstLater := Readings.space_first_later (linked := shared.links) (required := shared.required)
      (demanded := shared.demanded) (targeted := shared.targeted)
      (observed := shared.observed) timeIndex spaceIndex)
    (lastLater := Readings.space_last_later (linked := shared.links) (required := shared.required)
      (demanded := shared.demanded) (targeted := shared.targeted)
      (observed := shared.observed) timeIndex spaceIndex)
    (forward := (shared.space timeIndex spaceIndex).val) trace
    (Paths.polynomial
      (parameter + (⟨((left :: retained.original.times)[timeIndex.val]'timeIndex.isLt).parameter, 0⟩ : Canonical) *
        increment))
    (segment.pointAt (spaceFirst retained.original spaceIndex).parameter)
    (segment.pointAt (spaceLast retained.original spaceIndex).parameter -
      segment.pointAt (spaceFirst retained.original spaceIndex).parameter)
    (Space.polynomial_eq retained.original timeIndex spaceIndex)

end SpaceReverse

end Shared

end Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.JointGrid.Vertices.Edges

end
