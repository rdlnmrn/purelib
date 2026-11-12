module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Traces
public import Purelib.Riemann.Paths.OwnerTracePath.Dyadic.Links
import Purelib.Data.List.DependentProduct
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Refinement

import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Vertices
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Edges
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.RootContinuation.FixedRootBoxBudget
import Purelib.Riemann.RootContinuation.FixedRootBoxPath
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Joint
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Spatial
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTracePath.Dyadic
import Purelib.Riemann.Paths.OwnerTracePath.Dyadic.Advance
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

/-! # Actual strip-edge link prefixes before common-corner readings

The original time/spatial polynomial and Range laws supply all inputs of
one shared link-prefix worker. The GIVEN419 advances, comparisons, source
Owners and original finite requests are retained. These operations select
and build links but perform no displayed OwnerReading acquisition.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.JointGrid.Vertices

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.FixedRootBoxPath (Inside PathData)
open Purelib.Riemann.Paths.OwnerTracePath

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
    (cached : Vertices range budget factory segment firstInside lastInside increment admitted firstPath lastPath grid)
    (ordered : left.parameter ≤ right.parameter)

namespace Time

variable (timeIndex : Fin cached.times.length) (spaceIndex : Fin (left :: cached.spaces).length)

/-- The actual retained advance and its genuine link prefix before shared endpoint readings. -/
@[expose] def Links (given : TimeEdge cached ordered timeIndex spaceIndex) :=
  (_polynomial : { value : CoefficientPolynomial // value = timePolynomial cached timeIndex spaceIndex }) ×
  OwnerPath.Dyadic.AdvanceLinks patch (cached.owner timeIndex.castSucc spaceIndex)
    (cached.owner timeIndex.succ spaceIndex) (cached.time_boxes timeIndex spaceIndex)
    (cached.time_small ordered timeIndex spaceIndex) given
    (first_eq cached timeIndex spaceIndex) (last_eq cached timeIndex spaceIndex)
    (Eq.mpr (congrArg (fun box : Box => box.Refines patch.base.seed.owner.track.initial.box)
      (cached.owner_box timeIndex.castSucc spaceIndex)) (Box.refines_refl _))
    (nonzero cached timeIndex spaceIndex) (timeScale cached timeIndex) (timeScale_nonnegative cached timeIndex)
    (variation cached timeIndex spaceIndex) (scale_small cached ordered timeIndex spaceIndex)

/-- Construct the temporal link prefix on the GIVEN advance before displayed readings. -/
def link (given : TimeEdge cached ordered timeIndex spaceIndex) : Links cached ordered timeIndex spaceIndex given :=
  let polynomial := timePolynomial cached timeIndex spaceIndex
  let result := OwnerPath.Dyadic.linkAdvance (polynomial := polynomial) patch
    (cached.owner timeIndex.castSucc spaceIndex)
    (cached.owner timeIndex.succ spaceIndex) (cached.time_boxes timeIndex spaceIndex)
    (cached.time_small ordered timeIndex spaceIndex) given
    (first_eq cached timeIndex spaceIndex) (last_eq cached timeIndex spaceIndex)
    (Eq.mpr (congrArg (fun box : Box => box.Refines patch.base.seed.owner.track.initial.box)
      (cached.owner_box timeIndex.castSucc spaceIndex)) (Box.refines_refl _))
    (nonzero cached timeIndex spaceIndex) (timeScale cached timeIndex) (timeScale_nonnegative cached timeIndex)
    (variation cached timeIndex spaceIndex) (scale_small cached ordered timeIndex spaceIndex)

  ⟨⟨polynomial, rfl⟩, result⟩

namespace Links

variable {cached ordered timeIndex spaceIndex}
    {given : TimeEdge cached ordered timeIndex spaceIndex} (linked : Links cached ordered timeIndex spaceIndex given)

/-- Read the SAME actual temporal whole path before any displayed endpoint or interior reading. -/
@[expose] def whole : OwnerPath (timePolynomial cached timeIndex spaceIndex)
    (Cast.Path.ofCoordinate OwnerPath.Dyadic.first.parameter)
    (OwnerPath.Dyadic.sourceOwner (source := cached.owner timeIndex.castSucc spaceIndex)
      (firstEq := first_eq cached timeIndex spaceIndex))
    (Cast.Path.ofCoordinate OwnerPath.Dyadic.last.parameter)
    (OwnerPath.Dyadic.targetOwner (target := cached.owner timeIndex.succ spaceIndex)
      (lastEq := last_eq cached timeIndex spaceIndex)) := OwnerPath.Dyadic.AdvanceLinks.whole (linked := linked.2)

/-- The SAME temporal path includes its genuine final stationary handoff. -/
theorem nonempty : linked.whole.vertices ≠ [] := OwnerPath.Dyadic.AdvanceLinks.nonempty (linked := linked.2)

end Links

end Time

variable (zeroInside : Inside 0) (oneInside : Inside 1)
    (firstFactory : firstPath =
      range.spatialPath budget factory segment firstInside lastInside increment admitted 0 zeroInside)
    (lastFactory : lastPath =
      range.spatialPath budget factory segment firstInside lastInside increment admitted 1 oneInside)

namespace Space

variable (timeIndex : Fin (left :: cached.times).length) (spaceIndex : Fin cached.spaces.length)

/-- The GIVEN spatial advance and its selected link prefix with the actual stationary target handoff. -/
@[expose] def Links
    (given : SpaceEdge cached ordered zeroInside oneInside firstFactory lastFactory timeIndex spaceIndex) :=
  (_polynomial : { value : CoefficientPolynomial // value = spacePolynomial cached timeIndex spaceIndex }) ×
  OwnerPath.Dyadic.AdvanceLinks patch (cached.owner timeIndex spaceIndex.castSucc)
    (cached.owner timeIndex spaceIndex.succ) (cached.space_boxes timeIndex spaceIndex)
    (cached.space_small ordered zeroInside oneInside firstFactory lastFactory timeIndex spaceIndex) given
    (first_eq cached timeIndex spaceIndex) (last_eq cached timeIndex spaceIndex)
    (Eq.mpr (congrArg (fun box : Box => box.Refines patch.base.seed.owner.track.initial.box)
      (cached.owner_box timeIndex spaceIndex.castSucc)) (Box.refines_refl _))
    (nonzero cached timeIndex spaceIndex) (spaceScale cached spaceIndex) (spaceScale_nonnegative cached spaceIndex)
    (variation cached zeroInside oneInside firstFactory lastFactory timeIndex spaceIndex)
    (scale_small cached ordered timeIndex spaceIndex)

/-- Construct the spatial link prefix on the GIVEN advance with its exact physical interval maps. -/
def link (given : SpaceEdge cached ordered zeroInside oneInside firstFactory lastFactory timeIndex spaceIndex) :
    Links cached ordered zeroInside oneInside firstFactory lastFactory timeIndex spaceIndex given :=
  let polynomial := spacePolynomial cached timeIndex spaceIndex
  let result := OwnerPath.Dyadic.linkAdvance (polynomial := polynomial) patch
    (cached.owner timeIndex spaceIndex.castSucc)
    (cached.owner timeIndex spaceIndex.succ) (cached.space_boxes timeIndex spaceIndex)
    (cached.space_small ordered zeroInside oneInside firstFactory lastFactory timeIndex spaceIndex) given
    (first_eq cached timeIndex spaceIndex) (last_eq cached timeIndex spaceIndex)
    (Eq.mpr (congrArg (fun box : Box => box.Refines patch.base.seed.owner.track.initial.box)
      (cached.owner_box timeIndex spaceIndex.castSucc)) (Box.refines_refl _))
    (nonzero cached timeIndex spaceIndex) (spaceScale cached spaceIndex) (spaceScale_nonnegative cached spaceIndex)
    (variation cached zeroInside oneInside firstFactory lastFactory timeIndex spaceIndex)
    (scale_small cached ordered timeIndex spaceIndex)

  ⟨⟨polynomial, rfl⟩, result⟩

namespace Links

variable {cached ordered zeroInside oneInside firstFactory lastFactory timeIndex spaceIndex}
    {given : SpaceEdge cached ordered zeroInside oneInside firstFactory lastFactory timeIndex spaceIndex}
    (linked : Links cached ordered zeroInside oneInside firstFactory lastFactory timeIndex spaceIndex given)

/-- Read the SAME actual spatial whole path before any displayed endpoint or interior reading. -/
@[expose] def whole : OwnerPath (spacePolynomial cached timeIndex spaceIndex)
    (Cast.Path.ofCoordinate OwnerPath.Dyadic.first.parameter)
    (OwnerPath.Dyadic.sourceOwner (source := cached.owner timeIndex spaceIndex.castSucc)
      (firstEq := first_eq cached timeIndex spaceIndex))
    (Cast.Path.ofCoordinate OwnerPath.Dyadic.last.parameter)
    (OwnerPath.Dyadic.targetOwner (target := cached.owner timeIndex spaceIndex.succ)
      (lastEq := last_eq cached timeIndex spaceIndex)) := OwnerPath.Dyadic.AdvanceLinks.whole (linked := linked.2)

/-- The SAME spatial path includes its genuine final stationary handoff, including stationary parent occurrences. -/
theorem nonempty : linked.whole.vertices ≠ [] := OwnerPath.Dyadic.AdvanceLinks.nonempty (linked := linked.2)

end Links

end Space

namespace Edges

variable {cached ordered zeroInside oneInside firstFactory lastFactory}
    (retained : Edges cached ordered zeroInside oneInside firstFactory lastFactory)

/-- One original temporal link preparation per SAME unique retained temporal edge occurrence. -/
@[expose] def TimeLinks := DependentProduct retained.original.times (fun timeIndex =>
  DependentProduct (left :: retained.original.spaces) (fun spaceIndex =>
    Time.Links retained.original ordered timeIndex spaceIndex (retained.time timeIndex spaceIndex)))

/-- One original spatial link preparation per SAME unique retained spatial edge occurrence. -/
@[expose] def SpaceLinks := DependentProduct (left :: retained.original.times) (fun timeIndex =>
  DependentProduct retained.original.spaces (fun spaceIndex =>
    Space.Links retained.original ordered zeroInside oneInside firstFactory lastFactory timeIndex spaceIndex
      (retained.space timeIndex spaceIndex)))

/-- Prepare each genuine temporal edge prefix once, without displayed native readings. -/
def timeLinks : TimeLinks retained :=
  DependentProduct.ofFn retained.original.times (fun timeIndex =>
    DependentProduct.ofFn (left :: retained.original.spaces) (fun spaceIndex =>
      Time.link retained.original ordered timeIndex spaceIndex (retained.time timeIndex spaceIndex)))

/-- Prepare each genuine spatial edge prefix once, without displayed native readings. -/
def spaceLinks : SpaceLinks retained :=
  DependentProduct.ofFn (left :: retained.original.times) (fun timeIndex =>
    DependentProduct.ofFn retained.original.spaces (fun spaceIndex =>
      Space.link retained.original ordered zeroInside oneInside firstFactory lastFactory timeIndex spaceIndex
        (retained.space timeIndex spaceIndex)))

/-- The SAME original419 cache and both unique actual link-prefix tables with their complete factories. -/
@[expose] def Links :=
  (_original : { value : Edges cached ordered zeroInside oneInside firstFactory lastFactory // value = retained }) ×
  (_times : { value : TimeLinks retained // value = timeLinks retained }) ×
    { spaces : SpaceLinks retained // spaces = spaceLinks retained }

/-- Bind both unique link-prefix tables before any shared-corner or interior native reading. -/
def links : Links retained :=
  let times := timeLinks retained
  let spaces := spaceLinks retained
  ⟨⟨retained, rfl⟩, ⟨times, rfl⟩, ⟨spaces, rfl⟩⟩

namespace Links

variable {retained} (linked : Links retained)

/-- Read the SAME retained original419 edge and vertex preparation. -/
@[expose] def original : Edges cached ordered zeroInside oneInside firstFactory lastFactory := linked.1.val

/-- The complete original preparation is the GIVEN value, without ownerAt, advance or geometry replay. -/
theorem original_eq : linked.original = retained := linked.1.property

/-- Read one SAME temporal link-prefix cache at its original two bounded occurrences. -/
@[expose] def time (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin (left :: retained.original.spaces).length) :
    Time.Links retained.original ordered timeIndex spaceIndex (retained.time timeIndex spaceIndex) :=
  DependentProduct.get (left :: retained.original.spaces)
    (DependentProduct.get retained.original.times linked.2.1.val timeIndex) spaceIndex

/-- Read one SAME spatial link-prefix cache at its original two bounded occurrences. -/
@[expose] def space (timeIndex : Fin (left :: retained.original.times).length)
    (spaceIndex : Fin retained.original.spaces.length) :
    Space.Links retained.original ordered zeroInside oneInside firstFactory lastFactory timeIndex spaceIndex
      (retained.space timeIndex spaceIndex) :=
  DependentProduct.get retained.original.spaces
    (DependentProduct.get (left :: retained.original.times) linked.2.2.val timeIndex) spaceIndex

end Links

end Edges

end Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.JointGrid.Vertices

end
