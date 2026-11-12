module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered
public import Purelib.Curves.Legendre.Periods.Jets.Source.Parameter
public import Purelib.Data.Rat.List.Minimum
public import Purelib.Data.List.OfFn.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-! # One retained parameter range for the actual finite covered-parent spine

Every original covered occurrence constructs its Range once. The original
list product stores those complete caches with their factory identities;
a retained table of their bounds feeds one positive finite minimum. All
source stages then use that same cache, parent list and coefficient count.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {count : Nat} {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}

set_option genInjectivity false in
/-- Actual range caches, their bound table and the positive minimum on the identical covered-parent family.

Every range retains equality to the complete original prepared-patch
factory. The finite table reads those cached entries; the final scalar
stores the existing original positiveMinimum computation and positivity.
No source stage or point-query callback is part of this construction.
-/
structure ParameterRange
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {count : Nat} {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count parents) : Type _ where
  /-- The same ordered original range caches and their complete prepared-patch factory identities. -/
  entries : DependentProduct parents (fun index =>
    { range : Variation.Point.Range ((covered.entry index).val.neighborhood count) //
      range = Variation.Point.Range.ofPreparedPatch (frame := frame) (covered.entry index).val count })
  /-- The same one cached bound list reads only the retained original range entries. -/
  boundsCache : { values : List Rational // values = List.ofFn (fun index : Fin parents.length =>
    (DependentProduct.get parents entries index).val.bound) }
  /-- The same computed positive minimum retains its exact original list and positivity certificate. -/
  boundCache : { bound : Rational // bound = Rat.List.Minimum.positiveMinimum boundsCache.val ∧ 0 < bound }

constructive_injectivity ParameterRange

namespace ParameterRange

variable {covered : CoveredParents count parents}

/-- Construct and cache every actual range once, then cache its finite bound table and original positive minimum. -/
def build (covered : CoveredParents count parents) : ParameterRange covered := by
  let entries := DependentProduct.ofFn parents (fun index =>
    let patch := (covered.entry index).val
    let range := Variation.Point.Range.ofPreparedPatch (frame := frame) patch count
    (⟨range, rfl⟩ : { range : Variation.Point.Range (patch.neighborhood count) //
      range = Variation.Point.Range.ofPreparedPatch (frame := frame) patch count }))
  let bounds := List.ofFn (fun index : Fin parents.length =>
    (DependentProduct.get parents entries index).val.bound)
  let bound := Rat.List.Minimum.positiveMinimum bounds
  have positive : 0 < bound := Rat.List.Minimum.positiveMinimum_pos bounds (by
    intro value member
    rcases Data.List.OfFn.Basic.mem_ofFn.mp member with ⟨index, equal⟩
    rewrite [← equal]
    exact (DependentProduct.get parents entries index).val.bound_positive)
  exact ⟨entries, ⟨bounds, rfl⟩, ⟨bound, rfl, positive⟩⟩

/-- Read the same retained range at its original bounded parent occurrence without running its factory again. -/
@[expose] def entry (ranges : ParameterRange covered) (index : Fin parents.length) :
    Variation.Point.Range ((covered.entry index).val.neighborhood count) :=
  (DependentProduct.get parents ranges.entries index).val

/-- The complete retained entry is the original prepared-patch range factory at that exact occurrence. -/
theorem entry_eq (ranges : ParameterRange covered) (index : Fin parents.length) :
    ranges.entry index = Variation.Point.Range.ofPreparedPatch (frame := frame) (covered.entry index).val count :=
  (DependentProduct.get parents ranges.entries index).property

/-- Read the one cached table of bounds on the original occurrence spine. -/
@[expose] def bounds (ranges : ParameterRange covered) : List Rational := ranges.boundsCache.val

/-- The retained bound table reads only the already stored ranges at their original bounded indices. -/
theorem bounds_eq (ranges : ParameterRange covered) :
    ranges.bounds = List.ofFn (fun index : Fin parents.length => (ranges.entry index).bound) :=
  ranges.boundsCache.property

/-- Read the single cached common parameter bound, independent of all source targets and programme stages. -/
@[expose] def bound (ranges : ParameterRange covered) : Rational := ranges.boundCache.val

/-- The common bound is the existing original positiveMinimum of the identical retained bound table. -/
theorem bound_eq (ranges : ParameterRange covered) :
    ranges.bound = Rat.List.Minimum.positiveMinimum ranges.bounds := ranges.boundCache.property.1

/-- Every original covered-parent family has a strictly positive computed common parameter range. -/
theorem bound_positive (ranges : ParameterRange covered) : 0 < ranges.bound := ranges.boundCache.property.2

/-- The retained positive minimum pays the actual original range of every bounded parent occurrence. -/
theorem bound_le_entry (ranges : ParameterRange covered) (index : Fin parents.length) :
    ranges.bound ≤ (ranges.entry index).bound := by
  rewrite [ranges.bound_eq, ranges.bounds_eq]
  exact Rat.List.Minimum.positiveMinimum_le_of_mem
    (Data.List.OfFn.Basic.mem_ofFn.mpr ⟨index, rfl⟩)

variable {floor : Nat} {baseStart baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}

/-- Continue an actual retained query at any source stage using the same precomputed whole-cover range.

The query is only transported to its exact original stored-model index.
Its six-observation bundle executes once and retains the identical acquired
Point used by the resulting Step. No range, source or parent preparation
is executed in this operation.
-/
def queryStep (ranges : ParameterRange covered) (prepared : PreparedParents covered floor targets)
    (index : Fin parents.length) (input : Rational) (lower : 0 ≤ input) (upper : input ≤ 1)
    (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ ranges.bound) :
    let retained := prepared.entry index
    (observed : CellModels.Observations frame (PreparedParent.liftedCell (parents[index.val]'index.isLt))
      retained.preparation.models retained.modelQuery.requests input) ×
      Variation.Point.Step observed.retained.sample increment :=
  let retained := prepared.entry index
  retained.modelQuery.advance frame (ranges.entry index) input lower upper increment
    (admitted.trans (ranges.bound_le_entry index))

/-- The whole-cover query step preserves the complete actual original query answer as its first cached component. -/
theorem queryStep_observation (ranges : ParameterRange covered) (prepared : PreparedParents covered floor targets)
    (index : Fin parents.length) (input : Rational) (lower : 0 ≤ input) (upper : input ≤ 1)
    (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ ranges.bound) :
    (ranges.queryStep prepared index input lower upper increment admitted).1 =
      (prepared.entry index).modelQuery.observe frame input lower upper := by
  unfold queryStep
  exact Cell.Query.advance_observation (prepared.entry index).modelQuery frame (ranges.entry index)
    input lower upper increment (admitted.trans (ranges.bound_le_entry index))

/-- The actual stored source producer's first original endpoint admits the identical whole-cover parameter range.

The supplied equality is the complete existing source-factory identity.
Only its erased entry readback supplies the already stored endpoint's
acquisition identity; the preparation and endpoint query are not replayed.
-/
def firstStep (ranges : ParameterRange covered) (prepared : PreparedParents covered floor targets)
    (fromFactory : prepared = prepareCovered covered floor targets) (index : Fin parents.length)
    (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ ranges.bound) :
    Variation.Point.Step (prepared.entry index).firstSample increment :=
  let factory := (congrArg (fun retained : PreparedParents covered floor targets => retained.entry index)
    fromFactory).trans (prepareCovered_entry covered floor targets index)
  PreparedParent.firstStep (prepared.entry index) factory (ranges.entry index) increment
    (admitted.trans (ranges.bound_le_entry index))

/-- Continue the retained finishing endpoint with the same whole-cover range and exact factory identity. -/
def lastStep (ranges : ParameterRange covered) (prepared : PreparedParents covered floor targets)
    (fromFactory : prepared = prepareCovered covered floor targets) (index : Fin parents.length)
    (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ ranges.bound) :
    Variation.Point.Step (prepared.entry index).lastSample increment :=
  let factory := (congrArg (fun retained : PreparedParents covered floor targets => retained.entry index)
    fromFactory).trans (prepareCovered_entry covered floor targets index)
  PreparedParent.lastStep (prepared.entry index) factory (ranges.entry index) increment
    (admitted.trans (ranges.bound_le_entry index))

end ParameterRange

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

end
