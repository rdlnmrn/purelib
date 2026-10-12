module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.NatCast
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Rational.Squares
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PolygonSewing
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Data.Int.Cast.Defs
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Data.Nat.Init
import Mathlib.Algebra.Ring.Defs
import Purelib.Topology.Surface.Sewing.SewingProjection
import Mathlib.Algebra.Group.Defs
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Data

open Purelib.Data.Gaussian.Norm.Basic

open Purelib.Data.Rat

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.Patch

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.PolygonSewing

open Purelib.Topology.Surface.Sewing.PrimitiveSewing

open Purelib.Topology.Surface.Sewing.PrimitiveSewing.CutPatch

open Purelib.Topology.Surface.Sewing.VertexSewing

@[expose] public section

/-!
# Facewise primitive errors through the retained cut assembly

Each face retains its original three local readings and the actual cut
triangle on which they are compared. A list of ancestor-seam corrections
explains each increment error. Finite Cauchy--Schwarz pays the trace length
times the sum of its squared charges, not an exponentially doubled budget.
-/

namespace Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces

open Purelib.Algebra
open Purelib.Data.List

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Topology.Surface.Sewing.PolygonSewing.PolygonStokes (BoundarySplit)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianNormSqSum)
open Purelib.Algebra.FiniteSum.Rational.Squares (coordinateSum)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing.EndpointGluing (PrimitiveSew)
open Purelib.Topology.Surface.Cut.Patch (CutPatch)

/-- Rational coordinates for finite sewing-error accounting. -/
abbrev Coordinate := Fraction.Rational

/-- Read one of a triangle's three ordered vertices by its bounded corner index. -/
def corner {count : Nat} (triangle : Stokes.OrientedTriangle count) (index : Fin 3) : Fin count :=
  if index.val = 0 then triangle.first else if index.val = 1 then triangle.second else triangle.third

/-- Mapping triangle vertices commutes with reading a corner. -/
theorem corner_map {first second : Nat} (map : Fin first → Fin second) (triangle : Stokes.OrientedTriangle first) (index
  : Fin 3) :
    corner (OrientedTriangle.map map triangle) index = map (corner triangle index)
      := by
  unfold corner
  split <;> first | rfl | (split <;> rfl)

set_option genInjectivity false in
/-- Original face readings with their actual inherited sewing discrepancies.

Each corner error is a retained finite sum of ancestor corrections, with a depth bound and charge bound giving its
squared-error allowance. -/
structure FaceTrace {faceCount count : Nat} (localValues : Fin faceCount → PrimitiveSewing.PrimitiveValues 3) (values :
  PrimitiveSewing.PrimitiveValues count) where
  /-- Original source face occurrence. -/ source : Fin faceCount
  /-- Actual cut triangle carrying the sewn readings. -/ triangle : Stokes.OrientedTriangle count
  /-- Cached discrepancies for the three affine corner readings. -/ errors : PrimitiveSewing.PrimitiveValues 3
  /-- Each discrepancy compares the sewn and original local increments from corner zero. -/ errors_eq : ∀ index, errors
    index = (values (corner triangle index) - values triangle.first) -
    (localValues source index - localValues source 0)
  /-- Retained finite ancestor-correction list for each corner. -/ terms : Data.Vector (List
    Gaussian.Basic.Canonical) 3
  /-- Each cached error is the Gaussian sum of its retained correction list. -/ sums_eq : ∀ index, errors index =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (terms index)
  /-- Uniform upper bound on the number of retained ancestor corrections. -/ depth : Nat
  /-- Every corner's correction-list length is at most the retained depth. -/ length_le : ∀ index, (terms index).length
    ≤ depth
  /-- Cached rational cast of the depth. -/ countValue : Coordinate
  /-- The cached count equals the exact natural depth cast. -/ countValue_eq : countValue = (depth :
    Coordinate)
  /-- Nonnegative upper bound for each corner's sum of squared correction norms. -/ charge :
    Coordinate
  /-- The retained ancestor charge is nonnegative. -/ charge_nonnegative : 0 ≤ charge
  /-- Each corner's retained correction terms have squared norms summing to at most the charge. -/ norms_le : ∀ index,
    Gaussian.Norm.Sum.Basic.gaussianNormSqSum (terms index) ≤ charge
  /-- Cached squared-error allowance for a corner increment. -/ allowance : Coordinate
  /-- The allowance is the retained depth cast multiplied by the retained charge. -/ allowance_eq : allowance =
    countValue * charge

constructive_injectivity FaceTrace

namespace FaceTrace

variable {faceCount firstCount secondCount : Nat} {localValues : Fin faceCount → PrimitiveSewing.PrimitiveValues 3}
  {first : PrimitiveSewing.PrimitiveValues firstCount} {second : PrimitiveSewing.PrimitiveValues secondCount}
  {firstEdge : Stokes.OrientedEdge firstCount} {secondEdge : Stokes.OrientedEdge secondCount}

/-- Sum of the squared discrepancies in the face's two affine increments. -/
def squaredErrors (trace : FaceTrace localValues first) : Fraction.Rational :=
  Data.Gaussian.Norm.Basic.normSq (trace.errors 1) + Data.Gaussian.Norm.Basic.normSq (trace.errors 2)

/-- Finite Cauchy--Schwarz bounds each cached corner error by its allowance. -/
theorem error_bound (trace : FaceTrace localValues first) (index : Fin 3) :
  Data.Gaussian.Norm.Basic.normSq
  (trace.errors index) ≤ trace.allowance := by
  rw [Gaussian.Norm.Basic.normSq_eq_canonical]
  rw [trace.sums_eq, trace.allowance_eq, trace.countValue_eq]
  exact (Gaussian.Norm.Sum.Basic.normSq_gaussianSum_le _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (trace.norms_le index)
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _))).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Fraction.Cast.Order.natCast_le_direct (trace.length_le index)) trace.charge_nonnegative))

/-- The actual sewn affine increment differs from its original local increment by the retained allowance. -/
theorem increment_error_bound (trace : FaceTrace localValues first) (index : Fin 3) :
    Data.Gaussian.Norm.Basic.normSq ((first (corner trace.triangle index) - first
      trace.triangle.first) -
      (localValues trace.source index - localValues trace.source 0)) ≤ trace.allowance := by
  rw [← trace.errors_eq]
  exact trace.error_bound index

/-- Start the original triangle's trace with zero errors and empty correction lists. -/
def leaf (localValues : Fin faceCount → PrimitiveSewing.PrimitiveValues 3) (source : Fin faceCount) :
    FaceTrace localValues (localValues source) where
  source := source
  triangle := ⟨0, 1, 2⟩
  errors := Data.Vector.Basic.vectorOfFn fun _ => 0
  errors_eq := by
    intro index
    have same : corner (⟨0, 1, 2⟩ : Stokes.OrientedTriangle 3) index = index := by
      apply Fin.ext
      unfold corner
      split
      · change 0 = index.val; omega
      · split
        · change 1 = index.val; omega
        · change 2 = index.val; omega
    rw [Data.Vector.Basic.vectorOfFn_apply, same]
    exact (Gaussian.Basic.sub_self _).symm
  terms := Data.Vector.Basic.vectorOfFn fun _ => []
  sums_eq := fun index => by rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]; rfl
  depth := 0
  length_le := fun index => by rw [Data.Vector.Basic.vectorOfFn_apply]; exact Nat.le_refl _
  countValue := 0
  countValue_eq := rfl
  charge := 0
  charge_nonnegative := le_rfl
  norms_le := fun index => by rw [Data.Vector.Basic.vectorOfFn_apply]; exact le_rfl
  allowance := 0
  allowance_eq := rfl

/-- Transport a face through the left side of a sewing without changing its cached discrepancies. -/
def mapLeft (trace : FaceTrace localValues first)
    (joined : EndpointGluing.PrimitiveSew first second firstEdge secondEdge) : FaceTrace localValues
      joined.values where
  source := trace.source
  triangle := OrientedTriangle.map EndpointGluing.left trace.triangle
  errors := trace.errors
  errors_eq := fun index => by
    rw [corner_map]
    dsimp only [OrientedTriangle.map]
    rw [joined.left_eq, joined.left_eq]
    exact trace.errors_eq index
  terms := trace.terms
  sums_eq := trace.sums_eq
  depth := trace.depth
  length_le := trace.length_le
  countValue := trace.countValue
  countValue_eq := trace.countValue_eq
  charge := trace.charge
  charge_nonnegative := trace.charge_nonnegative
  norms_le := trace.norms_le
  allowance := trace.allowance
  allowance_eq := trace.allowance_eq

/-- Extend a right-side face trace by the actual new sewing correction.

The correction is prepended to each corner's retained terms; depth increases by one and the new seam charge is added to
the inherited charge. -/
def mapRight (trace : FaceTrace localValues second)
    (joined : EndpointGluing.PrimitiveSew first second firstEdge secondEdge) : FaceTrace localValues
      joined.values :=
  let map := EndpointGluing.right firstEdge secondEdge
  let corrections := Data.Vector.Basic.vectorOfFn fun index : Fin 3 =>
    (joined.values (map (corner trace.triangle index)) - joined.values (map trace.triangle.first)) -
      (second (corner trace.triangle index) - second trace.triangle.first)
  let errors := Data.Vector.Basic.vectorOfFn fun index => corrections index + trace.errors index
  let terms := Data.Vector.Basic.vectorOfFn fun index => corrections index :: trace.terms index
  let countValue := trace.countValue + 1
  let charge := joined.charge + trace.charge
  { source := trace.source
    triangle := OrientedTriangle.map map trace.triangle
    errors := errors
    errors_eq := by
      intro index
      rw [Data.Vector.Basic.vectorOfFn_apply, trace.errors_eq, Data.Vector.Basic.vectorOfFn_apply,
        corner_map]
      dsimp only [OrientedTriangle.map]
      ring1
    terms := terms
    sums_eq := fun index => by
      rw [show errors index = corrections index + trace.errors index from Data.Vector.Basic.vectorOfFn_apply _ _,
        show terms index = corrections index :: trace.terms index from Data.Vector.Basic.vectorOfFn_apply _ _,
          Data.Gaussian.Norm.Sum.Basic.gaussianSum, trace.sums_eq]
    depth := trace.depth + 1
    length_le := fun index => by
      rw [Data.Vector.Basic.vectorOfFn_apply, List.length_cons]
      exact Nat.add_le_add_right (trace.length_le index) 1
    countValue := countValue
    countValue_eq := by change trace.countValue + 1 = _; rw [trace.countValue_eq, NatCast.add, Nat.cast_one]
    charge := charge
    charge_nonnegative := add_nonneg joined.charge_nonnegative trace.charge_nonnegative
    norms_le := fun index => by
      rw [Data.Vector.Basic.vectorOfFn_apply, Gaussian.Norm.Sum.Basic.gaussianNormSqSum]
      apply add_le_add ?_ (trace.norms_le index)
      rw [Data.Vector.Basic.vectorOfFn_apply]
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using
        joined.right_increment trace.triangle.first (corner trace.triangle index)
    allowance := countValue * charge
    allowance_eq := rfl }

end FaceTrace

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {localValues : Fin faceCount → PrimitiveSewing.PrimitiveValues 3}

set_option genInjectivity false in
/-- Ordered face traces and cached aggregate error data for one cut patch.

The triangle and source equalities retain the original occurrence order, while both aggregate sums are tied to those
same traces. -/
structure FaceBank {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge vertexCount)}
    (patch : Patch.CutPatch faces indices boundary) (localValues : Fin faceCount → PrimitiveSewing.PrimitiveValues 3)
      (values : PrimitiveSewing.PrimitiveValues patch.count) where
  /-- Face traces in the original cut-triangle occurrence order. -/ entries : List (FaceTrace
    localValues values)
  /-- The trace triangles are exactly the patch's retained triangle list. -/ triangles_eq : entries.map
    Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces.FaceTrace.triangle = patch.triangles
  /-- The trace sources are exactly the original face index list. -/ sources_eq : entries.map
    Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces.FaceTrace.source = indices
  /-- Cached sum of all retained face allowances. -/ totalAllowance : Coordinate
  /-- The cached aggregate equals the coordinate sum of the trace allowances. -/ totalAllowance_eq : totalAllowance =
    Squares.coordinateSum (entries.map Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces.FaceTrace.allowance)
  /-- Cached sum of the two affine squared errors from every face. -/ squaredErrors : Coordinate
  /-- The cached aggregate equals the coordinate sum of the trace squared errors. -/ squaredErrors_eq : squaredErrors =
    Squares.coordinateSum (entries.map SewnPrimitiveFaces.FaceTrace.squaredErrors)

constructive_injectivity FaceBank

namespace FaceBank

/-- Package checked ordered face traces and compute their aggregate allowance and squared errors. -/
def ofEntries {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge vertexCount)}
    {patch : Patch.CutPatch faces indices boundary} {values : PrimitiveSewing.PrimitiveValues patch.count}
    (entries : List (FaceTrace localValues values))
    (triangles : entries.map Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces.FaceTrace.triangle = patch.triangles)
    (sources : entries.map Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces.FaceTrace.source = indices) :
      FaceBank patch localValues values where
  entries := entries
  triangles_eq := triangles
  sources_eq := sources
  totalAllowance := Squares.coordinateSum (entries.map
    Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces.FaceTrace.allowance)
  totalAllowance_eq := rfl
  squaredErrors := Squares.coordinateSum (entries.map SewnPrimitiveFaces.FaceTrace.squaredErrors)
  squaredErrors_eq := rfl

/-- Left transport maps every retained triangle by the left vertex embedding.

The original face-trace transport keeps the same source and cached errors.
Mapping its triangle projection therefore agrees with mapping each original
triangle through the retained left sewing embedding. -/
private theorem left_triangles {firstCount secondCount : Nat} {first : PrimitiveSewing.PrimitiveValues firstCount}
  {second : PrimitiveSewing.PrimitiveValues secondCount}
    {firstEdge : Stokes.OrientedEdge firstCount} {secondEdge : Stokes.OrientedEdge secondCount}
    (entries : List (FaceTrace localValues first)) (joined : EndpointGluing.PrimitiveSew first second
      firstEdge secondEdge) :
    (entries.map (fun trace => trace.mapLeft joined)).map
      Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces.FaceTrace.triangle =
      (entries.map Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces.FaceTrace.triangle).map (OrientedTriangle.map
        EndpointGluing.left) := by
  rw [Map.map_map, Map.map_map]
  rfl

/-- Right transport maps every retained triangle by the seam's right vertex embedding.

The original right transport adds the retained seam correction to each error.
Its triangle projection still reads precisely the original triangle through the
same retained right sewing embedding. -/
private theorem right_triangles {firstCount secondCount : Nat} {first : PrimitiveSewing.PrimitiveValues firstCount}
  {second : PrimitiveSewing.PrimitiveValues secondCount}
    {firstEdge : Stokes.OrientedEdge firstCount} {secondEdge : Stokes.OrientedEdge secondCount}
    (entries : List (FaceTrace localValues second)) (joined : EndpointGluing.PrimitiveSew first
      second firstEdge secondEdge) :
    (entries.map (fun trace => trace.mapRight joined)).map
      Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces.FaceTrace.triangle =
      (entries.map Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces.FaceTrace.triangle).map (OrientedTriangle.map
        (EndpointGluing.right firstEdge secondEdge)) := by
  rw [Map.map_map, Map.map_map]
  rfl

/-- Left transport preserves the ordered list of original source faces.

The left transport retains each original source index unchanged. Structural
map composition reads those same indices in the exact original trace order. -/
private theorem left_sources {firstCount secondCount : Nat} {first : PrimitiveSewing.PrimitiveValues firstCount} {second
  : PrimitiveSewing.PrimitiveValues secondCount}
    {firstEdge : Stokes.OrientedEdge firstCount} {secondEdge : Stokes.OrientedEdge secondCount}
    (entries : List (FaceTrace localValues first)) (joined : EndpointGluing.PrimitiveSew first second
      firstEdge secondEdge) :
    (entries.map (fun trace => trace.mapLeft joined)).map
      Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces.FaceTrace.source = entries.map FaceTrace.source := by
  rw [Map.map_map]
  rfl

/-- Right transport preserves the ordered list of original source faces.

The new seam correction changes the retained errors and their charges, while
the original right trace source remains unchanged. Mapping source projections
therefore preserves the same ordered source occurrences. -/
private theorem right_sources {firstCount secondCount : Nat} {first : PrimitiveSewing.PrimitiveValues firstCount}
  {second : PrimitiveSewing.PrimitiveValues secondCount}
    {firstEdge : Stokes.OrientedEdge firstCount} {secondEdge : Stokes.OrientedEdge secondCount}
    (entries : List (FaceTrace localValues second)) (joined : EndpointGluing.PrimitiveSew first
      second firstEdge secondEdge) :
    (entries.map (fun trace => trace.mapRight joined)).map
      Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces.FaceTrace.source = entries.map FaceTrace.source := by
  rw [Map.map_map]
  rfl

/-- Join two existing face banks along the actual primitive sewing.

Left traces retain their errors; right traces acquire the new correction before the ordered lists and aggregate caches
are combined. -/
def join {firstIndices secondIndices : List (Fin faceCount)}
    {firstBoundary secondBoundary : List (Stokes.OrientedEdge vertexCount)}
    {first : Patch.CutPatch faces firstIndices firstBoundary} {second : Patch.CutPatch faces secondIndices
      secondBoundary}
    {firstBase : PolygonStokes.BoundarySplit firstBoundary} {secondBase : PolygonStokes.BoundarySplit secondBoundary}
    {opposite : secondBase.edge = firstBase.edge.reverse} {seam : CutPatch.Seam first second firstBase secondBase}
    {leftValues : PrimitiveSewing.PrimitiveValues first.count} {rightValues : PrimitiveSewing.PrimitiveValues
      second.count}
    (leftBank : FaceBank first localValues leftValues) (rightBank : FaceBank
      second localValues rightValues)
    (joined : EndpointGluing.PrimitiveSew leftValues rightValues seam.firstLift.split.edge seam.secondLift.split.edge) :
    FaceBank (CutPatch.sew first second firstBase secondBase opposite seam) localValues joined.values
      :=
  let entries := leftBank.entries.map (fun trace => trace.mapLeft joined) ++ rightBank.entries.map (fun trace =>
    trace.mapRight joined)
  ofEntries entries
    (show entries.map Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces.FaceTrace.triangle =
      first.triangles.map (OrientedTriangle.map EndpointGluing.left) ++
        second.triangles.map (OrientedTriangle.map (EndpointGluing.right seam.firstLift.split.edge
          seam.secondLift.split.edge)) from by
      dsimp only [entries]
      rw [Map.map_append, left_triangles, right_triangles, leftBank.triangles_eq,
        rightBank.triangles_eq])
    (show entries.map Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces.FaceTrace.source = firstIndices ++
      secondIndices from by
      dsimp only [entries]
      rw [Map.map_append, left_sources, right_sources, leftBank.sources_eq, rightBank.sources_eq])

/-- Every original face occurrence is covered in the actual cut-triangle order.

The retained reading tree determines the original leaf traces and each actual
sewing. All sums and face errors are materialized once from those readings,
preserving the existing primitive and seam owners. -/
def build : {indices : List (Fin faceCount)} → {boundary : List (Stokes.OrientedEdge vertexCount)} →
    {patch : Patch.CutPatch faces indices boundary} → {assembly : CutPatch.Assembly faces patch} →
    {values : PrimitiveSewing.PrimitiveValues patch.count} → Assembly.Readings localValues assembly values →
      FaceBank patch localValues values
  | _, _, _, _, _, .triangle source =>
      ofEntries [SewnPrimitiveFaces.FaceTrace.leaf localValues source] rfl rfl
  | _, _, _, _, _, .sew left right joined =>
      join (build left)
        (build right) joined

/-- The two affine errors of all retained faces sum to at most twice their total allowance. -/
private theorem sum_errors_le {count : Nat} {values : PrimitiveSewing.PrimitiveValues count} : (entries : List
  (FaceTrace localValues values)) →
    Squares.coordinateSum (entries.map SewnPrimitiveFaces.FaceTrace.squaredErrors) ≤
      2 * Squares.coordinateSum (entries.map Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces.FaceTrace.allowance)
  | [] => by change (0 : Coordinate) ≤ 2 * 0; rw [Fraction.Field.mul_zero_direct]
  | trace :: entries =>
      (add_le_add (add_le_add (trace.error_bound 1) (trace.error_bound 2))
        (sum_errors_le entries)).trans_eq (by
        change (trace.allowance + trace.allowance) + 2 * Squares.coordinateSum (entries.map
          Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces.FaceTrace.allowance) =
          2 * (trace.allowance + Squares.coordinateSum (entries.map
            Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces.FaceTrace.allowance))
        ring1)

/-- This accounts for both affine increments of every retained face. The finite face count is included in the cached
sum, even on a growing mesh. -/
theorem aggregate_error_bound {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge vertexCount)}
    {patch : Patch.CutPatch faces indices boundary} {values : PrimitiveSewing.PrimitiveValues patch.count}
    (bank : FaceBank patch localValues values) : bank.squaredErrors ≤ 2 * bank.totalAllowance := by
  rw [bank.squaredErrors_eq, bank.totalAllowance_eq]
  exact sum_errors_le bank.entries

end FaceBank
end Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
