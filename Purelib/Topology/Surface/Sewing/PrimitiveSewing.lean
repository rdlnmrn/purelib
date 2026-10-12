module
import Purelib.Data.Nat.Subtraction
import Purelib.Data.List.Append
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PolygonSewing
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Data.Int.Cast.Defs
import Purelib.Topology.Surface.Sewing.SewingProjection
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data

open Purelib.Data.Gaussian.Norm.Basic

open Purelib.Data.Rat

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.Patch

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.PolygonSewing

open Purelib.Topology.Surface.Sewing.VertexSewing

@[expose] public section

/-!
# Primitive readings on the actual sewn cut vertices

Each join translates the right primitive to agree at the first seam endpoint.
The second endpoint uses the left reading and retains its exact mismatch.
That mismatch, not an assumed exact gluing, bounds the change in every right
edge increment. The assembly traverses cached seams and never replays a
boundary lookup. Local polynomial accuracy remains a separate obligation.
-/

namespace Purelib.Topology.Surface.Sewing.PrimitiveSewing

open Purelib.Data.List

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Topology.Surface.Sewing.PolygonSewing.PolygonStokes (BoundarySplit)
open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open Purelib.Topology.Surface.Cut.Patch.CutPatch (Assembly Seam)
open Purelib.Topology.Surface.Sewing.SewingTree (SewnPatch)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)

/-- Gaussian primitive readings indexed by the original finite cut-vertex bank. -/
abbrev PrimitiveValues (count : Nat) := Data.Vector Gaussian.Basic.Canonical count

namespace EndpointGluing

open Purelib.Topology.Surface.Sewing.VertexSewing.EndpointGluing (left right right_start right_finish)

variable {firstCount secondCount : Nat}

/-- Cache the original left primitive and the translated right primitive in their combined vertex bank. -/
def concatenate (first : PrimitiveSewing.PrimitiveValues firstCount) (second : PrimitiveSewing.PrimitiveValues
  secondCount) (shift : Gaussian.Basic.Canonical) :
    PrimitiveSewing.PrimitiveValues (firstCount + secondCount) :=
  Data.Vector.Basic.vectorOfFn fun index => if inside : index.val < firstCount then first ⟨index.val, inside⟩
    else second ⟨index.val - firstCount, by omega⟩ + shift

open Purelib.Topology.Surface.Sewing.VertexSewing.EndpointGluing in
/-- The combined primitive preserves every original left-bank value. -/
theorem concatenate_left (first : PrimitiveSewing.PrimitiveValues firstCount) (second : PrimitiveSewing.PrimitiveValues
  secondCount)
    (shift : Gaussian.Basic.Canonical) (index : Fin firstCount) : EndpointGluing.concatenate first second shift (left
      index) = first index := by
  rw [EndpointGluing.concatenate, Data.Vector.Basic.vectorOfFn_apply]
  exact dif_pos index.isLt

open Purelib.Topology.Surface.Sewing.VertexSewing.EndpointGluing in
set_option genInjectivity false in
/-- Retained primitive gluing across one original selected seam.

The right primitive is translated at the first endpoint; the second endpoint keeps its exact defect and
squared-magnitude charge. -/
structure PrimitiveSew (first : PrimitiveSewing.PrimitiveValues firstCount) (second : PrimitiveSewing.PrimitiveValues
  secondCount)
    (firstEdge : Stokes.OrientedEdge firstCount) (secondEdge : Stokes.OrientedEdge secondCount) where
  /-- Cached translation aligning the first original seam endpoint. -/ shift : Gaussian.Basic.Canonical
  /-- The shift is the left finish value minus the original right start value. -/ shift_eq : shift = first
    firstEdge.finish - second secondEdge.start
  /-- Cached discrepancy at the second original seam endpoint after translation. -/ defect : Gaussian.Basic.Canonical
  /-- The defect is the left start value minus the translated original right finish value. -/ defect_eq : defect = first
    firstEdge.start - (second secondEdge.finish + shift)
  /-- Cached squared magnitude of the retained endpoint defect. -/ charge : Fraction.Rational
  /-- The charge is exactly the norm square of the original retained defect. -/ charge_eq : charge =
    Data.Gaussian.Norm.Basic.normSq
    defect
  /-- Cached primitive on the original combined cut-vertex bank. -/ values : PrimitiveSewing.PrimitiveValues (firstCount
    + secondCount)
  /-- Every original left reading is preserved under the retained left embedding. -/ left_eq : ∀ index, values (left
    index) = first index
  /-- Original right readings gain the common translation and exactly the retained finish-endpoint correction. -/
    right_eq : ∀ index, values (right firstEdge secondEdge index) = second index + shift +
    if index = secondEdge.finish then defect else 0

constructive_injectivity PrimitiveSew

namespace PrimitiveSew

variable {first : Purelib.Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues firstCount} {second :
  Purelib.Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues secondCount}
  {firstEdge : Stokes.OrientedEdge firstCount} {secondEdge : Stokes.OrientedEdge secondCount}

open Purelib.Topology.Surface.Sewing.VertexSewing.EndpointGluing in
/-- Cache the seam translation, retained endpoint defect, charge and combined primitive values.

The first original seam endpoint determines the translation. The distinct second
endpoint retains the exact mismatch, while all other bounded right-bank positions
keep the original translated readings. -/
def build (first : PrimitiveSewing.PrimitiveValues firstCount) (second : PrimitiveSewing.PrimitiveValues secondCount)
    (firstEdge : Stokes.OrientedEdge firstCount) (secondEdge : Stokes.OrientedEdge secondCount)
    (distinct : secondEdge.start ≠ secondEdge.finish) : EndpointGluing.PrimitiveSew first second firstEdge secondEdge :=
  let shift := first firstEdge.finish - second secondEdge.start
  let defect := first firstEdge.start - (second secondEdge.finish + shift)
  { shift := shift, shift_eq := rfl, defect := defect, defect_eq := rfl
    charge := Data.Gaussian.Norm.Basic.normSq defect, charge_eq := rfl
    values := EndpointGluing.concatenate first second shift
    left_eq := EndpointGluing.concatenate_left first second shift
    right_eq := by
      intro index
      by_cases atStart : index = secondEdge.start
      · subst index
        rw [EndpointGluing.right_start, EndpointGluing.concatenate_left, if_neg distinct]
        dsimp only [shift]
        ring1
      · by_cases atFinish : index = secondEdge.finish
        · subst index
          rw [EndpointGluing.right_finish firstEdge secondEdge distinct, EndpointGluing.concatenate_left, if_pos rfl]
          dsimp only [defect]
          ring1
        · rw [right, if_neg atStart, if_neg atFinish, EndpointGluing.concatenate, Data.Vector.Basic.vectorOfFn_apply]
          rw [dif_neg (show ¬ firstCount + index.val < firstCount by omega),
            if_neg atFinish, Gaussian.Basic.add_zero]
          apply congrArg (fun position : Fin secondCount => second position + shift)
          apply Fin.ext
          exact Data.Nat.Subtraction.add_sub_cancel_left firstCount index.val }

/-- The retained squared endpoint-defect charge is nonnegative. -/
theorem charge_nonnegative (sample : EndpointGluing.PrimitiveSew first second firstEdge secondEdge) : 0 ≤ sample.charge
  := by
  rw [sample.charge_eq]
  exact Gaussian.Norm.Basic.normSq_nonneg _

/-- Only the sum of the oppositely oriented seam increments is paid. An arbitrary constant translation of either local
primitive is harmless. -/
theorem defect_eq_increments (sample : EndpointGluing.PrimitiveSew first second firstEdge secondEdge) :
    sample.defect = -((first firstEdge.finish - first firstEdge.start) +
      (second secondEdge.finish - second secondEdge.start)) := by
  rw [sample.defect_eq, sample.shift_eq]
  ring1

/-- Existing errors in the two input patches are paid before the local model mismatch. None of these three allowances is
silently discarded. -/
theorem charge_le (sample : EndpointGluing.PrimitiveSew first second firstEdge secondEdge)
    (leftModel rightModel : Gaussian.Basic.Canonical) (leftError rightError mismatch : Fraction.Rational)
    (leftBound : Data.Gaussian.Norm.Basic.normSq ((first firstEdge.finish - first firstEdge.start) - leftModel) ≤
      leftError)
    (rightBound : Data.Gaussian.Norm.Basic.normSq ((second secondEdge.finish - second secondEdge.start) - rightModel) ≤
      rightError)
    (matched : Data.Gaussian.Norm.Basic.normSq (leftModel + rightModel) ≤ mismatch) :
    sample.charge ≤ 4 * (leftError + rightError) + 2 * mismatch := by
  rw [sample.charge_eq, sample.defect_eq_increments, Gaussian.Norm.Basic.normSq_neg]
  let leftGap := (first firstEdge.finish - first firstEdge.start) - leftModel
  let rightGap := (second secondEdge.finish - second secondEdge.start) - rightModel
  have gaps : Data.Gaussian.Norm.Basic.normSq (leftGap + rightGap) ≤ 2 * (leftError + rightError) :=
    (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add leftBound rightBound) (by decide))
  have equal : (first firstEdge.finish - first firstEdge.start) + (second secondEdge.finish - second secondEdge.start) =
      (leftGap + rightGap) + (leftModel + rightModel) := by dsimp only [leftGap, rightGap]; ring1
  rw [equal]
  exact (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add gaps matched) (by decide)).trans_eq (by
      ring1))

open Purelib.Topology.Surface.Sewing.VertexSewing.EndpointGluing
/-- Every translated original right-bank value differs by at most the retained endpoint-defect charge.

The selected finish endpoint retains precisely the cached defect. Every other
original right-bank index has zero residual after removing the same translation,
so the retained norm-square charge bounds both cases. -/
theorem right_discrepancy (sample : EndpointGluing.PrimitiveSew first second firstEdge secondEdge) (index : Fin
  secondCount) :
    Data.Gaussian.Norm.Basic.normSq (sample.values (right firstEdge secondEdge index) - (second index + sample.shift))
      ≤ sample.charge
      := by
  rw [sample.right_eq, sample.charge_eq]
  by_cases matched : index = secondEdge.finish
  · have residual : second index + sample.shift + sample.defect - (second index + sample.shift) = sample.defect := by
      ring1
    rw [if_pos matched, residual]
  · rw [if_neg matched, Gaussian.Basic.add_zero, Gaussian.Basic.sub_self, Gaussian.Norm.Basic.normSq_zero]
    exact Gaussian.Norm.Basic.normSq_nonneg _

/-- The two endpoint corrections are the same cached defect, so their difference costs at most one charge, including
reversed or degenerate edges. -/
theorem right_increment (sample : EndpointGluing.PrimitiveSew first second firstEdge secondEdge) (start finish : Fin
  secondCount) :
    Data.Gaussian.Norm.Basic.normSq ((sample.values (right firstEdge secondEdge finish) - sample.values (right
      firstEdge secondEdge
      start)) -
      (second finish - second start)) ≤ sample.charge := by
  rw [sample.right_eq, sample.right_eq, sample.charge_eq]
  by_cases firstAt : start = secondEdge.finish <;> by_cases lastAt : finish = secondEdge.finish
  · rw [if_pos firstAt, if_pos lastAt]
    have equal : (second finish + sample.shift + sample.defect - (second start + sample.shift + sample.defect)) -
        (second finish - second start) = 0 := by ring1
    rw [equal, Gaussian.Norm.Basic.normSq_zero]; exact Gaussian.Norm.Basic.normSq_nonneg _
  · rw [if_pos firstAt, if_neg lastAt]
    have equal : (second finish + sample.shift + 0 - (second start + sample.shift + sample.defect)) -
        (second finish - second start) = -sample.defect := by ring1
    rw [equal, Gaussian.Norm.Basic.normSq_neg]
  · rw [if_neg firstAt, if_pos lastAt]
    have equal : (second finish + sample.shift + sample.defect - (second start + sample.shift + 0)) -
        (second finish - second start) = sample.defect := by ring1
    rw [equal]
  · rw [if_neg firstAt, if_neg lastAt]
    have equal : (second finish + sample.shift + 0 - (second start + sample.shift + 0)) -
        (second finish - second start) = 0 := by ring1
    rw [equal, Gaussian.Norm.Basic.normSq_zero]; exact Gaussian.Norm.Basic.normSq_nonneg _

end PrimitiveSew
end EndpointGluing

namespace CutPatch.Assembly

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}

open Purelib.Topology.Surface.Sewing.VertexSewing.EndpointGluing in
set_option genInjectivity false in
/-- Local primitive readings and the retained seam data of an assembly.

Each triangle keeps its supplied reading. Each original sew node retains both
input certificates together with the exact translation, endpoint mismatch and
norm-square charge of its selected seam. -/
inductive Readings (localValues : Fin faceCount → PrimitiveSewing.PrimitiveValues 3) :
    {indices : List (Fin faceCount)} → {boundary : List (Stokes.OrientedEdge vertexCount)} →
    {patch : Patch.CutPatch faces indices boundary} → CutPatch.Assembly faces patch → PrimitiveSewing.PrimitiveValues
      patch.count → Type where
  /-- Retain the supplied primitive of one original triangle assembly. -/ | triangle (index : Fin faceCount) :
    Purelib.Topology.Surface.Sewing.PrimitiveSewing.CutPatch.Assembly.Readings localValues (.triangle index)
    (localValues index)
  /-- Combine the two original reading certificates using the retained seam primitive and its defect. -/ | sew
    {firstIndices secondIndices : List (Fin faceCount)}
      {firstBoundary secondBoundary : List (Stokes.OrientedEdge vertexCount)}
      {first : Patch.CutPatch faces firstIndices firstBoundary} {second : Patch.CutPatch faces secondIndices
        secondBoundary}
      {leftAssembly : CutPatch.Assembly faces first} {rightAssembly : CutPatch.Assembly faces second}
      {firstBase : PolygonStokes.BoundarySplit firstBoundary} {secondBase : PolygonStokes.BoundarySplit secondBoundary}
      {opposite : secondBase.edge = firstBase.edge.reverse} {seam : CutPatch.Seam first second firstBase secondBase}
      {leftValues : PrimitiveSewing.PrimitiveValues first.count} {rightValues : PrimitiveSewing.PrimitiveValues
        second.count}
      (left : Purelib.Topology.Surface.Sewing.PrimitiveSewing.CutPatch.Assembly.Readings localValues leftAssembly
        leftValues) (right : Purelib.Topology.Surface.Sewing.PrimitiveSewing.CutPatch.Assembly.Readings localValues
        rightAssembly rightValues)
      (joined : PrimitiveSewing.EndpointGluing.PrimitiveSew leftValues rightValues seam.firstLift.split.edge
        seam.secondLift.split.edge) :
      Purelib.Topology.Surface.Sewing.PrimitiveSewing.CutPatch.Assembly.Readings localValues (.sew leftAssembly
        rightAssembly firstBase secondBase opposite seam) joined.values

constructive_injectivity Readings

namespace Readings

open Purelib.Topology.Surface.Sewing.VertexSewing.EndpointGluing
/-- Read every original seam charge from the retained assembly reading tree. -/
def charges {localValues : Fin faceCount → PrimitiveSewing.PrimitiveValues 3} :
    {indices : List (Fin faceCount)} → {boundary : List (Stokes.OrientedEdge vertexCount)} →
    {patch : Patch.CutPatch faces indices boundary} → {assembly : CutPatch.Assembly faces patch} →
    {values : PrimitiveSewing.PrimitiveValues patch.count} → Assembly.Readings localValues assembly values → List
      Fraction.Rational
  | _, _, _, _, _, .triangle _ => []
  | _, _, _, _, _, .sew left right joined => joined.charge :: (left.charges ++ right.charges)

/-- The retained seam-charge count is one less than the original face-occurrence count.

Each original sew node retains one charge before the two unchanged charge
tails. Their displayed lengths add to the original two face-occurrence counts,
including the leaf assembly with no join charge. -/
theorem charges_length {localValues : Fin faceCount → PrimitiveSewing.PrimitiveValues 3}
    {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge vertexCount)}
    {patch : Patch.CutPatch faces indices boundary} {assembly : CutPatch.Assembly faces patch}
    {values : PrimitiveSewing.PrimitiveValues patch.count} (readings : Assembly.Readings localValues assembly values) :
    readings.charges.length + 1 = indices.length := by
  induction readings with
  | triangle => rfl
  | sew left right joined ihLeft ihRight =>
      simp only [Readings.charges, List.length_cons, Append.length_append]
      omega

end Readings

set_option genInjectivity false in
/-- Cached primitive values and all original seam charges for one retained cut assembly.

The assembly-indexed reading certificate owns these exact values. Its ordered
charge list is cached with an equality to that same retained certificate, so
readback uses the original seam tree. -/
structure Sample {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge vertexCount)}
    {patch : Patch.CutPatch faces indices boundary} (assembly : CutPatch.Assembly faces patch) (localValues : Fin
      faceCount → PrimitiveSewing.PrimitiveValues 3) where
  /-- Cached primitive on the original assembly's cut vertices. -/ values : PrimitiveSewing.PrimitiveValues patch.count
  /-- Retained construction certificate connecting the exact primitive values to the original assembly. -/ readings :
    Assembly.Readings localValues assembly values
  /-- Cached complete list of original seam-defect charges. -/ charges : List Fraction.Rational
  /-- The charge cache reads exactly the retained assembly certificate. -/ charges_eq : charges = readings.charges

constructive_injectivity Sample

open Purelib.Topology.Surface.Sewing.PrimitiveSewing.CutPatch.Assembly
  Purelib.Topology.Surface.Sewing.VertexSewing.EndpointGluing in
/-- Every checked cut assembly has primitive readings. Only local triangle values are requested; compatibility, a
successful scan, or extra geometry is not a premise. The nonzero mismatches remain available in the result. -/
def sample (localValues : Fin faceCount → PrimitiveSewing.PrimitiveValues 3) :
    {indices : List (Fin faceCount)} → {boundary : List (Stokes.OrientedEdge vertexCount)} →
    {patch : Patch.CutPatch faces indices boundary} → (assembly : CutPatch.Assembly faces patch) → Assembly.Sample
      assembly localValues
  | _, _, _, .triangle index => ⟨localValues index, .triangle index, [], rfl⟩
  | _, _, _, .sew left right firstBase secondBase opposite seam =>
      let leftSample := sample localValues left
      let rightSample := sample localValues right
      let joined := PrimitiveSewing.EndpointGluing.PrimitiveSew.build leftSample.values rightSample.values
        seam.firstLift.split.edge seam.secondLift.split.edge
        (by apply CutPatch.nonloop; exact seam.secondLift.split.edge_mem)
      ⟨joined.values, .sew leftSample.readings rightSample.readings joined,
        joined.charge :: (leftSample.charges ++ rightSample.charges), by
          rw [leftSample.charges_eq, rightSample.charges_eq]; rfl⟩

open Purelib.Topology.Surface.Sewing.PrimitiveSewing.CutPatch.Assembly in
/-- The cached charge list contains one charge per original assembly join. -/
theorem Sample.charges_length {localValues : Fin faceCount → PrimitiveSewing.PrimitiveValues 3}
    {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge vertexCount)}
    {patch : Patch.CutPatch faces indices boundary} {assembly : CutPatch.Assembly faces patch}
    (sample : Assembly.Sample assembly localValues) : sample.charges.length + 1 = indices.length := by
  rw [sample.charges_eq]
  exact sample.readings.charges_length

end CutPatch.Assembly

/-- Build retained primitive values and seam charges for the exact original sewn patch assembly. -/
def SewnPatch.primitiveSample {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle
  vertexCount}
    (patch : SewingTree.SewnPatch faces) (localValues : Fin faceCount → PrimitiveSewing.PrimitiveValues 3) :
    PrimitiveSewing.CutPatch.Assembly.Sample patch.assembly localValues := PrimitiveSewing.CutPatch.Assembly.sample
      localValues patch.assembly

end Purelib.Topology.Surface.Sewing.PrimitiveSewing
