module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Algebra.NatCast
import Purelib.Data.List.Append
import Purelib.Data.Nat.Order
import Purelib.Algebra.FiniteSum.Rational.Squares
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
public import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary
import Purelib.Topology.Surface.Sewing.SewingProjection
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Topology.Surface.Sewing.PolygonSewing
import Purelib.Data.Vector.Basic
import Purelib.Tactic.Ring

public section

/-!
# Whole-tree accounting for sewn primitive errors

The geometry fixes the right-ancestor depth and the amplification of local
seam mismatches before primitive accuracy is selected. Actual charges are
summed once; every retained face pays its full ancestor trace, and the final
bound includes the number of faces.
-/

namespace Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting
open Purelib.Algebra.FiniteSum.Rational

open Purelib.Algebra
open Purelib.Data.Nat
open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.Patch

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.PrimitiveSewing.CutPatch

open Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary
open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (Coordinate)

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Algebra.FiniteSum.Rational.Squares (coordinateSum)

set_option genInjectivity false in
/-- The finite geometry controlling inherited sewing errors.

Depth counts right-ancestor translations, factor bounds total contact charge, and faces retains the number of original
triangles. -/
structure Shape where
  /-- Maximum number of right-ancestor translations along a face's assembly route. -/ depth : Nat
  /-- Integer multiplier bounding total contact charge from one local mismatch tolerance. -/ factor : Nat
  /-- Number of original faces in the assembly. -/ faces : Nat

constructive_injectivity Shape

namespace Shape

/-- Combine two assembly profiles across one sewing seam.

The right depth increases by one; each child's charge factor is multiplied by its depth contribution before adding the
new seam allowance. -/
@[expose] def join (left right : SewnPrimitiveAccounting.Shape) : Shape :=
  ⟨max left.depth (right.depth + 1),
    (16 * left.depth + 1) * left.factor + (16 * right.depth + 1) * right.factor + 2,
    left.faces + right.faces⟩

/-- The joined integer factor casts to the same rational amplification formula.

Natural addition and multiplication casts preserve the displayed depth and charge factors. The scalar rational identity
retains each of those same operands. -/
theorem join_factor_cast (left right : SewnPrimitiveAccounting.Shape) :
    ((left.join right).factor : SewnPrimitiveFaces.Coordinate) =
      (16 * (left.depth : SewnPrimitiveFaces.Coordinate) + 1) * left.factor + (16 * (right.depth :
        SewnPrimitiveFaces.Coordinate) + 1) * right.factor + 2 := by
  change (((16 * left.depth + 1) * left.factor + (16 * right.depth + 1) * right.factor + 2 : Nat) :
    SewnPrimitiveFaces.Coordinate) = _
  simp only [NatCast.add, NatCast.mul, Nat.cast_ofNat, Nat.cast_one, -eq_self]
  rfl

/-- The joined factor pays both child charges and the new seam charge under their stated bounds.

The two nonnegative depth multipliers transport the supplied child bounds. The seam bound then yields the joined factor
at the same tolerance. -/
theorem charge_bound (left right : SewnPrimitiveAccounting.Shape) (leftCharge rightCharge newCharge tolerance :
  SewnPrimitiveFaces.Coordinate)
    (leftBound : leftCharge ≤ (left.factor : SewnPrimitiveFaces.Coordinate) * tolerance)
    (rightBound : rightCharge ≤ (right.factor : SewnPrimitiveFaces.Coordinate) * tolerance)
    (newBound : newCharge ≤ 16 * ((left.depth : SewnPrimitiveFaces.Coordinate) * leftCharge + (right.depth :
      SewnPrimitiveFaces.Coordinate) * rightCharge) + 2 * tolerance) :
    leftCharge + rightCharge + newCharge ≤ ((left.join right).factor : SewnPrimitiveFaces.Coordinate) * tolerance := by
  have leftNonnegative : (0 : SewnPrimitiveFaces.Coordinate) ≤ 16 * (left.depth : SewnPrimitiveFaces.Coordinate) + 1 :=
    add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _))) (by decide)
  have rightNonnegative : (0 : SewnPrimitiveFaces.Coordinate) ≤ 16 * (right.depth : SewnPrimitiveFaces.Coordinate) + 1
    :=
    add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _))) (by decide)
  calc
    _ ≤ leftCharge + rightCharge + (16 * ((left.depth : SewnPrimitiveFaces.Coordinate) * leftCharge + (right.depth :
      SewnPrimitiveFaces.Coordinate) * rightCharge) + 2 * tolerance) :=
      add_le_add le_rfl newBound
    _ = (16 * (left.depth : SewnPrimitiveFaces.Coordinate) + 1) * leftCharge + (16 * (right.depth :
      SewnPrimitiveFaces.Coordinate) + 1) * rightCharge + 2 * tolerance := by
      ring1
    _ ≤ (16 * (left.depth : SewnPrimitiveFaces.Coordinate) + 1) * ((left.factor : SewnPrimitiveFaces.Coordinate) *
      tolerance) +
        (16 * (right.depth : SewnPrimitiveFaces.Coordinate) + 1) * ((right.factor : SewnPrimitiveFaces.Coordinate) *
          tolerance) + 2 * tolerance :=
      add_le_add (add_le_add
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct leftBound leftNonnegative)
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct rightBound rightNonnegative)) le_rfl
    _ = _ := by rw [Shape.join_factor_cast]; ring1

end Shape

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {localValues : Fin faceCount → PrimitiveSewing.PrimitiveValues 3}

/-- Compute the depth, contact factor and face count from an assembly tree.

A single triangle has depth and charge factor zero; each sewing combines its children's retained geometry. -/
@[expose] def shape : {indices : List (Fin faceCount)} → {boundary : List (Stokes.OrientedEdge vertexCount)} →
    {patch : Patch.CutPatch faces indices boundary} → CutPatch.Assembly faces patch → SewnPrimitiveAccounting.Shape
  | _, _, _, .triangle _ => ⟨0, 0, 1⟩
  | _, _, _, .sew left right _ _ _ _ => (Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting.shape left).join
    (Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting.shape right)

/-- The computed face count equals the original assembly index-list length.

Each triangle contributes one face, and each sewing concatenates its retained child index lists. Their lengths give the
computed face count. -/
theorem shape_faces {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge vertexCount)}
    {patch : Patch.CutPatch faces indices boundary} (assembly : CutPatch.Assembly faces patch) :
    (SewnPrimitiveAccounting.shape assembly).faces = indices.length := by
  induction assembly with
  | triangle => rfl
  | sew left right firstBase secondBase opposite seam ihLeft ihRight =>
      change (SewnPrimitiveAccounting.shape left).faces + (SewnPrimitiveAccounting.shape right).faces = _
      rw [ihLeft, ihRight, Append.length_append]

/-- Sum each retained sewing charge once along the actual reading tree.

Each sewing contributes its stored charge after the two child totals. Triangle readings contribute zero. -/
@[expose] def totalCharge : {indices : List (Fin faceCount)} → {boundary : List (Stokes.OrientedEdge vertexCount)} →
    {patch : Patch.CutPatch faces indices boundary} → {assembly : CutPatch.Assembly faces patch} →
    {values : PrimitiveSewing.PrimitiveValues patch.count} → Assembly.Readings localValues assembly values →
      SewnPrimitiveFaces.Coordinate
  | _, _, _, _, _, .triangle _ => 0
  | _, _, _, _, _, .sew left right joined => Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting.totalCharge left +
    Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting.totalCharge right + joined.charge

/-- The sum of retained sewing charges is nonnegative.

The stored seam charge and both retained child totals are nonnegative, so their displayed sum is nonnegative. -/
theorem totalCharge_nonnegative {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge vertexCount)}
    {patch : Patch.CutPatch faces indices boundary} {assembly : CutPatch.Assembly faces patch}
    {values : PrimitiveSewing.PrimitiveValues patch.count} (readings : Assembly.Readings localValues assembly values) :
    0 ≤ SewnPrimitiveAccounting.totalCharge readings := by
  induction readings with
  | triangle => exact le_rfl
  | sew left right joined ihLeft ihRight => exact add_nonneg (add_nonneg ihLeft ihRight) joined.charge_nonnegative

/-- Recursive total charge agrees with the coordinate sum of the retained charge list.

The retained charge list contains each seam charge and both child lists. Its coordinate sum agrees with the recursive
charge on those same readings. -/
theorem totalCharge_eq {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge vertexCount)}
    {patch : Patch.CutPatch faces indices boundary} {assembly : CutPatch.Assembly faces patch}
    {values : PrimitiveSewing.PrimitiveValues patch.count} (readings : Assembly.Readings localValues assembly values) :
    SewnPrimitiveAccounting.totalCharge readings = Squares.coordinateSum readings.charges := by
  induction readings with
  | triangle => rfl
  | sew left right joined ihLeft ihRight =>
      change SewnPrimitiveAccounting.totalCharge left + SewnPrimitiveAccounting.totalCharge right + joined.charge =
        joined.charge + Squares.coordinateSum (left.charges ++ right.charges)
      rw [ihLeft, ihRight, Squares.coordinateSum_append]
      ring1

/-- A trace uses only ancestor charges, never the charges of an unrelated subtree. Bounding by their full nonnegative
sum is therefore valid.

A face trace belongs to exactly one child bank at each sewing. Its depth is bounded by the retained assembly maximum and
its charge by the nonnegative whole-tree sum. -/
theorem trace_bounds {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge vertexCount)}
    {patch : Patch.CutPatch faces indices boundary} {assembly : CutPatch.Assembly faces patch}
    {values : PrimitiveSewing.PrimitiveValues patch.count} (readings : Assembly.Readings localValues assembly values) :
    ∀ trace ∈ (FaceBank.build readings).entries,
      trace.depth ≤ (SewnPrimitiveAccounting.shape assembly).depth ∧ trace.charge ≤ SewnPrimitiveAccounting.totalCharge
        readings := by
  induction readings with
  | triangle source =>
      intro trace member
      have equal := Membership.mem_singleton.mp member
      cases equal
      exact ⟨Nat.le_refl _, le_rfl⟩
  | sew left right joined ihLeft ihRight =>
      intro trace member
      change trace ∈ (FaceBank.build left).entries.map (fun trace => trace.mapLeft joined) ++
        (FaceBank.build right).entries.map (fun trace => trace.mapRight joined) at member
      rcases Membership.mem_append.mp member with fromLeft | fromRight
      · rcases Map.mem_map.mp fromLeft with ⟨original, originalMember, equal⟩
        cases equal
        have bound := ihLeft original originalMember
        exact ⟨bound.1.trans (Order.le_max_left _ _), bound.2.trans
          ((le_add_of_nonneg_right (SewnPrimitiveAccounting.totalCharge_nonnegative right)).trans
            (le_add_of_nonneg_right joined.charge_nonnegative))⟩
      · rcases Map.mem_map.mp fromRight with ⟨original, originalMember, equal⟩
        cases equal
        have bound := ihRight original originalMember
        refine ⟨(Nat.add_le_add_right bound.1 1).trans (Order.le_max_right _ _), ?_⟩
        change joined.charge + original.charge ≤ SewnPrimitiveAccounting.totalCharge left +
          SewnPrimitiveAccounting.totalCharge right + joined.charge
        exact (add_le_add le_rfl bound.2).trans
          ((le_add_of_nonneg_left (SewnPrimitiveAccounting.totalCharge_nonnegative left)).trans_eq (by ring1))

/-- Each cached face allowance is bounded by assembly depth times total sewing charge.

The cached allowance equation uses that trace's count and charge. Their certified bounds multiply through nonnegative
rational factors. -/
theorem trace_allowance_le {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge vertexCount)}
    {patch : Patch.CutPatch faces indices boundary} {assembly : CutPatch.Assembly faces patch}
    {values : PrimitiveSewing.PrimitiveValues patch.count} (readings : Assembly.Readings localValues assembly values)
    (trace : SewnPrimitiveFaces.FaceTrace localValues values) (member : trace ∈ (FaceBank.build readings).entries) :
    trace.allowance ≤ ((SewnPrimitiveAccounting.shape assembly).depth : SewnPrimitiveFaces.Coordinate) *
      SewnPrimitiveAccounting.totalCharge readings := by
  rw [trace.allowance_eq, trace.countValue_eq]
  have bound := SewnPrimitiveAccounting.trace_bounds readings trace member
  exact Fraction.Order.Arithmetic.mul_le_mul_direct
    (Fraction.Cast.Order.natCast_le_direct bound.1) bound.2 trace.charge_nonnegative
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _))

/-- Uniformly bounded face allowances sum to at most their count times the common limit.

Every displayed trace is charged at most the supplied limit. Structural recursion adds the bound once for each retained
list occurrence. -/
private theorem sum_allowances_le {count : Nat} {values : PrimitiveSewing.PrimitiveValues count} (limit :
  SewnPrimitiveFaces.Coordinate) :
    (entries : List (SewnPrimitiveFaces.FaceTrace localValues values)) → (∀ trace ∈ entries, trace.allowance ≤ limit) →
      Squares.coordinateSum (entries.map FaceTrace.allowance) ≤ (entries.length : SewnPrimitiveFaces.Coordinate) * limit
  | [], _ => by change (0 : SewnPrimitiveFaces.Coordinate) ≤ 0 * limit; rw [Fraction.Field.zero_mul_direct]
  | trace :: entries, bounded =>
      (add_le_add (bounded trace List.mem_cons_self)
        (Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting.sum_allowances_le limit entries (fun entry member =>
          bounded entry (List.mem_cons_of_mem _ member)))).trans_eq (by
          change limit + (entries.length : SewnPrimitiveFaces.Coordinate) * limit = ((entries.length + 1 : Nat) :
            SewnPrimitiveFaces.Coordinate) * limit
          rw [NatCast.add, Nat.cast_one]
          ring1)

/-- Bound the face bank's squared errors by twice the face count times depth times total charge.

Every face occurrence and its inherited ancestor allowance is retained in the finite estimate. -/
theorem aggregate_le {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge vertexCount)}
    {patch : Patch.CutPatch faces indices boundary} {assembly : CutPatch.Assembly faces patch}
    {values : PrimitiveSewing.PrimitiveValues patch.count} (readings : Assembly.Readings localValues assembly values) :
    (FaceBank.build readings).squaredErrors ≤
      2 * ((SewnPrimitiveAccounting.shape assembly).faces : SewnPrimitiveFaces.Coordinate) *
        (SewnPrimitiveAccounting.shape assembly).depth * SewnPrimitiveAccounting.totalCharge readings := by
  have lengthEq : (FaceBank.build readings).entries.length = (SewnPrimitiveAccounting.shape assembly).faces := by
    have lengths := congrArg List.length (FaceBank.build readings).sources_eq
    rw [Map.length_map, ← SewnPrimitiveAccounting.shape_faces assembly] at lengths
    exact lengths
  have bound := SewnPrimitiveAccounting.sum_allowances_le _ (FaceBank.build readings).entries
    (SewnPrimitiveAccounting.trace_allowance_le readings)
  rw [← (FaceBank.build readings).totalAllowance_eq, lengthEq] at bound
  exact (FaceBank.build readings).aggregate_error_bound.trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bound (by decide)).trans_eq (by ring1))

end Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting
