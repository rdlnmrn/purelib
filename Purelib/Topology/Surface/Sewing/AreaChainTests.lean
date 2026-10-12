module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Surface.Sewing.SewingRetraction
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Topology.Surface.Sewing.VertexSewing
import Mathlib.Data.Int.Cast.Defs
import Purelib.Tactic.Ring
import Purelib.Data.List.Membership
import Purelib.Algebra.Ring.IntCast
import Purelib.Algebra.Group.Negation

public section

/-!
# Finite primitive tests recover oriented chain values

For each displayed vertex use its indicator as one primitive and the
outgoing edge values as the other. Summing these finitely many area tests
recovers twice the value of any antisymmetric edge word. Thus an identity
for every primitive assignment implies an identity for every edge valuation.
No extension of functions, completed space, or choice of basis is involved.
-/

namespace Purelib.Topology.Surface.Sewing.AreaChainTests

open Purelib.Algebra

open Purelib.Data

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint Triangulation edgeArea edgeListArea
  triangleEdgeOccurrences triangleWedgeSum_eq_edgeListArea)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add sumFin_sub sumFin_ite_eq sumFin_zero)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)

open Purelib.Data.List Purelib.Algebra.Ring

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid SubNegMonoid.toNeg

variable {count : Nat}

/-- Pair a selected-vertex indicator with the original outgoing edge reading to form a finite primitive test.

The selected vertex contributes the unit indicator; the second coordinate
retains the supplied reading of its ordered outgoing edge. -/
@[expose] def primitive (value : Stokes.OrientedEdge count → Gaussian.Basic.Canonical) (selected vertex : Fin count) :
  PrimitivePoint :=
  ⟨if selected = vertex then 1 else 0, value ⟨selected, vertex⟩⟩

/-- A finite indicator-weighted sum reads the value at its selected vertex.

The finite sum keeps every displayed vertex index. Only the selected
indicator contributes, and all other terms are zero. -/
private theorem indicator_sum (selected : Fin count) (value : Fin count → Gaussian.Basic.Canonical) :
    FiniteSum.Fin.sumFin (fun index => (if index = selected then 1 else 0) * value index) = value selected := by
  apply (FiniteSum.Fin.sumFin_congr ?_).trans (FiniteSum.Fin.sumFin_ite_eq selected value)
  intro index
  by_cases same : index = selected
  · rw [if_pos same, if_pos same, one_mul]
  · rw [if_neg same, if_neg same, zero_mul]

/-- Summing all selected-vertex primitive area tests gives twice the original antisymmetric edge value.

Antisymmetry identifies the reversed reading with its negative. The finite
vertex sum retains the supplied edge endpoints and scalar readings. -/
theorem edge_sum (value : Stokes.OrientedEdge count → Gaussian.Basic.Canonical) (anti : ∀ edge, value edge.reverse =
  -value edge)
    (edge : Stokes.OrientedEdge count) :
    FiniteSum.Fin.sumFin (fun selected => Stokes.edgeArea (primitive value selected edge.start) (primitive value
      selected edge.finish)) =
      value edge * 2 := by
  dsimp only [primitive, Stokes.edgeArea]
  rw [FiniteSum.Fin.sumFin_sub, indicator_sum, indicator_sum]
  change value edge - value edge.reverse = value edge * 2
  rw [anti]
  ring1

/-- Summing all finite primitive area tests gives twice the value of the original oriented edge word.

The edge identity is applied in the displayed occurrence order. The
retained tail contributes the same recursively evaluated word value. -/
theorem word_sum (value : Stokes.OrientedEdge count → Gaussian.Basic.Canonical) (anti : ∀ edge, value edge.reverse =
  -value edge)
    (word : List (Stokes.OrientedEdge count)) :
    FiniteSum.Fin.sumFin (fun selected => Stokes.edgeListArea (primitive value selected) word) =
      SewingRetraction.wordValue value word * 2 := by
  induction word with
  | nil => exact FiniteSum.Fin.sumFin_zero.trans (zero_mul _).symm
  | cons edge word ih =>
      change FiniteSum.Fin.sumFin (fun selected => Stokes.edgeArea (primitive value selected edge.start) (primitive
        value selected edge.finish) +
        Stokes.edgeListArea (primitive value selected) word) = (value edge + SewingRetraction.wordValue value word) * 2
      rw [FiniteSum.Fin.sumFin_add, edge_sum value anti, ih]
      ring1

/-- Testing every primitive is sufficient for actual oriented chain readback, not only for the special wedge-valued edge
assignments.

The hypotheses compare area readings for every finite primitive assignment.
Selected-vertex indicators recover each antisymmetric word valuation. -/
theorem wordValue_eq {first last : List (Stokes.OrientedEdge count)}
    (areas : ∀ points : Fin count → Stokes.PrimitivePoint, Stokes.edgeListArea points first = Stokes.edgeListArea points
      last)
    (value : Stokes.OrientedEdge count → Gaussian.Basic.Canonical) (anti : ∀ edge, value edge.reverse = -value edge) :
    SewingRetraction.wordValue value first = SewingRetraction.wordValue value last := by
  apply Gaussian.Field.mul_right_cancel_of_ne (factor := 2) (by decide)
  rw [← word_sum value anti first, ← word_sum value anti last]
  exact FiniteSum.Fin.sumFin_congr (fun selected => areas (primitive value selected))

/-- The integer coefficient of an oriented edge, with its reverse counted negatively.

The selected orientation contributes positively and its reverse negatively.
The coefficient retains occurrence order without identifying list lengths. -/
@[expose] def edgeCoefficient (selected edge : Stokes.OrientedEdge count) : Int :=
  (if edge = selected then 1 else 0) - (if edge.reverse = selected then 1 else 0)

/-- Reversing an edge negates its signed coefficient at the selected orientation.

Reversal interchanges the two orientation indicators. Their signed
difference consequently changes sign. -/
theorem edgeCoefficient_reverse (selected edge : Stokes.OrientedEdge count) :
    edgeCoefficient selected edge.reverse = -edgeCoefficient selected edge := by
  unfold edgeCoefficient
  rw [OrientedEdge.reverse_reverse]
  ring1

/-- Sum the signed occurrences of the selected edge over the original ordered edge word.

Each displayed edge contributes its signed orientation indicator before
the recursively accumulated tail. -/
@[expose] def coefficient (selected : Stokes.OrientedEdge count) : List (Stokes.OrientedEdge count) → Int
  | [] => 0
  | edge :: word => AreaChainTests.edgeCoefficient selected edge + coefficient selected word

/-- Unique oriented occurrences determine a coefficient by membership.

Duplicate-freeness makes each orientation indicator Boolean in value.
Internal edges with both orientations present therefore have coefficient zero. -/
theorem coefficient_nodup (selected : Stokes.OrientedEdge count) (word : List (Stokes.OrientedEdge count))
    (unique : word.Nodup) :
    coefficient selected word = (if selected ∈ word then 1 else 0) -
      (if selected.reverse ∈ word then 1 else 0) := by
  induction word with
  | nil =>
      have absent : selected ∉ ([] : List (Stokes.OrientedEdge count)) := fun member => nomatch member
      have absentReverse : selected.reverse ∉ ([] : List (Stokes.OrientedEdge count)) := fun member => nomatch member
      rw [coefficient, if_neg absent, if_neg absentReverse]
      rfl
  | cons head tail ih =>
      obtain ⟨fresh, tailUnique⟩ := List.pairwise_cons.mp unique
      have absent : head ∉ tail := fun member => fresh head member rfl
      rw [coefficient, ih tailUnique, Membership.member_indicator_cons selected head tail absent,
        Membership.member_indicator_cons selected.reverse head tail absent]
      have reversed : head.reverse = selected ↔ head = selected.reverse :=
        ⟨fun same => (OrientedEdge.reverse_reverse head).symm.trans (congrArg OrientedEdge.reverse same),
          fun same => (congrArg OrientedEdge.reverse same).trans (OrientedEdge.reverse_reverse selected)⟩
      unfold edgeCoefficient
      by_cases same : head.reverse = selected
      · rw [if_pos same, if_pos (reversed.mp same)]; ring1
      · rw [if_neg same, if_neg (fun equal => same (reversed.mpr equal))]; ring1

/-- In a duplicate-free edge word, coefficient one means the selected orientation occurs and its reverse does not.

The four orientation-membership cases determine the scalar coefficient.
Only the selected orientation without its reverse contributes one. -/
theorem coefficient_eq_one_iff (selected : Stokes.OrientedEdge count) (word : List (Stokes.OrientedEdge count))
    (unique : word.Nodup) :
    coefficient selected word = 1 ↔ selected ∈ word ∧ selected.reverse ∉ word := by
  rw [coefficient_nodup selected word unique]
  by_cases forward : selected ∈ word
  · by_cases backward : selected.reverse ∈ word
    · rw [if_pos forward, if_pos backward]
      exact ⟨fun impossible => False.elim ((by decide : ((1 : Int) - 1) ≠ 1) impossible),
        fun both => False.elim (both.2 backward)⟩
    · rw [if_pos forward, if_neg backward]
      exact ⟨fun _ => ⟨forward, backward⟩, fun _ => rfl⟩
  · by_cases backward : selected.reverse ∈ word
    · rw [if_neg forward, if_pos backward]
      exact ⟨fun impossible => False.elim ((by decide : ((0 : Int) - 1) ≠ 1) impossible),
        fun both => False.elim (forward both.1)⟩
    · rw [if_neg forward, if_neg backward]
      exact ⟨fun impossible => False.elim ((by decide : ((0 : Int) - 0) ≠ 1) impossible),
        fun both => False.elim (forward both.1)⟩

/-- Casting the integer coefficient gives evaluation of the original word by the same signed Gaussian edge reading.

The cast preserves each integer contribution and the displayed order
of the finite Gaussian word sum. -/
private theorem coefficient_cast (selected : Stokes.OrientedEdge count) (word : List (Stokes.OrientedEdge count)) :
    (coefficient selected word : Gaussian.Basic.Canonical) = SewingRetraction.wordValue (fun edge => (edgeCoefficient
      selected edge : Gaussian.Basic.Canonical)) word := by
  induction word with
  | nil => exact IntCast.cast_zero
  | cons edge word ih => rw [coefficient, IntCast.add, ih]; rfl

/-- The real coordinate of a Gaussian integer cast is the corresponding rational cast.

Each integer sign case uses the retained natural or negative-successor
cast equation and the Gaussian coordinate projection. -/
private theorem gaussian_int_re (value : Int) :
    (value : Gaussian.Basic.Canonical).re = (value : Purelib.Data.Rat.Fraction.Rational) := by
  cases value with
  | ofNat value =>
      change (((value : Nat) : Int) : Gaussian.Basic.Canonical).re = (((value : Nat) : Int) : Fraction.Rational)
      rw [Int.cast_natCast, Cast.natCast_re, Int.cast_natCast]
  | negSucc value => rw [IntCast.cast_negSucc, Gaussian.Basic.neg_re,
      Cast.natCast_re, IntCast.cast_negSucc]

/-- Equality of all finite primitive area tests implies equality of every original integer edge coefficient.

The selected signed edge reading is antisymmetric. Its Gaussian real
coordinate recovers the integer coefficient through injective rational casts. -/
theorem coefficient_eq {first last : List (Stokes.OrientedEdge count)}
    (areas : ∀ points : Fin count → Stokes.PrimitivePoint, Stokes.edgeListArea points first = Stokes.edgeListArea points
      last)
    (selected : Stokes.OrientedEdge count) : coefficient selected first = coefficient selected last := by
  apply Fraction.Cast.Compatibility.intCast_injective_direct
  have same := wordValue_eq areas (fun edge => (edgeCoefficient selected edge : Gaussian.Basic.Canonical)) (by
    intro edge
    rw [edgeCoefficient_reverse]
    exact IntCast.neg (edgeCoefficient selected edge))
  rw [← coefficient_cast, ← coefficient_cast] at same
  have realParts := congrArg Gaussian.Basic.Canonical.re same
  rw [gaussian_int_re, gaussian_int_re] at realParts
  exact realParts

/-- The triangulation's occurrence certificate gives exact integer incidence, even when its displayed boundary still
contains retracings.

The retained wedge-sum certificate compares every primitive assignment.
It therefore preserves the coefficient of each displayed orientation. -/
theorem triangulation_coefficient {faceCount : Nat} (triangulation : Stokes.Triangulation count faceCount)
    (selected : Stokes.OrientedEdge count) :
    coefficient selected (Stokes.triangleEdgeOccurrences triangulation.faces) = coefficient selected
      triangulation.boundary :=
  coefficient_eq (fun points => (Stokes.triangleWedgeSum_eq_edgeListArea points triangulation.faces).symm.trans
    (triangulation.wedgeSum_eq_boundaryArea points)) selected

end Purelib.Topology.Surface.Sewing.AreaChainTests
