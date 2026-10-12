module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Weighted
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Integration.Path.WeightedPathArea
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
public import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! Finite common refinements of two samplings of the same source primitive.
Zero-length steps are retained and contribute zero area. No limiting path,
new primitive owner, or final-vertex-count estimate is used. -/
namespace Purelib.Integration.Path.Dyadic.SourceResampling

open Purelib.Riemann.Periods.CenteredBilinearPath (Coordinate Sample area)

open Purelib.Data.Rat in
/-- The rational carrier for original source parameters and resampling bounds. -/
abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian carrier for source area readings. -/
abbrev Gaussian := Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility

open Purelib.Integration.Path in
/-- An ordered retained parameter list linking its exact original first and last endpoints. -/
inductive Chain : Coordinate → List Coordinate →
  Coordinate → Prop
  /-- The exact empty chain or refinement at its retained endpoint. -/ | nil (point :
    Coordinate) : Chain point [] point
  /-- Retain the first ordering witness and the exact original tail chain. -/ | cons {first next last :
    Coordinate} {tail : List Coordinate}
      (ordered : first ≤ next) (rest : Chain next tail last) :
        Chain first (next :: tail) last

namespace Chain

open Purelib.Integration.Path
/-- An empty retained parameter chain has identical first and last endpoints. -/
theorem nil_eq {first last : Dyadic.SourceResampling.Coordinate} (chain : Dyadic.SourceResampling.Chain first [] last) :
  first = last := by
  cases chain
  rfl

/-- A nonempty retained chain gives its first ordering witness and the exact tail chain. -/
theorem cons_parts {first next last : Dyadic.SourceResampling.Coordinate} {tail : List
  Dyadic.SourceResampling.Coordinate}
    (chain : Dyadic.SourceResampling.Chain first (next :: tail) last) : first ≤ next ∧ Dyadic.SourceResampling.Chain
      next tail last := by
  cases chain with
  | cons ordered rest => exact ⟨ordered, rest⟩

/-- The original first endpoint of an ordered chain is at most its last endpoint. -/
theorem endpoints {first last : Dyadic.SourceResampling.Coordinate} {tail : List Dyadic.SourceResampling.Coordinate}
    (chain : Dyadic.SourceResampling.Chain first tail last) : first ≤ last := by
  induction chain with
  | nil => exact le_rfl
  | cons ordered _ ih => exact ordered.trans ih

end Chain

open Purelib.Integration.Path in
/-- An exact ordered parameter refinement built by retaining, inserting or duplicating original points.

The coarse and fine lists share their indexed original endpoints; every insertion retains its two bounding witnesses. -/
inductive Refinement : Coordinate → List Coordinate → List
  Coordinate → Coordinate → Prop
  /-- The exact empty chain or refinement at its retained endpoint. -/ | nil (point :
    Coordinate) : Refinement point [] [] point
  /-- Keep the original next point in both lists and retain the tail refinement. -/ | keep {first next last :
    Coordinate} {coarse fine : List Coordinate}
      (ordered : first ≤ next) (rest : Refinement next coarse fine
        last) :
      Refinement first (next :: coarse) (next :: fine) last
  /-- Insert a bounded intermediate point while retaining the original next coarse point and tail refinement. -/ |
    insert {first middle next last : Coordinate} {coarse fine : List
    Coordinate}
      (lower : first ≤ middle) (upper : middle ≤ next)
      (rest : Refinement middle (next :: coarse) fine last) :
      Refinement first (next :: coarse) (middle :: fine) last
  /-- Insert one occurrence of the exact current point into the fine list. -/ | duplicate {first last :
    Coordinate} {coarse fine : List Coordinate}
      (rest : Refinement first coarse fine last) :
        Refinement first coarse (first :: fine) last

namespace Refinement

open Purelib.Integration.Path
/-- A retained refinement certifies the exact original coarse list as an ordered chain. -/
theorem coarse_chain {first last : Dyadic.SourceResampling.Coordinate} {coarse fine : List
  Dyadic.SourceResampling.Coordinate}
    (refinement : Dyadic.SourceResampling.Refinement first coarse fine last) : Dyadic.SourceResampling.Chain first
      coarse last := by
  induction refinement with
  | nil => exact .nil _
  | keep ordered _ ih => exact .cons ordered ih
  | insert lower upper _ ih =>
    cases ih with
    | cons _ tail => exact .cons (lower.trans upper) tail
  | duplicate _ ih => exact ih

/-- A retained refinement certifies its exact fine list as an ordered chain. -/
theorem fine_chain {first last : Dyadic.SourceResampling.Coordinate} {coarse fine : List
  Dyadic.SourceResampling.Coordinate}
    (refinement : Dyadic.SourceResampling.Refinement first coarse fine last) : Dyadic.SourceResampling.Chain first fine
      last := by
  induction refinement with
  | nil => exact .nil _
  | keep ordered _ ih => exact .cons ordered ih
  | insert lower _ _ ih => exact .cons lower ih
  | duplicate _ ih => exact .cons le_rfl ih

/-- Every retained ordered chain refines itself with the exact same point list. -/
theorem refl {first last : Dyadic.SourceResampling.Coordinate} {points : List Dyadic.SourceResampling.Coordinate}
    (chain : Dyadic.SourceResampling.Chain first points last) : Dyadic.SourceResampling.Refinement first points points
      last := by
  induction chain with
  | nil => exact .nil _
  | cons ordered _ ih => exact .keep ordered ih

/-- A closed ordered chain refines its empty endpoint chain.

Every retained step has the same endpoint value by antisymmetry. The
refinement keeps all ordered occurrences as exact endpoint duplications. -/
theorem terminal {first : Dyadic.SourceResampling.Coordinate} {points : List Dyadic.SourceResampling.Coordinate}
    (chain : Dyadic.SourceResampling.Chain first points first) : Dyadic.SourceResampling.Refinement first [] points
      first := by
  induction points with
  | nil => exact .nil _
  | cons next tail ih =>
    cases chain with
    | cons lower rest =>
      have equal := lower.antisymm rest.endpoints
      cases equal
      exact .duplicate (ih rest)

end Refinement

set_option genInjectivity false in
open Purelib.Integration.Path in
/-- One retained parameter list with separate refinement witnesses from both exact original lists.

The point list retains both inputs through their own indexed refinement
witnesses, preserving the shared endpoints and ordered parameter occurrences. -/
structure CommonRefinement (first : Coordinate) (left right : List
  Coordinate) (last : Coordinate) where
  /-- The retained common fine parameter list. -/ points : List Coordinate
  /-- The refinement witness from the exact original left list. -/ left : Refinement first left
    points last
  /-- The refinement witness from the exact original right list. -/ right : Refinement first
    right points last

constructive_injectivity CommonRefinement

open Purelib.Integration.Path in
/-- Merge the two original ordered parameter chains into a retained common refinement.

The original first and last endpoints and both refinement witnesses are preserved; equality is handled by the first-list
branch and duplicates retain their exact list occurrences. -/
@[expose] def common (first last : Coordinate) (left right : List
  Coordinate)
    (leftChain : Chain first left last) (rightChain : Chain first right
      last) :
    CommonRefinement first left right last :=
  match left, right with
  | [], points => by
      have equal := leftChain.nil_eq
      subst last
      exact ⟨points, Refinement.terminal rightChain, Refinement.refl
        rightChain⟩
  | head :: tail, [] => by
      have equal := rightChain.nil_eq
      subst last
      exact ⟨head :: tail, Refinement.refl leftChain,
        Refinement.terminal leftChain⟩
  | a :: leftTail, b :: rightTail => by
      have leftParts := leftChain.cons_parts
      have rightParts := rightChain.cons_parts
      if ordered : a ≤ b then
        let tail := common a last leftTail (b :: rightTail) leftParts.2
          (.cons ordered rightParts.2)
        exact ⟨a :: tail.points, .keep leftParts.1 tail.left, .insert leftParts.1 ordered tail.right⟩
      else
        have ordered := (lt_of_not_ge ordered).le
        let tail := common b last (a :: leftTail) rightTail (.cons
          ordered leftParts.2) rightParts.2
        exact ⟨b :: tail.points, .insert rightParts.1 ordered tail.left, .keep rightParts.1 tail.right⟩
termination_by left.length + right.length
decreasing_by all_goals simp only [List.length_cons]; omega0

open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- Sum the directed original primitive edge areas in retained parameter-list order. -/
@[expose] def rawArea (values : Coordinate → Stokes.PrimitivePoint) :
  Coordinate → List Coordinate → Gaussian
  | _, [] => 0
  | first, next :: tail => Stokes.edgeArea (values first) (values next) +
    rawArea values next tail

open Purelib.Integration.Path in
/-- Every consecutive original parameter step is bounded above by the retained common width. -/
@[expose] def widths : Coordinate → List Coordinate →
  Coordinate → Prop
  | _, [], _ => True
  | first, next :: tail, width => next - first ≤ width ∧ widths next
    tail width

section
open Purelib.Topology.Polygon
/-- Inserting the middle primitive point changes edge area by the area of its two exact successive increments. -/
private theorem triangle_identity (a b c : Stokes.PrimitivePoint) :
    Stokes.edgeArea a b + Stokes.edgeArea b c - Stokes.edgeArea a c = Stokes.edgeArea ((Stokes.PrimitivePoint.sub b) a)
      ((Stokes.PrimitivePoint.sub c) b) := by
  dsimp only [Stokes.edgeArea, Stokes.PrimitivePoint.sub]
  ring1

/-- A directed primitive edge from a point to itself has zero area. -/
private theorem edge_self (point : Stokes.PrimitivePoint) : Stokes.edgeArea point point = 0 := by
  dsimp only [Stokes.edgeArea]
  ring1

end

section
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Riemann.Readings
open Purelib.Topology.Polygon
/-- An ordered retained refinement changes source area by at most four times density squared, width squared and endpoint
width squared.

The original coarse steps obey the supplied width bound, both endpoints lie in the unit interval, and the same original
two-coordinate movement certificate applies throughout. -/
theorem refinement_bound (values : Coordinate → Stokes.PrimitivePoint) {density width :
  Coordinate}
    (increment : ∀ a b, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
      (PrimitiveAreaBounds.PrimitivePoint.Bounded ((Stokes.PrimitivePoint.sub (values b)) (values a))) (density * (b -
        a) ^ 2))
    {first last : Coordinate} {coarse fine : List Coordinate}
    (refinement : Refinement first coarse fine last)
    (lower : 0 ≤ first) (upper : last ≤ 1) (steps : widths first coarse width) :
    Data.Gaussian.Norm.Basic.normSq (rawArea values first fine - rawArea
      values first coarse) ≤
      (4 * density ^ 2 * width ^ 2) * (last - first) ^ 2 := by
  induction refinement with
  | nil =>
    change Data.Gaussian.Norm.Basic.normSq ((0 : Gaussian) - 0) ≤ _
    rw [sub_self, Norm.Basic.normSq_zero]
    exact le_of_eq (by ring1)
  | @keep first next last coarse fine ordered rest ih =>
    have tail := ih (lower.trans ordered) upper steps.2
    change Data.Gaussian.Norm.Basic.normSq ((Stokes.edgeArea (values first) (values next) +
      rawArea
      values next fine) -
      (Stokes.edgeArea (values first) (values next) + rawArea values next coarse)) ≤ _
    rw [show (Stokes.edgeArea (values first) (values next) + rawArea values next fine) -
        (Stokes.edgeArea (values first) (values next) + rawArea values next coarse) =
        rawArea values next fine - rawArea values next coarse by ring1]
    exact tail.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.pow_le_pow_direct (Fraction.Order.Arithmetic.sub_nonneg_direct
        rest.coarse_chain.endpoints)
        (Fraction.Order.Arithmetic.sub_le_sub_direct le_rfl ordered) 2)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Fraction.Order.Arithmetic.sq_nonneg_direct _)) (Fraction.Order.Arithmetic.sq_nonneg_direct _)))
  | @insert first middle next last coarse fine lowerStep upperStep rest ih =>
    have chain := rest.coarse_chain
    have nextLast : next ≤ last := by cases chain with | cons _ tail => exact tail.endpoints
    have middleLast := upperStep.trans nextLast
    have tailSteps : widths middle (next :: coarse) width :=
      ⟨(Fraction.Order.Arithmetic.sub_le_sub_direct le_rfl lowerStep).trans steps.1, steps.2⟩
    have tail := ih (lower.trans lowerStep) upper tailSteps
    have firstBound := increment first middle lower (lowerStep.trans (middleLast.trans upper))
      (lower.trans lowerStep) (middleLast.trans upper)
    have lastBound := increment middle next (lower.trans lowerStep) (middleLast.trans upper)
      (lower.trans (lowerStep.trans upperStep)) (nextLast.trans upper)
    have triangle := PrimitiveAreaBounds.PrimitivePoint.area_bound firstBound lastBound
    rw [← Norm.Basic.normSq_eq_canonical] at triangle
    have widthLe := Fraction.Order.Arithmetic.pow_le_pow_direct (Fraction.Order.Arithmetic.sub_nonneg_direct upperStep)
      tailSteps.1 2
    have triangleBound : Data.Gaussian.Norm.Basic.normSq (Stokes.edgeArea ((Stokes.PrimitivePoint.sub (values middle))
      (values first)) ((Stokes.PrimitivePoint.sub (values next)) (values middle))) ≤
        (4 * density ^ 2 * width ^ 2) * (middle - first) ^ 2 := by
      have normalized := triangle.trans_eq
        (show 4 * (density * (middle - first) ^ 2) * (density * (next - middle) ^ 2) =
          (4 * density ^ 2 * (middle - first) ^ 2) * (next - middle) ^ 2 by ring1)
      exact normalized.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct widthLe
        (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          (Fraction.Order.Arithmetic.sq_nonneg_direct density))
          (Fraction.Order.Arithmetic.sq_nonneg_direct (middle - first)))).trans_eq (by ring1))
    have joined := Norm.Weighted.normSq_add_weighted
      (Fraction.Order.Arithmetic.sub_nonneg_direct lowerStep) (Fraction.Order.Arithmetic.sub_nonneg_direct middleLast)
        triangleBound tail
    have identity : rawArea values first (middle :: fine) - rawArea
      values first (next :: coarse) =
        Stokes.edgeArea ((Stokes.PrimitivePoint.sub (values middle)) (values first)) ((Stokes.PrimitivePoint.sub (values
          next)) (values middle)) +
          (rawArea values middle fine - rawArea values middle (next ::
            coarse)) := by
      rw [← triangle_identity]
      dsimp only [rawArea]
      ring1
    exact (congrArg Data.Gaussian.Norm.Basic.normSq identity).trans_le (joined.trans_eq (by ring1))
  | @duplicate first last coarse fine rest ih =>
    change Data.Gaussian.Norm.Basic.normSq ((Stokes.edgeArea (values first) (values first) +
      rawArea
      values first fine) - rawArea values first coarse) ≤ _
    rw [edge_self, _root_.zero_add]
    exact ih lower upper steps

/-- Two original ordered parameter chains with shared endpoints obey the common-width source-area comparison.

The comparison retains both chains and constructs a common refinement; its sixteenfold bound keeps density, mesh width
and endpoint span as separate squared factors. -/
theorem resampling_bound (values : Coordinate → Stokes.PrimitivePoint) {density width :
  Coordinate}
    (increment : ∀ a b, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
      (PrimitiveAreaBounds.PrimitivePoint.Bounded ((Stokes.PrimitivePoint.sub (values b)) (values a))) (density * (b -
        a) ^ 2))
    {first last : Coordinate} {left right : List Coordinate}
    (leftChain : Chain first left last) (rightChain : Chain first right
      last)
    (lower : 0 ≤ first) (upper : last ≤ 1)
    (leftSteps : widths first left width) (rightSteps : widths first
      right width) :
    Data.Gaussian.Norm.Basic.normSq (rawArea values first left - rawArea
      values first right) ≤
      16 * density ^ 2 * width ^ 2 * (last - first) ^ 2 := by
  let shared := common first last left right leftChain rightChain
  have a := refinement_bound values increment shared.left lower upper leftSteps
  have b := refinement_bound values increment shared.right lower upper rightSteps
  have estimate := (Norm.Bounds.normSq_sub_le_two
    (rawArea values first shared.points - rawArea values first right)
    (rawArea values first shared.points - rawArea values first
      left)).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct b a) (by
        decide))
  have equal : (rawArea values first shared.points - rawArea values
    first right) -
      (rawArea values first shared.points - rawArea values first left) =
        rawArea values first left - rawArea values first right := by
          ring1
  exact (congrArg Data.Gaussian.Norm.Basic.normSq equal).symm.trans_le (estimate.trans_eq (by ring1))

end

section
open Purelib.Data.List
open Purelib.Integration.Path
/-- An indexed monotone parameter family gives the exact ordered list chain of its successor vertices. -/
theorem chain_ofFn {count : Nat} (parameters : Fin (count + 1) → Coordinate)
    (ordered : ∀ edge : Fin count, parameters edge.castSucc ≤ parameters edge.succ) :
    Chain (parameters 0) (List.ofFn (fun edge : Fin count => parameters edge.succ))
      (parameters (Fin.last count)) := by
  induction count with
  | zero => exact .nil _
  | succ count ih =>
    rw [OfFn.Basic.ofFn_succ]
    exact .cons (ordered 0) (ih (fun vertex => parameters vertex.succ) (fun edge => ordered edge.succ))

/-- Indexed edge-width bounds give the same common width bound for the exact successor-vertex list. -/
theorem widths_ofFn {count : Nat} (parameters : Fin (count + 1) → Coordinate) (width :
  Coordinate)
    (bounded : ∀ edge : Fin count, parameters edge.succ - parameters edge.castSucc ≤ width) :
    widths (parameters 0) (List.ofFn (fun edge : Fin count => parameters edge.succ)) width := by
  induction count with
  | zero => trivial
  | succ count ih =>
    rw [OfFn.Basic.ofFn_succ]
    exact ⟨bounded 0, ih (fun vertex => parameters vertex.succ) (fun edge => bounded edge.succ)⟩

end

open Purelib.Algebra in
open Purelib.Data.List in
open Purelib.Integration.Path in
open Purelib.Riemann.Periods in
open Purelib.Topology.Polygon in
/-- The list area of the exact indexed parameter family equals its original finite primitive path area. -/
theorem rawArea_ofFn (values : Coordinate → Stokes.PrimitivePoint) {count : Nat}
    (parameters : Fin (count + 1) → Coordinate) :
    rawArea values (parameters 0) (List.ofFn (fun edge : Fin count => parameters edge.succ)) =
      CenteredBilinearPath.area (fun vertex => values (parameters vertex)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [OfFn.Basic.ofFn_succ, rawArea, ih (fun vertex => parameters vertex.succ)]
    exact (FiniteSum.Fin.sumFin_succ
      (fun edge : Fin (count + 1) => Stokes.edgeArea (values (parameters edge.castSucc)) (values (parameters
        edge.succ)))).symm

end Purelib.Integration.Path.Dyadic.SourceResampling
