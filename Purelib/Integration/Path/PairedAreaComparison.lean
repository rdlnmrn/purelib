module

meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes

import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Integration.Path.PairedIncrementArea
public import Purelib.Integration.Path.PairedIncrementComparison
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! Actual cached two-component comparisons. The original componentwise
PrimitivePoint metric and scalar constants remain distinct from Gaussian
mixed-value comparison. All later payment/readback uses the retained pair
list and the two executable summaries. -/
namespace Purelib.Integration.Path.PairedAreaComparison

open Purelib.Data.List

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)

open Purelib.Data.Rat.Fraction (Rational)

/-- An ordered list of original paired primitive readings. -/
@[reducible, expose] def Pairs := List (PrimitivePoint × PrimitivePoint)
/-- The retained pair list is exactly the original canonical pair list. -/
@[reducible, expose] def PairIdentity (canonical retained : Pairs) : Prop := retained = canonical
/-- The retained first readings are the first projection of the original pairs. -/
@[reducible, expose] def FirstIdentity (pairs : Pairs) (retained : List PrimitivePoint) : Prop := retained = pairs.map
  Prod.fst
/-- The retained second readings are the second projection of the original pairs. -/
@[reducible, expose] def SecondIdentity (pairs : Pairs) (retained : List PrimitivePoint) : Prop := retained = pairs.map
  Prod.snd
section
open Purelib.Data.Rat
open Purelib.Riemann.Readings
/-- Every original pair's two-coordinate difference satisfies the common squared-norm error bound. -/
@[reducible, expose] def PairErrors (pairs : Pairs) (error : Fraction.Rational) : Prop :=
  ∀ pair ∈ pairs, PrimitiveAreaBounds.PrimitivePoint.Bounded (pair.1.sub pair.2) error
/-- Every original first reading satisfies the common two-coordinate bound. -/
@[reducible, expose] def FirstBounds (pairs : Pairs) (bound : Fraction.Rational) : Prop :=
  ∀ pair ∈ pairs, PrimitiveAreaBounds.PrimitivePoint.Bounded pair.1 bound
/-- Every original second reading satisfies the common two-coordinate bound. -/
@[reducible, expose] def SecondBounds (pairs : Pairs) (bound : Fraction.Rational) : Prop :=
  ∀ pair ∈ pairs, PrimitiveAreaBounds.PrimitivePoint.Bounded pair.2 bound
end

open Purelib.Data.Rat in
/-- Sixteen times the fourth power of original pair count times error and magnitude bounds. -/
@[reducible, expose] def BoundSpecification (count : Nat) (error bound : Fraction.Rational) : Rational :=
  16 * (count : Fraction.Rational)^4 * error * bound

/-- Select the paired reading or the reading conjugating only its first coordinate. -/
inductive View where
  /-- Retain the original first and second coordinates without conjugation. -/ | paired
  /-- Conjugate the original first coordinate and retain the original second coordinate. -/ | conjugate

open Purelib.Data.Gaussian in
/-- Form the selected two-coordinate reading from the two original Gaussian values. -/
@[expose] def point (view : View) (left right : Basic.Canonical) : PrimitivePoint :=
  match view with
  | .paired => ⟨left, right⟩
  | .conjugate => ⟨Data.Gaussian.Basic.conj left, right⟩

/-- Negate both coordinates of the original primitive reading. -/
@[expose] def negative (value : PrimitivePoint) : PrimitivePoint := ⟨-value.left, -value.right⟩

open Purelib.Integration.Path in
/-- Negating every original reading negates the retained total. -/
private theorem negative_total {α : Type} (value : α → PrimitivePoint) (entries : List α) :
    PairedIncrementArea.total (entries.map (fun entry => negative (value entry))) =
      negative (PairedIncrementArea.total (entries.map value)) := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
      change (negative (value head)).add (PairedIncrementArea.total (tail.map _)) =
        negative ((value head).add (PairedIncrementArea.total (tail.map value)))
      rw [ih]
      apply congrArg₂ PrimitivePoint.mk <;> simp only [negative, PrimitivePoint.add] <;> ring1

open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- Negating both coordinates of every original reading preserves signed paired area. -/
theorem negative_area {α : Type} (value : α → PrimitivePoint) (entries : List α) :
    PairedIncrementArea.area (entries.map (fun entry => negative (value entry))) = PairedIncrementArea.area (entries.map
      value) := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
      rw [List.map_cons, List.map_cons, PairedAreaBlocks.area_cons,
        PairedAreaBlocks.area_cons, ih, negative_total]
      apply congrArg (fun scalar => scalar + PairedIncrementArea.area (tail.map value))
      simp only [Stokes.edgeArea, negative]
      ring1

/-- Negating the original primitive reading twice returns that reading. -/
private theorem negative_negative (value : PrimitivePoint) : negative (negative value) = value := by
  cases value with
  | mk left right =>
      change PrimitivePoint.mk (-(-left)) (-(-right)) = _
      rw [neg_neg, neg_neg]

/-- Negating the already-negated mapped readings returns the original mapped list. -/
theorem negative_map {α : Type} (value : α → PrimitivePoint) (entries : List α) :
    (entries.map (fun entry => negative (value entry))).map negative = entries.map value := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
      change negative (negative (value head)) :: _ = value head :: _
      rw [negative_negative]
      exact congrArg (List.cons (value head)) ih

/-- Zipping the two original mapped reading lists equals mapping their paired readings. -/
theorem zip_maps {α : Type} (first second : α → PrimitivePoint) (entries : List α) :
    List.zip (entries.map first) (entries.map second) = entries.map (fun entry => (first entry, second entry)) := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
      change (first head, second head) :: _ = (first head, second head) :: _
      exact congrArg (List.cons (first head, second head)) ih

section
open Purelib.Integration.Path
/-- Transport a retained summary across the supplied exact equality of original entry lists. -/
@[expose] def reindexSummary {first second : List PrimitivePoint} (equal : first = second) (summary :
  PairedIncrementArea.Summary first) : PairedIncrementArea.Summary second :=
  equal ▸ summary

/-- Transporting a retained summary preserves its cached area. -/
theorem reindexSummary_area {first second : List PrimitivePoint} (equal : first = second) (summary :
  PairedIncrementArea.Summary first) :
    (reindexSummary equal summary).areaValue = summary.areaValue := by
  cases equal
  rfl

/-- Negate a retained summary's cached total while preserving its cached area.

The returned summary is indexed by the exact coordinatewise-negated original entries, with both cache equalities
certified. -/
@[expose] def negateSummary {entries : List PrimitivePoint} (summary : PairedIncrementArea.Summary entries) :
  PairedIncrementArea.Summary (entries.map negative) :=
  { totalValue := negative summary.totalValue
    total_eq := by
      rw [summary.total_eq]
      have copied := negative_total id entries
      change PairedIncrementArea.total (entries.map negative) =
        negative (PairedIncrementArea.total (entries.map id)) at copied
      rw [Map.map_id] at copied
      exact copied.symm
    areaValue := summary.areaValue
    area_eq := by
      rw [summary.area_eq]
      have copied := negative_area id entries
      change PairedIncrementArea.area (entries.map negative) = PairedIncrementArea.area (entries.map id) at copied
      rw [Map.map_id] at copied
      exact copied.symm }

end

set_option genInjectivity false in
open Purelib.Integration.Path in
/-- A retained primitive-reading list and summary with its exact original-list identity.

The summary remains indexed by the retained entries, so cached area readback uses the same observations. -/
structure Observation (canonical : List PrimitivePoint) where
  /-- The retained primitive-reading list. -/ entries : List PrimitivePoint
  /-- The retained entries equal the exact original canonical list. -/ entries_eq : entries = canonical
  /-- The cached summary indexed by the retained entries. -/ summary : PairedIncrementArea.Summary entries

constructive_injectivity Observation

namespace Observation

open Purelib.Integration.Path in
/-- Build an observation by retaining the original entries and their freshly computed paired summary. -/
@[expose] def realize (canonical : List PrimitivePoint) : Observation canonical :=
  ⟨canonical, rfl, PairedIncrementArea.Summary.build canonical⟩

/-- Transport the retained observation's original-list identity while reusing its entries and summary. -/
@[expose] def reindex {first second : List PrimitivePoint} (equal : first = second) (observation : Observation first) :
  Observation second :=
  { entries := observation.entries
    entries_eq := observation.entries_eq.trans equal
    summary := observation.summary }

/-- Negate the retained observation entries and transport their exact original-list identity. -/
@[expose] def negate {entries : List PrimitivePoint} (observation : Observation entries) : Observation (entries.map
  negative) :=
  { entries := observation.entries.map negative
    entries_eq := congrArg (List.map negative) observation.entries_eq
    summary := negateSummary observation.summary }

open Purelib.Integration.Path in
/-- The observation's cached area equals the area of the original canonical entries. -/
theorem area_readback {entries : List PrimitivePoint} (observation : Observation entries) :
    observation.summary.areaValue = PairedIncrementArea.area entries :=
  observation.summary.area_eq.trans (congrArg PairedIncrementArea.area observation.entries_eq)

end Observation

open Purelib.Data.Rat in
/-- The original pairwise error and separate first and second magnitude bounds with nonnegative parameters.

All pointwise certificates range over the exact retained pair list used by the area comparison. -/
structure Evidence (pairs : Pairs) (error bound : Fraction.Rational) where
  /-- The retained common pairwise error bound is nonnegative. -/ error_nonnegative : 0 ≤ error
  /-- The retained common magnitude bound is nonnegative. -/ bound_nonnegative : 0 ≤ bound
  /-- The original pairwise differences satisfy the retained error bound. -/ errors : PairErrors pairs error
  /-- The original first readings satisfy the retained magnitude bound. -/ first_bounded : FirstBounds pairs bound
  /-- The original second readings satisfy the retained magnitude bound. -/ second_bounded : SecondBounds pairs bound

set_option genInjectivity false in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- A retained area comparison keeping the original pairs, both projected summaries, residual and quantitative bound.

The identities connect every cached list and value to the original pairs; the certificate bounds the squared norm of
that exact residual. -/
structure Cached (canonical : Pairs) (error bound : Fraction.Rational) where
  /-- The retained original paired-reading list. -/ pairs : Pairs
  /-- The retained pairs equal the original canonical pairs. -/ pairs_eq : PairIdentity canonical pairs
  /-- The retained first projected reading list. -/ first : List PrimitivePoint
  /-- The retained first list is the first projection of these exact pairs. -/ first_eq : FirstIdentity pairs first
  /-- The retained second projected reading list. -/ second : List PrimitivePoint
  /-- The retained second list is the second projection of these exact pairs. -/ second_eq : SecondIdentity pairs second
  /-- The cached summary indexed by the retained first list. -/ firstSummary : PairedIncrementArea.Summary first
  /-- The cached summary indexed by the retained second list. -/ secondSummary : PairedIncrementArea.Summary second
  /-- The error and separate magnitude evidence for the exact retained pairs. -/ evidence : Evidence pairs error bound
  /-- The cached signed difference of the two retained areas. -/ residual : Basic.Canonical
  /-- The residual is the first cached area minus the second cached area. -/ residual_eq : residual =
    firstSummary.areaValue - secondSummary.areaValue
  /-- The cached squared-norm comparison bound. -/ areaBound : Fraction.Rational
  /-- The cached bound equals the specification at the retained pair count. -/ areaBound_eq : areaBound =
    BoundSpecification pairs.length error bound
  /-- The exact cached residual satisfies the cached squared-norm bound. -/ bounded : Data.Gaussian.Norm.Basic.normSq
    residual ≤ areaBound

constructive_injectivity Cached

namespace Cached

variable {pairs : Pairs} {error bound : Purelib.Data.Rat.Fraction.Rational}

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- Build the original pair comparison while reusing the two supplied projected summaries.

The exact residual and count-based bound are cached once, with the original error and separate first/second magnitude
evidence retained. -/
@[expose] def realizeSupplied (pairs : Pairs) (error bound : Fraction.Rational)
    (firstSummary : PairedIncrementArea.Summary (pairs.map Prod.fst)) (secondSummary : PairedIncrementArea.Summary
      (pairs.map Prod.snd))
    (errorNonnegative : 0 ≤ error) (boundNonnegative : 0 ≤ bound)
    (errors : PairErrors pairs error) (firstBound : FirstBounds pairs bound)
    (secondBound : SecondBounds pairs bound) : Cached pairs error bound :=
  let first := pairs.map Prod.fst
  let second := pairs.map Prod.snd
  let residual := firstSummary.areaValue - secondSummary.areaValue
  let areaBound := BoundSpecification pairs.length error bound
  have bounded : Data.Gaussian.Norm.Basic.normSq residual ≤ areaBound := by
    change Data.Gaussian.Norm.Basic.normSq (firstSummary.areaValue - secondSummary.areaValue) ≤
      BoundSpecification pairs.length error bound
    rw [firstSummary.area_eq, secondSummary.area_eq]
    exact PairedIncrementComparison.area_difference_bound pairs
      errorNonnegative boundNonnegative errors firstBound secondBound
  { pairs := pairs
    pairs_eq := rfl
    first := first
    first_eq := rfl
    second := second
    second_eq := rfl
    firstSummary := firstSummary
    secondSummary := secondSummary
    evidence := ⟨errorNonnegative, boundNonnegative, errors, firstBound, secondBound⟩
    residual := residual
    residual_eq := rfl
    areaBound := areaBound
    areaBound_eq := rfl
    bounded := bounded }

open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- Build the retained comparison from the exact original pair list and its supplied pointwise evidence.

Both projected summaries are computed once; the residual and explicit fourth-power count bound are retained with their
specification equalities. -/
@[expose] def realize (pairs : Pairs) (error bound : Fraction.Rational)
    (errorNonnegative : 0 ≤ error) (boundNonnegative : 0 ≤ bound)
    (errors : PairErrors pairs error) (firstBound : FirstBounds pairs bound)
    (secondBound : SecondBounds pairs bound) : Cached pairs error bound :=
  realizeSupplied pairs error bound (PairedIncrementArea.Summary.build (pairs.map Prod.fst))
    (PairedIncrementArea.Summary.build (pairs.map Prod.snd)) errorNonnegative boundNonnegative errors firstBound
      secondBound

open Purelib.Integration.Path in
/-- Read the cached residual as the original first projected area minus the original second projected area. -/
theorem residual_readback (comparison : Cached pairs error bound) :
    comparison.residual = PairedIncrementArea.area (pairs.map Prod.fst) - PairedIncrementArea.area (pairs.map Prod.snd)
      := by
  rw [comparison.residual_eq, comparison.firstSummary.area_eq, comparison.secondSummary.area_eq,
    comparison.first_eq, comparison.second_eq, comparison.pairs_eq]

/-- Read the cached bound as the exact specification for the original pair count and bounds. -/
theorem bound_readback (comparison : Cached pairs error bound) :
    comparison.areaBound = BoundSpecification pairs.length error bound := by
  rw [comparison.areaBound_eq, comparison.pairs_eq]

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Transport a retained comparison's residual bound through payment of its exact cached area bound. -/
theorem pay (comparison : Cached pairs error bound) {target : Fraction.Rational}
    (paid : comparison.areaBound ≤ target) : Data.Gaussian.Norm.Basic.normSq comparison.residual ≤ target :=
  comparison.bounded.trans paid

end Cached
end Purelib.Integration.Path.PairedAreaComparison

end
