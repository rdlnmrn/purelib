module
import Purelib.Data.List.Reverse
import Purelib.Data.Gaussian.Norm.Sum.Basic
-- The existing Walks/FromStates/BranchCutLifts/CellularHomology public path
-- already retains the finite-sum owner; this proof dependency stays ordinary.
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.List.OfFn.Basic
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Filter
import Purelib.Data.List.Search
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Polynomial.Geometry.Grid.ClearGrid
public import Purelib.Polynomial.Geometry.Grid.Walks
public import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Polynomial.Geometry.Grid.Winding
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Tactic.Ring

open Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell Interval)

/-!
# Actual face loops and exact perimeter cancellation on a clear grid

Every cell boundary is a four-edge, endpoint-closed walk using the retained
adjacent intervals and line certificates.  The sum of arbitrary oriented
edge values over all faces is the subdivided exterior perimeter.  This is
finite incidence algebra; it assumes neither primitive gluing nor a flat
square-root sheet assignment.
-/

public section

section

open Purelib.Polynomial.Geometry.Grid

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial

universe u

namespace Purelib.Polynomial.Geometry.Grid.CellBoundary

/-- Sum Gaussian values over an explicit finite list.

The recursion preserves list order and uses zero for the empty list. -/
@[expose] def sumValues {Alpha : Type u} (value : Alpha → Gaussian.Basic.Canonical) : List Alpha →
  Gaussian.Basic.Canonical
  | [] => 0
  | head :: tail => value head + sumValues value tail

/-- Complementary Boolean selections partition the displayed Gaussian sum.

Both filters preserve the same source occurrence order. Every head contributes
to exactly one side, while scalar addition transports the unchanged tail. -/
theorem sum_filter_partition {Item : Type u} (keep : Item → Bool)
    (value : Item → Gaussian.Basic.Canonical) (items : List Item) :
    sumValues value (items.filter keep) + sumValues value (items.filter (fun item => !(keep item))) =
      sumValues value items := by
  induction items with
  | nil => exact Gaussian.Basic.zero_add _
  | cons head tail ih =>
      cases selected : keep head with
      | false =>
          rw [List.Filter.filter_cons_of_neg (by rw [selected]; intro impossible; nomatch impossible),
            List.Filter.filter_cons_of_pos (by rw [selected]; rfl)]
          change sumValues value (tail.filter keep) + (value head +
            sumValues value (tail.filter (fun item => !(keep item)))) =
              value head + sumValues value tail
          rw [← ih]
          ring1
      | true =>
          rw [List.Filter.filter_cons_of_pos selected,
            List.Filter.filter_cons_of_neg (by rw [selected]; intro impossible; nomatch impossible)]
          change (value head + sumValues value (tail.filter keep)) +
            sumValues value (tail.filter (fun item => !(keep item))) =
              value head + sumValues value tail
          rw [← ih]
          ring1

/-- Disjoint Boolean selections split their union's Gaussian sum.

Each source occurrence contributes to at most one selected list. The retained
union predicate and both filtered lists use the same displayed source spine. -/
private theorem sum_filter_or {Item : Type u} (first second : Item → Bool)
    (disjoint : ∀ item, first item = true → second item = true → False)
    (value : Item → Gaussian.Basic.Canonical) (items : List Item) :
    sumValues value (items.filter (fun item => first item || second item)) =
      sumValues value (items.filter first) + sumValues value (items.filter second) := by
  induction items with
  | nil => exact (Gaussian.Basic.zero_add _).symm
  | cons head tail ih =>
      cases left : first head <;> cases right : second head
      · rw [List.Filter.filter_cons_of_neg (by rw [left, right]; intro impossible; nomatch impossible),
          List.Filter.filter_cons_of_neg (by rw [left]; intro impossible; nomatch impossible),
          List.Filter.filter_cons_of_neg (by rw [right]; intro impossible; nomatch impossible)]
        exact ih
      · rw [List.Filter.filter_cons_of_pos (by rw [left, right]; rfl),
          List.Filter.filter_cons_of_neg (by rw [left]; intro impossible; nomatch impossible),
          List.Filter.filter_cons_of_pos right]
        change value head + sumValues value (tail.filter (fun item => first item || second item)) =
          sumValues value (tail.filter first) + (value head + sumValues value (tail.filter second))
        rw [ih]
        ring1
      · rw [List.Filter.filter_cons_of_pos (by rw [left, right]; rfl),
          List.Filter.filter_cons_of_pos left,
          List.Filter.filter_cons_of_neg (by rw [right]; intro impossible; nomatch impossible)]
        change value head + sumValues value (tail.filter (fun item => first item || second item)) =
          (value head + sumValues value (tail.filter first)) + sumValues value (tail.filter second)
        rw [ih]
        ring1
      · exact (disjoint head left right).elim

/-- A pairwise disjoint Boolean family partitions its selected Gaussian sum.

The label list determines the family order and the source list retains its
occurrences. Disjointness applies to those same entries and each label's
original predicate. -/
theorem sum_filter_family {Item Label : Type u} (keep : Label → Item → Bool)
    (value : Item → Gaussian.Basic.Canonical) (labels : List Label)
    (disjoint : labels.Pairwise (fun first second => ∀ item,
      keep first item = true → keep second item = true → False)) (items : List Item) :
    sumValues value (items.filter (fun item => labels.any (fun label => keep label item))) =
      sumValues (fun label => sumValues value (items.filter (keep label))) labels := by
  induction labels with
  | nil =>
      change sumValues value (items.filter (fun _ => false)) = 0
      rw [List.Filter.filter_false]
      rfl
  | cons head tail ih =>
      have separate : ∀ item, keep head item = true → tail.any (fun label => keep label item) = true → False := by
        intro item kept found
        obtain ⟨label, member, other⟩ := List.Search.any_witness (fun label => keep label item) tail found
        exact (List.pairwise_cons.mp disjoint).1 label member item kept other
      change sumValues value (items.filter (fun item => keep head item || tail.any (fun label => keep label item))) = _
      rw [sum_filter_or _ _ separate, ih (List.pairwise_cons.mp disjoint).2]
      rfl

/-- The finite Gaussian sum distributes over pointwise addition. -/
theorem sumValues_add {Alpha : Type u} (first second : Alpha → Gaussian.Basic.Canonical) (entries : List Alpha) :
    sumValues (fun entry => first entry + second entry) entries =
      sumValues first entries + sumValues second entries := by
  induction entries with
  | nil => change (0 : Gaussian.Basic.Canonical) = 0 + 0; ring1
  | cons head tail ih => simp only [sumValues, ih, -eq_self, -iff_self]; ring1

/-- The finite Gaussian sum distributes over pointwise subtraction. -/
theorem sumValues_sub {Alpha : Type u} (first second : Alpha → Gaussian.Basic.Canonical) (entries : List Alpha) :
    sumValues (fun entry => first entry - second entry) entries =
      sumValues first entries - sumValues second entries := by
  induction entries with
  | nil => change (0 : Gaussian.Basic.Canonical) = 0 - 0; ring1
  | cons head tail ih => simp only [sumValues, ih, -eq_self, -iff_self]; ring1

/-- Summing zero over a finite list gives zero. -/
theorem sumValues_zero {Alpha : Type u} (entries : List Alpha) : sumValues (fun _ => (0 :
  Gaussian.Basic.Canonical)) entries = 0 := by
  induction entries with
  | nil => rfl
  | cons head tail ih => simp only [sumValues, ih, -eq_self, -iff_self]; ring1

/-- Negating every summand negates the finite Gaussian sum. -/
theorem sumValues_neg {Alpha : Type u} (value : Alpha → Gaussian.Basic.Canonical) (entries : List Alpha) :
    sumValues (fun entry => -value entry) entries = -sumValues
      value entries := by
  induction entries with
  | nil => change (0 : Gaussian.Basic.Canonical) = -0; ring1
  | cons head tail ih => simp only [sumValues, ih, -eq_self, -iff_self]; ring1

/-- Pointwise equality on the displayed list preserves its finite sum. -/
theorem sumValues_congr {Alpha : Type u} (first second : Alpha → Gaussian.Basic.Canonical) (entries : List Alpha)
    (equal : ∀ entry ∈ entries, first entry = second entry) : sumValues first entries =
      sumValues second entries := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
      rw [sumValues, sumValues, equal head List.mem_cons_self, ih
        (fun entry member => equal entry (List.mem_cons_of_mem _ member))]

/-- Summing over a mapped list equals summing the composite value function. -/
theorem sumValues_map {Alpha : Type u} {Beta : Type u} (value : Beta → Gaussian.Basic.Canonical) (transform : Alpha →
  Beta) (entries : List Alpha) :
    sumValues value (entries.map transform) = sumValues (fun entry
      => value (transform entry)) entries := by
  induction entries with
  | nil => rfl
  | cons head tail ih => exact congrArg (fun rest => value (transform head) + rest) ih

/-- Concatenating lists adds their finite Gaussian sums. -/
theorem sumValues_append {Alpha : Type u} (value : Alpha → Gaussian.Basic.Canonical) (first second : List Alpha) :
    sumValues value (first ++ second) = sumValues value first +
      sumValues value second := by
  induction first with
  | nil =>
      change sumValues value second = 0 + sumValues value second;
      ring1
  | cons head tail ih =>
      simp only [List.cons_append, sumValues, ih, -eq_self, -iff_self];
      ring1

/-- Summing a flattened family equals the finite sum of the individual list sums.

The original flatMap order concatenates the head's retained list with the
remaining lists. Scalar addition transports the tail equality directly. -/
theorem sumValues_flatMap {Alpha Beta : Type u} (value : Beta → Gaussian.Basic.Canonical) (transform : Alpha → List
  Beta) (entries : List Alpha) :
    sumValues value (entries.flatMap transform) = sumValues (fun
      entry => sumValues value (transform entry)) entries := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
      rewrite [List.Flatten.flatMap_cons, sumValues_append]
      change sumValues value (transform head) +
          sumValues value (tail.flatMap transform) =
        sumValues value (transform head) +
          sumValues
            (fun entry => sumValues value (transform entry)) tail
      exact congrArg (fun remaining =>
        sumValues value (transform head) + remaining) ih

/-- The two explicit finite list summations commute. -/
theorem sumValues_swap {Alpha Beta : Type u} (value : Alpha → Beta → Gaussian.Basic.Canonical) (first : List Alpha)
  (second : List Beta) :
    sumValues (fun left => sumValues (value left) second) first =
      sumValues (fun right => sumValues (fun left => value left
        right) first) second := by
  induction first with
  | nil => exact (sumValues_zero second).symm
  | cons head tail ih =>
      change sumValues (value head) second + sumValues (fun left
        => sumValues (value left) second) tail = _
      rw [ih, ← sumValues_add]
      rfl

end Purelib.Polynomial.Geometry.Grid.CellBoundary

section
open Purelib.Data.Gaussian
open Purelib.Polynomial

namespace Purelib.Polynomial.Geometry.Grid.CellBoundary

/-- A permutation preserves the Gaussian sum over a displayed list.

The retained permutation moves only the ordered occurrences. Scalar addition
handles each adjacent swap and preserves the same finite values. -/
theorem sumValues_perm {Item : Type u} (value : Item → Basic.Canonical) {first last : List Item}
    (order : List.Perm first last) : sumValues value first =
      sumValues value last := by
  induction order with
  | nil => rfl
  | cons head order ih => exact congrArg (value head + ·) ih
  | swap first last tail => change value _ + (value _ + _) = value _ + (value _ + _); ring1
  | trans first last ihFirst ihLast => exact ihFirst.trans ihLast

/-- A filtered Gaussian sum is the original sum with zero at rejected entries.

The Boolean predicate retains or removes each displayed head. The unchanged
tail contributes the same recursively accumulated scalar sum. -/
theorem sumValues_filter {Item : Type u} (keep : Item → Bool) (value : Item → Basic.Canonical) (items : List Item) :
    sumValues value (items.filter keep) = sumValues (fun item =>
      if keep item then value item else 0) items := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      cases selected : keep head with
      | false =>
          have rejected : keep head ≠ true := by rw [selected]; intro impossible; nomatch impossible
          rw [List.Filter.filter_cons_of_neg rejected]
          change sumValues value (tail.filter keep) =
            (if keep head then value head else 0) + sumValues (fun item => if keep item then value item else 0) tail
          rw [if_neg rejected, Basic.zero_add]
          exact ih
      | true =>
          rw [List.Filter.filter_cons_of_pos selected]
          change value head + sumValues value (tail.filter keep) =
            (if keep head then value head else 0) + sumValues (fun item => if keep item then value item else 0) tail
          rw [if_pos selected]
          exact congrArg (value head + ·) ih

end Purelib.Polynomial.Geometry.Grid.CellBoundary

end

namespace Purelib.Polynomial.Geometry.Grid.CellBoundary

open Purelib.Algebra.FiniteSum.Fin (sumFin) in
open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Polynomial in
/-- Summing the bounded-index list agrees with its finite indexed sum.

The original ofFn enumeration retains every supplied finite index.
Its structural successor decomposition matches the finite sum decomposition. -/
theorem sumValues_ofFn {count : Nat} (values : Fin count → Basic.Canonical) :
    sumValues (fun index => values index) (List.ofFn fun index : Fin count => index) = sumFin
      values := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [OfFn.Basic.ofFn_succ, FiniteSum.Fin.sumFin_succ]
      change values 0 + sumValues values (List.ofFn (fun index : Fin count => index.succ)) =
        _
      rw [← show (List.ofFn fun index : Fin count => index).map Fin.succ =
        List.ofFn (fun index : Fin count => index.succ) from OfFn.Basic.map_ofFn]
      rw [sumValues_map, ih]

end Purelib.Polynomial.Geometry.Grid.CellBoundary

section
open Purelib.Algebra
open Purelib.Data.Gaussian

namespace Purelib.Polynomial.Geometry.Grid.CellBoundary

/-- A filtered Gaussian sum is its masked finite sum over the original list.

Every retained position reads the same bounded list entry. Rejected positions
contribute zero, and the filter preserves the original occurrence order. -/
theorem sumValues_filter_eq_sumFin {Item : Type} (items : List Item)
    (keep : Item → Bool) (value : Item → Basic.Canonical) :
    sumValues value (items.filter keep) =
      FiniteSum.Fin.sumFin (fun position : Fin items.length =>
        if keep (items[position.val]'position.isLt) then
          value (items[position.val]'position.isLt) else 0) := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      rw [FiniteSum.Fin.sumFin_succ]
      cases selected : keep head with
      | false =>
          have rejected : keep head ≠ true := by rw [selected]; intro impossible; nomatch impossible
          rw [List.Filter.filter_cons_of_neg rejected]
          change sumValues value (tail.filter keep) =
            (if keep head then value head else 0) +
              FiniteSum.Fin.sumFin (fun position : Fin tail.length =>
                if keep (tail[position.val]'position.isLt) then
                  value (tail[position.val]'position.isLt) else 0)
          rw [if_neg rejected, Basic.zero_add]
          exact ih
      | true =>
          rw [List.Filter.filter_cons_of_pos selected]
          change value head + sumValues value (tail.filter keep) =
            (if keep head then value head else 0) +
              FiniteSum.Fin.sumFin (fun position : Fin tail.length =>
                if keep (tail[position.val]'position.isLt) then
                  value (tail[position.val]'position.isLt) else 0)
          rw [if_pos selected]
          exact congrArg (value head + ·) ih

/-- Transport the masked filtered sum to an exact retained list length.

The supplied equality changes only the finite index type. Each value and
selection still comes from the same bounded position in the original list. -/
theorem sumValues_filter_eq_sumFin_count {Item : Type} (items : List Item)
    (keep : Item → Bool) (value : Item → Basic.Canonical) {count : Nat}
    (equal : items.length = count) :
    sumValues value (items.filter keep) =
      FiniteSum.Fin.sumFin (fun position : Fin count =>
        if keep (items[position.val]'(by rw [equal]; exact position.isLt)) then
          value (items[position.val]'(by rw [equal]; exact position.isLt)) else 0) := by
  subst count
  exact sumValues_filter_eq_sumFin items keep value

end Purelib.Polynomial.Geometry.Grid.CellBoundary

end

section

variable {Alpha : Type u} {key : Alpha → Fraction.Rational}

namespace Purelib.Polynomial.Geometry.Grid.CellBoundary.Interval

/-- Read the last entry of a list with a supplied first entry.

The first entry is returned when the remaining list is empty. -/
@[expose] def lastFrom (first : Alpha) : List Alpha → Alpha
  | [] => first
  | next :: rest => lastFrom next rest

/-- Differences across adjacent ordered intervals telescope to the first and last values. -/
theorem sum_differences (value : Alpha → Gaussian.Basic.Canonical) (first : Alpha) (rest : List Alpha)
    (ordered : (first :: rest).Pairwise (fun left right => key left < key right)) :
    sumValues (fun interval => value interval.lower - value interval.upper)
      (Interval.adjacent (first :: rest) ordered) =
      value first - value (lastFrom first rest) := by
  induction rest generalizing first with
  | nil => change (0 : Gaussian.Basic.Canonical) = value first - value first; ring1
  | cons next rest ih =>
      change value first - value next +
        sumValues (fun interval => value interval.lower - value interval.upper)
          (Interval.adjacent (next :: rest) _) = _
      rw [ih]
      change value first - value next + (value next - value (lastFrom next rest)) =
        value first - value (lastFrom next rest)
      ring1

end Purelib.Polynomial.Geometry.Grid.CellBoundary.Interval

end

namespace Purelib.Polynomial.Geometry.Grid.CellBoundary

set_option genInjectivity false in
/-- Values on positively oriented horizontal and vertical grid edges.  A
reversed traversal consumes their negatives, not an independent reading. -/
structure EdgeValues where
  /-- The value of a positively oriented horizontal edge, indexed by its two abscissae and ordinate. -/ horizontal :
    Fraction.Rational → Fraction.Rational → Fraction.Rational → Gaussian.Basic.Canonical
  /-- The value of a positively oriented vertical edge, indexed by its abscissa and two ordinates. -/ vertical :
    Fraction.Rational → Fraction.Rational → Fraction.Rational → Gaussian.Basic.Canonical

constructive_injectivity EdgeValues

end Purelib.Polynomial.Geometry.Grid.CellBoundary

section

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box}

namespace Purelib.Polynomial.Geometry.Grid.CellBoundary.EdgeValues

/-- Add the four oriented edge values around a grid cell.

Bottom and right are positive; top and left use the negatives of their stored positive-direction readings. -/
@[expose] def cellBoundary (values : EdgeValues) (cell : ClearGrid.Cell
  polynomial ambient) : Gaussian.Basic.Canonical :=
  values.horizontal cell.box.xLower cell.box.xUpper cell.box.yLower +
    values.vertical cell.box.xUpper cell.box.yLower cell.box.yUpper -
      values.horizontal cell.box.xLower cell.box.xUpper cell.box.yUpper -
        values.vertical cell.box.xLower cell.box.yLower cell.box.yUpper

/-- Read an edge value with its actual traversal orientation.

A reversed edge negates the recursively retained original edge reading. -/
@[expose] def edge (values : EdgeValues) {grid : ClearGrid polynomial
  ambient} :
    {start finish : Gaussian.Basic.Canonical} → Walks.Edge grid start finish → Gaussian.Basic.Canonical
  | _, _, .horizontal interval _ line _ => values.horizontal interval.lower.coordinate interval.upper.coordinate
    line.coordinate
  | _, _, .vertical interval _ line _ => values.vertical line.coordinate interval.lower.coordinate
    interval.upper.coordinate
  | _, _, .reverse other => -values.edge other

/-- Sum the oriented readings of the actual edge list of a grid walk.

The empty walk contributes zero, and each stored edge contributes once in traversal order. -/
@[expose] def walk (values : EdgeValues) {grid : ClearGrid polynomial
  ambient} :
    {start finish : Gaussian.Basic.Canonical} → Walks.Walk grid start finish → Gaussian.Basic.Canonical
  | _, _, .nil _ => 0
  | _, _, .cons head tail => values.edge head + values.walk tail

/-- Appending walks adds their retained edge-value sums. -/
theorem walk_append (values : EdgeValues) {grid : ClearGrid polynomial
  ambient} :
    {start middle finish : Gaussian.Basic.Canonical} → (first : Walks.Walk grid start middle) → (second :
      Walks.Walk grid middle finish) →
      values.walk (first.append second) = values.walk first + values.walk second
  | _, _, _, .nil _, second => by change values.walk second = 0 + values.walk second; ring1
  | _, _, _, .cons head tail, second => by
      change values.edge head + values.walk (tail.append second) = _
      rw [walk_append values tail second]
      change _ = (values.edge head + values.walk tail) + values.walk second
      ring1

/-- Reversing a walk onto a suffix subtracts the original value and adds the suffix value. -/
private theorem walk_reverseOnto (values : EdgeValues) {grid : ClearGrid
  polynomial ambient} :
    {start middle finish : Gaussian.Basic.Canonical} → (first : Walks.Walk grid start middle) → (second :
      Walks.Walk grid start finish) →
      values.walk (first.reverseOnto second) = -values.walk first + values.walk second
  | _, _, _, .nil _, second => by change values.walk second = -0 + values.walk second; ring1
  | _, _, _, .cons head tail, second => by
      change values.walk (tail.reverseOnto (.cons (.reverse head) second)) = _
      rw [walk_reverseOnto values tail]
      change -values.walk tail + (-values.edge head + values.walk second) =
        -(values.edge head + values.walk tail) + values.walk second
      ring1

open Purelib.Polynomial.Geometry.Grid.CellBoundary.EdgeValues in
/-- Reversing a walk negates its edge-value sum. -/
theorem walk_reverse (values : EdgeValues) {grid : ClearGrid polynomial
  ambient} {start finish : Gaussian.Basic.Canonical}
    (walk : Walks.Walk grid start finish) : values.walk walk.reverse = -values.walk walk := by
  rw [Walks.Walk.reverse, walk_reverseOnto]
  change -values.walk walk + 0 = _
  ring1

/-- Sum the oriented exterior readings along every retained grid interval.

The first and last grid lines supply the boundary coordinates; a missing coordinate-line list yields zero. -/
@[expose] def perimeter (values : EdgeValues) (grid : ClearGrid polynomial
  ambient) : Gaussian.Basic.Canonical :=
  match grid.vertical, grid.horizontal with
  | [], _ | _, [] => 0
  | xFirst :: xRest, yFirst :: yRest =>
      let xLast := CellBoundary.Interval.lastFrom xFirst xRest
      let yLast := CellBoundary.Interval.lastFrom yFirst yRest
      CellBoundary.sumValues (fun interval => values.horizontal interval.lower.coordinate
        interval.upper.coordinate yFirst.coordinate -
        values.horizontal interval.lower.coordinate interval.upper.coordinate yLast.coordinate) grid.xIntervals +
      CellBoundary.sumValues (fun interval => values.vertical xLast.coordinate interval.lower.coordinate
        interval.upper.coordinate -
        values.vertical xFirst.coordinate interval.lower.coordinate interval.upper.coordinate) grid.yIntervals

/-- Adjacent sides cancel exactly at their retained grid coordinates.  The
exterior retains every subdivision; it is not replaced by four long chords. -/
theorem sum_cells_eq_perimeter (values : EdgeValues) (grid : ClearGrid
  polynomial ambient) :
    CellBoundary.sumValues values.cellBoundary grid.cells = values.perimeter grid := by
  cases grid with
  | mk vertical horizontal xOrdered yOrdered =>
      cases vertical with
      | nil => rfl
      | cons xFirst xRest =>
          cases horizontal with
          | nil =>
              change CellBoundary.sumValues values.cellBoundary
                ((Interval.adjacent (xFirst :: xRest) xOrdered).flatMap fun _ => []) = 0
              rw [sumValues_flatMap]
              exact sumValues_zero _
          | cons yFirst yRest =>
              let xs := Interval.adjacent (xFirst :: xRest) xOrdered
              let ys := Interval.adjacent (yFirst :: yRest) yOrdered
              let bottomTop := fun (x : Interval
                (ClearGrid.VerticalLine.coordinate (polynomial := polynomial) (ambient := ambient)))
                  (y : Interval (ClearGrid.HorizontalLine.coordinate (polynomial
                    := polynomial) (ambient := ambient))) =>
                values.horizontal x.lower.coordinate x.upper.coordinate y.lower.coordinate -
                values.horizontal x.lower.coordinate x.upper.coordinate y.upper.coordinate
              let rightLeft := fun (x : Interval
                (ClearGrid.VerticalLine.coordinate (polynomial := polynomial) (ambient := ambient)))
                  (y : Interval (ClearGrid.HorizontalLine.coordinate (polynomial
                    := polynomial) (ambient := ambient))) =>
                values.vertical x.upper.coordinate y.lower.coordinate y.upper.coordinate -
                values.vertical x.lower.coordinate y.lower.coordinate y.upper.coordinate
              have separated : CellBoundary.sumValues values.cellBoundary
                  (xs.flatMap fun x => ys.map fun y => (⟨x, y⟩ : ClearGrid.Cell polynomial ambient)) =
                    CellBoundary.sumValues (fun x => CellBoundary.sumValues (bottomTop x)
                      ys) xs +
                      CellBoundary.sumValues (fun x => CellBoundary.sumValues (rightLeft x)
                        ys) xs := by
                rw [sumValues_flatMap, ← sumValues_add]
                apply sumValues_congr
                intro x _
                rw [sumValues_map, ← sumValues_add]
                apply sumValues_congr
                intro y _
                unfold cellBoundary Cell.box
                dsimp only [bottomTop, rightLeft]
                ring1
              change CellBoundary.sumValues values.cellBoundary (xs.flatMap fun x => ys.map fun y => (⟨x,
                y⟩ : ClearGrid.Cell polynomial ambient)) = _
              rw [separated, sumValues_swap rightLeft xs ys]
              apply congrArg₂ (· + ·)
              · apply sumValues_congr
                intro x _
                exact CellBoundary.Interval.sum_differences (fun y => values.horizontal x.lower.coordinate
                  x.upper.coordinate y.coordinate) _ _ yOrdered
              · apply sumValues_congr
                intro y _
                have telescope := CellBoundary.Interval.sum_differences
                  (fun x => values.vertical x.coordinate y.lower.coordinate y.upper.coordinate) _ _ xOrdered
                have negative := sumValues_congr (rightLeft · y)
                  (fun x => -(values.vertical x.lower.coordinate y.lower.coordinate y.upper.coordinate -
                    values.vertical x.upper.coordinate y.lower.coordinate y.upper.coordinate)) xs (fun _ _ => by
                        dsimp only [rightLeft];
                        ring1)
                rw [negative, sumValues_neg, telescope]
                ring1

end Purelib.Polynomial.Geometry.Grid.CellBoundary.EdgeValues

end

section

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {grid :
  ClearGrid polynomial ambient}

namespace Purelib.Polynomial.Geometry.Grid.CellBoundary.Cell

/-- A listed grid cell retains adjacent intervals from both grid coordinate lists. -/
theorem intervals_mem (cell : ClearGrid.Cell polynomial ambient) (member : cell ∈ grid.cells) :
    cell.horizontal ∈ grid.xIntervals ∧ cell.vertical ∈ grid.yIntervals := by
  obtain ⟨x, xMember, member⟩ := Data.List.Flatten.mem_flatMap.mp member
  obtain ⟨y, yMember, equal⟩ := Data.List.Map.mem_map.mp member
  cases equal
  exact ⟨xMember, yMember⟩

end Purelib.Polynomial.Geometry.Grid.CellBoundary.Cell

namespace Purelib.Polynomial.Geometry.Grid.ClearGrid.Cell

/-- The lower-left anchor of a listed grid cell is a vertex of the same grid. -/
theorem anchor_mem (cell : ClearGrid.Cell
  polynomial ambient) (member : cell ∈ grid.cells) : FromStates.ContainsVertex grid cell.box.anchor
  :=
  let intervals := CellBoundary.Cell.intervals_mem cell member
  ⟨Data.List.Map.mem_map_of_mem (Interval.endpoints_mem _ grid.vertical_ordered intervals.1).1,
    Data.List.Map.mem_map_of_mem (Interval.endpoints_mem _ grid.horizontal_ordered
      intervals.2).1⟩

end Purelib.Polynomial.Geometry.Grid.ClearGrid.Cell

namespace Purelib.Polynomial.Geometry.Grid.CellBoundary.Cell

/-- Four actual adjacent edges, counterclockwise and closed at the cell's
lower-left corner.  No splitter, owner acquisition or winding calculation
is executed to construct this geometric boundary. -/
@[expose] def boundaryWalk (cell : ClearGrid.Cell polynomial ambient) (member : cell ∈ grid.cells) :
    Walks.Walk grid cell.box.anchor cell.box.anchor :=
  let intervals := intervals_mem cell member
  let xEnds := Interval.endpoints_mem _ grid.vertical_ordered intervals.1
  let yEnds := Interval.endpoints_mem _ grid.horizontal_ordered intervals.2
  .cons (.horizontal cell.horizontal intervals.1 cell.vertical.lower yEnds.1)
    (.cons (.vertical cell.vertical intervals.2 cell.horizontal.upper xEnds.2)
      (.cons (.reverse (.horizontal cell.horizontal intervals.1 cell.vertical.upper yEnds.2))
        (.cons (.reverse (.vertical cell.vertical intervals.2 cell.horizontal.lower xEnds.1)) (.nil _))))

/-- The displayed cell boundary walk has exactly four edges. -/
theorem boundaryWalk_edgeCount (cell : ClearGrid.Cell polynomial ambient) (member : cell ∈ grid.cells) :
    (boundaryWalk cell member).edgeCount = 4 := rfl

/-- Evaluating the displayed boundary walk gives the four-edge cell boundary sum. -/
theorem boundaryWalk_value (cell : ClearGrid.Cell polynomial ambient) (member : cell ∈ grid.cells) (values
  : EdgeValues) :
    values.walk (boundaryWalk cell member) = values.cellBoundary cell := by
  simp only [boundaryWalk, EdgeValues.walk,
    EdgeValues.edge, EdgeValues.cellBoundary,
    Cell.box, -eq_self, -iff_self]
  ring1

/-- The displayed boundary walk has the raw winding of its exact cell box. -/
theorem boundaryWalk_winding (cell : ClearGrid.Cell polynomial ambient) (member : cell ∈ grid.cells) :
    Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding (boundaryWalk cell
      member).path =
      Winding.Box.Basic.quadrupledBoxWinding polynomial cell.box := by
  simp only [boundaryWalk, Walks.Walk.path,
    Walks.Edge.segment, Curves.Hyperelliptic.Branches.BranchCutLifts.ClearSegment.reverse,
    Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding,
      Riemann.Paths.PreparedPathWinding.ClearSegment.rawWinding_eq_coordinateWinding,
      Riemann.Paths.PreparedPathWinding.ClearSegment.coordinateWinding, -eq_self, -iff_self]
  rw [Winding.Box.Basic.quadrupledBoxWinding_eq]
  dsimp only [Cell.box]
  ring1

end Purelib.Polynomial.Geometry.Grid.CellBoundary.Cell

end

end

end

public section
section

open Purelib.Data
open Purelib.Data.List
open Purelib.Data.Gaussian.Norm.Sum.Basic

namespace Purelib.Polynomial.Geometry.Grid.CellBoundary

/-- Summing mapped finite values retains the same original Gaussian list sum.

The pointwise value function supplies every ordered entry. Structural recursion
preserves the head value and transports only the unchanged tail sum. -/
theorem sumValues_eq_gaussianSum_map {A : Type u} (value : A → Gaussian.Basic.Canonical) (entries : List A) :
    sumValues value entries = Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map value) := by
  induction entries with
  | nil => rfl
  | cons head tail ih => exact congrArg (value head + ·) ih

/-- Summing each retained word gives the Gaussian sum of the ordered flattened entries.

Both nested sums keep every original entry and repeated occurrence. Flattening
concatenates the original words in order, and the append law combines their sums. -/
theorem sumValues_flatten {A : Type u} (value : A → Gaussian.Basic.Canonical) (words : List (List A)) :
    sumValues (sumValues value) words = Data.Gaussian.Norm.Sum.Basic.gaussianSum (words.flatten.map value) := by
  induction words with
  | nil => rfl
  | cons head tail ih =>
      change sumValues value head + sumValues (sumValues value) tail = _
      rw [sumValues_eq_gaussianSum_map, ih, List.flatten_cons, Map.map_append,
        Data.Gaussian.Norm.Sum.Basic.gaussianSum_append]

end Purelib.Polynomial.Geometry.Grid.CellBoundary

end

section

open Purelib
open Purelib.Data
open Purelib.Algebra
open Purelib.Topology
open Purelib.Curves

namespace Purelib.Polynomial.Geometry.Grid.CellBoundary

/-- Reversing the displayed occurrence list preserves its Gaussian value sum.

The same values are added once in reverse order; structural recursion uses the
original sum operation and transports the unchanged tail by scalar addition. -/
public theorem sumValues_reverse {Item : Type} (value : Item → Data.Gaussian.Basic.Canonical) (items : List Item) :
    sumValues value items.reverse = sumValues value items := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      rw [List.Reverse.reverse_cons, sumValues_append, ih]
      change sumValues value tail + (value head + 0) = value head + sumValues value tail
      ring1

end Purelib.Polynomial.Geometry.Grid.CellBoundary

end
