module

import Purelib.Data.Vector.Basic
import Purelib.Data.Fin

public import Purelib.Data.Vector.Scan
meta import Purelib.Elab.ConstructiveInjectivity

public section

/-!
# Constructive sheet gauges on a finite rectangular grid

The grid has `columns + 1` by `rows + 1` cells.  A flat bank of adjacent
transition bits determines a gauge on every cell: scan the first column,
then propagate whole cached columns horizontally.  The square identities
prove agreement on the remaining vertical edges.  This statement applies
to a rectangle, not to a punctured grid with nontrivial sheet monodromy.
-/

namespace Purelib.Topology.Grid.Signs

open Purelib
open Purelib.Data.Vector

/-- The finite function vector used for rows and columns. -/
abbrev Vector := Data.Vector

open Purelib.Data.Vector.Scan (scan scan_zero scan_step propagate propagate_zero propagate_step)

set_option genInjectivity false in
/-- Boolean transition data with trivial holonomy on each grid square.

Horizontal transitions join successive columns and vertical transitions join successive rows. The square equation
identifies the two routes around every elementary square. -/
structure FlatGrid (columns rows : Nat) where
  /-- Transition bits from each column to the next at every row. -/ horizontal : Signs.Vector (Signs.Vector Bool (rows +
    1)) columns
  /-- Transition bits from each row to the next at every column. -/ vertical : Signs.Vector (Signs.Vector Bool rows)
    (columns + 1)
  /-- The two routes around each elementary square have equal Boolean transition. -/ square : ∀ column row,
    (horizontal column row.castSucc ^^ vertical column.succ row) =
      (vertical column.castSucc row ^^ horizontal column row.succ)

constructive_injectivity FlatGrid

set_option genInjectivity false in
/-- A retained Boolean value at each cell satisfying the grid transitions.

The horizontal and vertical equations certify differences of adjacent values. Either global initial value is allowed,
and the stored values need not be a canonical scan. -/
structure Gauge {columns rows : Nat} (grid : Signs.FlatGrid columns rows) where
  /-- The retained sheet bit at each cell. -/ values : Signs.Vector (Signs.Vector Bool (rows + 1)) (columns + 1)
  /-- Horizontal neighbors differ by the corresponding stored transition bit. -/ horizontal : ∀ column row,
    values column.succ row = (values column.castSucc row ^^ grid.horizontal column row)
  /-- Vertical neighbors differ by the corresponding stored transition bit. -/ vertical : ∀ column row,
    values column row.succ = (values column row.castSucc ^^ grid.vertical column row)

constructive_injectivity Gauge

namespace Gauge

variable {columns rows : Nat} {grid : Signs.FlatGrid columns rows}

/-- Construct a gauge by scanning a spanning tree of the rectangular grid.

Scan the first column from the supplied initial bit, then propagate complete columns horizontally. Flatness proves
agreement with the remaining vertical transitions. -/
@[expose] def build (grid : Signs.FlatGrid columns rows) (initial : Bool := false) : Signs.Gauge grid :=
  let first := Scan.scan Bool.xor initial (grid.vertical 0)
  let values := Scan.propagate Bool.xor first grid.horizontal
  { values := values
    horizontal := Scan.propagate_step Bool.xor first grid.horizontal
    vertical := by
      intro column row
      induction column using Data.Fin.induction with
      | zero =>
          change Scan.propagate Bool.xor first grid.horizontal 0 row.succ =
            (Scan.propagate Bool.xor first grid.horizontal 0 row.castSucc ^^ grid.vertical 0 row)
          rw [Scan.propagate_zero]
          exact Scan.scan_step Bool.xor (grid.vertical 0) initial row
      | succ column ih =>
          change Scan.propagate Bool.xor first grid.horizontal column.succ row.succ =
            (Scan.propagate Bool.xor first grid.horizontal column.succ row.castSucc ^^ grid.vertical column.succ row)
          rw [Scan.propagate_step, Scan.propagate_step, ih, Bool.xor_assoc, Bool.xor_assoc, grid.square] }

/-- The constructed gauge retains its supplied value at the origin. -/
theorem build_origin (grid : Signs.FlatGrid columns rows) (initial : Bool) :
    (Gauge.build grid initial).values 0 0 = initial := by
  change Scan.propagate Bool.xor (Scan.scan Bool.xor initial (grid.vertical 0)) grid.horizontal 0 0 = initial
  rw [Scan.propagate_zero, Scan.scan_zero]

/-- Applying the same Boolean transition to two values preserves their difference. -/
private theorem xor_cancel_pair (first second edge : Bool) :
    ((first ^^ edge) ^^ (second ^^ edge)) = (first ^^ second) := by
  cases first <;> cases second <;> cases edge <;> rfl

/-- Two gauges on a flat rectangular grid differ by one global bit.

Their Boolean difference at every cell equals their difference at the origin, by propagation along rows and columns. -/
theorem difference_constant (left right : Signs.Gauge grid) (column : Fin (columns + 1)) (row : Fin (rows + 1)) :
    (left.values column row ^^ right.values column row) = (left.values 0 0 ^^ right.values 0 0) := by
  have firstColumn : ∀ row : Fin (rows + 1),
      (left.values 0 row ^^ right.values 0 row) = (left.values 0 0 ^^ right.values 0 0) := by
    intro row
    induction row using Data.Fin.induction with
    | zero => rfl
    | succ row ih => rw [left.vertical, right.vertical, Gauge.xor_cancel_pair, ih]
  induction column using Data.Fin.induction with
  | zero => exact firstColumn row
  | succ column ih => rw [left.horizontal, right.horizontal, Gauge.xor_cancel_pair, ih]

/-- Gauges with equal origin values have equal retained cell values.

Constancy of the Boolean difference determines each entry; finite vector extensionality then identifies the value
arrays. -/
theorem values_eq_of_origin (left right : Signs.Gauge grid) (origin : left.values 0 0 = right.values 0 0) :
    left.values = right.values := by
  apply Data.Vector.Basic.vector_ext
  intro column
  apply Data.Vector.Basic.vector_ext
  intro row
  have difference := left.difference_constant right column row
  rw [origin, Bool.xor_self] at difference
  have xor_false (first second : Bool) : (first ^^ second) = false → first = second := by
    cases first <;> cases second <;> decide
  exact xor_false _ _ difference

/-- The difference of horizontally adjacent gauge values is the stored horizontal transition. -/
theorem horizontal_difference (gauge : Signs.Gauge grid) (column : Fin columns) (row : Fin (rows + 1)) :
    (gauge.values column.castSucc row ^^ gauge.values column.succ row) = grid.horizontal column row := by
  rw [gauge.horizontal, ← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]

/-- The difference of vertically adjacent gauge values is the stored vertical transition. -/
theorem vertical_difference (gauge : Signs.Gauge grid) (column : Fin (columns + 1)) (row : Fin rows) :
    (gauge.values column row.castSucc ^^ gauge.values column row.succ) = grid.vertical column row := by
  rw [gauge.vertical, ← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]

end Gauge

end Purelib.Topology.Grid.Signs

end
