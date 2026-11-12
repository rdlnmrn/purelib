module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Row
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic

/-! # Original relation-cell selection on a retained Legendre source path

The row selects the same existing first, second or scalar relation list.
Every original source cell and its selected coefficient/primitive caches
remain unchanged; selection acquires no source or observation.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Row

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell LiftedPath)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)

variable {parameter : Canonical} {start finish : LiftedPoint 2} {original : LiftedPath 2 start finish}

/-- Select the original row's whole retained relation-cell list without rebuilding any source cell. -/
@[expose] def cells (row : Row) (sources : Path parameter original) : List CellModel :=
  match row with
  | .inl coordinate => Fin.cases sources.zero (fun _ => sources.one) coordinate
  | .inr _ => sources.scalar

/-- Every original row has an empty cell list on the original empty source path. -/
theorem cells_nil (row : Row) (point : LiftedPoint 2) :
    row.cells (Path.nil (parameter := parameter) point) = [] := by
  cases row with
  | inl coordinate => exact Fin.cases (Eq.refl _) (fun _ => Eq.refl _) coordinate
  | inr _ => rfl

/-- The selected original path list retains exactly its selected original head cell and unchanged tail. -/
theorem cells_cons (row : Row) {first middle last : LiftedPoint 2} {lifted : LiftedCell first middle}
    {remaining : LiftedPath 2 middle last} (head : Cell (parameter := parameter) lifted)
    (tail : Path parameter remaining) :
    row.cells (Path.cons head tail) = row.cell head.models :: row.cells tail := by
  cases row with
  | inl coordinate => exact Fin.cases (Eq.refl _) (fun _ => Eq.refl _) coordinate
  | inr _ => rfl

end Purelib.Curves.Legendre.Periods.Jets.Source.Row

end
