module

public import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Fin.Bijection.Basic
import Init.Prelude
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data
open Purelib.Data.Fin.Bijection.Basic

public section

/-!
# Finite sheet-aware paths for period integration

A lifted path below is an inductive finite chain.  Every geometric edge
carries an explicit permutation of the labelled sheets and a proof that the
chosen endpoint sheet is the transported start sheet.  A separate inductive
relation verifies that a progressive integration model follows exactly the
same displayed geometric edges.  This separation lets several algebraic
differentials share one persistent lifted cycle while retaining their own
local polynomial integrand models.
-/

namespace Purelib.Geometry.Path.Gaussian.Lifted.Basic

set_option genInjectivity false in
/-- One displayed point of the base path together with its labelled sheet.

The canonical coordinate and finite sheet label are retained together. Their original carriers provide the endpoint
indices for every lifted cell and path. -/
structure LiftedPoint (sheets : Nat) where
  /-- The displayed Gaussian coordinate of the lifted point. -/ coordinate : Gaussian.Basic.Canonical
  /-- The sheet label at this coordinate. -/ sheet : Fin sheets

constructive_injectivity LiftedPoint

set_option genInjectivity false in
/-- One finite geometric edge and its certified sheet transport.

The original bijection transports the starting sheet to the finishing sheet. The stored equation links that exact
transport to the dependent endpoint labels. -/
structure LiftedCell {sheets : Nat}
    (start finish : LiftedPoint sheets) where
  /-- The retained bijection transporting labels along this cell. -/ sheetTransport : Data.Fin.Bijection sheets sheets
  /-- The transport sends the starting sheet to the finishing sheet. -/ finishSheet_eq : sheetTransport.forward
    start.sheet = finish.sheet

constructive_injectivity LiftedCell

namespace LiftedCell

/-- Reverse one displayed lifted edge, including its finite sheet permutation.

The retained backward map becomes the reversed forward map. Applying it to the original endpoint equation proves the
reversed transport without rebuilding the permutation. -/
@[expose] def reverse {sheets : Nat} {start finish : LiftedPoint sheets}
    (cell : LiftedCell start finish) : LiftedCell finish start where
  sheetTransport := cell.sheetTransport.reverse
  finishSheet_eq := by
    change cell.sheetTransport.backward finish.sheet = start.sheet
    rw [← cell.finishSheet_eq]
    exact cell.sheetTransport.backward_forward start.sheet

end LiftedCell

set_option genInjectivity false in
/-- A finite path whose dependent endpoints enforce geometric and sheet continuity between consecutive cells.

The empty path retains its original point. Each nonempty path retains one cell and the exact remaining path, with their
shared point appearing in the dependent indices. -/
inductive LiftedPath (sheets : Nat) :
    LiftedPoint sheets -> LiftedPoint sheets -> Type
  /-- The empty lifted path starts and finishes at the same lifted point. -/ | nil (point : LiftedPoint sheets) :
    LiftedPath sheets point point
  /-- Prepend a cell whose finishing point is the starting point of the remaining path. -/ | cons {start middle finish :
    LiftedPoint sheets}
      (cell : LiftedCell start middle)
      (remaining : LiftedPath sheets middle finish) :
      LiftedPath sheets start finish

constructive_injectivity LiftedPath

namespace LiftedPath

/-- Count the geometric cells in the finite lifted path.

The empty path has count zero. Each original cell contributes one to the count of the retained remaining path. -/
@[expose] def cellCount {sheets : Nat} : {start finish : LiftedPoint sheets} ->
    LiftedPath sheets start finish -> Nat
  | _, _, .nil _ => 0
  | _, _, .cons _ remaining => remaining.cellCount + 1

/-- Append two finite lifted paths with the same displayed middle point.

Recursion traverses the original first path and retains every cell in order. At its empty endpoint the exact second path
is returned. -/
@[expose] def append {sheets : Nat}
    {start middle finish : LiftedPoint sheets}
    (first : LiftedPath sheets start middle)
    (second : LiftedPath sheets middle finish) :
    LiftedPath sheets start finish :=
  match first with
  | .nil _ => second
  | .cons cell remaining => .cons cell (remaining.append second)

/-- Reverse a finite lifted path in the literal cell order.

The recursion materializes the original reversed chain by appending each reversed cell to the reversed remaining path.
Every cell retains its corresponding inverse sheet permutation. -/
@[expose] def reverse {sheets : Nat} : {start finish : LiftedPoint sheets} ->
    LiftedPath sheets start finish -> LiftedPath sheets finish start
  | _, _, .nil point => .nil point
  | _, _, .cons cell remaining =>
      remaining.reverse.append (.cons cell.reverse (.nil _))

/-- Change only the propositionally equal starting lifted-point index.

Equality elimination transports the original path to the equal starting point. Every retained cell and sheet permutation
remains unchanged. -/
@[expose] def castStart {sheets : Nat}
    {left right finish : LiftedPoint sheets} (equal : left = right)
    (path : LiftedPath sheets left finish) :
    LiftedPath sheets right finish := by
  subst right
  exact path

/-- Change only the propositionally equal finishing lifted-point index.

Equality elimination transports the original path to the equal finishing point. Every retained cell and sheet
permutation remains unchanged. -/
@[expose] def castFinish {sheets : Nat}
    {start left right : LiftedPoint sheets} (equal : left = right)
    (path : LiftedPath sheets start left) :
    LiftedPath sheets start right := by
  subst right
  exact path

/-- Appending lifted paths adds their cell counts.

The finite induction follows the retained first path. Each original cell contributes one to the count, while the exact
second path is appended unchanged at the empty endpoint. -/
@[simp] theorem cellCount_append {sheets : Nat}
    {start middle finish : LiftedPoint sheets}
    (first : LiftedPath sheets start middle)
    (second : LiftedPath sheets middle finish) :
    (first.append second).cellCount = first.cellCount + second.cellCount := by
  induction first with
  | nil => exact (Nat.zero_add second.cellCount).symm
  | cons cell remaining inductionHypothesis =>
      change (remaining.append second).cellCount + 1 =
        (remaining.cellCount + 1) + second.cellCount
      rw [inductionHypothesis]
      omega0

/-- The retained bijection transporting labels along this cell. -/
@[expose] def sheetTransport {sheets : Nat} :
    {start finish : LiftedPoint sheets} ->
      LiftedPath sheets start finish -> Data.Fin.Bijection sheets sheets
  | _, _, .nil _ => Data.Fin.Bijection.identity sheets
  | _, _, .cons cell remaining =>
      Data.Fin.Bijection.comp
        remaining.sheetTransport cell.sheetTransport

/-- The composed permutation carries the initial sheet to the final sheet.

Finite induction applies each stored cell equation to the remaining path transport. The conclusion concerns the exact
composed bijection retained by the original path. -/
theorem sheetTransport_start {sheets : Nat}
    {start finish : LiftedPoint sheets}
    (path : LiftedPath sheets start finish) :
    path.sheetTransport.forward start.sheet = finish.sheet := by
  induction path with
  | nil point => rfl
  | cons cell remaining inductionHypothesis =>
      change remaining.sheetTransport.forward
        (cell.sheetTransport.forward _) = _
      rw [cell.finishSheet_eq, inductionHypothesis]

/-- Reversing a lifted path preserves its cell count.

Each reversed cell contributes the same single count. The append count equation combines it with the reversed remaining
path without changing the finite chain length. -/
@[simp] theorem cellCount_reverse {sheets : Nat}
    {start finish : LiftedPoint sheets}
    (path : LiftedPath sheets start finish) :
    path.reverse.cellCount = path.cellCount := by
  induction path with
  | nil point => rfl
  | cons cell remaining inductionHypothesis =>
      rw [LiftedPath.reverse, LiftedPath.cellCount_append, inductionHypothesis]
      change remaining.cellCount + 1 = remaining.cellCount + 1
      rfl

end LiftedPath
end Purelib.Geometry.Path.Gaussian.Lifted.Basic
