module

public import Purelib.Geometry.Path.Gaussian.Lifted.Basic

/-! # Endpoint index transport of original lifted cells

Exact endpoint identities transport the original cell without replacing its
retained sheet bijection or its equation on the selected sheet.
-/

public section

namespace Purelib.Geometry.Path.Gaussian.Lifted.Basic.LiftedCell

/-- Transport only the two exact endpoint indices of an original lifted cell. -/
@[expose] def castEndpoints {sheets : Nat} {start finish first last : LiftedPoint sheets}
    (cell : LiftedCell start finish) (startEq : start = first) (finishEq : finish = last) :
    LiftedCell first last := by
  cases startEq
  cases finishEq
  exact cell

/-- Endpoint transport preserves the complete original lifted cell up to its dependent indices. -/
theorem castEndpoints_heq {sheets : Nat} {start finish first last : LiftedPoint sheets}
    (cell : LiftedCell start finish) (startEq : start = first) (finishEq : finish = last) :
    HEq (cell.castEndpoints startEq finishEq) cell := by
  cases startEq
  cases finishEq
  exact HEq.rfl

/-- Endpoint transport retains the original complete finite sheet bijection. -/
theorem sheetTransport_castEndpoints {sheets : Nat} {start finish first last : LiftedPoint sheets}
    (cell : LiftedCell start finish) (startEq : start = first) (finishEq : finish = last) :
    (cell.castEndpoints startEq finishEq).sheetTransport = cell.sheetTransport := by
  cases startEq
  cases finishEq
  rfl

end Purelib.Geometry.Path.Gaussian.Lifted.Basic.LiftedCell

end
