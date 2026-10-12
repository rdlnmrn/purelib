module

public import Purelib.Data.Sign.Basic
meta import Purelib.Elab.Deriving.Repr

/-!
# Coordinate-change shapes of formal small turns

Nonzero endpoint coordinate signs retain their compatible turn orientation.
The original equality tests select one of three coordinate-change shapes.
-/

namespace Purelib.Data.Sign.Pair.Turn

-- The original small-turn API is owned by Purelib.Data.Sign.Pair.Turn.Turn; retain those public names.

open _root_.Purelib.Data (Sign)
open Purelib.Data.Sign.Pair.Turn

/-- Certify a finite quadrant transition consistent with a supplied turn sign.

Both endpoint coordinate pairs must be strictly nonzero. At most one coordinate
changes sign, and a real or imaginary sign change constrains the turn orientation by
the initial coordinate product. -/
@[expose] public def SmallTurnCompatible
    (Aₗ Bₗ Aᵣ Bᵣ turn : Sign) : Prop :=
  Aₗ ≠ .zero ∧ Bₗ ≠ .zero ∧ Aᵣ ≠ .zero ∧ Bᵣ ≠ .zero ∧
    if Aₗ = Aᵣ then
      if Bₗ = Bᵣ then True
      else turn = Sign.neg (Sign.mul Aₗ Bₗ)
    else Bₗ = Bᵣ ∧ turn = Sign.mul Aₗ Bₗ

/-- Decide small-turn compatibility by the explicit sign equalities and nonzero
conditions. -/
public instance instDecidableSmallTurnCompatible (Aₗ Bₗ Aᵣ Bᵣ turn : Sign) :
    Decidable (SmallTurnCompatible Aₗ Bₗ Aᵣ Bᵣ turn) := by
  unfold SmallTurnCompatible
  infer_instance

@[expose] public section

/-- The three possible coordinate-change shapes of a small quadrant turn.

A transition changes neither coordinate, only the real sign, or only the imaginary
sign. -/
inductive SmallTurnShape where
  /-- Neither coordinate sign changes. -/ | same
  /-- The real coordinate sign changes while the imaginary sign is retained. -/ | realChange
  /-- The imaginary coordinate sign changes while the real sign is retained. -/ | imagChange
deriving DecidableEq

derive_exposed_repr SmallTurnShape

end

/-- Apply a finite turn shape to a pair of coordinate signs.

The same shape leaves both signs unchanged; realChange or imagChange negates exactly
the indicated coordinate. -/
@[expose] public def applySmallTurnShape
    (shape : SmallTurnShape) (real imag : Sign) :
    Sign × Sign :=
  match shape with
  | .same => (real, imag)
  | .realChange => (Sign.neg real, imag)
  | .imagChange => (real, Sign.neg imag)

/-- Read a turn shape from the coordinate equalities of two sign pairs.

If the real signs agree, distinguish unchanged and changed imaginary signs. Otherwise
select realChange; compatibility hypotheses separately certify that this choice
reconstructs the endpoint. -/
@[expose] public def smallTurnShape
    (realLeft imagLeft realRight imagRight : Sign) : SmallTurnShape :=
  if realLeft = realRight then
    if imagLeft = imagRight then .same else .imagChange
  else .realChange

/-- The shape read from a compatible small turn reconstructs its target sign pair.

The compatibility evidence excludes zero coordinates and simultaneous coordinate
changes, so applying the selected shape to the source yields the exact target. -/
public theorem apply_smallTurnShape_eq_of_compatible
    (Aₗ Bₗ Aᵣ Bᵣ turn : Sign)
    (compatible : SmallTurnCompatible Aₗ Bₗ Aᵣ Bᵣ turn) :
    applySmallTurnShape (smallTurnShape Aₗ Bₗ Aᵣ Bᵣ) Aₗ Bₗ =
      (Aᵣ, Bᵣ) := by
  revert compatible
  cases Aₗ <;> cases Bₗ <;> cases Aᵣ <;> cases Bᵣ <;> cases turn <;> decide

end Purelib.Data.Sign.Pair.Turn
