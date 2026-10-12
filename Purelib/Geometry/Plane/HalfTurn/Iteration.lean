module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.HalfTurn.Basic
import Purelib.Algebra.Field.ExplicitField
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Tactic.Ring
import Purelib.Algebra.NatCast

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Algebra

@[expose] public section

/-!
# Divine Proportions, Exercise 4.2: finite successive rotations

The book introduces a completed two-sided point sequence.  The executable
iterator below starts from the two displayed points and computes only a
requested natural-number prefix.  Its closed coordinate formula shows that
the points form an arithmetic progression, from which the requested rotation
symmetry follows on every finite window in both orientations.
-/

namespace Purelib.Geometry.Plane.HalfTurn.Iteration

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

set_option genInjectivity false in
/-- An adjacent pair in the finite successive-rotation construction. -/
structure SuccessiveRotationPair (K : Type*) where
  /-- The first point of the adjacent pair. -/ previous : Point K
  /-- The next point, used as the center of the following half-turn. -/ current : Point K

constructive_injectivity SuccessiveRotationPair

namespace SuccessiveRotationPair

/-- One source step `(Aₙ,Aₙ₊₁) ↦ (Aₙ₊₁,ρ_{Aₙ₊₁}(Aₙ))`. -/
def step (state : Geometry.Plane.HalfTurn.Iteration.SuccessiveRotationPair K) :
  Geometry.Plane.HalfTurn.Iteration.SuccessiveRotationPair K where
  previous := state.current
  current := HalfTurn.Basic.rotateInPoint state.current state.previous

end SuccessiveRotationPair

/-- Execute exactly the requested number of successive rotations. -/
def successiveRotationPairAt
    (initial : Purelib.Geometry.Plane.HalfTurn.Iteration.SuccessiveRotationPair K) : Nat →
      Purelib.Geometry.Plane.HalfTurn.Iteration.SuccessiveRotationPair K
  | 0 => initial
  | index + 1 => (Purelib.Geometry.Plane.HalfTurn.Iteration.successiveRotationPairAt initial index).step

/-- The point `Aₙ` computed by the finite iterator. -/
def successiveRotationPointAt
    (initial : Geometry.Plane.HalfTurn.Iteration.SuccessiveRotationPair K) (index : Nat) : Point K :=
  (Geometry.Plane.HalfTurn.Iteration.successiveRotationPairAt initial index).previous

/-- The explicit arithmetic-progression point determined by the initial pair. -/
def successiveRotationFormula
    (initial : Geometry.Plane.HalfTurn.Iteration.SuccessiveRotationPair K) (index : Nat) : Point K :=
  ⟨initial.previous.x + (index : K) *
      (initial.current.x - initial.previous.x),
    initial.previous.y + (index : K) *
      (initial.current.y - initial.previous.y)⟩

/-- Both entries of every finitely computed state have the expected closed coordinate formula. -/
theorem successiveRotationPairAt_formula
    (initial : Geometry.Plane.HalfTurn.Iteration.SuccessiveRotationPair K) (index : Nat) :
    (HalfTurn.Iteration.successiveRotationPairAt initial index).previous =
        HalfTurn.Iteration.successiveRotationFormula initial index ∧
      (HalfTurn.Iteration.successiveRotationPairAt initial index).current =
        HalfTurn.Iteration.successiveRotationFormula initial (index + 1) := by
  induction index with
  | zero =>
      constructor <;>
        apply Point.ext <;>
        unfold HalfTurn.Iteration.successiveRotationPairAt HalfTurn.Iteration.successiveRotationFormula <;>
        simp only [AddMonoidWithOne.natCast_zero,
          AddMonoidWithOne.natCast_succ, AddZeroClass.zero_add,
          MulZeroClass.zero_mul, AddZeroClass.add_zero, MulOneClass.one_mul,
          -eq_self, -iff_self] <;>
        first | rfl | ring1
  | succ index inductionHypothesis =>
      change
        (HalfTurn.Iteration.successiveRotationPairAt initial index).current =
            HalfTurn.Iteration.successiveRotationFormula initial (Nat.succ index) ∧
          HalfTurn.Basic.rotateInPoint
              (HalfTurn.Iteration.successiveRotationPairAt initial index).current
              (HalfTurn.Iteration.successiveRotationPairAt initial index).previous =
            HalfTurn.Iteration.successiveRotationFormula initial (Nat.succ index + 1)
      constructor
      · simpa only [Nat.succ_eq_add_one] using inductionHypothesis.2
      · rw [inductionHypothesis.1, inductionHypothesis.2]
        apply Point.ext <;>
          unfold HalfTurn.Basic.rotateInPoint HalfTurn.Iteration.successiveRotationFormula <;>
          simp only [AddMonoidWithOne.natCast_succ, -eq_self, -iff_self] <;>
          ring1

/-- The point projection of the iterator is the displayed closed formula. -/
theorem successiveRotationPointAt_formula
    (initial : Geometry.Plane.HalfTurn.Iteration.SuccessiveRotationPair K) (index : Nat) :
    Geometry.Plane.HalfTurn.Iteration.successiveRotationPointAt initial index =
      Geometry.Plane.HalfTurn.Iteration.successiveRotationFormula initial index :=
  (Geometry.Plane.HalfTurn.Iteration.successiveRotationPairAt_formula initial index).1

/-- Exercise 4.2, in finite-prefix form. The center is `leftIndex + offset`, and the other endpoint is the same distance
beyond it. Both orientations of the book's equation `ρ_{Aₖ}(Aₗ)=A_{2k-l}` are retained. -/
theorem exercise_4_2
    (initial : Geometry.Plane.HalfTurn.Iteration.SuccessiveRotationPair K) (offset leftIndex : Nat) :
    HalfTurn.Basic.rotateInPoint
        (Geometry.Plane.HalfTurn.Iteration.successiveRotationPointAt initial (leftIndex + offset))
        (Geometry.Plane.HalfTurn.Iteration.successiveRotationPointAt initial leftIndex) =
          Geometry.Plane.HalfTurn.Iteration.successiveRotationPointAt initial (leftIndex + 2 * offset) ∧
      HalfTurn.Basic.rotateInPoint
        (Geometry.Plane.HalfTurn.Iteration.successiveRotationPointAt initial (leftIndex + offset))
        (Geometry.Plane.HalfTurn.Iteration.successiveRotationPointAt initial (leftIndex + 2 * offset)) =
          Geometry.Plane.HalfTurn.Iteration.successiveRotationPointAt initial leftIndex := by
  constructor <;>
    simp only [Geometry.Plane.HalfTurn.Iteration.successiveRotationPointAt_formula] <;>
    apply Point.ext <;>
    unfold HalfTurn.Basic.rotateInPoint HalfTurn.Iteration.successiveRotationFormula <;>
    simp only [NatCast.add, NatCast.mul, -eq_self, -iff_self] <;>
    ring1

end Purelib.Geometry.Plane.HalfTurn.Iteration

end
