import DivineProportions.Plane.Reflection

/-!
# Divine Proportions, Exercise 4.2: finite successive rotations

The book introduces a completed two-sided point sequence.  The executable
iterator below starts from the two displayed points and computes only a
requested natural-number prefix.  Its closed coordinate formula shows that
the points form an arithmetic progression, from which the requested rotation
symmetry follows on every finite window in both orientations.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- An adjacent pair in the finite successive-rotation construction. -/
structure SuccessiveRotationPair (K : Type*) where
  previous : Point K
  current : Point K

namespace SuccessiveRotationPair

/-- One source step `(Aₙ,Aₙ₊₁) ↦ (Aₙ₊₁,ρ_{Aₙ₊₁}(Aₙ))`. -/
def step (state : SuccessiveRotationPair K) : SuccessiveRotationPair K where
  previous := state.current
  current := rotateInPoint state.current state.previous

end SuccessiveRotationPair

/-- Execute exactly the requested number of successive rotations. -/
def successiveRotationPairAt
    (initial : SuccessiveRotationPair K) : Nat → SuccessiveRotationPair K
  | 0 => initial
  | index + 1 => (successiveRotationPairAt initial index).step

/-- The point `Aₙ` computed by the finite iterator. -/
def successiveRotationPointAt
    (initial : SuccessiveRotationPair K) (index : Nat) : Point K :=
  (successiveRotationPairAt initial index).previous

/-- The explicit arithmetic-progression point determined by the initial
pair. -/
def successiveRotationFormula
    (initial : SuccessiveRotationPair K) (index : Nat) : Point K :=
  ⟨initial.previous.x + (index : K) *
      (initial.current.x - initial.previous.x),
    initial.previous.y + (index : K) *
      (initial.current.y - initial.previous.y)⟩

/-- Both entries of every finitely computed state have the expected closed
coordinate formula. -/
theorem successiveRotationPairAt_formula
    (initial : SuccessiveRotationPair K) (index : Nat) :
    (successiveRotationPairAt initial index).previous =
        successiveRotationFormula initial index ∧
      (successiveRotationPairAt initial index).current =
        successiveRotationFormula initial (index + 1) := by
  induction index with
  | zero =>
      constructor <;>
        apply Point.ext <;>
        unfold successiveRotationPairAt successiveRotationFormula <;>
        simp
  | succ index inductionHypothesis =>
      change
        (successiveRotationPairAt initial index).current =
            successiveRotationFormula initial (Nat.succ index) ∧
          rotateInPoint
              (successiveRotationPairAt initial index).current
              (successiveRotationPairAt initial index).previous =
            successiveRotationFormula initial (Nat.succ index + 1)
      constructor
      · simpa only [Nat.succ_eq_add_one] using inductionHypothesis.2
      · rw [inductionHypothesis.1, inductionHypothesis.2]
        apply Point.ext <;>
          unfold rotateInPoint successiveRotationFormula <;>
          simp only [Nat.cast_succ] <;>
          ring1

/-- The point projection of the iterator is the displayed closed formula. -/
theorem successiveRotationPointAt_formula
    (initial : SuccessiveRotationPair K) (index : Nat) :
    successiveRotationPointAt initial index =
      successiveRotationFormula initial index :=
  (successiveRotationPairAt_formula initial index).1

/-- Exercise 4.2, in finite-prefix form.  The center is
`leftIndex + offset`, and the other endpoint is the same distance beyond it.
Both orientations of the book's equation `ρ_{Aₖ}(Aₗ)=A_{2k-l}` are retained. -/
theorem exercise_4_2
    (initial : SuccessiveRotationPair K) (offset leftIndex : Nat) :
    rotateInPoint
        (successiveRotationPointAt initial (leftIndex + offset))
        (successiveRotationPointAt initial leftIndex) =
          successiveRotationPointAt initial (leftIndex + 2 * offset) ∧
      rotateInPoint
        (successiveRotationPointAt initial (leftIndex + offset))
        (successiveRotationPointAt initial (leftIndex + 2 * offset)) =
          successiveRotationPointAt initial leftIndex := by
  constructor <;>
    simp only [successiveRotationPointAt_formula] <;>
    apply Point.ext <;>
    unfold rotateInPoint successiveRotationFormula <;>
    simp only [Nat.cast_add, Nat.cast_mul] <;>
    ring1

end DivineProportions
