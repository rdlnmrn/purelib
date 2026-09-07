import DivineProportions.Trigonometry.Quadrea

/-!
# Divine Proportions, §13.1 and Theorem 91: finite plane isometries

An isometry carries both an executable point map and an executable inverse.
Its metric law is the finite equality asserting preservation of quadrance;
there is no completed space, infinite carrier argument, or selected inverse.

Theorem 91 follows exactly the source proof through the Triple-quad formula.
The hypothesis `2 ≠ 0` is exposed because over characteristic two the book's
quadrance degenerates and no longer detects collinearity.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- The origin `O ≡ [0,0]`. -/
def planeOrigin : Point K := ⟨0, 0⟩

/-- A finite, constructive plane isometry: a point map, a displayed inverse,
and the source's quadrance-preservation law. -/
structure PlaneIsometry (K : Type*) [RFAP.ExplicitField K] where
  toFun : Point K → Point K
  inverseFun : Point K → Point K
  inverse_after : ∀ point, inverseFun (toFun point) = point
  after_inverse : ∀ point, toFun (inverseFun point) = point
  preservesQuadrance : ∀ first second,
    quadrance (toFun first) (toFun second) = quadrance first second

instance : CoeFun (PlaneIsometry K) (fun _ => Point K → Point K) where
  coe isometry := isometry.toFun

namespace PlaneIsometry

/-- The identity isometry. -/
def identity : PlaneIsometry K where
  toFun := fun point => point
  inverseFun := fun point => point
  inverse_after := fun _ => rfl
  after_inverse := fun _ => rfl
  preservesQuadrance := fun _ _ => rfl

/-- Exercise 13.1, inverse half: the displayed inverse of an isometry is an
isometry, with the original map as its displayed inverse. -/
def inverse (isometry : PlaneIsometry K) : PlaneIsometry K where
  toFun := isometry.inverseFun
  inverseFun := isometry.toFun
  inverse_after := isometry.after_inverse
  after_inverse := isometry.inverse_after
  preservesQuadrance := by
    intro first second
    calc
      quadrance (isometry.inverseFun first) (isometry.inverseFun second) =
          quadrance
            (isometry (isometry.inverseFun first))
            (isometry (isometry.inverseFun second)) :=
              (isometry.preservesQuadrance
                (isometry.inverseFun first)
                (isometry.inverseFun second)).symm
      _ = quadrance first second := by
        rw [isometry.after_inverse, isometry.after_inverse]

/-- Exercise 13.1, composition half: the composite first applies `inner` and
then `outer`; its inverse is displayed in the opposite order. -/
def comp (outer inner : PlaneIsometry K) : PlaneIsometry K where
  toFun := fun point => outer (inner point)
  inverseFun := fun point => inner.inverseFun (outer.inverseFun point)
  inverse_after := by
    intro point
    rw [outer.inverse_after, inner.inverse_after]
  after_inverse := by
    intro point
    rw [inner.after_inverse, outer.after_inverse]
  preservesQuadrance := by
    intro first second
    rw [outer.preservesQuadrance, inner.preservesQuadrance]

@[simp] theorem identity_apply (point : Point K) :
    (identity : PlaneIsometry K) point = point := rfl

@[simp] theorem inverse_apply (isometry : PlaneIsometry K) (point : Point K) :
    isometry.inverse point = isometry.inverseFun point := rfl

@[simp] theorem comp_apply (outer inner : PlaneIsometry K) (point : Point K) :
    outer.comp inner point = outer (inner point) := rfl

/-- The point map of an isometry is injective, with its displayed inverse
providing the direct cancellation proof. -/
theorem injective (isometry : PlaneIsometry K) :
    Function.Injective isometry := by
  intro first second equalImages
  calc
    first = isometry.inverseFun (isometry first) :=
      (isometry.inverse_after first).symm
    _ = isometry.inverseFun (isometry second) := by rw [equalImages]
    _ = second := isometry.inverse_after second

/-- Every target point has the explicitly displayed inverse image. -/
theorem surjective (isometry : PlaneIsometry K) :
    Function.Surjective isometry := by
  intro point
  exact ⟨isometry.inverseFun point, isometry.after_inverse point⟩

/-- An orthogonality is an isometry fixing the displayed origin. -/
def IsOrthogonality (isometry : PlaneIsometry K) : Prop :=
  isometry planeOrigin = planeOrigin

/-- Isometries preserve the symmetric quadrea polynomial because they
preserve each of its three quadrance inputs. -/
theorem preservesQuadrea (isometry : PlaneIsometry K)
    (first second third : Point K) :
    quadrea (isometry first) (isometry second) (isometry third) =
      quadrea first second third := by
  unfold quadrea
  rw [isometry.preservesQuadrance, isometry.preservesQuadrance,
    isometry.preservesQuadrance]

/-- Theorem 91 (Isometries preserve collinearity), by the source's Quadrea
argument.  The characteristic-two exclusion is mathematically necessary for
this metric definition of isometry. -/
theorem preservesCollinearity [Nontrivial K] [DecidableEq K]
    (isometry : PlaneIsometry K) (twoNonzero : (2 : K) ≠ 0)
    (first second third : Point K) :
    Collinear first second third ↔
      Collinear (isometry first) (isometry second) (isometry third) := by
  have sourceIff :
      quadrea first second third = 0 ↔ Collinear first second third := by
    exact triple_quad_formula first second third twoNonzero
  have imageIff :
      quadrea (isometry first) (isometry second) (isometry third) = 0 ↔
        Collinear (isometry first) (isometry second) (isometry third) := by
    exact triple_quad_formula
      (isometry first) (isometry second) (isometry third) twoNonzero
  constructor
  · intro collinear
    apply imageIff.1
    rw [isometry.preservesQuadrea]
    exact sourceIff.2 collinear
  · intro collinear
    apply sourceIff.1
    rw [← isometry.preservesQuadrea first second third]
    exact imageIff.2 collinear

end PlaneIsometry

end DivineProportions
