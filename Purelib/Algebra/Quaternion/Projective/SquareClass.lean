module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.SquareClass.Basic
public import Purelib.Algebra.Field.SumsOfSquares.Four
public import Purelib.Algebra.Quaternion.Projective.Basic
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Algebra.Field.SquareClass.Basic

open Purelib.Algebra.Field.SumsOfSquares.Four

open Purelib.Algebra.Quaternion.Projective

open Purelib.Algebra.Quaternion.Projective.Basic

open Purelib.LinearAlgebra.Coordinates3

section
@[expose] public section

/-!
# Rational rotations, Theorem 61: the quadrance class

Square classes are represented quotient-free.  Equality carries an explicit
nonzero square factor, so invariance and multiplicativity remain executable
finite field calculations.
-/

section

variable {K : Type*} [ExplicitField K]

namespace Purelib.Algebra.Quaternion.Projective.SquareClass

section NonNullProportion

/-- Read the nonzero quaternion norm as a displayed square-class representative.

The representative retains the input norm and its existing nonzero certificate. -/
def NonNullProportion.quadranceClass (proportion :
  Basic.NonNullProportion K) :
    SquareClassRepresentative K where
  value := proportion.toProportion.norm
  nonzero := proportion.normNonzero

/-- Equivalent projective proportions have equivalent quadrance classes.

The supplied homogeneous scale witnesses the corresponding square factor between their norms. -/
theorem NonNullProportion.quadranceClass_respects_equivalent
    {left right : Basic.NonNullProportion K} (equivalent : left.Equivalent right) :
    (SquareClass.NonNullProportion.quadranceClass left).Equivalent (SquareClass.NonNullProportion.quadranceClass right)
      := by
  rcases equivalent with ⟨factor, factorNonzero, rightValue⟩
  refine ⟨factor, factorNonzero, ?_⟩
  change right.toProportion.norm = factor ^ 2 * left.toProportion.norm
  rw [rightValue, Proportion.norm_scale]

/-- The quadrance-class map preserves the displayed non-null quaternion product.

Equality retains the product of the two original norm representatives. -/
theorem NonNullProportion.quadranceClass_mul (left right :
  Basic.NonNullProportion K) :
    (SquareClass.NonNullProportion.quadranceClass (Basic.NonNullProportion.mul left right)) =
      SquareClassRepresentative.mul (SquareClass.NonNullProportion.quadranceClass left)
        (SquareClass.NonNullProportion.quadranceClass right) := by
  apply SquareClassRepresentative.ext
  exact Proportion.norm_mul left.toProportion right.toProportion

end NonNullProportion

end Purelib.Algebra.Quaternion.Projective.SquareClass

namespace Purelib.Algebra.Field.SumsOfSquares.Four.FourSquareRepresentation

/-- Construct a non-null quaternion proportion from a four-square representation.

The target is a retained nonzero square-class representative; the four certified roots become its scalar and vector
coordinates. -/
def proportion
    (target : SquareClassRepresentative K)
    (representation : FourSquareRepresentation target.value) :
    Basic.NonNullProportion K where
  scalar := representation.scalar
  vector := ⟨representation.t, representation.r, representation.s⟩
  normNonzero := by
    rw [show Proportion.norm
        ⟨representation.scalar,
          (⟨representation.t, representation.r, representation.s⟩ :
            Vector K)⟩ = target.value by
      unfold Proportion.norm Vector.quadrance Vector.dot
      change representation.scalar ^ 2 +
          (representation.t * representation.t +
            representation.r * representation.r +
            representation.s * representation.s) = target.value
      calc
        representation.scalar ^ 2 +
              (representation.t * representation.t +
                representation.r * representation.r +
                representation.s * representation.s) =
            representation.scalar ^ 2 + representation.t ^ 2 +
              representation.r ^ 2 + representation.s ^ 2 := by ring1
        _ = target.value := representation.equation]
    exact target.nonzero

/-- The quaternion proportion built from four squares realizes the retained target value.

Its quadrance class reads exactly the sum certified by the input representation. -/
theorem realizes_quadranceClass
    (target : SquareClassRepresentative K)
    (representation : FourSquareRepresentation target.value) :
    (SquareClass.NonNullProportion.quadranceClass (representation.proportion target)).value = target.value := by
  change Proportion.norm
      ⟨representation.scalar,
        (⟨representation.t, representation.r, representation.s⟩ : Vector K)⟩ =
    target.value
  unfold Proportion.norm Vector.quadrance Vector.dot
  change representation.scalar ^ 2 +
      (representation.t * representation.t +
        representation.r * representation.r +
        representation.s * representation.s) = target.value
  calc
    representation.scalar ^ 2 +
          (representation.t * representation.t +
            representation.r * representation.r +
            representation.s * representation.s) =
        representation.scalar ^ 2 + representation.t ^ 2 +
          representation.r ^ 2 + representation.s ^ 2 := by ring1
    _ = target.value := representation.equation

end Purelib.Algebra.Field.SumsOfSquares.Four.FourSquareRepresentation

end

end
