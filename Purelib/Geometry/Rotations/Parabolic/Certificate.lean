module
public import Purelib.Geometry.Rotations.Basic
import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.LinearAlgebra.Coordinates3.Matrix

open Purelib.Geometry

open Purelib.LinearAlgebra.Coordinates3

section
@[expose] public section

/-!
# Section 13.3: open problems

Problem 68 is refuted as printed by the projection counterexample already
recorded for Conjecture 52; its hardened unital five-parameter replacement is
proved over the paper's primary rational field.  For Problem 69, the missing PDF glyph is the
quadrance-class homomorphism `chi`, represented here by
`RotationQuadranceClass.ofRotation`; the exact excluded affine quadric is
`Q = -1`.  The executable finite enumerators and small-field regression
tables live in `FiniteFieldCounting`.  Problems 70 and 71 retain the pointwise
finite data and algebraic parts that follow from the preceding development;
Problem 70's finitely generated subgroup clause is classified through exact
arbitrary finite-word queries and its complete finite `chi` quotient;
Problem 72 is completed by the constructive projective polarity in
`ProjectiveDuality`.
-/

namespace Purelib.Geometry.Rotations.Parabolic.Certificate

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- A checked certificate for the parabolic class singled out in Problem 69. The characteristic-polynomial identity is
pointwise finite algebra and does not enumerate the ambient field. -/
structure ParabolicRotationCertificate (rotation :
  Rotations.Basic.Rotation K) where
  /-- The rotation matrix differs from the identity. -/ nonidentityMatrix : rotation.matrix ≠ Matrix3.identity
  /-- The characteristic polynomial is `(X - 1)^3` at every scalar input. -/ characteristicUnipotent : ∀ X : K,
    Matrix3.characteristicValue rotation.matrix X = (X - 1) ^ 3
end Purelib.Geometry.Rotations.Parabolic.Certificate

end
