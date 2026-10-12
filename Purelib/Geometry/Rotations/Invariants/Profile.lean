module

import Purelib.Geometry.Rotations.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.SquareClass.Basic
public import Purelib.Geometry.Rotations.Projective.SquareClass
import Purelib.Geometry.Rotations.Spread
import Init.Prelude
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry

open Purelib.Geometry.Rotations

open Purelib.Geometry.Rotations.Projective.SquareClass

section
public section

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

namespace Purelib.Geometry.Rotations.Invariants.Profile

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

set_option genInjectivity false in
/-- Cached local invariants of one rotation. The global finite solution in `FiniteFieldCounting` complements this
pointwise profile with executable carriers, classifications, and closed counts. -/
structure RotationInvariantProfile [DecidableEq K]
    (rotation : Rotations.Basic.Rotation K) (twoNonzero : (2 : K) ≠ 0) where
  /-- The cached half-spread scalar of the original rotation. -/ halfSpreadValue : K
  /-- The cached scalar is exactly the trace-defined half spread. -/ halfSpread_spec : halfSpreadValue =
    Spread.halfSpread rotation
  /-- The cached square-class representative of the rotation quadrance invariant. -/ quadranceClass :
    SquareClass.Basic.SquareClassRepresentative K
  /-- The cached class is exactly the class computed from the original rotation. -/ quadranceClass_spec : quadranceClass
    =
    RotationQuadranceClass.ofRotation rotation twoNonzero

constructive_injectivity RotationInvariantProfile

/-- The canonical pointwise profile requires only the finite calculations already formalized in Theorems 58 and 61. -/
@[expose] def rotationInvariantProfile [DecidableEq K] (rotation :
  Rotations.Basic.Rotation K)
    (twoNonzero : (2 : K) ≠ 0) :
    RotationInvariantProfile rotation twoNonzero where
  halfSpreadValue := Spread.halfSpread rotation
  halfSpread_spec := rfl
  quadranceClass := RotationQuadranceClass.ofRotation rotation twoNonzero
  quadranceClass_spec := rfl

/-! ## Problem 70 -/

end Purelib.Geometry.Rotations.Invariants.Profile

end
