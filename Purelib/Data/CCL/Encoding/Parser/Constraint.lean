module

import Purelib.Data.Gaussian.Basic
public import Purelib.Data.CCL.Encoding.Parser.Semantics.Basic
import Purelib.Data.CCL.Encoding.Parser.Syntax
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
public import Purelib.Geometry.Projective.Homography.Basic
import Purelib.Geometry.Projective.Homography.Composition
import Purelib.LinearAlgebra.Coordinates2.Matrix
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-!
# Finite raw-prefix parser over constructive Gaussian fractions

The completed-block encoder is not enough for a persistent root name: a
request may stop inside a unary header or after only one or two sector bits.
This module records exactly that unfinished syntax, the finite decoder
product, and the finite list of already completed block constraints.  It is
the state needed by the box/CCL next-bit controller; no stream, completion,
or collection of compatible points is formed.
-/

namespace Purelib.Data.CCL.Encoding.Parser

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
set_option genInjectivity false in
/-- Retain one completed block constraint and its matrix pullback from the current tail.

The block kind, exponent and sector are preserved alongside the exact matrix. Holding the constraint requires both a
nonzero homographic denominator and the retained block's radial and sector conditions. -/
structure Constraint where
  /-- The exact homography pulling the current tail back to this constraint's completed block. -/ matrix :
    LinearAlgebra.Coordinates2.Matrix.GaussianMatrix
  /-- The retained initial-high, initial-low or loop block kind. -/ kind : Parser.Syntax.BlockKind
  /-- The retained natural normalization exponent. -/ exponent : Nat
  /-- The retained nominal sector of the completed block. -/ sector : ComplexContinuedFraction.Encoding.Sector
deriving DecidableEq

constructive_injectivity Constraint

namespace Constraint

end Constraint
namespace Constraint

open Purelib.Data.CCL.Encoding in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Precompose the retained constraint with a block matrix, preserving its original kind, exponent and sector. -/
def precompose (constraint : Constraint)
  (block : LinearAlgebra.Coordinates2.Matrix.GaussianMatrix) : Constraint :=
  { constraint with matrix := Matrix2.mul constraint.matrix block }

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Projective in
/-- Require a nonzero retained denominator and the exact completed-block predicate at the matrix image of the supplied
tail. -/
def Holds (constraint : Constraint)
  (tail : Basic.Canonical) : Prop :=
  Homography.Basic.denominator constraint.matrix tail ≠ 0 ∧
    Parser.Semantics.Basic.fullBlockHolds constraint.kind constraint.exponent constraint.sector
      (Homography.Basic.homographic constraint.matrix tail)

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Gaussian in
/-- Decide the retained constraint's denominator and completed-block conditions at a Gaussian tail. -/
instance holdsDecidable (constraint :
  Constraint) (tail : Basic.Canonical) :
    Decidable (constraint.Holds tail) := by
  unfold Holds
  infer_instance

end Constraint
end Purelib.Data.CCL.Encoding.Parser

end

section
@[expose] public section

/-!
# Affine semantics of constructive raw-parser states

Parser constraints are evaluated on the current affine tail.  These finite
algebraic lemmas prove that decoder homographies compose in parser order and
that completing a raw block preserves the represented original input.
-/

namespace Purelib.Data.CCL.Encoding.Parser.Constraint

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Projective in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- With nonzero block denominator, the precomposed constraint holds exactly when the original holds at the block
homography image. -/
theorem constraint_precompose_iff
    (constraint : Constraint) (block : LinearAlgebra.Coordinates2.Matrix.GaussianMatrix) (tail :
      Basic.Canonical)
    (blockDenominator : Homography.Basic.denominator block tail ≠ 0) :
    (constraint.precompose block).Holds tail ↔
      constraint.Holds (Homography.Basic.homographic block tail) := by
  constructor
  · rintro ⟨productDenominator, blockHolds⟩
    have oldDenominator :
        Homography.Basic.denominator constraint.matrix (Homography.Basic.homographic block tail) ≠ 0 :=
      (Homography.Composition.denominator_mul_ne_iff constraint.matrix block tail
        blockDenominator).1 productDenominator
    refine ⟨oldDenominator, ?_⟩
    rw [← Homography.Composition.homographic_mul constraint.matrix block tail blockDenominator
      oldDenominator]
    exact blockHolds
  · rintro ⟨oldDenominator, blockHolds⟩
    have productDenominator :
        Homography.Basic.denominator (Matrix2.mul constraint.matrix block) tail ≠ 0 :=
      (Homography.Composition.denominator_mul_ne_iff constraint.matrix block tail
        blockDenominator).2 oldDenominator
    refine ⟨productDenominator, ?_⟩
    change Parser.Semantics.Basic.fullBlockHolds constraint.kind constraint.exponent
      constraint.sector
        (Homography.Basic.homographic (Matrix2.mul constraint.matrix block) tail)
    rw [Homography.Composition.homographic_mul constraint.matrix block tail blockDenominator
      oldDenominator]
    exact blockHolds
end Purelib.Data.CCL.Encoding.Parser.Constraint

end
