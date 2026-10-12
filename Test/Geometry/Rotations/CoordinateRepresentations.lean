module

import Purelib.Algebra.Quadratic.Pair.Basic
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Algebra.Quadratic.Pair.Coordinates
import Purelib.Geometry.Projective.Plane.AffineChart
public import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Algebra.Quadratic

open Purelib.LinearAlgebra

namespace Test.Geometry.Rotations.CoordinateRepresentations

variable {K : Type*}

set_option genInjectivity false in
/-- The reference three-coordinate vector layout used by the carrier correspondence. -/
private structure RetainedVector3 (K : Type*) where
  /-- The reference first vector coordinate. -/ x : K
  /-- The reference second vector coordinate. -/ y : K
  /-- The reference third vector coordinate. -/ z : K

constructive_injectivity RetainedVector3

set_option genInjectivity false in
/-- The reference three homogeneous point coordinates before canonical vector transport. -/
private structure RetainedHomogeneousPoint (K : Type*) where
  /-- The reference first homogeneous coordinate. -/ x : K
  /-- The reference second homogeneous coordinate. -/ y : K
  /-- The reference third homogeneous coordinate. -/ z : K

constructive_injectivity RetainedHomogeneousPoint

set_option genInjectivity false in
/-- The reference ordered triple of scalar coordinates. -/
private structure RetainedScalarTriple (K : Type*) where
  /-- The reference first triple coordinate. -/ first : K
  /-- The reference second triple coordinate. -/ second : K
  /-- The reference third triple coordinate. -/ third : K

constructive_injectivity RetainedScalarTriple

set_option genInjectivity false in
/-- The reference four-entry matrix layout in row order. -/
private structure RetainedMat2 (K : Type*) where
  /-- The reference upper-left matrix coordinate. -/ a : K
  /-- The reference upper-right matrix coordinate. -/ b : K
  /-- The reference lower-left matrix coordinate. -/ c : K
  /-- The reference lower-right matrix coordinate. -/ d : K

constructive_injectivity RetainedMat2

set_option genInjectivity false in
/-- The reference time/radial four-entry matrix layout. -/
private structure RetainedMatrix2 (K : Type*) where
  /-- The reference time-time matrix coordinate. -/ tt : K
  /-- The reference time-radial matrix coordinate. -/ tr : K
  /-- The reference radial-time matrix coordinate. -/ rt : K
  /-- The reference radial-radial matrix coordinate. -/ rr : K

constructive_injectivity RetainedMatrix2

set_option genInjectivity false in
/-- The reference ordered scalar pair used by the quadratic carrier. -/
private structure RetainedScalarPair (K : Type*) where
  /-- The reference first pair coordinate. -/ first : K
  /-- The reference second pair coordinate. -/ second : K

constructive_injectivity RetainedScalarPair

/-- Transport the reference vector coordinates to the canonical three-coordinate vector. -/
private def vector3To (value : RetainedVector3 K) :
    Coordinates3.Vector K := ⟨value.x, value.y, value.z⟩
/-- Read the canonical vector into its reference coordinate layout. -/
private def vector3From (value : Coordinates3.Vector K) :
    RetainedVector3 K := ⟨value.t, value.r, value.s⟩
/-- Transport the reference homogeneous point coordinates to the canonical vector. -/
private def homogeneousTo (value : RetainedHomogeneousPoint K) :
    Coordinates3.Vector K := ⟨value.x, value.y, value.z⟩
/-- Read the canonical vector into the reference homogeneous point layout. -/
private def homogeneousFrom (value : Coordinates3.Vector K) :
    RetainedHomogeneousPoint K := ⟨value.t, value.r, value.s⟩
/-- Transport the reference ordered scalar triple to the canonical vector. -/
private def tripleTo (value : RetainedScalarTriple K) :
    Coordinates3.Vector K := ⟨value.first, value.second, value.third⟩
/-- Read the canonical vector into the reference ordered scalar triple. -/
private def tripleFrom (value : Coordinates3.Vector K) :
    RetainedScalarTriple K := ⟨value.t, value.r, value.s⟩
/-- Transport the reference row-ordered matrix entries to the canonical two-dimensional matrix. -/
private def matTo (value : RetainedMat2 K) :
    Coordinates2.Matrix K := ⟨value.a, value.b, value.c, value.d⟩
/-- Read the canonical matrix into the reference row-ordered layout. -/
private def matFrom (value : Coordinates2.Matrix K) :
    RetainedMat2 K := ⟨value.a, value.b, value.c, value.d⟩
/-- Transport the reference time/radial matrix entries to the canonical matrix. -/
private def matrixTo (value : RetainedMatrix2 K) :
    Coordinates2.Matrix K := ⟨value.tt, value.tr, value.rt, value.rr⟩
/-- Read the canonical matrix into the reference time/radial layout. -/
private def matrixFrom (value : Coordinates2.Matrix K) :
    RetainedMatrix2 K := ⟨value.a, value.b, value.c, value.d⟩
/-- Transport the reference scalar pair to the quadratic pair with parameter one. -/
private def pairTo [One K] (value : RetainedScalarPair K) :
    Algebra.Quadratic.Pair K (1 : K) := ⟨value.first, value.second⟩
/-- Read the quadratic pair with parameter one into its reference ordered scalar pair. -/
private def pairFrom [One K] (value : Algebra.Quadratic.Pair K (1 : K)) :
    RetainedScalarPair K := ⟨value.re, value.im⟩

/-- Canonical transport and readback preserve the reference vector. -/
private theorem vector_reference_roundtrip (value : RetainedVector3 K) : vector3From (vector3To value) = value := by
  cases value; rfl
/-- Reference vector readback and transport preserve the canonical carrier value. -/
private theorem vector_canonical_roundtrip (value : Coordinates3.Vector K) :
    vector3To (vector3From value) = value := by cases value; rfl
/-- Canonical transport and readback preserve the reference homogeneous point. -/
private theorem homogeneous_reference_roundtrip (value : RetainedHomogeneousPoint K) : homogeneousFrom (homogeneousTo
  value) = value := by
  cases value; rfl
/-- Reference homogeneous point readback and transport preserve the canonical carrier value. -/
private theorem homogeneous_canonical_roundtrip (value : Coordinates3.Vector K) :
    homogeneousTo (homogeneousFrom value) = value := by cases value; rfl
/-- Canonical transport and readback preserve the reference ordered scalar triple. -/
private theorem triple_reference_roundtrip (value : RetainedScalarTriple K) : tripleFrom (tripleTo value) = value := by
  cases value; rfl
/-- Reference ordered scalar triple readback and transport preserve the canonical carrier value. -/
private theorem triple_canonical_roundtrip (value : Coordinates3.Vector K) :
    tripleTo (tripleFrom value) = value := by cases value; rfl
/-- Canonical transport and readback preserve the reference row-ordered matrix. -/
private theorem mat_reference_roundtrip (value : RetainedMat2 K) : matFrom (matTo value) = value := by cases value; rfl
/-- Reference row-ordered matrix readback and transport preserve the canonical carrier value. -/
private theorem mat_canonical_roundtrip (value : Coordinates2.Matrix K) :
    matTo (matFrom value) = value := by cases value; rfl
/-- Canonical transport and readback preserve the reference time/radial matrix. -/
private theorem matrix_reference_roundtrip (value : RetainedMatrix2 K) : matrixFrom (matrixTo value) = value := by
  cases value
  rfl
/-- Reference time/radial matrix readback and transport preserve the canonical carrier value. -/
private theorem matrix_canonical_roundtrip (value : Coordinates2.Matrix K) :
    matrixTo (matrixFrom value) = value := by cases value; rfl
/-- Canonical transport and readback preserve the reference quadratic scalar pair. -/
private theorem pair_reference_roundtrip [One K] (value : RetainedScalarPair K) : pairFrom (pairTo value) = value := by
  cases value; rfl
/-- Reference quadratic scalar pair readback and transport preserve the canonical carrier value. -/
private theorem pair_canonical_roundtrip [One K] (value : Algebra.Quadratic.Pair K (1 : K)) :
    pairTo (pairFrom value) = value := by cases value; rfl

/-- Multiply the reference row-ordered two-dimensional matrices by their retained coordinate formula. -/
private def retainedMatMul [Add K] [Mul K] (left right : RetainedMat2 K) : RetainedMat2 K :=
  ⟨left.a * right.a + left.b * right.c, left.a * right.b + left.b * right.d,
    left.c * right.a + left.d * right.c, left.c * right.b + left.d * right.d⟩
/-- Multiply the reference time/radial matrices by their retained coordinate formula. -/
private def retainedMatrixMul [Add K] [Mul K] (left right : RetainedMatrix2 K) : RetainedMatrix2 K :=
  ⟨left.tt * right.tt + left.tr * right.rt,
    left.tt * right.tr + left.tr * right.rr,
    left.rt * right.tt + left.rr * right.rt,
    left.rt * right.tr + left.rr * right.rr⟩
/-- Multiply the reference scalar pairs by the Gaussian coordinate formula. -/
private def retainedPairMul [CommRing K] (left right : RetainedScalarPair K) : RetainedScalarPair K :=
  ⟨left.first * right.first - left.second * right.second,
    left.first * right.second + left.second * right.first⟩

/-- Canonical transport preserves the reference row-ordered matrix product. -/
private theorem mat_product_correspondence [Add K] [Mul K] (left right : RetainedMat2 K) :
    matTo (retainedMatMul left right) =
      Coordinates2.Matrix.mul (matTo left) (matTo right) := rfl
/-- Canonical transport preserves the reference time/radial matrix product. -/
private theorem matrix_product_correspondence [Add K] [Mul K] (left right : RetainedMatrix2 K) :
    matrixTo (retainedMatrixMul left right) =
      Coordinates2.Matrix.mul (matrixTo left) (matrixTo right) := rfl
/-- Canonical transport preserves the reference pair product for quadratic parameter one. -/
private theorem pair_product_correspondence [CommRing K] (left right : RetainedScalarPair K) :
    pairTo (retainedPairMul left right) =
      Algebra.Quadratic.Pair.multiply (pairTo left) (pairTo right) := by
  apply Algebra.Quadratic.Pair.ext
  · change left.first * right.first - left.second * right.second =
      left.first * right.first - (1 : K) * left.second * right.second
    ring1
  · rfl

/-- Add the reference three-coordinate vectors entry by entry. -/
private def retainedVectorAdd [Add K] (left right : RetainedVector3 K) : RetainedVector3 K :=
  ⟨left.x + right.x, left.y + right.y, left.z + right.z⟩
/-- Scale each reference homogeneous point coordinate by the supplied scalar. -/
private def retainedHomogeneousScale [Mul K] (factor : K)
    (value : RetainedHomogeneousPoint K) : RetainedHomogeneousPoint K :=
  ⟨factor * value.x, factor * value.y, factor * value.z⟩
/-- Scale each reference ordered triple coordinate by the supplied scalar. -/
private def retainedTripleScale [Mul K] (factor : K)
    (value : RetainedScalarTriple K) : RetainedScalarTriple K :=
  ⟨factor * value.first, factor * value.second, factor * value.third⟩

/-- Canonical transport preserves the reference vector sum. -/
private theorem vector_add_correspondence [Algebra.Field.ExplicitField K] (left right : RetainedVector3 K) :
    vector3To (retainedVectorAdd left right) =
      Coordinates3.Vector.add (vector3To left) (vector3To right) := rfl
/-- Canonical transport preserves scalar multiplication of the reference homogeneous coordinates. -/
private theorem homogeneous_scale_correspondence [Algebra.Field.ExplicitField K] (factor : K) (value :
  RetainedHomogeneousPoint K) :
    homogeneousTo (retainedHomogeneousScale factor value) =
      Coordinates3.Vector.scale factor (homogeneousTo value) := rfl
/-- Canonical transport preserves scalar multiplication of the reference ordered triple. -/
private theorem triple_scale_correspondence [Algebra.Field.ExplicitField K] (factor : K) (value : RetainedScalarTriple
  K) :
    tripleTo (retainedTripleScale factor value) =
      Coordinates3.Vector.scale factor (tripleTo value) := rfl

/-- The reference explicit-field assumptions suffice for the exact matrix-product correspondence. -/
private theorem matrix_reference_hypotheses_product_correspondence
    [Algebra.Field.ExplicitField K] (left right : RetainedMatrix2 K) :
    matrixTo (retainedMatrixMul left right) =
      Coordinates2.Matrix.mul (matrixTo left) (matrixTo right) := rfl

/-- The reference three-coordinate dot product. -/
private def retainedVectorDot [Mul K] [Add K] (left right : RetainedVector3 K) : K :=
  left.x * right.x + left.y * right.y + left.z * right.z
/-- The reference three-coordinate vector's dot product with itself. -/
private def retainedVectorQuadrance [Mul K] [Add K] (value : RetainedVector3 K) : K :=
  retainedVectorDot value value

/-- The retained reference quadrance of a sum equals the individual quadrances plus twice the reference dot product. -/
private theorem vector_reference_quadrance_add_contract
    [Algebra.Field.ExplicitField K] (left right : RetainedVector3 K) :
    retainedVectorQuadrance (retainedVectorAdd left right) =
      retainedVectorQuadrance left + retainedVectorQuadrance right +
        2 * retainedVectorDot left right := by
  change Coordinates3.Vector.quadrance
      (Coordinates3.Vector.add (vector3To left) (vector3To right)) =
    Coordinates3.Vector.quadrance (vector3To left) +
      Coordinates3.Vector.quadrance (vector3To right) +
        2 * Coordinates3.Vector.dot (vector3To left) (vector3To right)
  rw [Coordinates3.Vector.quadrance_add]
  ring1

end Test.Geometry.Rotations.CoordinateRepresentations
