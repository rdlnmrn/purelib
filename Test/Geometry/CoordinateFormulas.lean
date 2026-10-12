module

public import Purelib.Geometry.Projective.GaussianInt.Embedding
public import Purelib.LinearAlgebra.Coordinates3.Vector
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Embedding
import Purelib.Geometry.Projective.Line.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix

open Purelib

open Purelib.Data

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.GaussianInt

open Purelib.LinearAlgebra

public section
namespace Test.Geometry.CoordinateFormulas

/-- Embed both retained Gaussian-integer projective coordinates into the canonical Gaussian-rational carrier. -/
@[expose] public def referenceMapProj
    (point : Line.Proj Data.GaussianInt) :
    Line.Proj Data.Gaussian.Basic.Canonical :=
  ⟨GaussianInt.toGaussian point.p,
    GaussianInt.toGaussian point.q⟩

/-- Embed all four reference Gaussian-integer matrix entries into the canonical Gaussian-rational carrier. -/
@[expose] public def referenceMapMat
    (matrix : Coordinates2.Matrix Data.GaussianInt) :
    Coordinates2.Matrix Data.Gaussian.Basic.Canonical :=
  ⟨GaussianInt.toGaussian matrix.a,
    GaussianInt.toGaussian matrix.b,
    GaussianInt.toGaussian matrix.c,
    GaussianInt.toGaussian matrix.d⟩

/-- The retained coordinate embedding is definitionally the canonical projective embedding. -/
theorem mapProj_readback
    (point : Line.Proj Data.GaussianInt) :
    CoordinateFormulas.referenceMapProj point =
      Embedding.mapProj point := rfl

/-- The retained entrywise matrix embedding is definitionally the canonical matrix embedding. -/
theorem mapMat_readback
    (matrix : Coordinates2.Matrix Data.GaussianInt) :
    CoordinateFormulas.referenceMapMat matrix =
      Embedding.mapMat matrix := rfl

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The reference three-coordinate spread formula with retained non-null quadrance hypotheses. -/
@[expose] public def referenceSpread
    (first second : Coordinates3.Vector K)
    (_firstNonNull : Coordinates3.Vector.quadrance first ≠ 0)
    (_secondNonNull : Coordinates3.Vector.quadrance second ≠ 0) : K :=
  1 - Coordinates3.Vector.dot first second ^ 2 /
    (Coordinates3.Vector.quadrance first *
      Coordinates3.Vector.quadrance second)

/-- The retained spread formula is definitionally the canonical vector spread with the same non-null evidence. -/
theorem spread_readback
    (first second : Coordinates3.Vector K)
    (firstNonNull : Coordinates3.Vector.quadrance first ≠ 0)
    (secondNonNull : Coordinates3.Vector.quadrance second ≠ 0) :
    CoordinateFormulas.referenceSpread first second firstNonNull secondNonNull =
      Coordinates3.Vector.spread
        first second firstNonNull secondNonNull := rfl

end Test.Geometry.CoordinateFormulas
