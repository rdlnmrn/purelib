module
import Purelib.Data.Gaussian.Basic
public import Purelib.Geometry.Projective.Bihomographic.Basic
import Purelib.Geometry.Projective.Line.Basic
public import Purelib.Geometry.Projective.Line.Matrix
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Tactic.Ring

open Purelib

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Bihomographic.Basic

open Purelib.Geometry.Projective.Line

open Purelib.Geometry.Projective.Line.Basic

open Purelib.LinearAlgebra.Coordinates2.Matrix

section
@[expose] public section

/-!
# Constructive bihomographic states for elementary CCL arithmetic

The arithmetic state is kept homogeneous.  This avoids dividing by an input
or output denominator merely to state substitution correctness, and it makes
zero and pole outcomes ordinary projective coordinates rather than hidden
exceptional values.
-/

namespace Purelib.Geometry.Projective.Bihomographic.Basic.State
section

/-- Consume a projective matrix from the left input. -/
def precomposeLeft (state : Bihomographic.Basic.State)
  (matrix : GaussianMatrix) : Bihomographic.Basic.State :=
  { a := state.a * matrix.a + state.c * matrix.c
    b := state.b * matrix.a + state.d * matrix.c
    c := state.a * matrix.b + state.c * matrix.d
    d := state.b * matrix.b + state.d * matrix.d
    e := state.e * matrix.a + state.g * matrix.c
    f := state.f * matrix.a + state.h * matrix.c
    g := state.e * matrix.b + state.g * matrix.d
    h := state.f * matrix.b + state.h * matrix.d }

/-- Consume a projective matrix from the right input. -/
def precomposeRight (state : Bihomographic.Basic.State)
  (matrix : GaussianMatrix) : Bihomographic.Basic.State :=
  { a := state.a * matrix.a + state.b * matrix.c
    b := state.a * matrix.b + state.b * matrix.d
    c := state.c * matrix.a + state.d * matrix.c
    d := state.c * matrix.b + state.d * matrix.d
    e := state.e * matrix.a + state.f * matrix.c
    f := state.e * matrix.b + state.f * matrix.d
    g := state.g * matrix.a + state.h * matrix.c
    h := state.g * matrix.b + state.h * matrix.d }

/-- Apply a projective matrix to the output value. In the transducer this is used with the adjugate of an emitted
decoder block. -/
def postcompose (matrix :
  GaussianMatrix) (state : Bihomographic.Basic.State) : Bihomographic.Basic.State :=
  { a := matrix.a * state.a + matrix.b * state.e
    b := matrix.a * state.b + matrix.b * state.f
    c := matrix.a * state.c + matrix.b * state.g
    d := matrix.a * state.d + matrix.b * state.h
    e := matrix.c * state.a + matrix.d * state.e
    f := matrix.c * state.b + matrix.d * state.f
    g := matrix.c * state.c + matrix.d * state.g
    h := matrix.c * state.d + matrix.d * state.h }

/-- Left input substitution is exact as a homogeneous polynomial identity. -/
theorem map_precomposeLeft (state :
  Bihomographic.Basic.State) (matrix : GaussianMatrix) (x y : GaussianLine)
  :
    (state.precomposeLeft matrix).map x y =
      state.map (Line.Matrix.act matrix x) y := by
  apply Proj.ext <;>
    apply Data.Gaussian.Basic.ext <;>
      simp only [State.map, precomposeLeft, Line.Matrix.act,
        Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im,
        Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im] <;> ring1

/-- Right input substitution is exact as a homogeneous polynomial identity. -/
theorem map_precomposeRight (state :
  Bihomographic.Basic.State) (matrix : GaussianMatrix) (x y : GaussianLine)
  :
    (state.precomposeRight matrix).map x y =
      state.map x (Line.Matrix.act matrix y) := by
  apply Proj.ext <;>
    apply Data.Gaussian.Basic.ext <;>
      simp only [State.map, precomposeRight, Line.Matrix.act,
        Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im,
        Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im] <;> ring1

/-- Output substitution is exact, including at a zero denominator. -/
theorem map_postcompose (matrix :
  GaussianMatrix) (state : Bihomographic.Basic.State) (x y : GaussianLine) :
    (state.postcompose matrix).map x y =
      Line.Matrix.act matrix (state.map x y) := by
  apply Proj.ext <;>
    apply Data.Gaussian.Basic.ext <;>
      simp only [State.map, postcompose, Line.Matrix.act,
        Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im,
        Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im] <;> ring1

/-- After emitting a decoder block, the adjugate state maps the old output back to the new projective tail, up to the
displayed nonzero determinant. -/
theorem map_postcompose_adjugate (matrix :
  GaussianMatrix) (state : Bihomographic.Basic.State)
    (x y : GaussianLine) :
    (state.postcompose
      (BoundaryAdjugate.adjugate matrix)).map x y =
      Line.Matrix.act (BoundaryAdjugate.adjugate matrix)
        (state.map x y) :=
  map_postcompose _ _ _ _

end
end Purelib.Geometry.Projective.Bihomographic.Basic.State

end
