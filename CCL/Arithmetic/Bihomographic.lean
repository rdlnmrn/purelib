import mathlib.Tactic.QuotientFreeRing
import CCL.Arithmetic.RedundantOutput
import CCL.Boundary.Pullback

/-!
# Constructive bihomographic states for elementary CCL arithmetic

The arithmetic state is kept homogeneous.  This avoids dividing by an input
or output denominator merely to state substitution correctness, and it makes
zero and pole outcomes ordinary projective coordinates rather than hidden
exceptional values.
-/

namespace CCL.Bihomographic

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Proj := CCL.GaussianProjective.Proj
abbrev Mat2 := CCL.GaussianProjective.Mat2

open RFAP.ConstructiveGaussian.Gaussian

/-- Eight coefficients for
`(a x y + b x + c y + d) / (e x y + f x + g y + h)`. -/
structure State where
  a : Gaussian
  b : Gaussian
  c : Gaussian
  d : Gaussian
  e : Gaussian
  f : Gaussian
  g : Gaussian
  h : Gaussian

namespace State

/-- Homogeneous evaluation on two projective inputs. -/
def map (state : State) (x y : Proj) : Proj :=
  ⟨state.a * x.p * y.p + state.b * x.p * y.q +
      state.c * x.q * y.p + state.d * x.q * y.q,
    state.e * x.p * y.p + state.f * x.p * y.q +
      state.g * x.q * y.p + state.h * x.q * y.q⟩

/-- The ordinary affine specialization, still returned homogeneously. -/
def affineMap (state : State) (x y : Gaussian) : Proj :=
  state.map (CCL.Proj.affine x) (CCL.Proj.affine y)

/-- Consume a projective matrix from the left input. -/
def precomposeLeft (state : State) (matrix : Mat2) : State :=
  { a := state.a * matrix.a + state.c * matrix.c
    b := state.b * matrix.a + state.d * matrix.c
    c := state.a * matrix.b + state.c * matrix.d
    d := state.b * matrix.b + state.d * matrix.d
    e := state.e * matrix.a + state.g * matrix.c
    f := state.f * matrix.a + state.h * matrix.c
    g := state.e * matrix.b + state.g * matrix.d
    h := state.f * matrix.b + state.h * matrix.d }

/-- Consume a projective matrix from the right input. -/
def precomposeRight (state : State) (matrix : Mat2) : State :=
  { a := state.a * matrix.a + state.b * matrix.c
    b := state.a * matrix.b + state.b * matrix.d
    c := state.c * matrix.a + state.d * matrix.c
    d := state.c * matrix.b + state.d * matrix.d
    e := state.e * matrix.a + state.f * matrix.c
    f := state.e * matrix.b + state.f * matrix.d
    g := state.g * matrix.a + state.h * matrix.c
    h := state.g * matrix.b + state.h * matrix.d }

/-- Apply a projective matrix to the output value.  In the transducer this is
used with the adjugate of an emitted decoder block. -/
def postcompose (matrix : Mat2) (state : State) : State :=
  { a := matrix.a * state.a + matrix.b * state.e
    b := matrix.a * state.b + matrix.b * state.f
    c := matrix.a * state.c + matrix.b * state.g
    d := matrix.a * state.d + matrix.b * state.h
    e := matrix.c * state.a + matrix.d * state.e
    f := matrix.c * state.b + matrix.d * state.f
    g := matrix.c * state.c + matrix.d * state.g
    h := matrix.c * state.d + matrix.d * state.h }

/-- Left input substitution is exact as a homogeneous polynomial identity. -/
theorem map_precomposeLeft (state : State) (matrix : Mat2) (x y : Proj) :
    (state.precomposeLeft matrix).map x y =
      state.map (CCL.Mat2.act matrix x) y := by
  apply CCL.Proj.ext <;>
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [map, precomposeLeft, CCL.Mat2.act, add_re, add_im,
        mul_re, mul_im] <;> ring1

/-- Right input substitution is exact as a homogeneous polynomial identity. -/
theorem map_precomposeRight (state : State) (matrix : Mat2) (x y : Proj) :
    (state.precomposeRight matrix).map x y =
      state.map x (CCL.Mat2.act matrix y) := by
  apply CCL.Proj.ext <;>
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [map, precomposeRight, CCL.Mat2.act, add_re, add_im,
        mul_re, mul_im] <;> ring1

/-- Output substitution is exact, including at a zero denominator. -/
theorem map_postcompose (matrix : Mat2) (state : State) (x y : Proj) :
    (state.postcompose matrix).map x y =
      CCL.Mat2.act matrix (state.map x y) := by
  apply CCL.Proj.ext <;>
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [map, postcompose, CCL.Mat2.act, add_re, add_im,
        mul_re, mul_im] <;> ring1

/-- After emitting a decoder block, the adjugate state maps the old output
back to the new projective tail, up to the displayed nonzero determinant. -/
theorem map_postcompose_adjugate (matrix : Mat2) (state : State)
    (x y : Proj) :
    (state.postcompose
      (CCL.CCLPullback.adjugate matrix)).map x y =
      CCL.Mat2.act (CCL.CCLPullback.adjugate matrix)
        (state.map x y) :=
  map_postcompose _ _ _ _

end State

/-- The four elementary projective operations. -/
inductive Operation where
  | add | sub | mul | div
deriving DecidableEq, Repr

/-- Initial coefficient tuple for an elementary operation. -/
def initial : Operation → State
  | .add => ⟨0, 1, 1, 0, 0, 0, 0, 1⟩
  | .sub => ⟨0, 1, -1, 0, 0, 0, 0, 1⟩
  | .mul => ⟨1, 0, 0, 0, 0, 0, 0, 1⟩
  | .div => ⟨0, 1, 0, 0, 0, 0, 1, 0⟩

theorem initial_add (x y : Gaussian) :
    (initial .add).affineMap x y = CCL.Proj.affine (x + y) := by
  apply CCL.Proj.ext <;>
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [State.affineMap, State.map, initial, CCL.Proj.affine,
        add_re, add_im, mul_re, mul_im, zero_re, zero_im, one_re, one_im] <;>
      ring1

theorem initial_sub (x y : Gaussian) :
    (initial .sub).affineMap x y = CCL.Proj.affine (x - y) := by
  apply CCL.Proj.ext <;>
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [State.affineMap, State.map, initial, CCL.Proj.affine,
        sub_re, sub_im, add_re, add_im, mul_re, mul_im, neg_re, neg_im,
        zero_re, zero_im, one_re, one_im] <;> ring1

theorem initial_mul (x y : Gaussian) :
    (initial .mul).affineMap x y = CCL.Proj.affine (x * y) := by
  apply CCL.Proj.ext <;>
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [State.affineMap, State.map, initial, CCL.Proj.affine,
        add_re, add_im, mul_re, mul_im, zero_re, zero_im, one_re, one_im] <;>
      ring1

/-- Division is the homogeneous pair `[x:y]`.  If `y=0`, this is the pole
coordinate rather than an illicit affine quotient. -/
theorem initial_div (x y : Gaussian) :
    (initial .div).affineMap x y = ⟨x, y⟩ := by
  apply CCL.Proj.ext <;>
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [State.affineMap, State.map, initial, CCL.Proj.affine,
        add_re, add_im, mul_re, mul_im, zero_re, zero_im, one_re, one_im] <;>
      ring1

end CCL.Bihomographic
