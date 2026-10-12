module

import Purelib.Data.Gaussian.Basic
public import Purelib.Geometry.Projective.Line.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Geometry.Projective.Line

open Purelib.Geometry.Projective.Line.Basic

section
@[expose] public section

/-!
# Constructive bihomographic states for elementary CCL arithmetic

The arithmetic state is kept homogeneous.  This avoids dividing by an input
or output denominator merely to state substitution correctness, and it makes
zero and pole outcomes ordinary projective coordinates rather than hidden
exceptional values.
-/

namespace Purelib.Geometry.Projective.Bihomographic.Basic

set_option genInjectivity false in
/-- Eight coefficients for `(a x y + b x + c y + d) / (e x y + f x + g y + h)`. -/
structure State where
  /-- Coefficient of the product term in the numerator. -/ a : Data.Gaussian.Basic.Canonical
  /-- Coefficient of the first variable in the numerator. -/ b : Data.Gaussian.Basic.Canonical
  /-- Coefficient of the second variable in the numerator. -/ c : Data.Gaussian.Basic.Canonical
  /-- Constant term in the numerator. -/ d : Data.Gaussian.Basic.Canonical
  /-- Coefficient of the product term in the denominator. -/ e : Data.Gaussian.Basic.Canonical
  /-- Coefficient of the first variable in the denominator. -/ f : Data.Gaussian.Basic.Canonical
  /-- Coefficient of the second variable in the denominator. -/ g : Data.Gaussian.Basic.Canonical
  /-- Constant term in the denominator. -/ h : Data.Gaussian.Basic.Canonical

constructive_injectivity State

namespace State

/-- Homogeneous evaluation on two projective inputs. -/
def map (state :
  State) (x y : GaussianLine) :
  GaussianLine :=
  ⟨state.a * x.p * y.p + state.b * x.p * y.q +
      state.c * x.q * y.p + state.d * x.q * y.q,
    state.e * x.p * y.p + state.f * x.p * y.q +
      state.g * x.q * y.p + state.h * x.q * y.q⟩

/-- The ordinary affine specialization, still returned homogeneously. -/
def affineMap (state :
  State) (x y : Data.Gaussian.Basic.Canonical) :
  GaussianLine :=
  state.map (Proj.affine x) (Proj.affine y)
end State
end Purelib.Geometry.Projective.Bihomographic.Basic

end
