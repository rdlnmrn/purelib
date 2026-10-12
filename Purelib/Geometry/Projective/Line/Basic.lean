module

public import Purelib.Data.Gaussian.Basic
public import Purelib.Data.GaussianInt.Basic
meta import Purelib.Elab.Deriving.Repr
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Tactic.Ring.Basic

import Init.Prelude
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Data

section
section
@[expose] public section
namespace Purelib.Geometry.Projective.Line

set_option genInjectivity false in
/-- A finite homogeneous coordinate pair `[p : q]`. -/
@[ext]
structure Proj (K : Type*) where
  /-- Numerator coordinate of the homogeneous pair. -/ p : K
  /-- Denominator coordinate of the homogeneous pair. -/ q : K
deriving DecidableEq

constructive_injectivity Proj

derive_exposed_repr Proj

end Purelib.Geometry.Projective.Line
end
end

end

section
@[expose] public section
namespace Purelib.Geometry.Projective.Line.Basic
/-- Homogeneous coordinate pairs over the integral Gaussian carrier. -/
abbrev SourceEncodingEncoderIntegralProjAlias :=
  Proj GaussianInt.Basic.SourceEncodingEncoderGaussianIntAlias
end Purelib.Geometry.Projective.Line.Basic

end

section
section
@[expose] public section
namespace Purelib.Geometry.Projective.Line.Basic
/-- Homogeneous coordinate pairs over Gaussian integers. -/
abbrev SourceCCFEncoderIntegralProjAlias := Proj
  Data.GaussianInt
end Purelib.Geometry.Projective.Line.Basic
end

end

section
section
@[expose] public section
namespace Purelib.Geometry.Projective.Line.Basic
/-- Homogeneous coordinate pairs over canonical Gaussian rationals. -/
abbrev SourceCCFEncoderProjAlias := Proj
  Data.Gaussian.Basic.Canonical
end Purelib.Geometry.Projective.Line.Basic
end

end

section
section
section
@[expose] public section
namespace Purelib.Geometry.Projective.Line
/-- Homogeneous coordinate pairs over canonical Gaussian rationals. -/
abbrev GaussianLine :=
  Proj Data.Gaussian.Basic.Canonical
end Purelib.Geometry.Projective.Line
end
end

end

section
@[expose] public section
namespace Purelib.Geometry.Projective.Line.Basic
/-- The Gaussian rational homogeneous coordinate type. -/
abbrev SourceEncodingEncoderProjAlias :=
  GaussianLine
end Purelib.Geometry.Projective.Line.Basic

end

section
section
@[expose] public section
namespace Purelib.Geometry.Projective.Line.Proj
section

/-- Equality of the represented projective coordinates by cross multiplication. -/
def Equivalent [Mul K] (x y : Proj K) : Prop := x.p * y.q = y.p * x.q
end
end Purelib.Geometry.Projective.Line.Proj
end
end

end

section
section
@[expose] public section
namespace Purelib.Geometry.Projective.Line.Proj.Equivalent
section

/-- Every homogeneous coordinate pair is equivalent to itself. -/
theorem refl [CommRing K] (x : Proj K) : x.Equivalent x := by
  rfl
end
end Purelib.Geometry.Projective.Line.Proj.Equivalent
end
end

end

section
section
@[expose] public section
namespace Purelib.Geometry.Projective.Line.Proj.Equivalent
section

/-- Cross-multiplication equivalence of homogeneous coordinates is symmetric. -/
theorem symm [CommRing K] {x y : Proj K} (h : x.Equivalent y) :
    y.Equivalent x := by
  dsimp [Equivalent] at h ⊢
  exact h.symm
end
end Purelib.Geometry.Projective.Line.Proj.Equivalent
end
end

end

section
section
@[expose] public section
namespace Purelib.Geometry.Projective.Line.Proj.Equivalent
section

/-- Cross-multiplication equivalence is transitive through a nonzero denominator over an integral domain; no field
division is needed. -/
theorem trans_of_mid_q_domain [CommRing K] [IsDomain K]
    {x y z : Proj K} (hxy : x.Equivalent y) (hyz : y.Equivalent z)
    (hyq : y.q ≠ 0) : x.Equivalent z := by
  dsimp [Equivalent] at hxy hyz ⊢
  apply (mul_left_cancel₀ hyq)
  calc
    y.q * (x.p * z.q) = z.q * (x.p * y.q) := by ring1
    _ = z.q * (y.p * x.q) := by rw [hxy]
    _ = x.q * (y.p * z.q) := by ring1
    _ = x.q * (z.p * y.q) := by rw [hyz]
    _ = y.q * (z.p * x.q) := by ring1

end
end Purelib.Geometry.Projective.Line.Proj.Equivalent
end
end

end

section
section
@[expose] public section
namespace Purelib.Geometry.Projective.Line.Proj
section

/-- Embed an affine value as `[z : 1]`. -/
def affine [One K] (z : K) : Proj K := ⟨z, 1⟩
end
end Purelib.Geometry.Projective.Line.Proj
end
end

end

section
section
@[expose] public section
namespace Purelib.Geometry.Projective.Line.Proj
section

/-- The formal projective coordinate `ω = [1 : 0]`. -/
def omega [Zero K] [One K] : Proj K := ⟨1, 0⟩
end
end Purelib.Geometry.Projective.Line.Proj
end
end

end
