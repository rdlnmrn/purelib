import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import Mathlib.Tactic.Ring.Basic

/-!
# Finite projective and matrix bookkeeping

The paper uses homogeneous coordinate pairs as finite records.  We therefore do
not quotient by scalar multiplication here: every identity needed by the
algorithms is an equality of the displayed coordinate pairs.
-/

namespace CCL

/-- A finite homogeneous coordinate pair `[p : q]`. -/
@[ext]
structure Proj (K : Type*) where
  p : K
  q : K
deriving DecidableEq, Repr

namespace Proj

/-- The formal projective coordinate `ω = [1 : 0]`. -/
def omega [Zero K] [One K] : Proj K := ⟨1, 0⟩

/-- Embed an affine value as `[z : 1]`. -/
def affine [One K] (z : K) : Proj K := ⟨z, 1⟩

/-- Equality of the represented projective coordinates by cross multiplication. -/
def Equivalent [Mul K] (x y : Proj K) : Prop := x.p * y.q = y.p * x.q

theorem Equivalent.refl [CommRing K] (x : Proj K) : x.Equivalent x := by
  rfl

theorem Equivalent.symm [CommRing K] {x y : Proj K} (h : x.Equivalent y) :
    y.Equivalent x := by
  dsimp [Equivalent] at h ⊢
  exact h.symm

/-- Cross-multiplication equivalence is transitive through a nonzero
denominator over an integral domain; no field division is needed. -/
theorem Equivalent.trans_of_mid_q_domain [CommRing K] [IsDomain K]
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

end Proj

/-- A transparent two-by-two matrix. -/
@[ext]
structure Mat2 (K : Type*) where
  a : K
  b : K
  c : K
  d : K
deriving DecidableEq, Repr

namespace Mat2

/-- Matrix action on a homogeneous coordinate pair. -/
def act [Add K] [Mul K] (M : Mat2 K) (x : Proj K) : Proj K :=
  ⟨M.a * x.p + M.b * x.q, M.c * x.p + M.d * x.q⟩

/-- Explicit two-by-two matrix product. -/
def mul [Add K] [Mul K] (M N : Mat2 K) : Mat2 K :=
  ⟨M.a * N.a + M.b * N.c, M.a * N.b + M.b * N.d,
   M.c * N.a + M.d * N.c, M.c * N.b + M.d * N.d⟩

/-- Continued-fraction substitution matrix `A(t, μ)`. -/
def cf [Zero K] [One K] (t μ : K) : Mat2 K := ⟨t, μ, 1, 0⟩

/-- Scaling matrix `S_λ`. -/
def scale [Zero K] [One K] (l : K) : Mat2 K := ⟨l, 0, 0, 1⟩

/-- Translation matrix `T_s`. -/
def translate [Zero K] [One K] (s : K) : Mat2 K := ⟨1, s, 0, 1⟩

/-- Inversion matrix `I_λ`. -/
def invert [Zero K] [One K] (l : K) : Mat2 K := ⟨0, 1, l, 0⟩

section CommRing

variable {K : Type*} [CommRing K]

/-- Lemma 2.1, homogeneous continued-fraction substitution. -/
theorem cf_substitution (t μ y : K) :
    act (cf t μ) (Proj.affine y) = ⟨t * y + μ, y⟩ := by
  ext <;> simp [act, cf, Proj.affine]

/-- Lemma 2.1, the displayed decoder-matrix update. -/
theorem mul_cf (M : Mat2 K) (t μ : K) :
    mul M (cf t μ) =
      ⟨M.a * t + M.b, M.a * μ, M.c * t + M.d, M.c * μ⟩ := by
  ext <;> simp [mul, cf]

theorem act_mul (M N : Mat2 K) (x : Proj K) :
    act (mul M N) x = act M (act N x) := by
  ext <;> simp only [act, mul] <;> ring1

theorem scale_action (l z : K) :
    act (scale l) (Proj.affine z) = ⟨l * z, 1⟩ := by
  ext <;> simp [act, scale, Proj.affine]

theorem translate_action (s z : K) :
    act (translate s) (Proj.affine z) = ⟨z + s, 1⟩ := by
  ext <;> simp [act, translate, Proj.affine, add_comm]

theorem invert_action (l z : K) :
    act (invert l) (Proj.affine z) = ⟨1, l * z⟩ := by
  ext <;> simp [act, invert, Proj.affine]

/-- Applying a finite decoder to `ω` returns its first column. -/
theorem act_omega (M : Mat2 K) :
    act M (Proj.omega : Proj K) = ⟨M.a, M.c⟩ := by
  ext <;> simp [act, Proj.omega]

/-- A matrix action respects cross-multiplication equivalence. -/
theorem act_respects_equivalent (M : Mat2 K) {x y : Proj K}
    (h : x.Equivalent y) : (act M x).Equivalent (act M y) := by
  dsimp [Proj.Equivalent, act] at h ⊢
  calc
    (M.a * x.p + M.b * x.q) * (M.c * y.p + M.d * y.q) =
        (M.a * y.p + M.b * y.q) * (M.c * x.p + M.d * x.q) +
          (M.a * M.d - M.b * M.c) * (x.p * y.q - y.p * x.q) := by
      ring1
    _ = (M.a * y.p + M.b * y.q) * (M.c * x.p + M.d * x.q) := by
      rw [h]
      ring1

end CommRing

end Mat2

end CCL
