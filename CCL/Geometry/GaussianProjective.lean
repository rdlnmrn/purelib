import mathlib.Tactic.QuotientFreeRing
import mathlib.RFAP.ConstructiveGaussian
import CCL.Geometry.Projective

/-!
# Projective coordinates over constructive Gaussian fractions

The generic finite projective records are specialized here without importing the old `Rat`
coordinate model.  Transitivity is proved with the explicit Gaussian cancellation theorem, so it
does not synthesize a generic domain instance through a choice-bearing compatibility constructor.
-/

namespace CCL.GaussianProjective

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Proj := CCL.Proj Gaussian
abbrev Mat2 := CCL.Mat2 Gaussian

theorem equivalent_trans_of_mid_q {x y z : Proj}
    (hxy : CCL.Proj.Equivalent x y) (hyz : CCL.Proj.Equivalent y z)
    (hyq : y.q ≠ 0) : CCL.Proj.Equivalent x z := by
  dsimp [CCL.Proj.Equivalent] at hxy hyz ⊢
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne hyq
  calc
    (x.p * z.q) * y.q = z.q * (x.p * y.q) := by ring1
    _ = z.q * (y.p * x.q) := by rw [hxy]
    _ = x.q * (y.p * z.q) := by ring1
    _ = x.q * (z.p * y.q) := by rw [hyz]
    _ = (z.p * x.q) * y.q := by ring1

end CCL.GaussianProjective
