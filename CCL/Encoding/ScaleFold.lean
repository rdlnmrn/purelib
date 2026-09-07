import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Geometry.Chordal

/-!
# Constructive invariance under decoder scale folds

Right multiplication by `S_λ` moves a nonzero scale from an affine tail into
the first decoder column.  These finite identities are the formal content of
the scale- and quarter-unit-fold invariance used by the CCL parser.
-/

namespace CCL.ScaleFold

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Proj := CCL.GaussianProjective.Proj
abbrev Mat2 := CCL.GaussianProjective.Mat2

open RFAP.ConstructiveGaussian.Gaussian
open CCL.Chordal

/-- Move one displayed tail scale into the first matrix column. -/
def rightScale (matrix : Mat2) (scale : Gaussian) : Mat2 :=
  CCL.Mat2.mul matrix (CCL.Mat2.scale scale)

/-- The affine denominator weight `D_M(t)` from the manuscript. -/
def denominatorWeight (matrix : Mat2) (tail : Gaussian) : Coordinate :=
  normSq (matrix.a * tail + matrix.b) +
    normSq (matrix.c * tail + matrix.d)

@[simp] theorem rightScale_a (matrix : Mat2) (scale : Gaussian) :
    (rightScale matrix scale).a = matrix.a * scale := by
  simp [rightScale, CCL.Mat2.mul, CCL.Mat2.scale]

@[simp] theorem rightScale_b (matrix : Mat2) (scale : Gaussian) :
    (rightScale matrix scale).b = matrix.b := by
  simp [rightScale, CCL.Mat2.mul, CCL.Mat2.scale]

@[simp] theorem rightScale_c (matrix : Mat2) (scale : Gaussian) :
    (rightScale matrix scale).c = matrix.c * scale := by
  simp [rightScale, CCL.Mat2.mul, CCL.Mat2.scale]

@[simp] theorem rightScale_d (matrix : Mat2) (scale : Gaussian) :
    (rightScale matrix scale).d = matrix.d := by
  simp [rightScale, CCL.Mat2.mul, CCL.Mat2.scale]

/-- Folding the scale preserves the displayed affine output exactly. -/
theorem act_affine (matrix : Mat2) (scale tail : Gaussian) :
    CCL.Mat2.act (rightScale matrix scale) (CCL.Proj.affine tail) =
      CCL.Mat2.act matrix (CCL.Proj.affine (scale * tail)) := by
  rw [rightScale, CCL.Mat2.act_mul, CCL.Mat2.scale_action]
  rfl

/-- The two first columns represent the same projective point. -/
theorem act_omega_equivalent (matrix : Mat2) (scale : Gaussian) :
    CCL.Proj.Equivalent
      (CCL.Mat2.act (rightScale matrix scale) CCL.Proj.omega)
      (CCL.Mat2.act matrix CCL.Proj.omega) := by
  simp only [CCL.Proj.Equivalent, CCL.Mat2.act, CCL.Proj.omega,
    rightScale_a, rightScale_b, rightScale_c, rightScale_d,
    mul_one, mul_zero, add_zero]
  ring1

/-- Right scale multiplication multiplies the determinant by `scale`. -/
theorem det_rightScale (matrix : Mat2) (scale : Gaussian) :
    CCL.Chordal.Mat2.det (rightScale matrix scale) =
      CCL.Chordal.Mat2.det matrix * scale := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [CCL.Chordal.Mat2.det,
      rightScale_a, rightScale_b, rightScale_c, rightScale_d,
      sub_re, sub_im, mul_re, mul_im] <;>
    ring1

/-- Determinant norm acquires precisely the norm of the folded scale. -/
theorem normSq_det_rightScale (matrix : Mat2) (scale : Gaussian) :
    normSq (CCL.Chordal.Mat2.det (rightScale matrix scale)) =
      normSq scale * normSq (CCL.Chordal.Mat2.det matrix) := by
  rw [det_rightScale, normSq_mul]
  ring1

/-- The first-column weight acquires the same scale norm. -/
theorem firstColumnWeight_rightScale (matrix : Mat2) (scale : Gaussian) :
    normSq (rightScale matrix scale).a +
        normSq (rightScale matrix scale).c =
      normSq scale * (normSq matrix.a + normSq matrix.c) := by
  simp only [rightScale_a, rightScale_c, normSq_mul]
  ring1

/-- Moving the scale between matrix and tail preserves `D_M` exactly. -/
theorem denominatorWeight_rightScale (matrix : Mat2) (scale tail : Gaussian) :
    denominatorWeight (rightScale matrix scale) tail =
      denominatorWeight matrix (scale * tail) := by
  simp only [denominatorWeight, rightScale_a, rightScale_b,
    rightScale_c, rightScale_d]
  congr 1 <;> congr 1 <;> ring1

/-- Two affine tails are transported to exactly the same displayed points
before and after a common scale fold. -/
theorem chordalSq_twoTail (matrix : Mat2) (scale left right : Gaussian) :
    chordalSq
        (CCL.Mat2.act (rightScale matrix scale) (CCL.Proj.affine left))
        (CCL.Mat2.act (rightScale matrix scale) (CCL.Proj.affine right)) =
      chordalSq
        (CCL.Mat2.act matrix (CCL.Proj.affine (scale * left)))
        (CCL.Mat2.act matrix (CCL.Proj.affine (scale * right))) := by
  rw [act_affine, act_affine]

/-- With the decoder matrix nonsingular and the folded scale nonzero, the
one-tail truncation quadrance is also exactly invariant. -/
theorem chordalSq_truncation (matrix : Mat2) (scale tail : Gaussian)
    (matrixNonzero : CCL.Chordal.Mat2.det matrix ≠ 0)
    (scaleNonzero : scale ≠ 0) :
    chordalSq
        (CCL.Mat2.act (rightScale matrix scale) (CCL.Proj.affine tail))
        (CCL.Mat2.act (rightScale matrix scale) CCL.Proj.omega) =
      chordalSq
        (CCL.Mat2.act matrix (CCL.Proj.affine (scale * tail)))
        (CCL.Mat2.act matrix CCL.Proj.omega) := by
  rw [act_affine]
  apply chordalSq_eq_of_equivalent_right
  · apply CCL.Chordal.Mat2.act_hasNonzeroCoordinate
    · rw [det_rightScale]
      exact RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
        matrixNonzero scaleNonzero
    · exact Proj.omega_hasNonzeroCoordinate
  · exact CCL.Chordal.Mat2.act_hasNonzeroCoordinate
      matrixNonzero Proj.omega_hasNonzeroCoordinate
  · exact act_omega_equivalent matrix scale

end CCL.ScaleFold
