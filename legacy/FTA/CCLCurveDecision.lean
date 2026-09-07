import FTA.ProjectivePathBounds
import FTA.CCLPathIntersection
import FTA.Maximality

/-!
# Finite zero-or-positive decisions on CCL branch arcs

On a rational parameter cell with clear endpoints, the common-factor Sturm
count is a computed integer and is provably nonnegative.  Exact comparison
with zero therefore returns either a positive root-on-arc count or the affine
clearance certificate obtained by denominator division.  This is the two-way
curve branch used in Theorem 10.2.
-/

namespace FTA
namespace CCLCurveDecision

open CCL CCL.GaussianRat
open FTA.ComputablePolynomial
open FTA.ComputablePolynomial.DensePolynomial
open FTA.PathClearance
open FTA.ProjectivePath
open FTA.ProjectivePathBounds
open FTA.SquarefreeFactorization

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial := DensePolynomial QI
abbrev RationalInterval := FTA.SturmTransducer.RationalInterval

theorem commonFactorRootCount2_nonnegative
    (p : GaussianPolynomial) (path : Path)
    (hnonzero : (clearedReal p path).isZero = false ∨
      (clearedImag p path).isZero = false)
    (interval : RationalInterval) (proper : interval.Proper)
    (lowerClear :
      (PathClearance.commonFactor (clearedReal p path)
        (clearedImag p path)).eval interval.lower ≠ 0)
    (upperClear :
      (PathClearance.commonFactor (clearedReal p path)
        (clearedImag p path)).eval interval.upper ≠ 0) :
    0 ≤ ProjectivePath.commonFactorRootCount2 p path hnonzero
      interval.lower interval.upper := by
  exact factorRootCount2_nonnegative
    (PathClearance.commonFactor_isZero_false hnonzero)
    proper lowerClear upperClear

/-- Computed outcome for one rational branch-curve parameter cell. -/
inductive Decision (p : GaussianPolynomial) (path : Path)
    (hnonzero : (clearedReal p path).isZero = false ∨
      (clearedImag p path).isZero = false)
    (interval : RationalInterval) where
  | clear (certificate : AffineCertificate p path interval)
  | positiveCount
      (positive : 0 < ProjectivePath.commonFactorRootCount2 p path hnonzero
        interval.lower interval.upper)

/-- Total finite comparison of the exact curve count with zero. -/
def decide
    (p : GaussianPolynomial) (path : Path)
    (hnonzero : (clearedReal p path).isZero = false ∨
      (clearedImag p path).isZero = false)
    (interval : RationalInterval) (proper : interval.Proper)
    (lowerClear :
      (PathClearance.commonFactor (clearedReal p path)
        (clearedImag p path)).eval interval.lower ≠ 0)
    (upperClear :
      (PathClearance.commonFactor (clearedReal p path)
        (clearedImag p path)).eval interval.upper ≠ 0) :
    Decision p path hnonzero interval := by
  let count := ProjectivePath.commonFactorRootCount2 p path hnonzero
    interval.lower interval.upper
  if hzero : count = 0 then
    exact .clear (computeAffineClearance p path hnonzero interval proper
      lowerClear upperClear (by simpa only [count] using hzero))
  else
    have hnonnegative : 0 ≤ count := by
      simpa only [count] using commonFactorRootCount2_nonnegative p path
        hnonzero interval proper lowerClear upperClear
    exact .positiveCount (lt_of_le_of_ne hnonnegative (Ne.symm hzero))

theorem decide_clear_count_eq_zero
    (p : GaussianPolynomial) (path : Path)
    (hnonzero : (clearedReal p path).isZero = false ∨
      (clearedImag p path).isZero = false)
    (interval : RationalInterval) (proper : interval.Proper)
    (lowerClear :
      (PathClearance.commonFactor (clearedReal p path)
        (clearedImag p path)).eval interval.lower ≠ 0)
    (upperClear :
      (PathClearance.commonFactor (clearedReal p path)
        (clearedImag p path)).eval interval.upper ≠ 0)
    (certificate : AffineCertificate p path interval)
    (houtcome : decide p path hnonzero interval proper lowerClear upperClear =
      .clear certificate) :
    ProjectivePath.commonFactorRootCount2 p path hnonzero
      interval.lower interval.upper = 0 := by
  rw [decide] at houtcome
  split at houtcome
  · assumption
  · simp at houtcome

/-! ## A uniform margin for finitely many relevant arcs -/

/-- One zero-count relevant arc with its computed affine clearance. -/
structure ClearArc (p : GaussianPolynomial) where
  path : Path
  interval : RationalInterval
  certificate : AffineCertificate p path interval

def clearanceBounds {p : GaussianPolynomial} (arcs : List (ClearArc p)) : List ℚ :=
  arcs.map fun arc => arc.certificate.bound

/-- The paper's single positive `δ`, obtained from all finitely many relevant
zero-count parameter cells.  The positive default also handles an empty list. -/
def uniformClearance {p : GaussianPolynomial} (arcs : List (ClearArc p)) : ℚ :=
  FTA.Maximality.positiveMinimum (clearanceBounds arcs)

theorem uniformClearance_pos {p : GaussianPolynomial}
    (arcs : List (ClearArc p)) : 0 < uniformClearance arcs := by
  apply FTA.Maximality.positiveMinimum_pos
  intro value hvalue
  rw [clearanceBounds, List.mem_map] at hvalue
  rcases hvalue with ⟨arc, _harc, rfl⟩
  exact arc.certificate.positive

theorem uniformClearance_le_on_arc {p : GaussianPolynomial}
    {arcs : List (ClearArc p)} {arc : ClearArc p} (harc : arc ∈ arcs)
    {t : ℚ} (hLower : arc.interval.lower ≤ t)
    (hUpper : t ≤ arc.interval.upper)
    (hden : arc.path.denominator.eval (FTA.PathPolynomial.ofRat t) ≠ 0) :
    uniformClearance arcs ≤ normSq (p.eval (arc.path.value t)) := by
  apply (FTA.Maximality.positiveMinimum_le_of_mem
    (values := clearanceBounds arcs)
    (value := arc.certificate.bound) (by
      exact List.mem_map.mpr ⟨arc, harc, rfl⟩)).trans
  exact arc.certificate.lower t hLower hUpper hden

end CCLCurveDecision
end FTA
