import FTA.CCLSectorTangent

/-!
# Sector-owner sampling inside rational boxes

Safe rational cuts place the supported track strictly inside its current box.
At such an anchor, the active weak sector owners use the parser-specific
tangent direction, while inactive sector owners, earlier strict parser forms,
and all four inward box forms are protected as strict priors.  One explicit
reciprocal step therefore enters every active owner, makes every sector owner
strict, preserves every earlier strict comparison, and remains strictly inside
the rational box.  This is the box-compatible owner step required by Lemma
10.3.
-/

namespace FTA
namespace CCLSectorBoxGrid

open CCL CCL.GaussianRat
open FTA.CCLGeometry
open FTA.CCLMultiOwnerGrid
open FTA.CCLOwnerDirection
open FTA.CCLOwnerGrid
open FTA.CCLSectorTangent

abbrev QI := CCL.GaussianRat

/-- Strict rational-box membership, used as the protected-margin invariant
for owner perturbations. -/
def StrictContains (box : RatBox) (z : QI) : Prop :=
  box.xLower < z.re ∧ z.re < box.xUpper ∧
    box.yLower < z.im ∧ z.im < box.yUpper

theorem all_boxForms_pos_of_strictContains
    {box : RatBox} {z : QI} (strict : StrictContains box z) :
    ∀ form ∈ boxForms box, 0 < form.eval z := by
  intro form member
  simp [boxForms] at member
  rcases member with rfl | rfl | rfl | rfl
  · rw [eval_boxXLowerForm]
    exact sub_pos.mpr strict.1
  · rw [eval_boxXUpperForm]
    exact sub_pos.mpr strict.2.1
  · rw [eval_boxYLowerForm]
    exact sub_pos.mpr strict.2.2.1
  · rw [eval_boxYUpperForm]
    exact sub_pos.mpr strict.2.2.2

theorem strictContains_of_all_boxForms_pos
    {box : RatBox} {z : QI}
    (positive : ∀ form ∈ boxForms box, 0 < form.eval z) :
    StrictContains box z := by
  have xLower := positive (boxXLowerForm box) (by simp [boxForms])
  have xUpper := positive (boxXUpperForm box) (by simp [boxForms])
  have yLower := positive (boxYLowerForm box) (by simp [boxForms])
  have yUpper := positive (boxYUpperForm box) (by simp [boxForms])
  simp only [eval_boxXLowerForm] at xLower
  simp only [eval_boxXUpperForm] at xUpper
  simp only [eval_boxYLowerForm] at yLower
  simp only [eval_boxYUpperForm] at yUpper
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem strictContains_iff_all_boxForms_pos (box : RatBox) (z : QI) :
    StrictContains box z ↔ ∀ form ∈ boxForms box, 0 < form.eval z :=
  ⟨all_boxForms_pos_of_strictContains,
    strictContains_of_all_boxForms_pos⟩

/-- Sector owner forms that are already strict at the anchor. -/
def inactiveSectorOwnerForms (sector : Sector) (M : Mat2 QI) (z : QI) :
    List HermitianForm :=
  (sectorOwnerForms sector M).filter fun form => decide (form.eval z ≠ 0)

theorem activeSectorOwnerForms_eval_zero
    {sector : Sector} {M : Mat2 QI} {z : QI} {form : HermitianForm}
    (member : form ∈ activeSectorOwnerForms sector M z) :
    form.eval z = 0 := by
  exact of_decide_eq_true (List.mem_filter.mp member).2

theorem inactiveSectorOwnerForms_eval_ne_zero
    {sector : Sector} {M : Mat2 QI} {z : QI} {form : HermitianForm}
    (member : form ∈ inactiveSectorOwnerForms sector M z) :
    form.eval z ≠ 0 := by
  exact of_decide_eq_true (List.mem_filter.mp member).2

theorem sectorOwnerForms_active_or_inactive
    {sector : Sector} {M : Mat2 QI} {z : QI} {form : HermitianForm}
    (member : form ∈ sectorOwnerForms sector M) :
    form ∈ activeSectorOwnerForms sector M z ∨
      form ∈ inactiveSectorOwnerForms sector M z := by
  by_cases zero : form.eval z = 0
  · left
    exact List.mem_filter.mpr ⟨member, by simp [zero]⟩
  · right
    exact List.mem_filter.mpr ⟨member, by simp [zero]⟩

/-- Every non-active constraint protected by the common owner radius. -/
def sectorBoxPriors (sector : Sector) (M : Mat2 QI) (z : QI)
    (earlier : List HermitianForm) (box : RatBox) : List HermitianForm :=
  inactiveSectorOwnerForms sector M z ++ earlier ++ boxForms box

theorem sectorBoxPriors_pos
    {sector : Sector} {M : Mat2 QI} {z : QI}
    {earlier : List HermitianForm} {box : RatBox}
    (ownerNonnegative : ∀ form ∈ sectorOwnerForms sector M,
      0 ≤ form.eval z)
    (earlierPositive : ∀ form ∈ earlier, 0 < form.eval z)
    (strictBox : StrictContains box z) :
    ∀ form ∈ sectorBoxPriors sector M z earlier box,
      0 < form.eval z := by
  intro form member
  rw [sectorBoxPriors, List.mem_append] at member
  rcases member with priorRegion | boxForm
  · rw [List.mem_append] at priorRegion
    rcases priorRegion with inactive | prior
    · have nonzero := inactiveSectorOwnerForms_eval_ne_zero inactive
      have ownerMember := (List.mem_filter.mp inactive).1
      exact lt_of_le_of_ne (ownerNonnegative form ownerMember) (Ne.symm nonzero)
    · exact earlierPositive form prior
  · exact all_boxForms_pos_of_strictContains strictBox form boxForm

/-- The explicit point returned by the sector/box owner grid. -/
def sectorBoxPoint
    (sector : Sector) (M : Mat2 QI) (z : QI)
    (determinantNonzero : determinant M ≠ 0)
    (earlier : List HermitianForm) (box : RatBox) : QI :=
  let direction := sectorTangentDirection sector M z determinantNonzero
  let priors := sectorBoxPriors sector M z earlier box
  step z (multiOwnerEpsilon direction priors) direction.vector

/-- Proof-bearing result of the bounded box-compatible sector step. -/
structure SectorBoxSample
    (sector : Sector) (M : Mat2 QI) (earlier : List HermitianForm)
    (box : RatBox) where
  point : QI
  sectorStrict : ∀ form ∈ sectorOwnerForms sector M, 0 < form.eval point
  earlierStrict : ∀ form ∈ earlier, 0 < form.eval point
  boxStrict : StrictContains box point

/-- One total rational construction once the decoder is invertible and the
anchor satisfies the selected weak sector row strictly inside its box. -/
def computeSectorBoxSample
    (sector : Sector) (M : Mat2 QI) (z : QI)
    (determinantNonzero : determinant M ≠ 0)
    (earlier : List HermitianForm) (box : RatBox)
    (ownerNonnegative : ∀ form ∈ sectorOwnerForms sector M,
      0 ≤ form.eval z)
    (earlierPositive : ∀ form ∈ earlier, 0 < form.eval z)
    (strictBox : StrictContains box z) :
    SectorBoxSample sector M earlier box := by
  let direction := sectorTangentDirection sector M z determinantNonzero
  let active := activeSectorOwnerForms sector M z
  let priors := sectorBoxPriors sector M z earlier box
  let epsilon := multiOwnerEpsilon direction priors
  let point := step z epsilon direction.vector
  have priorsPositive : ∀ form ∈ priors, 0 < form.eval z := by
    simpa only [priors] using sectorBoxPriors_pos ownerNonnegative
      earlierPositive strictBox
  have priorsNonzero : ∀ form ∈ priors, form.eval z ≠ 0 := by
    intro form member
    exact (priorsPositive form member).ne'
  have onActive : ∀ form ∈ active, form.eval z = 0 := by
    intro form member
    exact activeSectorOwnerForms_eval_zero member
  have entered : ∀ form ∈ active, 0 < form.eval point := by
    simpa only [active, priors, epsilon, point, direction] using
      enters_all_boundaries direction priors onActive priorsNonzero
  have preserved : ∀ form ∈ priors,
      0 < form.eval z * form.eval point := by
    simpa only [priors, epsilon, point, direction] using
      preserves_all_priors direction priors priorsNonzero
  have priorsAfter : ∀ form ∈ priors, 0 < form.eval point := by
    intro form member
    rcases mul_pos_iff.mp (preserved form member) with signs | signs
    · exact signs.2
    · exact (not_lt_of_ge (priorsPositive form member).le signs.1).elim
  refine
    { point
      sectorStrict := ?_
      earlierStrict := ?_
      boxStrict := ?_ }
  · intro form member
    rcases sectorOwnerForms_active_or_inactive (z := z) member with
      activeMember | inactiveMember
    · exact entered form activeMember
    · apply priorsAfter form
      simp [priors, sectorBoxPriors, inactiveMember]
  · intro form member
    apply priorsAfter form
    simp [priors, sectorBoxPriors, member]
  · apply strictContains_of_all_boxForms_pos
    intro form member
    apply priorsAfter form
    simp [priors, sectorBoxPriors, member]

end CCLSectorBoxGrid
end FTA
