import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeRing
import CCL.Boundary.Description

/-!
# Boundary provenance for finite CCL formulas

This module follows the syntax tree of each next-bit formula.  Every atom is
paired with a constructive description of its exact zero boundary.  Formula
inspection can therefore hand an unresolved atom directly to the finite
curve-event layer without guessing its geometric origin from coefficients.
-/

namespace CCL.CCLFormulaBoundaries

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Mat2 := CCL.GaussianProjective.Mat2
abbrev HermitianForm := CCL.CCLGeometry.HermitianForm
abbrev Atom := CCL.CCLFormula.Atom
abbrev Formula := CCL.CCLFormula.Formula
abbrev Description := CCL.CCLBoundaryDescription.Description

open RFAP.ConstructiveGaussian.Gaussian
open CCL.RawParser
open CCL.CCLGeometry
open CCL.CCLFormula

/-- One formula atom with its exact boundary provenance and the shared affine
denominator matrix used by every parameterized source. -/
structure DescribedAtom (reference : Mat2) where
  atom : Atom
  boundary : Description reference atom.form

/-- Boundary descriptions in exactly the same finite order as
`Formula.atoms`. -/
structure Descriptions (reference : Mat2) (formula : Formula) where
  entries : List (DescribedAtom reference)
  atoms_eq : entries.map (fun entry => entry.atom) = formula.atoms

namespace Descriptions

def truth {reference : Mat2} : Descriptions reference .truth := ⟨[], rfl⟩
def falsity {reference : Mat2} : Descriptions reference .falsity := ⟨[], rfl⟩

def atom {reference : Mat2} (value : Atom)
    (boundary : Description reference value.form) :
    Descriptions reference (.atom value) :=
  ⟨[⟨value, boundary⟩], rfl⟩

def and {reference : Mat2} {left right : Formula}
    (leftDescriptions : Descriptions reference left)
    (rightDescriptions : Descriptions reference right) :
    Descriptions reference (.and left right) :=
  ⟨leftDescriptions.entries ++ rightDescriptions.entries, by
    rw [List.map_append, leftDescriptions.atoms_eq,
      rightDescriptions.atoms_eq]
    rfl⟩

def or {reference : Mat2} {left right : Formula}
    (leftDescriptions : Descriptions reference left)
    (rightDescriptions : Descriptions reference right) :
    Descriptions reference (.or left right) :=
  ⟨leftDescriptions.entries ++ rightDescriptions.entries, by
    rw [List.map_append, leftDescriptions.atoms_eq,
      rightDescriptions.atoms_eq]
    rfl⟩

def cast {reference : Mat2} {left right : Formula} (equal : left = right)
    (descriptions : Descriptions reference left) :
    Descriptions reference right := by
  subst right
  exact descriptions

def find? {reference : Mat2} {formula : Formula}
    (descriptions : Descriptions reference formula)
    (target : Atom) : Option (DescribedAtom reference) :=
  descriptions.entries.find? fun entry => decide (entry.atom = target)

theorem find?_isSome_of_mem
    {reference : Mat2} {formula : Formula}
    (descriptions : Descriptions reference formula)
    (target : Atom) (member : target ∈ formula.atoms) :
    (descriptions.find? target).isSome := by
  rw [find?, QuotientFreeList.find?_isSome]
  have mappedMember : target ∈
      descriptions.entries.map (fun entry => entry.atom) := by
    rw [descriptions.atoms_eq]
    exact member
  rcases QuotientFreeList.mem_map.mp mappedMember with ⟨entry, entryMember, equal⟩
  refine ⟨entry, entryMember, ?_⟩
  exact decide_eq_true equal

structure Selected (reference : Mat2) (target : Atom) where
  entry : DescribedAtom reference
  equal : entry.atom = target

/-- Computationally select the description at a proved atom occurrence. -/
def select {reference : Mat2} {formula : Formula}
    (descriptions : Descriptions reference formula)
    (target : Atom) (member : target ∈ formula.atoms) :
    Selected reference target := by
  match found : descriptions.find? target with
  | none =>
      have impossible : False := by
        have present := descriptions.find?_isSome_of_mem target member
        rw [found] at present
        simp at present
      exact impossible.elim
  | some entry =>
      have checked := List.find?_some found
      change decide (entry.atom = target) = true at checked
      exact ⟨entry, of_decide_eq_true checked⟩

/-- Exact boundary description of a proved formula atom occurrence. -/
def boundaryFor
    {reference : Mat2} {formula : Formula}
    (descriptions : Descriptions reference formula)
    (target : Atom) (member : target ∈ formula.atoms) :
    Description reference target.form := by
  let selected := descriptions.select target member
  exact CCL.CCLBoundaryDescription.Description.cast
    (congrArg (fun atom : Atom => atom.form) selected.equal)
    selected.entry.boundary

end Descriptions

@[simp] private theorem pullbackForm_identity (form : HermitianForm) :
    CCL.CCLPullback.pullbackForm identityMatrix form = form := by
  apply HermitianForm.ext <;>
    simp only [CCL.CCLPullback.pullbackForm,
      identityMatrix, HermitianForm.add, HermitianForm.scale,
      affineNormForm, realCrossForm, imagCrossForm, normSq,
      RFAP.ConstructiveGaussian.Gaussian.one_re,
      RFAP.ConstructiveGaussian.Gaussian.one_im,
      RFAP.ConstructiveGaussian.Gaussian.zero_re,
      RFAP.ConstructiveGaussian.Gaussian.zero_im] <;>
    ring1

private theorem normalizedMatrix_det_ne
    (kind : BlockKind) (exponent : Nat) (matrix : Mat2)
    (matrixNonzero : CCL.Chordal.Mat2.det matrix ≠ 0) :
    CCL.Chordal.Mat2.det
      (normalizedMatrix kind exponent matrix) ≠ 0 := by
  rw [normalizedMatrix, CCL.RawParser.det_mul]
  exact mul_ne_zero_direct (normalizationMatrix_det_ne kind exponent)
    matrixNonzero

private theorem identityMatrix_det_ne :
    CCL.Chordal.Mat2.det identityMatrix ≠ 0 := by
  intro determinantZero
  have realZero := congrArg RFAP.ConstructiveGaussian.Gaussian.re determinantZero
  simp only [CCL.Chordal.Mat2.det, identityMatrix,
    RFAP.ConstructiveGaussian.Gaussian.mul_re,
    RFAP.ConstructiveGaussian.Gaussian.sub_re,
    RFAP.ConstructiveGaussian.Gaussian.one_re,
    RFAP.ConstructiveGaussian.Gaussian.one_im,
    RFAP.ConstructiveGaussian.Gaussian.zero_re,
    RFAP.ConstructiveGaussian.Gaussian.zero_im] at realZero
  exact RFAP.ConstructiveFraction.zero_ne_one realZero.symm

private def afterIdentityPullback
    (inner : Mat2) (form : HermitianForm)
    (description : Description inner
      (CCL.CCLPullback.pullbackForm inner form)) :
    Description inner
      (CCL.CCLPullback.pullbackForm inner
        (CCL.CCLPullback.pullbackForm identityMatrix form)) :=
  CCL.CCLBoundaryDescription.Description.cast
    (congrArg (CCL.CCLPullback.pullbackForm inner)
      (pullbackForm_identity form)).symm description

/-- Boundary descriptions for a radial bracket after one input-coordinate
pullback. -/
def pulledRadial
    (kind : BlockKind) (exponent : Nat) (inner : Mat2)
    (innerNonzero : CCL.Chordal.Mat2.det inner ≠ 0) :
    Descriptions inner
      ((radialFormula kind exponent identityMatrix).pullback inner) := by
  cases kind with
  | initialHigh =>
      simp only [radialFormula, Formula.pullback,
        pullbackAtom]
      exact Descriptions.and
        (Descriptions.atom _
          (afterIdentityPullback inner _
            (CCL.CCLBoundaryDescription.pulledAffineNormDyadic
              inner innerNonzero exponent)))
        (Descriptions.atom _
          (afterIdentityPullback inner _
            (CCL.CCLBoundaryDescription.pulledAffineNormDyadic
              inner innerNonzero (exponent + 1))))
  | initialLow =>
      simp only [radialFormula, Formula.pullback,
        pullbackAtom]
      exact Descriptions.and
        (Descriptions.atom _
          (afterIdentityPullback inner _
            (CCL.CCLBoundaryDescription.pulledScaledNormOne
              inner innerNonzero exponent)))
        (Descriptions.atom _
          (afterIdentityPullback inner _
            (CCL.CCLBoundaryDescription.pulledScaledNormTwo
              inner innerNonzero exponent)))
  | loop =>
      simp only [radialFormula, Formula.pullback,
        pullbackAtom]
      exact Descriptions.and
        (Descriptions.atom _
          (afterIdentityPullback inner _
            (CCL.CCLBoundaryDescription.pulledAffineNormDyadic
              inner innerNonzero exponent)))
        (Descriptions.atom _
          (afterIdentityPullback inner _
            (CCL.CCLBoundaryDescription.pulledAffineNormDyadic
              inner innerNonzero (exponent + 1))))

/-- Boundary descriptions for one complete sector row after pullback. -/
def pulledSector
    (sector : CCL.Sectors.Sector) (outer inner : Mat2)
    (outerNonzero : CCL.Chordal.Mat2.det outer ≠ 0)
    (innerNonzero : CCL.Chordal.Mat2.det inner ≠ 0)
    (outerLowerRow : outer.c = 0 ∧ outer.d = 1) :
    Descriptions inner ((sectorFormula sector outer).pullback inner) := by
  let realBoundary :=
    CCL.CCLBoundaryDescription.pulledRealComparison outer inner
      outerNonzero innerNonzero outerLowerRow
  let imaginaryBoundary :=
    CCL.CCLBoundaryDescription.pulledImaginaryComparison outer inner
      outerNonzero innerNonzero outerLowerRow
  cases sector with
  | east =>
      simp only [sectorFormula, Formula.pullback, pullbackAtom]
      exact Descriptions.and
        (Descriptions.atom _ (realBoundary (1 / 2)))
        (Descriptions.and
          (Descriptions.atom _ (imaginaryBoundary (-1 / 2)))
          (Descriptions.atom _ (imaginaryBoundary (1 / 2))))
  | northEast =>
      simp only [sectorFormula, Formula.pullback, pullbackAtom]
      exact Descriptions.and
        (Descriptions.atom _ (realBoundary (1 / 2)))
        (Descriptions.atom _ (imaginaryBoundary (1 / 2)))
  | north =>
      simp only [sectorFormula, Formula.pullback, pullbackAtom]
      exact Descriptions.and
        (Descriptions.atom _ (realBoundary (-1 / 2)))
        (Descriptions.and
          (Descriptions.atom _ (realBoundary (1 / 2)))
          (Descriptions.atom _ (imaginaryBoundary (1 / 2))))
  | northWest =>
      simp only [sectorFormula, Formula.pullback, pullbackAtom]
      exact Descriptions.and
        (Descriptions.atom _ (realBoundary (-1 / 2)))
        (Descriptions.atom _ (imaginaryBoundary (1 / 2)))
  | west =>
      simp only [sectorFormula, Formula.pullback, pullbackAtom]
      exact Descriptions.and
        (Descriptions.atom _ (realBoundary (-1 / 2)))
        (Descriptions.and
          (Descriptions.atom _ (imaginaryBoundary (-1 / 2)))
          (Descriptions.atom _ (imaginaryBoundary (1 / 2))))
  | southWest =>
      simp only [sectorFormula, Formula.pullback, pullbackAtom]
      exact Descriptions.and
        (Descriptions.atom _ (realBoundary (-1 / 2)))
        (Descriptions.atom _ (imaginaryBoundary (-1 / 2)))
  | south =>
      simp only [sectorFormula, Formula.pullback, pullbackAtom]
      exact Descriptions.and
        (Descriptions.atom _ (realBoundary (-1 / 2)))
        (Descriptions.and
          (Descriptions.atom _ (realBoundary (1 / 2)))
          (Descriptions.atom _ (imaginaryBoundary (-1 / 2))))
  | southEast =>
      simp only [sectorFormula, Formula.pullback, pullbackAtom]
      exact Descriptions.and
        (Descriptions.atom _ (realBoundary (1 / 2)))
        (Descriptions.atom _ (imaginaryBoundary (-1 / 2)))

private def pulledSectorList
    (sectors : List CCL.Sectors.Sector) (outer inner : Mat2)
    (outerNonzero : CCL.Chordal.Mat2.det outer ≠ 0)
    (innerNonzero : CCL.Chordal.Mat2.det inner ≠ 0)
    (outerLowerRow : outer.c = 0 ∧ outer.d = 1) :
    Descriptions inner
      ((Formula.any (sectors.map fun sector =>
        sectorFormula sector outer)).pullback inner) := by
  induction sectors with
  | nil =>
      simp only [List.map, Formula.any, Formula.pullback]
      exact Descriptions.falsity
  | cons sector sectors inductionHypothesis =>
      simp only [List.map, Formula.any, Formula.pullback]
      exact Descriptions.or
        (pulledSector sector outer inner outerNonzero innerNonzero
          outerLowerRow)
        inductionHypothesis

private theorem normalizedIdentity_lowerRow
    (kind : BlockKind) (exponent : Nat) :
    (normalizedMatrix kind exponent identityMatrix).c = 0 ∧
      (normalizedMatrix kind exponent identityMatrix).d = 1 := by
  have lower := normalizedMatrix_lowerRow kind exponent identityMatrix
  simpa only [identityMatrix] using lower

private def pulledSectorBits
    (kind : BlockKind) (exponent : Nat) (bits : SectorBits)
    (inner : Mat2)
    (innerNonzero : CCL.Chordal.Mat2.det inner ≠ 0) :
    Descriptions inner
      ((sectorBitsFormula kind exponent bits).pullback inner) := by
  let outer := normalizedMatrix kind exponent identityMatrix
  exact pulledSectorList (sectorCandidates bits) outer inner
    (normalizedMatrix_det_ne kind exponent identityMatrix
      identityMatrix_det_ne) innerNonzero
    (normalizedIdentity_lowerRow kind exponent)

/-- Boundary descriptions for every active parser phase after pullback. -/
def pulledActive
    (phase : Phase) (inner : Mat2)
    (innerNonzero : CCL.Chordal.Mat2.det inner ≠ 0) :
    Descriptions inner ((activeFormula phase).pullback inner) := by
  cases phase with
  | initial =>
      simp only [activeFormula, Formula.pullback]
      exact Descriptions.truth
  | highUnary count =>
      simp only [activeFormula, Formula.pullback, pullbackAtom]
      exact Descriptions.atom _
        (CCL.CCLBoundaryDescription.pulledAffineNormDyadic
          inner innerNonzero count)
  | lowUnary count =>
      cases count with
      | zero =>
          simp only [activeFormula, Formula.pullback, pullbackAtom]
          exact Descriptions.atom _ (by
            simpa only [pow_one] using
              (CCL.CCLBoundaryDescription.pulledAffineNormDyadic
                inner innerNonzero 1))
      | succ count =>
          simp only [activeFormula, Formula.pullback, pullbackAtom]
          exact Descriptions.atom _
            (CCL.CCLBoundaryDescription.pulledScaledNormOne
              inner innerNonzero count)
  | loopUnary count =>
      simp only [activeFormula, Formula.pullback, pullbackAtom]
      exact Descriptions.atom _
        (CCL.CCLBoundaryDescription.pulledAffineNormDyadic
          inner innerNonzero count)
  | sector kind exponent bits =>
      simp only [activeFormula, Formula.pullback]
      exact Descriptions.and
        (pulledRadial kind exponent inner innerNonzero)
        (pulledSectorBits kind exponent bits inner innerNonzero)

private def pulledResidual
    (kind : BlockKind) (exponent : Nat)
    (sector : CCL.Sectors.Sector) (inner : Mat2) :
    Description inner
      (CCL.CCLPullback.pullbackForm inner
        (CCL.CCLNextBit.residualForm kind exponent sector)) := by
  let matrix := normalizedMatrix kind exponent identityMatrix
  simpa only [CCL.CCLNextBit.residualForm, matrix] using
    (CCL.CCLBoundaryDescription.Description.pulledAffineNorm inner
      (matrix.a - sector.rep * matrix.c)
      (matrix.b - sector.rep * matrix.d))

/-- Complete atom-boundary provenance for one input-coordinate incremental
next-bit formula. -/
def inputIncremental
    (state : State)
    (stateNonzero : CCL.Chordal.Mat2.det state.matrix ≠ 0)
    (bit : Bool) :
    Descriptions (CCL.CCLPullback.adjugate state.matrix)
      (CCL.CCLNextBit.inputIncrementalAdvanceFormula state bit) := by
  let inner := CCL.CCLPullback.adjugate state.matrix
  have innerNonzero : CCL.Chordal.Mat2.det inner ≠ 0 := by
    change CCL.CCLPullback.determinant
      (CCL.CCLPullback.adjugate state.matrix) ≠ 0
    rw [CCL.CCLPullback.determinant_adjugate]
    exact stateNonzero
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      simpa only [CCL.CCLNextBit.inputIncrementalAdvanceFormula,
        CCL.CCLNextBit.incrementalAdvanceFormula, inner] using
        (pulledActive
          (step ⟨Phase.initial, matrix, history⟩ bit).phase
          (CCL.CCLPullback.adjugate matrix) innerNonzero)
  | highUnary count =>
      simpa only [CCL.CCLNextBit.inputIncrementalAdvanceFormula,
        CCL.CCLNextBit.incrementalAdvanceFormula, inner] using
        (pulledActive
          (step ⟨Phase.highUnary count, matrix, history⟩ bit).phase
          (CCL.CCLPullback.adjugate matrix) innerNonzero)
  | lowUnary count =>
      simpa only [CCL.CCLNextBit.inputIncrementalAdvanceFormula,
        CCL.CCLNextBit.incrementalAdvanceFormula, inner] using
        (pulledActive
          (step ⟨Phase.lowUnary count, matrix, history⟩ bit).phase
          (CCL.CCLPullback.adjugate matrix) innerNonzero)
  | loopUnary count =>
      simpa only [CCL.CCLNextBit.inputIncrementalAdvanceFormula,
        CCL.CCLNextBit.incrementalAdvanceFormula, inner] using
        (pulledActive
          (step ⟨Phase.loopUnary count, matrix, history⟩ bit).phase
          (CCL.CCLPullback.adjugate matrix) innerNonzero)
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          simpa only [CCL.CCLNextBit.inputIncrementalAdvanceFormula,
            CCL.CCLNextBit.incrementalAdvanceFormula, step, inner]
            using
            (pulledActive
              (step ⟨Phase.sector kind exponent .zero, matrix, history⟩
                bit).phase
              (CCL.CCLPullback.adjugate matrix) innerNonzero)
      | one first =>
          simpa only [CCL.CCLNextBit.inputIncrementalAdvanceFormula,
            CCL.CCLNextBit.incrementalAdvanceFormula, step, inner]
            using
            (pulledActive
              (step
                ⟨Phase.sector kind exponent (.one first), matrix, history⟩
                bit).phase
              (CCL.CCLPullback.adjugate matrix) innerNonzero)
      | two first second =>
          let selected := sectorOfBits first second bit
          let outer := normalizedMatrix kind exponent identityMatrix
          simp only [CCL.CCLNextBit.inputIncrementalAdvanceFormula,
            CCL.CCLNextBit.incrementalAdvanceFormula,
            CCL.CCLNextBit.advanceFormula, Formula.pullback,
            pullbackAtom]
          exact Descriptions.and
            (pulledRadial kind exponent
              (CCL.CCLPullback.adjugate matrix) innerNonzero)
            (Descriptions.and
              (pulledSector selected outer
                (CCL.CCLPullback.adjugate matrix)
                (normalizedMatrix_det_ne kind exponent identityMatrix
                  identityMatrix_det_ne) innerNonzero
                (normalizedIdentity_lowerRow kind exponent))
              (Descriptions.atom _
                (pulledResidual kind exponent selected
                  (CCL.CCLPullback.adjugate matrix))))

end CCL.CCLFormulaBoundaries
