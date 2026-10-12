module
import Purelib.Data.CCL.Encoding.Parser.State
import Purelib.Data.CCL.Encoding.Parser.Syntax
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Code
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.CCL.Boundary.Description
import Purelib.Geometry.CCL.Parser.Formula.Advance
public import Purelib.Geometry.CCL.Parser.Formula.Description.Radial
public import Purelib.Geometry.CCL.Parser.Formula.Input
import Purelib.Geometry.CCL.Parser.Formula.Residual
import Purelib.Geometry.CCL.Parser.Formula.Sector
import Purelib.Geometry.CCL.Parser.Formula.State
import Purelib.Geometry.CCL.Parser.Normalization
public import Purelib.Geometry.CCL.Sector.Formula.Description
import Purelib.Geometry.Projective.Hermitian.Boundary.Description
import Purelib.Geometry.Projective.Hermitian.Boundary.Dyadic
import Purelib.Geometry.Projective.Hermitian.Formula.Description
import Purelib.Geometry.Projective.Hermitian.Formula.Pullback
import Purelib.Geometry.Projective.Hermitian.Pullback
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.CCL.Encoding.Parser.Constraint
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.SignTest
import Purelib.Geometry.CCL.Parser.Formula.Radial
import Purelib.Geometry.CCL.Sector.Formula
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Projective.Hermitian.Formula.Basic
import Purelib.Geometry.Projective.Hermitian.Radial

public section

open Purelib

open Purelib.Data.CCL.Encoding.Parser

open Purelib.Data.CCL.Encoding.Parser.Syntax

open Purelib.Data.ComplexContinuedFraction.Encoding

open Purelib.Data.ComplexContinuedFraction.Encoding.Sector

open Purelib.Data.Rat

open Purelib.Geometry.CCL

open Purelib.Geometry.CCL.Boundary

open Purelib.Geometry.CCL.Parser

open Purelib.Geometry.CCL.Parser.Formula

open Purelib.Geometry.CCL.Sector.Formula

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Hermitian

open Purelib.Geometry.Projective.Hermitian.Boundary

open Purelib.Geometry.Projective.Hermitian.Formula

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates2.Matrix

/-!
# Boundary provenance for finite CCL formulas

This module follows the syntax tree of each next-bit formula.  Every atom is
paired with a constructive description of its exact zero boundary.  Formula
inspection can therefore hand an unresolved atom directly to the finite
curve-event layer without guessing its geometric origin from coefficients.
-/

namespace Purelib.Geometry.CCL.Parser.Formula.Description

/-- Boundary descriptions for every active parser phase after pullback. -/
@[expose] def pulledActive
    (phase : Syntax.Phase) (inner : GaussianMatrix)
    (innerNonzero : Matrix2.determinant inner ≠ 0) :
    Formula.Descriptions inner ((Formula.activeFormula phase).pullback inner) := by
  cases phase with
  | initial =>
      simp only [Formula.activeFormula, BoundaryFormula.pullback, -eq_self, -iff_self]
      exact Descriptions.truth
  | highUnary count =>
      simp only [Formula.activeFormula, BoundaryFormula.pullback,
        Purelib.Geometry.Projective.Hermitian.Formula.pullbackAtom, -eq_self, -iff_self]
      exact Descriptions.atom _
        (Boundary.pulledAffineNormDyadic
          inner innerNonzero count)
  | lowUnary count =>
      cases count with
      | zero =>
          simp only [Formula.activeFormula, BoundaryFormula.pullback,
            Purelib.Geometry.Projective.Hermitian.Formula.pullbackAtom, -eq_self, -iff_self]
          exact Descriptions.atom _ (by
            simpa only [pow_one, -eq_self, -iff_self] using
              (Boundary.pulledAffineNormDyadic
                inner innerNonzero 1))
      | succ count =>
          simp only [Formula.activeFormula, BoundaryFormula.pullback,
            Purelib.Geometry.Projective.Hermitian.Formula.pullbackAtom, -eq_self, -iff_self]
          exact Descriptions.atom _
            (Description.pulledScaledNormOne
              inner innerNonzero count)
  | loopUnary count =>
      simp only [Formula.activeFormula, BoundaryFormula.pullback,
        Purelib.Geometry.Projective.Hermitian.Formula.pullbackAtom, -eq_self, -iff_self]
      exact Descriptions.atom _
        (Boundary.pulledAffineNormDyadic
          inner innerNonzero count)
  | sector kind exponent bits =>
      simp only [Formula.activeFormula, BoundaryFormula.pullback, -eq_self, -iff_self]
      let outer := Parser.normalizedMatrix kind exponent Coordinates2.Matrix.identityMatrix
      have identityNonzero :
          Matrix2.determinant Coordinates2.Matrix.identityMatrix ≠ 0 := by
        intro determinantZero
        have realZero := congrArg Data.Gaussian.Basic.re determinantZero
        simp only [Matrix2.determinant, Coordinates2.Matrix.identityMatrix,
          Purelib.Data.Gaussian.Basic.mul_re,
          Purelib.Data.Gaussian.Basic.sub_re,
          Purelib.Data.Gaussian.Basic.one_re,
          Purelib.Data.Gaussian.Basic.one_im,
          Purelib.Data.Gaussian.Basic.zero_re,
          Purelib.Data.Gaussian.Basic.zero_im, -eq_self, -iff_self] at realZero
        exact Fraction.Field.zero_ne_one realZero.symm
      have outerNonzero :
          Matrix2.determinant outer ≠ 0 := by
        change Matrix2.determinant
          (Parser.normalizedMatrix kind exponent Coordinates2.Matrix.identityMatrix) ≠ 0
        rw [Parser.normalizedMatrix, Coordinates2.Matrix.det_mul]
        exact Data.Gaussian.Field.mul_ne_zero_direct
          (Parser.normalizationMatrix_det_ne kind exponent) identityNonzero
      have outerLowerRow : outer.c = 0 ∧ outer.d = 1 := by
        have lower := Parser.normalizedMatrix_lowerRow kind exponent Coordinates2.Matrix.identityMatrix
        simpa only [Coordinates2.Matrix.identityMatrix, outer, -eq_self, -iff_self] using lower
      have sectorDescriptions :
          Formula.Descriptions inner ((Formula.sectorBitsFormula kind exponent bits).pullback inner) := by
        simpa only [Formula.sectorBitsFormula, outer, -eq_self, -iff_self] using
          (Description.pulledSectorAlternatives (Code.sectorCandidates bits) outer inner
            outerNonzero innerNonzero outerLowerRow)
      exact Descriptions.and
        (Description.pulledRadial kind exponent inner innerNonzero)
        sectorDescriptions

/-- Describe the pulled-back zero boundary of a normalized sector residual.

Use the explicit affine numerator coefficients to retain an exact squared-norm boundary description. -/
private def pulledResidual
    (kind : Syntax.BlockKind) (exponent : Nat)
    (sector : Data.ComplexContinuedFraction.Encoding.Sector) (inner : GaussianMatrix) :
    Boundary.BoundaryDescription inner
      (Hermitian.pullbackForm inner
        (Formula.residualForm kind exponent sector)) := by
  let matrix := Parser.normalizedMatrix kind exponent Coordinates2.Matrix.identityMatrix
  simpa only [Formula.residualForm, matrix, -eq_self, -iff_self] using
    (BoundaryDescription.pulledAffineNorm inner
      (matrix.a - sector.rep * matrix.c)
      (matrix.b - sector.rep * matrix.d))

/-- Complete atom-boundary provenance for one input-coordinate incremental next-bit formula. -/
@[expose] def inputIncremental
    (state : Data.CCL.Encoding.Parser.State)
    (stateNonzero : Matrix2.determinant state.matrix ≠ 0)
    (bit : Bool) :
    Formula.Descriptions (BoundaryAdjugate.adjugate state.matrix)
      (Formula.inputIncrementalAdvanceFormula state bit) := by
  let inner := BoundaryAdjugate.adjugate state.matrix
  have innerNonzero : Matrix2.determinant inner ≠ 0 := by
    change BoundaryAdjugate.determinant
      (BoundaryAdjugate.adjugate state.matrix) ≠ 0
    rw [BoundaryAdjugate.determinant_adjugate]
    exact stateNonzero
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      simpa only [Formula.inputIncrementalAdvanceFormula,
        Formula.incrementalAdvanceFormula, inner, -eq_self, -iff_self] using
        (pulledActive
          (State.step ⟨Phase.initial, matrix, history⟩ bit).phase
          (BoundaryAdjugate.adjugate matrix) innerNonzero)
  | highUnary count =>
      simpa only [Formula.inputIncrementalAdvanceFormula,
        Formula.incrementalAdvanceFormula, inner, -eq_self, -iff_self] using
        (pulledActive
          (State.step ⟨Phase.highUnary count, matrix, history⟩ bit).phase
          (BoundaryAdjugate.adjugate matrix) innerNonzero)
  | lowUnary count =>
      simpa only [Formula.inputIncrementalAdvanceFormula,
        Formula.incrementalAdvanceFormula, inner, -eq_self, -iff_self] using
        (pulledActive
          (State.step ⟨Phase.lowUnary count, matrix, history⟩ bit).phase
          (BoundaryAdjugate.adjugate matrix) innerNonzero)
  | loopUnary count =>
      simpa only [Formula.inputIncrementalAdvanceFormula,
        Formula.incrementalAdvanceFormula, inner, -eq_self, -iff_self] using
        (pulledActive
          (State.step ⟨Phase.loopUnary count, matrix, history⟩ bit).phase
          (BoundaryAdjugate.adjugate matrix) innerNonzero)
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          simpa only [Formula.inputIncrementalAdvanceFormula,
            Formula.incrementalAdvanceFormula, State.step, inner, -eq_self, -iff_self]
            using
            (pulledActive
              (State.step ⟨Phase.sector kind exponent .zero, matrix, history⟩
                bit).phase
              (BoundaryAdjugate.adjugate matrix) innerNonzero)
      | one first =>
          simpa only [Formula.inputIncrementalAdvanceFormula,
            Formula.incrementalAdvanceFormula, State.step, inner, -eq_self, -iff_self]
            using
            (pulledActive
              (State.step
                ⟨Phase.sector kind exponent (.one first), matrix, history⟩
                bit).phase
              (BoundaryAdjugate.adjugate matrix) innerNonzero)
      | two first second =>
          let selected := Code.sectorOfBits first second bit
          let outer := Parser.normalizedMatrix kind exponent Coordinates2.Matrix.identityMatrix
          have identityNonzero :
              Matrix2.determinant Coordinates2.Matrix.identityMatrix ≠ 0 := by
            intro determinantZero
            have realZero := congrArg Data.Gaussian.Basic.re determinantZero
            simp only [Matrix2.determinant, Coordinates2.Matrix.identityMatrix,
              Purelib.Data.Gaussian.Basic.mul_re,
              Purelib.Data.Gaussian.Basic.sub_re,
              Purelib.Data.Gaussian.Basic.one_re,
              Purelib.Data.Gaussian.Basic.one_im,
              Purelib.Data.Gaussian.Basic.zero_re,
              Purelib.Data.Gaussian.Basic.zero_im, -eq_self, -iff_self] at realZero
            exact Fraction.Field.zero_ne_one realZero.symm
          have outerNonzero :
              Matrix2.determinant outer ≠ 0 := by
            change Matrix2.determinant
              (Parser.normalizedMatrix kind exponent Coordinates2.Matrix.identityMatrix) ≠ 0
            rw [Parser.normalizedMatrix, Coordinates2.Matrix.det_mul]
            exact Data.Gaussian.Field.mul_ne_zero_direct
              (Parser.normalizationMatrix_det_ne kind exponent) identityNonzero
          have outerLowerRow : outer.c = 0 ∧ outer.d = 1 := by
            have lower := Parser.normalizedMatrix_lowerRow kind exponent Coordinates2.Matrix.identityMatrix
            simpa only [Coordinates2.Matrix.identityMatrix, outer, -eq_self, -iff_self] using lower
          have residualDescription :
              Boundary.BoundaryDescription (BoundaryAdjugate.adjugate matrix)
                (Hermitian.pullbackForm
                  (BoundaryAdjugate.adjugate matrix)
                  (Formula.residualForm
                    kind exponent selected)) := by
            simpa only [Formula.residualForm, outer, -eq_self, -iff_self] using
              (BoundaryDescription.pulledAffineNorm
                (BoundaryAdjugate.adjugate matrix)
                (outer.a - selected.rep * outer.c)
                (outer.b - selected.rep * outer.d))
          simp only [Formula.inputIncrementalAdvanceFormula,
            Formula.incrementalAdvanceFormula,
            Purelib.Geometry.CCL.Parser.Formula.advanceFormula, BoundaryFormula.pullback,
            Purelib.Geometry.Projective.Hermitian.Formula.pullbackAtom, -eq_self, -iff_self]
          exact Descriptions.and
            (Description.pulledRadial kind exponent
              (BoundaryAdjugate.adjugate matrix) innerNonzero)
            (Descriptions.and
              (Description.pulledSector selected outer
                (BoundaryAdjugate.adjugate matrix)
                outerNonzero innerNonzero outerLowerRow)
              (Descriptions.atom _
                residualDescription))

end Purelib.Geometry.CCL.Parser.Formula.Description

end
