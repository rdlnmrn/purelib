module
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
public import Purelib.Geometry.CCL.Sector.Formula
public import Purelib.Geometry.Projective.Hermitian.Boundary.Pullback
import Purelib.Geometry.Projective.Hermitian.Formula.Basic
public import Purelib.Geometry.Projective.Hermitian.Formula.Description
public import Purelib.Geometry.Projective.Hermitian.Formula.Pullback
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.SignTest
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Projective.Hermitian.Boundary.Description
import Purelib.Geometry.Projective.Hermitian.Comparison
import Purelib.Geometry.Projective.Hermitian.Pullback

public section

open Purelib

open Purelib.Data.ComplexContinuedFraction.Encoding

open Purelib.Geometry.CCL

open Purelib.Geometry.Projective.Hermitian

open Purelib.Geometry.Projective.Hermitian.Formula

open Purelib.LinearAlgebra.Coordinates2.Matrix

/-!
# Boundary provenance for finite CCL formulas

This module follows the syntax tree of each next-bit formula.  Every atom is
paired with a constructive description of its exact zero boundary.  Formula
inspection can therefore hand an unresolved atom directly to the finite
curve-event layer without guessing its geometric origin from coefficients.
-/

namespace Purelib.Geometry.CCL.Sector.Formula.Description

/-- Boundary descriptions for one complete sector row after pullback. -/
@[expose] def pulledSector
    (sector : Data.ComplexContinuedFraction.Encoding.Sector) (outer inner : GaussianMatrix)
    (outerNonzero : Matrix2.determinant outer ≠ 0)
    (innerNonzero : Matrix2.determinant inner ≠ 0)
    (outerLowerRow : outer.c = 0 ∧ outer.d = 1) :
    Formula.Descriptions inner ((Sector.sectorFormula sector outer).pullback inner) := by
  let realBoundary :=
    Boundary.pulledRealComparison outer inner
      outerNonzero innerNonzero outerLowerRow
  let imaginaryBoundary :=
    Boundary.pulledImaginaryComparison outer inner
      outerNonzero innerNonzero outerLowerRow
  cases sector with
  | east =>
      simp only [Sector.sectorFormula, BoundaryFormula.pullback,
        Purelib.Geometry.Projective.Hermitian.Formula.pullbackAtom, -eq_self, -iff_self]
      exact Descriptions.and
        (Descriptions.atom _ (realBoundary (1 / 2)))
        (Descriptions.and
          (Descriptions.atom _ (imaginaryBoundary (-1 / 2)))
          (Descriptions.atom _ (imaginaryBoundary (1 / 2))))
  | northEast =>
      simp only [Sector.sectorFormula, BoundaryFormula.pullback,
        Purelib.Geometry.Projective.Hermitian.Formula.pullbackAtom, -eq_self, -iff_self]
      exact Descriptions.and
        (Descriptions.atom _ (realBoundary (1 / 2)))
        (Descriptions.atom _ (imaginaryBoundary (1 / 2)))
  | north =>
      simp only [Sector.sectorFormula, BoundaryFormula.pullback,
        Purelib.Geometry.Projective.Hermitian.Formula.pullbackAtom, -eq_self, -iff_self]
      exact Descriptions.and
        (Descriptions.atom _ (realBoundary (-1 / 2)))
        (Descriptions.and
          (Descriptions.atom _ (realBoundary (1 / 2)))
          (Descriptions.atom _ (imaginaryBoundary (1 / 2))))
  | northWest =>
      simp only [Sector.sectorFormula, BoundaryFormula.pullback,
        Purelib.Geometry.Projective.Hermitian.Formula.pullbackAtom, -eq_self, -iff_self]
      exact Descriptions.and
        (Descriptions.atom _ (realBoundary (-1 / 2)))
        (Descriptions.atom _ (imaginaryBoundary (1 / 2)))
  | west =>
      simp only [Sector.sectorFormula, BoundaryFormula.pullback,
        Purelib.Geometry.Projective.Hermitian.Formula.pullbackAtom, -eq_self, -iff_self]
      exact Descriptions.and
        (Descriptions.atom _ (realBoundary (-1 / 2)))
        (Descriptions.and
          (Descriptions.atom _ (imaginaryBoundary (-1 / 2)))
          (Descriptions.atom _ (imaginaryBoundary (1 / 2))))
  | southWest =>
      simp only [Sector.sectorFormula, BoundaryFormula.pullback,
        Purelib.Geometry.Projective.Hermitian.Formula.pullbackAtom, -eq_self, -iff_self]
      exact Descriptions.and
        (Descriptions.atom _ (realBoundary (-1 / 2)))
        (Descriptions.atom _ (imaginaryBoundary (-1 / 2)))
  | south =>
      simp only [Sector.sectorFormula, BoundaryFormula.pullback,
        Purelib.Geometry.Projective.Hermitian.Formula.pullbackAtom, -eq_self, -iff_self]
      exact Descriptions.and
        (Descriptions.atom _ (realBoundary (-1 / 2)))
        (Descriptions.and
          (Descriptions.atom _ (realBoundary (1 / 2)))
          (Descriptions.atom _ (imaginaryBoundary (-1 / 2))))
  | southEast =>
      simp only [Sector.sectorFormula, BoundaryFormula.pullback,
        Purelib.Geometry.Projective.Hermitian.Formula.pullbackAtom, -eq_self, -iff_self]
      exact Descriptions.and
        (Descriptions.atom _ (realBoundary (1 / 2)))
        (Descriptions.atom _ (imaginaryBoundary (-1 / 2)))

/-- Construct boundary descriptions for a finite disjunction of pulled-back sectors.

Preserve list order and the original outer and inner homographies, using their determinant and denominator-row
certificates. -/
private def pulledSectorList
    (sectors : List Data.ComplexContinuedFraction.Encoding.Sector) (outer inner : GaussianMatrix)
    (outerNonzero : Matrix2.determinant outer ≠ 0)
    (innerNonzero : Matrix2.determinant inner ≠ 0)
    (outerLowerRow : outer.c = 0 ∧ outer.d = 1) :
    Formula.Descriptions inner
      ((BoundaryFormula.any (sectors.map fun sector =>
        Sector.sectorFormula sector outer)).pullback inner) := by
  induction sectors with
  | nil =>
      simp only [List.map, BoundaryFormula.any, BoundaryFormula.pullback, -eq_self, -iff_self]
      exact Descriptions.falsity
  | cons sector sectors inductionHypothesis =>
      simp only [List.map, BoundaryFormula.any, BoundaryFormula.pullback, -eq_self, -iff_self]
      exact Descriptions.or
        (pulledSector sector outer inner outerNonzero innerNonzero
          outerLowerRow)
        inductionHypothesis

/-- Build the finite sector alternatives in their original formula order. -/
@[expose] def pulledSectorAlternatives
    (sectors : List Data.ComplexContinuedFraction.Encoding.Sector) (outer inner : GaussianMatrix)
    (outerNonzero : Matrix2.determinant outer ≠ 0)
    (innerNonzero : Matrix2.determinant inner ≠ 0)
    (outerLowerRow : outer.c = 0 ∧ outer.d = 1) :
    Formula.Descriptions inner
      ((BoundaryFormula.any (sectors.map fun sector =>
        Sector.sectorFormula sector outer)).pullback inner) := by
  induction sectors with
  | nil =>
      simp only [List.map, BoundaryFormula.any,
        BoundaryFormula.pullback, -eq_self, -iff_self]
      exact Descriptions.falsity
  | cons sector sectors inductionHypothesis =>
      simp only [List.map, BoundaryFormula.any,
        BoundaryFormula.pullback, -eq_self, -iff_self]
      exact Descriptions.or
        (pulledSector sector outer inner outerNonzero innerNonzero
          outerLowerRow)
        inductionHypothesis
end Purelib.Geometry.CCL.Sector.Formula.Description

end
