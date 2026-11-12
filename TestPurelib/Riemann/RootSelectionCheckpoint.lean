module

import scripts.checkpoint.RootSelection
import Purelib.Approximation.Gaussian.Sequence.Selection

/-! # Complete original selected comparisons and their actual checked samples -/

namespace TestPurelib.Riemann.RootSelectionCheckpoint

open Purelib
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.CoherentRoot.Localization
open Purelib.Approximation.Gaussian
open Purelib.Data.Rat.Fraction (Rational)

variable {polynomial : CoherentRoot.GaussianPolynomial} {input : FTA.Squarefree.Input polynomial}
  {source : Geometric.GeometricApproximation} {preparation : Preparation input source}

/-- A supplied original band retains the complete ordered checkpoint action at every control policy. -/
example (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate polynomial
      (Elimination.Axis.Separated.separatedEliminationDegree polynomial))
    (same : elimination = Elimination.Axis.Separated.separatedAxisEliminationCertificate polynomial
      input.nonzero input.degreePositive)
    (control : ClearanceCheckpoint.Control IO) (directory : System.FilePath)
    (current ambient : CoherentRoot.Box) (center : Data.Gaussian.Basic.Canonical) {radius : Rational}
    (positive : 0 < radius) (band : Geometry.Rational.Box.Band.Basic.BandBox center radius)
    (sameBand : band = Elimination.Axis.Band.selectedBand elimination center radius positive) :
    RawSubdivisionCheckpoint.bandLinesFromBand polynomial input.nonzero input.degreePositive elimination rfl same
      control directory current ambient center positive band sameBand =
      RawSubdivisionCheckpoint.bandLines polynomial input.nonzero input.degreePositive elimination same
        control directory current ambient center positive :=
  RawSubdivisionCheckpoint.bandLinesFromBand_eq polynomial input.nonzero input.degreePositive elimination rfl same
    control directory current ambient center positive band sameBand

/-- An authenticated saved isolation gives the whole original preparation, including its actual family. -/
example (boxes : FTA.Squarefree.BoxResult polynomial)
    (support : boxes.isolation.support = Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox polynomial)
    (same : boxes = FTA.Squarefree.Build.BoxFTA.prove input)
    (scale : Rational) (nonnegative : 0 ≤ scale)
    (residual : ∀ index, Data.Gaussian.Norm.Basic.normSq (polynomial.eval (source.sample index)) ≤
      Purelib.Approximation.Rational.Geometric.Basic.quarterRadius scale index) :
    Preparation.ofIsolation input boxes support source scale nonnegative residual =
      Preparation.ofResidual input source scale nonnegative residual :=
  Preparation.ofIsolation_eq_ofResidual input boxes support same source scale nonnegative residual

/-- Preparation retains the physical original parent and both starts before any final sample access. -/
example {left right : Nat} {target : Rational}
    (compared : RootSelectionCheckpoint.Compared preparation left right target) (positive : 0 < target)
    (sourceLater candidateLater : Nat)
    (sourceOrder : compared.value.leftIndex ≤ sourceLater)
    (candidateOrder : compared.value.rightIndex ≤ candidateLater) :
    compared.original = preparation ∧ left ≤ compared.value.leftIndex ∧ right ≤ compared.value.rightIndex ∧
      compared.value = compared.anchor.selection.equivalent.compare left right target positive ∧
      Data.Gaussian.Norm.Basic.normSq (source.sample sourceLater -
        compared.anchor.selection.root.approximation.sample candidateLater) < target :=
  ⟨compared.original_eq, compared.value.left_ge, compared.value.right_ge,
    compared.value_eq positive, compared.value.close sourceOrder candidateOrder⟩

/-- A particular saved comparison retains both original starts and its full all-later comparison. -/
example {left right : Nat} {target : Rational}
    (observed : RootSelectionCheckpoint.Observed preparation left right target) (positive : 0 < target)
    (sourceLater candidateLater : Nat)
    (sourceOrder : observed.comparison.value.leftIndex ≤ sourceLater)
    (candidateOrder : observed.comparison.value.rightIndex ≤ candidateLater) :
    left ≤ observed.comparison.value.leftIndex ∧ right ≤ observed.comparison.value.rightIndex ∧
      observed.comparison.value = observed.comparison.anchor.selection.equivalent.compare left right target positive ∧
      Data.Gaussian.Norm.Basic.normSq (source.sample sourceLater -
        observed.comparison.anchor.selection.root.approximation.sample candidateLater) < target :=
  ⟨observed.comparison.value.left_ge, observed.comparison.value.right_ge,
    observed.comparison.value_eq positive, observed.comparison.value.close sourceOrder candidateOrder⟩

/-- The shared reader result identifies the actual returned state, independently of the requested right start. -/
example {left right : Nat} {target : Rational}
    (observed : RootSelectionCheckpoint.Observed preparation left right target) :
    observed.state.val = observed.comparison.anchor.selection.root.stateAt observed.comparison.value.rightIndex ∧
      observed.reading = observed.comparison.anchor.selection.root.approximation.sample
        observed.comparison.value.rightIndex ∧
      observed.comparison.anchor.selection = preparation.select :=
  ⟨observed.state.property, observed.reading_eq, observed.comparison.anchor.selection_eq⟩

/-- The actual retained reading meets the unchanged original independent-start comparison request. -/
example {left right : Nat} {target : Rational}
    (observed : RootSelectionCheckpoint.Observed preparation left right target)
    (point : Data.Gaussian.Basic.Canonical) (constant : ∀ index, source.sample index = point) :
    Data.Gaussian.Norm.Basic.normSq (point - observed.reading) < target := by
  have paid := observed.comparison.value.close (Nat.le_refl observed.comparison.value.leftIndex)
    (Nat.le_refl observed.comparison.value.rightIndex)
  change Data.Gaussian.Norm.Basic.normSq (source.sample observed.comparison.value.leftIndex -
    observed.comparison.anchor.selection.root.approximation.sample observed.comparison.value.rightIndex) <
      target at paid
  have originalSource := constant observed.comparison.value.leftIndex
  rewrite [originalSource, ← observed.reading_eq] at paid
  exact paid

end TestPurelib.Riemann.RootSelectionCheckpoint
