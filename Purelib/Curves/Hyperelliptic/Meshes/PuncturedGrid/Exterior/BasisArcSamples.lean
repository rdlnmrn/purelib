module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.BilinearCombination
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateArcFamily
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisForwardEnergy
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateArcFamily

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateArcFamily.PairedArcRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Polynomial.Geometry.Grid

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings

public section

/-! Cached basis-pair exterior areas contract against the same complete cap
arc boundary, even when basis preparations have distinct model owners. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation (CapAttachment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily (PairedArcRequest)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential other :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_sub)
open _root_.Purelib.Data.Gaussian.Basic (conj)
open Purelib.Data.Gaussian.Norm.Basic (normSq_conj)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)

variable {index depth minimum : Nat} {box : Purelib.Geometry.Rational.Box} {target :
  Rational}
  {polynomials : RegularBasisPolynomials cap
    index box}
  {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains differential} (attached :
    CapAttachment prepared)

namespace BasisArcSamples

/-- Different basis preparations enumerate the same actual exterior edges. Their cap-arc readback therefore uses this
one retained attachment. -/
theorem basis_arcs_readback (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box)
    (first second : Fin genus)
    (basis : ExteriorProgram.AllSurfacePreparation regular domains (PeriodMatrix.standardDifferential first)) (depth :
      Nat) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (basis.occurrences.map (fun occurrence =>
      PairedArcRequest.conjugateArcValue
      occurrence (polynomials.get first) (polynomials.get second) depth)) =
    polynomials.forwardBoundary attached depth first second := by
  unfold CapBasisEnergy.RegularBasisPolynomials.forwardBoundary
  rw [Polynomial.Geometry.Grid.CellBoundary.sumValues_flatten, attached.words_flatten, ← basis.indexed_eq,
    Data.List.Map.map_map]
  apply congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum
  apply Map.map_congr_left
  intro occurrence _
  dsimp only [PairedArcRequest.conjugateArcValue, Function.comp_def]
  rw [occurrence.placement.start_eq, occurrence.placement.finish_eq]
  rfl

set_option genInjectivity false in
/-- One basis pair keeps its actual exterior preparation, request and path samples. The chord-corrected conjugate source
area is materialized once. -/
structure BasisArcSample (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box)
    (first second : Fin genus) (target : Fraction.Rational) (minimum depth : Nat) where
  /-- The actual original exterior preparation for the first retained basis differential. -/ prepared :
    ExteriorProgram.AllSurfacePreparation regular domains (PeriodMatrix.standardDifferential first)
  /-- The original paired arc request on this exact preparation and second basis differential. -/ request :
    PairedArcFamily.PairedArcRequest prepared (PeriodMatrix.standardDifferential second) target minimum
  /-- The acquired paired paths and samples using the exact retained reciprocal polynomials and common depth. -/
    evaluated : PairedArcRequest.Evaluation request (polynomials.get first) (polynomials.get second) depth
  /-- The retained polynomial stage pays this original paired arc request. -/ later : request.index ≤ index
  /-- The cached complete conjugate source area with every actual occurrence's chord correction. -/ sourceArea :
    Data.Gaussian.Basic.Canonical
  /-- The source area cache is exactly the sum of the acquired original source areas and their retained conjugate chord
    corrections. -/ sourceArea_eq : sourceArea = Data.Gaussian.Norm.Sum.Basic.gaussianSum (evaluated.retained.map
    (fun entry => Entry.conjugateSourceArea entry +
    PairedArcRequest.conjugateChordValue entry.plan.occurrence (polynomials.get first) (polynomials.get second)))

constructive_injectivity BasisArcSample

end BasisArcSamples

namespace BasisArcSamples.BasisArcSample
variable {first second : Fin genus}

/-- Retain the existing basis preparation, request and evaluation, then cache the complete chord-corrected source area
once. -/
@[expose] def ofEvaluation (basis : ExteriorProgram.AllSurfacePreparation regular domains
  (PeriodMatrix.standardDifferential first))
    (request : PairedArcFamily.PairedArcRequest basis (PeriodMatrix.standardDifferential second) target minimum)
    (evaluated : PairedArcRequest.Evaluation request (polynomials.get first) (polynomials.get second) depth)
    (later : request.index ≤ index) : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcSamples.BasisArcSample
      (regular := regular) (domains := domains) polynomials first second target minimum depth :=
  ⟨basis, request, evaluated, later, Data.Gaussian.Norm.Sum.Basic.gaussianSum (evaluated.retained.map (fun entry =>
    Entry.conjugateSourceArea entry +
    PairedArcRequest.conjugateChordValue entry.plan.occurrence (polynomials.get first) (polynomials.get second))), rfl⟩

/-- The cached original basis-pair source area is within its retained target of the complete reciprocal arc boundary. -/
theorem accurate (sample : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcSamples.BasisArcSample (regular :=
  regular) (domains := domains) polynomials first second target minimum depth) :
    Data.Gaussian.Norm.Basic.normSq (sample.sourceArea - polynomials.forwardBoundary attached depth first
      second) < target := by
  have bound := Evaluation.conjugate_arc_error sample.evaluated sample.later
  rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcSamples.basis_arcs_readback attached polynomials first
    second sample.prepared depth, ← sample.sourceArea_eq] at bound
  exact bound

end BasisArcSamples.BasisArcSample

/-- The displayed matrix retains every actual basis-pair source/cap owner. -/
@[expose] def BasisArcSamples (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box) (target :
  Fraction.Rational) (minimum depth : Nat) :=
  Data.Vector.DependentVector (fun first : Fin genus => Data.Vector.DependentVector (fun second : Fin genus =>
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcSamples.BasisArcSample (regular := regular) (domains :=
      domains) polynomials first second target minimum depth))

namespace BasisArcSamples

/-- Contract the retained basis-pair source area matrix against the supplied original coefficients. -/
@[expose] def sourceEnergy (samples : BasisArcSamples
  (regular := regular) (domains := domains) polynomials target minimum depth)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) : Gaussian :=
  FiniteSum.Fin.sumFin fun first => FiniteSum.Fin.sumFin fun second => Data.Gaussian.Basic.conj (coefficients
    first) * coefficients second *
    ((samples.get first).get second).sourceArea

/-- All basis-pair errors are paid homogeneously on the same reciprocal polynomials and common spatial depth, including
the zero vector. -/
theorem accurate (samples : BasisArcSamples (regular
  := regular) (domains := domains) polynomials target minimum depth)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    Data.Gaussian.Norm.Basic.normSq (samples.sourceEnergy coefficients -
      FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Basic.conj
        (coefficients first) * coefficients second *
        polynomials.forwardBoundary attached depth first second))) ≤
      (genus : Fraction.Rational)^2 * (Purelib.Riemann.Readings.PreparedObservationCoercivity.coefficientNormSq
        coefficients)^2 * target := by
  unfold sourceEnergy
  rw [← FiniteSum.Fin.sumFin_sub]
  have scalar := FiniteSum.Fin.sumFin_congr fun first => show
      FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Basic.conj (coefficients first) * coefficients second *
        ((samples.get first).get second).sourceArea) -
        FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Basic.conj (coefficients first) * coefficients second
          * polynomials.forwardBoundary attached depth first second) =
      FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Basic.conj (coefficients first) * coefficients second *
        (((samples.get first).get second).sourceArea - polynomials.forwardBoundary attached depth first second)) by
    rw [← FiniteSum.Fin.sumFin_sub]
    apply FiniteSum.Fin.sumFin_congr
    intro second
    ring1
  rw [scalar]
  have estimate := BilinearCombination.combination_bound (fun basis => Data.Gaussian.Basic.conj (coefficients
    basis)) coefficients _
    (fun first second => (((samples.get first).get second).accurate attached).le)
  rw [FiniteSum.Fin.sumFin_congr (fun basis => Data.Gaussian.Norm.Basic.normSq_conj (coefficients basis))] at estimate
  have same := FiniteSum.Fin.sumFin_congr
    (fun row : Fin genus => Data.Gaussian.Norm.Basic.normSq_eq_canonical (coefficients row))
  rw [same] at estimate
  exact estimate.trans_eq (by unfold PreparedObservationCoercivity.coefficientNormSq; ring1)

end BasisArcSamples
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
