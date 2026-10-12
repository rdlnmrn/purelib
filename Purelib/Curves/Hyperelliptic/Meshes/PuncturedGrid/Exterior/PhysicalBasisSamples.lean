module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisForwardEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSourceRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.BilinearCombination
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOccurrenceSchedule
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalArcAggregation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcSamples
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

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalArcAggregation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOccurrenceSchedule

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings

open Purelib.Topology.Polygon

public section

/-! Homogeneous basis comparison for actual cached physical exterior samples. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisSamples
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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalArcAggregation (physicalArcError
  physicalArcValue)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcSamples (basis_arcs_readback)
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

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst)

/-- Actual retained physical samples, with their finite vertex counts. -/
@[expose] def PhysicalOccurrenceValues (prepared : ExteriorProgram.AllSurfacePreparation regular domains differential)
    (counts : Fin prepared.occurrences.length → Nat) :=
  (i : Fin prepared.occurrences.length) → Fin (counts i + 1) → Stokes.PrimitivePoint

/-- The complete dependent bank of conjugate centered samples on the original retained physical occurrence values. -/
@[expose] def PhysicalOccurrenceSamples {prepared : ExteriorProgram.AllSurfacePreparation regular domains differential}
    {counts : Fin prepared.occurrences.length → Nat} (values :
      PhysicalOccurrenceValues prepared counts)
      :=
  Data.Vector.DependentVector (fun i : Fin prepared.occurrences.length =>
    CenteredBilinearPath.Sample (fun vertex => ConjugateIncrementComparison.conjugateFirst (values i vertex)))

set_option genInjectivity false in
/-- A basis pair retains the actual physical samples and synchronized source owners. Its orientation- and
chord-corrected area is computed once. -/
structure PhysicalBasisArcSample (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box)
    (first second : Fin genus) (target : Fraction.Rational) (minimum floor depth : Nat) where
  /-- The original complete exterior preparation for the first basis differential. -/ prepared :
    ExteriorProgram.AllSurfacePreparation regular domains (PeriodMatrix.standardDifferential first)
  /-- The original paired physical-source request for this basis pair and target. -/ request :
    PhysicalSourceRequest prepared (PeriodMatrix.standardDifferential second) target minimum floor
  /-- The actual physical piece count of each retained occurrence. -/ pieceCounts : Fin prepared.occurrences.length →
    Nat
  /-- The retained common physical, source and owner schedule for those original counts. -/ schedule :
    PhysicalOccurrenceSchedule request pieceCounts
  /-- The actual evaluations of the retained query-refined source plans using the original polynomial bank. -/ evaluated
    : PhysicalOccurrenceSchedule.Evaluations schedule (depth := depth) (polynomials.get first) (polynomials.get second)
  /-- The common cap depth pays every retained occurrence source schedule. -/ spatial : schedule.depth ≤ depth
  /-- The actual finite edge counts of the retained physical samples. -/ counts : Fin prepared.occurrences.length → Nat
  /-- The original retained physical occurrence values at those exact counts. -/ values :
    PhysicalOccurrenceValues prepared counts
  /-- The cached conjugate centered samples on the exact original values. -/ samples :
    PhysicalOccurrenceSamples values
  /-- Every original physical occurrence sample meets its retained paired arc-error allowance. -/ accurate : ∀ i,
    Data.Gaussian.Norm.Basic.normSq (PhysicalArcAggregation.physicalArcError
    (prepared.occurrences[i.val]'i.isLt)
    (polynomials.get first) (polynomials.get second) depth (samples.get i).centeredArea) < request.allowance
  /-- The cached physical area with each original occurrence sign and endpoint chord restored. -/ correctedArea :
    Data.Gaussian.Basic.Canonical
  /-- The area cache equals the exact sum of corrected original occurrence samples. -/ correctedArea_eq : correctedArea
    = FiniteSum.Fin.sumFin (fun i => PhysicalArcAggregation.physicalArcValue (prepared.occurrences[i.val]'i.isLt)
    (polynomials.get first) (polynomials.get second) (samples.get i).centeredArea)

constructive_injectivity PhysicalBasisArcSample

namespace PhysicalBasisArcSample
variable {first second : Fin genus} {floor : Nat}

/-- Retain the supplied basis-pair schedule, exact physical samples and accuracy certificates, and cache their corrected
total area. -/
@[expose] def ofSamples
    (basis : ExteriorProgram.AllSurfacePreparation regular domains (PeriodMatrix.standardDifferential first))
    (request : PhysicalSourceRequest basis (PeriodMatrix.standardDifferential second) target
      minimum floor)
    (pieceCounts : Fin basis.occurrences.length → Nat)
    (schedule : PhysicalOccurrenceSchedule request pieceCounts)
    (evaluated : PhysicalOccurrenceSchedule.Evaluations schedule (depth := depth) (polynomials.get first)
      (polynomials.get second))
    (spatial : schedule.depth ≤ depth)
    (counts : Fin basis.occurrences.length → Nat) (values :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisSamples.PhysicalOccurrenceValues basis counts)
    (samples : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisSamples.PhysicalOccurrenceSamples values)
    (accurate : ∀ i, Data.Gaussian.Norm.Basic.normSq (PhysicalArcAggregation.physicalArcError
      (basis.occurrences[i.val]'i.isLt)
      (polynomials.get first) (polynomials.get second) depth (samples.get i).centeredArea) < request.allowance) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisSamples.PhysicalBasisArcSample (regular := regular)
      (domains := domains) polynomials first second target minimum floor depth :=
  ⟨basis, request, pieceCounts, schedule, evaluated, spatial, counts, values, samples, accurate,
    FiniteSum.Fin.sumFin (fun i => PhysicalArcAggregation.physicalArcValue (basis.occurrences[i.val]'i.isLt)
      (polynomials.get first) (polynomials.get second) (samples.get i).centeredArea), rfl⟩

/-- The cached corrected physical area meets the requested error against the original cap attachment's forward basis
boundary. -/
theorem boundary_accurate
    (sample : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisSamples.PhysicalBasisArcSample (regular :=
      regular) (domains := domains) polynomials first second target minimum floor depth) :
    Data.Gaussian.Norm.Basic.normSq (sample.correctedArea - RegularBasisPolynomials.forwardBoundary polynomials
      attached depth first second) < target := by
  have bound := PhysicalSourceRequest.physical_arc_error sample.request (polynomials.get first) (polynomials.get second)
    (fun i => (sample.samples.get i).centeredArea) sample.accurate
  rw [BasisArcSamples.basis_arcs_readback attached polynomials first second sample.prepared depth, ←
    sample.correctedArea_eq] at bound
  exact bound

end PhysicalBasisArcSample

/-- Every basis pair shares the supplied reciprocal polynomial bank and cap depth. -/
@[expose] def PhysicalBasisArcSamples (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box)
    (target : Fraction.Rational) (minimum floor depth : Nat) :=
  Data.Vector.DependentVector (fun first : Fin genus => Data.Vector.DependentVector (fun second : Fin genus =>
    PhysicalBasisArcSample (regular := regular)
      (domains := domains) polynomials first second target minimum floor depth))

namespace PhysicalBasisArcSamples
variable {floor : Nat}

/-- Combine the cached corrected physical basis-pair areas with their conjugate coefficient factors. -/
@[expose] def energy (samples :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisSamples.PhysicalBasisArcSamples (regular := regular)
  (domains := domains) polynomials target minimum floor depth)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) : Gaussian :=
  FiniteSum.Fin.sumFin fun first => FiniteSum.Fin.sumFin fun second => Data.Gaussian.Basic.conj (coefficients
    first) * coefficients second *
    ((samples.get first).get second).correctedArea

/-- The retained physical basis samples give the homogeneous coefficient-mass error bound against the original forward
cap boundary combination. -/
theorem accurate (samples :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisSamples.PhysicalBasisArcSamples (regular := regular)
  (domains := domains) polynomials target minimum floor depth)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    Data.Gaussian.Norm.Basic.normSq (samples.energy coefficients -
      FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Basic.conj
        (coefficients first) * coefficients second *
        RegularBasisPolynomials.forwardBoundary polynomials attached depth first second))) ≤
      (genus : Fraction.Rational)^2 * (Purelib.Riemann.Readings.PreparedObservationCoercivity.coefficientNormSq
        coefficients)^2 * target := by
  unfold PhysicalBasisSamples.PhysicalBasisArcSamples.energy
  rw [← FiniteSum.Fin.sumFin_sub]
  have scalar := FiniteSum.Fin.sumFin_congr fun first => show
      FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Basic.conj (coefficients first) * coefficients second *
        ((samples.get first).get second).correctedArea) -
        FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Basic.conj (coefficients first) * coefficients second
          * RegularBasisPolynomials.forwardBoundary polynomials attached depth first second) =
      FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Basic.conj (coefficients first) * coefficients second *
        (((samples.get first).get second).correctedArea - RegularBasisPolynomials.forwardBoundary polynomials attached
          depth first second)) by
    rw [← FiniteSum.Fin.sumFin_sub]
    apply FiniteSum.Fin.sumFin_congr
    intro second
    ring1
  rw [scalar]
  have estimate := BilinearCombination.combination_bound (fun basis => Data.Gaussian.Basic.conj (coefficients
    basis)) coefficients _
    (fun first second => (((samples.get first).get second).boundary_accurate attached).le)
  rw [FiniteSum.Fin.sumFin_congr (fun basis => Data.Gaussian.Norm.Basic.normSq_conj (coefficients basis))] at estimate
  have coefficientIdentity :
      FiniteSum.Fin.sumFin
          (fun basis : Fin genus => Data.Gaussian.Norm.Basic.normSq (coefficients basis)) =
        PreparedObservationCoercivity.coefficientNormSq coefficients := by
    unfold PreparedObservationCoercivity.coefficientNormSq
    exact FiniteSum.Fin.sumFin_congr
      (fun basis => Data.Gaussian.Norm.Basic.normSq_eq_canonical (coefficients basis))
  exact estimate.trans_eq (by rw [coefficientIdentity]; ring1)

end PhysicalBasisArcSamples
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisSamples
