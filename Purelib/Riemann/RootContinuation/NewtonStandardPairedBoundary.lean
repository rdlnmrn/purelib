module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Riemann.RootContinuation.NewtonRequestedBoundary

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PairedAreaReadings
public import Purelib.Riemann.RootContinuation.NewtonRequestedFullHoleAggregate

@[expose] public section

/-! The standard-period triangle caches serve the actual Newton annuli,
including every omitted hole side. No second triangle bank is sampled. -/
namespace Purelib.Riemann.RootContinuation.NewtonStandardPairedBoundary

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Riemann.RootContinuation.NewtonRequestedBoundary (BoundaryPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PairedAreaReadings (CanonicalIntersectionRow
   PairedAreaOwnership)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard (PairedAreaReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms (CutChordPrograms)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods (ComponentSamples)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods (ChordPeriods)
open Purelib.Riemann.RootContinuation.NewtonSelectedInterfaceBank (InterfaceBank)
open Purelib.Riemann.RootContinuation.NewtonOmittedHoleBank (OmittedHoleBank)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}
  {original : BranchCellBank curve
    (Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve branches).branches higher}
  {preparation : NewtonPreparation original} {first second cycle : Fin genus}
  {target radius : Rational} {floor : Nat}
  {prepared : BoundaryPreparation preparation first second target radius floor}
  {row : CanonicalIntersectionRow
    prepared.lifted cycle} {source : Differential genus}
  {programs : CutChordPrograms prepared.lifted
    source}
  {firstComponents : ComponentSamples
    programs.programs first}
  {secondComponents : ComponentSamples
    programs.programs second}
  {firstPeriods : ChordPeriods row.span
    programs firstComponents}
  {secondPeriods : ChordPeriods row.span
    programs secondComponents}
  {segments : Purelib.Data.Vector.DependentVector (fun entry =>
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank (programs.programs.programs
    entry).period)}
  {minimum numericalFloor : Nat} {firstTarget secondTarget : Rational} {extraPoints : List
    Purelib.Data.Gaussian.Basic.Canonical}
  {stage : Nat} {cache : Numerics
    prepared.domains stage}

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Data in
/-- Read the complete Newton boundary from the actual standard-period triangle caches.

The retained ownership certificate identifies both original standard vectors, while the interface and omitted-hole
requests pay the annular area and every original hole-side remainder within four times the target. -/
def readStandardWith
    (periods : Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PairedAreaReadings firstPeriods
      secondPeriods segments prepared.domains minimum numericalFloor
      firstTarget secondTarget extraPoints prepared.paid.cut cache)
    (interfaces : InterfaceBank prepared.excision prepared.traces first second)
    (omitted : OmittedHoleBank prepared.excision prepared.traces first second)
    (later : prepared.index ≤ stage) (interfaceLater : interfaces.index ≤ stage) (omittedLater : omitted.index ≤ stage)
      :
    { readings : prepared.Readings cache //
      Hyperelliptic.Meshes.PuncturedGrid.Standard.PairedAreaReadings.PairedAreaOwnership periods.left periods.right
        readings.1 ∧
      Data.Gaussian.Norm.Basic.normSq (readings.2.val.annuli.selectedArea + prepared.fullHoleRemainder readings.1) <
        4 * target } := by
  let readings := prepared.readWith cache periods.area later
  have ownership : Hyperelliptic.Meshes.PuncturedGrid.Standard.PairedAreaReadings.PairedAreaOwnership periods.left
    periods.right readings.1 := by
    rw [RootContinuation.NewtonRequestedBoundary.BoundaryPreparation.readWith_cut]
    exact periods.ownership
  exact ⟨readings, ownership,
    prepared.full_holes_bound interfaces omitted readings.2.val later interfaceLater omittedLater⟩

end Purelib.Riemann.RootContinuation.NewtonStandardPairedBoundary
