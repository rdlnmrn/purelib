module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.CenteredPathIncrements
import Purelib.Integration.Path.Dyadic.SourceListResampling
import Purelib.Integration.Path.Dyadic.SourceResampling
import Purelib.Integration.Path.PairedAreaReversal
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceFragmentRuns
public import Purelib.Integration.Path.Dyadic.SourceReversal
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceFragmentRuns

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Integration.Path.Dyadic

@[expose] public section

/-! Ascending resampling certificates for reversed cached source fragments. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseSourceParameters
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences (PairedSourcePlan)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan
  (ParentEvaluation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues (FirstData SecondData sourceValues)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks (OwnedFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open Purelib.Data.Rat.Fraction.Compatibility
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential other :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential} {target : Coordinate} {minimum
    stage fine index : Nat}
  {box otherBox : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {plan : PairedSourcePlan occurrence
    other target minimum}

variable {evaluated :
  ParentEvaluation
  plan sample otherSample fine}
  {data : FirstData occurrence index}
    {otherData : SecondData occurrence
    other index}

namespace OwnedFragment

/-- The ascending parameter list obtained by reversing the original retained source fragment path. -/
def reversedSourceParameters (fragment : PairedFragmentBlocks.OwnedFragment evaluated data otherData) : List Coordinate
  :=
  SourceReversal.reverseParameters (fragment.parameters 0) (OwnedFragment.sourceParameters fragment)

/-- Read the ascending reverse path from the existing cached source sample. -/
theorem reversed_source_increments (fragment : PairedFragmentBlocks.OwnedFragment evaluated data otherData) :
    PairedAreaReversal.reverseIncrements (CenteredPathIncrements.Sample.increments fragment.source) =
      SourceListResampling.increments (PairedFragmentValues.sourceValues fragment.entry)
        (fragment.parameters (Fin.last fragment.count))
          (reversedSourceParameters
          fragment) := by
  have reversed := SourceReversal.increments_reverseParameters
    (PairedFragmentValues.sourceValues fragment.entry) (fragment.parameters 0) (OwnedFragment.sourceParameters fragment)
  rw [(OwnedFragment.source_parameters_terminal fragment)] at reversed
  rw [(OwnedFragment.source_increments_readback fragment) fragment.entry rfl]
  exact reversed.symm

/-- Reverse the actual descending parameter chain, retaining constant steps. -/
theorem reversed_source_chain (fragment : PairedFragmentBlocks.OwnedFragment evaluated data otherData)
    (descending : ∀ edge : Fin fragment.count,
      fragment.parameters edge.succ ≤ fragment.parameters edge.castSucc) :
    SourceResampling.Chain (fragment.parameters (Fin.last fragment.count))
      (reversedSourceParameters
        fragment) (fragment.parameters 0) := by
  apply SourceReversal.reverseParameters_chain
  rw [OwnedFragment.sourceParameters, OfFn.Basic.map_ofFn]
  apply SourceResampling.chain_ofFn (fun vertex => -fragment.parameters vertex)
  intro edge
  exact Fraction.Order.Arithmetic.neg_le_neg_direct (descending edge)

/-- Reversing the original source parameters preserves the supplied bound on every actual descending step. -/
theorem reversed_source_widths (fragment : PairedFragmentBlocks.OwnedFragment evaluated data otherData)
    (width : InverseRootPolynomial.Coordinate)
    (bounded : ∀ edge : Fin fragment.count,
      fragment.parameters edge.castSucc - fragment.parameters edge.succ ≤ width) :
    SourceResampling.widths (fragment.parameters (Fin.last fragment.count))
      (reversedSourceParameters
        fragment) width := by
  have signed : SourceResampling.widths (-fragment.parameters 0)
      ((OwnedFragment.sourceParameters fragment).map (fun point => -point)) width := by
    rw [OwnedFragment.sourceParameters, OfFn.Basic.map_ofFn]
    apply SourceResampling.widths_ofFn (fun vertex => -fragment.parameters vertex) width
    intro edge
    exact (show -fragment.parameters edge.succ - -fragment.parameters edge.castSucc =
      fragment.parameters edge.castSucc - fragment.parameters edge.succ by ring1).trans_le (bounded edge)
  have reversed := SourceReversal.reverseParameters_widths signed
  rw [(OwnedFragment.source_parameters_terminal fragment)] at reversed
  exact reversed

end OwnedFragment
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseSourceParameters
