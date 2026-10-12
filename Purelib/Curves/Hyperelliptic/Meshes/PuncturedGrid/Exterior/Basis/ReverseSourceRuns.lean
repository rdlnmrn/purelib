module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRunResampling
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseParameters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.Dyadic.SourceListResampling
import Purelib.Integration.Path.Dyadic.SourceResampling
import Purelib.Integration.Path.PairedAreaReversal
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Tactic.Ring

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRunResampling.BasisPreparedCommonRequest

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest

open
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs.BasisPreparedCommonRequest.Acquisition

open
  Acquisition.ChildPairs

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Integration.Path.Dyadic

open Purelib.Riemann.Readings

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

public section

/-! Compare descending common-basis runs with their signed cached source polygons. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceRuns
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonCover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest (BasisPreparedCommonRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations
  (PrimitiveBank)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries (RowData)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments (OwnedFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains (ReverseSourceChain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentBlocks (fragmentBlockError
  owned_fragments_area_bound)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
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
    regular domains differential}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {count : Nat} {patch : PreparedPatch parent}
  {sourceData : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {cover :
    Cover sourceData}
  {covers : BasisSourceCovers parent} {minimum
    floor index depth : Nat}
  {common : BasisCommonCover cover covers minimum}
  {areaAllowance sourceTarget coefficientTarget : Coordinate}
  {request : BasisPreparedCommonRequest
    regular common areaAllowance sourceTarget coefficientTarget floor}
  {box : Purelib.Geometry.Rational.Box}
  {polynomials : RegularBasisPolynomials cap
    index box}
  {originals :
    PrimitiveBank
    covers index}
  {cells : BasisSourceLocations.SampleBank
    covers index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_sub sumFin_congr sumFin_mul_right sumFin_zero)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)

variable {acquired :
  BasisPreparedCommonRequest.Acquisition
  request polynomials originals cells coefficients depth}

open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst conjugateFirst_error)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea (parameterStep)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks (maximum maximum_nonnegative
  le_maximum)

variable {faceIndex : Nat} {data :
  RowData occurrence faceIndex}

set_option genInjectivity false in
/-- Retain the descending physical fragments and the exact ascending reverse of their cached source increments. -/
structure ReverseSourceRun (acquired : BasisPreparedCommonRequest.Acquisition request polynomials originals cells
  coefficients depth)
    {faceIndex : Nat} (data : FragmentQueries.RowData occurrence faceIndex) where
  /-- The actual descending physical fragments in their retained occurrence order. -/ fragments : List
    (OwnedFragments.OwnedFragment (originals := originals) (coefficients := coefficients) data)
  /-- The ascending parameter list obtained from the reversed original source increments. -/ points : List
    InverseRootPolynomial.Coordinate
  /-- The reversed retained source increments are exactly the original primitive's parameterized increment list. -/
    source_eq : PairedAreaReversal.reverseIncrements ((fragments.map OwnedFragment.pair).map Prod.snd).flatten =
    SourceListResampling.increments
      (fun t => ConjugatePathReadback.conjugateDiagonal (PrimitiveBank.value originals coefficients t)) 0 points
  /-- The retained ascending parameters form a complete source chain from zero to one. -/ chain : SourceResampling.Chain
    0 points 1
  /-- The common upper bound on the actual reversed parameter steps. -/ width : InverseRootPolynomial.Coordinate
  /-- Every retained reversed parameter step fits the common width. -/ steps : SourceResampling.widths 0 points width

constructive_injectivity ReverseSourceRun

namespace ReverseSourceRun

/-- Derive the reversed readback and its width from the retained chain. -/
@[expose] def ofChain (fragments : List (OwnedFragments.OwnedFragment (originals := originals) (coefficients :=
  coefficients) data))
    (chain : ReverseSourceChains.ReverseSourceChain fragments 1 0) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceRuns.ReverseSourceRun acquired data :=
  { fragments := fragments
    points := ReverseSourceChain.parameters fragments
    source_eq := chain.source_readback
    chain := chain.parameters_chain
    width := PairedFragmentBlocks.maximum OwnedFragment.reverseSourceWidth fragments
    steps := chain.parameter_widths (fun _ member => PairedFragmentBlocks.le_maximum _ member) }

/-- The coefficient-independent allowance combining the original fragment error and reversed source-resampling error. -/
@[expose] def error (run : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceRuns.ReverseSourceRun
  acquired data) : Coordinate :=
  2 * (FragmentBlocks.fragmentBlockError (acquired := acquired) run.fragments +
    16 * (BasisSourceCovers.primitiveSlope covers)^2 *
      (max run.width ((1 / 2 : InverseRootPolynomial.Coordinate)^(common.depth + acquired.extraDepth)))^2)

/-- The complete descending physical area approximates the negative cached source area, with the same finite fragment
and resampling costs. -/
theorem cached_source_area_bound (run :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceRuns.ReverseSourceRun acquired data)
    {pairs : Acquisition.ChildPairs acquired} (weighted : ChildPairs.Weighted pairs) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area ((run.fragments.map OwnedFragment.pair).map
      Prod.fst).flatten +
      weighted.source.area) ≤ run.error * (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  have owned := FragmentBlocks.owned_fragments_area_bound (acquired := acquired) run.fragments
  have source := Weighted.source_run_bound weighted run.chain run.steps
  rw [← run.source_eq, PairedAreaReversal.area_reverseIncrements] at source
  have negative (a b : InverseRootPolynomial.Gaussian) : -a - b = -(a + b) := by ring1
  rw [negative, Data.Gaussian.Norm.Basic.normSq_neg] at source
  have bounded := (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct owned
      source) (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2))
  have cancel (a b c : InverseRootPolynomial.Gaussian) : (a - b) + (b + c) = a + c := by ring1
  rw [cancel] at bounded
  exact bounded.trans_eq (by unfold ReverseSourceRuns.ReverseSourceRun.error; ring1)

/-- The reversed total has the original parent's cached orientation. -/
theorem reversed_source_total (run :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceRuns.ReverseSourceRun acquired data)
    {pairs : Acquisition.ChildPairs acquired} (weighted : ChildPairs.Weighted pairs) :
    PairedIncrementArea.total
      (PairedAreaReversal.reverseIncrements ((run.fragments.map OwnedFragment.pair).map Prod.snd).flatten) =
      ConjugatePathReadback.conjugateDiagonal weighted.source.total := by
  rw [run.source_eq]
  exact Weighted.source_run_total weighted run.chain

/-- The original descending path has the opposite cached source total. -/
theorem source_total (run : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceRuns.ReverseSourceRun
  acquired data)
    {pairs : Acquisition.ChildPairs acquired} (weighted : ChildPairs.Weighted pairs) :
    PairedIncrementArea.total ((run.fragments.map OwnedFragment.pair).map Prod.snd).flatten =
      PrimitivePoint.zero.sub (ConjugatePathReadback.conjugateDiagonal weighted.source.total) := by
  have total := run.reversed_source_total weighted
  rw [PairedAreaReversal.total_reverseIncrements] at total
  have twice (point : Stokes.PrimitivePoint) : PrimitivePoint.zero.sub (PrimitivePoint.zero.sub point) = point := by
    cases point
    apply congrArg₂ PrimitivePoint.mk <;> dsimp [PrimitivePoint.zero, PrimitivePoint.sub] <;> ring1
  have opposite := congrArg (fun point => PrimitivePoint.zero.sub point) total
  rw [twice] at opposite
  exact opposite

end ReverseSourceRun

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceRuns
