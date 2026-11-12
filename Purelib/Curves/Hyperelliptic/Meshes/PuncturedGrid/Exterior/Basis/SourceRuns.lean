module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
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
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Integration.Path.ConjugatePathReadback
public import Purelib.Integration.Path.Dyadic.SourceListResampling
import Purelib.Integration.Path.Dyadic.SourceResampling
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentBlocks
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRunResampling
import Mathlib.Algebra.Ring.Defs
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
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRunResampling.BasisPreparedCommonRequest

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

public section

/-! Compare a complete owned source run with its cached common-parent polygon. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Differentials.Basic.Differential genus}
  {collar : Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {count : Nat} {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {sourceData : Charts.Reciprocal.UniformReciprocalModels.Data patch count} {cover :
    Charts.Reciprocal.UniformReciprocalCover.Cover sourceData}
  {covers : SourceLocations.BasisSourceCovers parent} {minimum floor index
    depth : Nat}
  {common : CommonCover.BasisCommonCover cover covers minimum}
  {areaAllowance sourceTarget coefficientTarget : Coordinate}
  {request : PreparedCommonRequest.BasisPreparedCommonRequest regular common
    areaAllowance sourceTarget coefficientTarget floor}
  {box : Rational.Box}
  {polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box}
  {originals : CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers index}
  {cells : SourceLocations.BasisSourceLocations.SampleBank covers index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

open Purelib.Data.Rat.Fraction.Compatibility

variable {acquired :
  PreparedCommonRequest.BasisPreparedCommonRequest.Acquisition request
  polynomials originals cells coefficients depth}

variable {faceIndex : Nat} {data : FragmentQueries.RowData occurrence
  faceIndex}

set_option genInjectivity false in
/-- A complete physical run retains the exact source parameter chain.
No area estimate or analytic closeness is supplied by the caller. -/
structure SourceRun (acquired :
  PreparedCommonRequest.BasisPreparedCommonRequest.Acquisition request
  polynomials originals cells coefficients depth)
    {faceIndex : Nat} (data : FragmentQueries.RowData occurrence
      faceIndex) where
  /-- The complete original owned-fragment list for this physical parent run. -/ fragments : List
    (OwnedFragments.OwnedFragment (originals := originals)
    (coefficients := coefficients) data)
  /-- The original physical source parameter chain. -/ points : List Coordinate
  /-- The retained source increments are exactly the conjugate primitive increments on this parameter chain. -/
    source_eq : ((fragments.map OwnedFragments.OwnedFragment.pair).map
    Prod.snd).flatten =
    Path.Dyadic.SourceListResampling.increments
      (fun t => Path.ConjugatePathReadback.conjugateDiagonal
        (CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
        originals coefficients t)) 0 points
  /-- The original parameter chain traverses the complete unit interval. -/ chain : Path.Dyadic.SourceResampling.Chain 0
    points 1
  /-- The common bound on the actual source parameter steps. -/ width : Coordinate
  /-- Every original parameter step satisfies the retained width bound. -/ steps : Path.Dyadic.SourceResampling.widths 0
    points width

constructive_injectivity SourceRun

namespace SourceRun

/-- Compute the full owned-fragment and source-resampling area error against the cached parent summary.

The actual fragment errors, physical width, common primitive slope and retained reference depth all remain explicit. -/
@[expose] def error (run : SourceRun acquired data) :
  Coordinate :=
  2 * (FragmentBlocks.fragmentBlockError (acquired := acquired)
    run.fragments +
    16 * (CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers)^2 *
      (max run.width ((1 / 2 : Coordinate)^(common.depth + acquired.extraDepth)))^2)

/-- All fragment areas, owner junctions and source resampling costs remain
in this bound against the actual cached parent source summary. -/
theorem cached_source_area_bound (run : SourceRun acquired
  data)
    {pairs :
      PreparedChildPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs
      acquired} (weighted :
      PreparedWeightedPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs.Weighted
      pairs) :
    Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area ((run.fragments.map
      OwnedFragments.OwnedFragment.pair).map Prod.fst).flatten -
      weighted.source.area) ≤ run.error * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 :=
        open Purelib.Data.Rat in by
  have owned := FragmentBlocks.owned_fragments_area_bound (acquired :=
    acquired) run.fragments
  rw [run.source_eq] at owned
  have source :=
    Acquisition.ChildPairs.Weighted.source_run_bound
    weighted run.chain run.steps
  have bounded := (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct owned
      source) (by decide : (0 : Coordinate) ≤ 2))
  rw [sub_add_sub_cancel] at bounded
  exact bounded.trans_eq (by unfold SourceRun.error; ring1)

/-- The resampled source total belongs to this parent's cached summary. -/
theorem source_total (run : SourceRun acquired data) {pairs
  : PreparedChildPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs
  acquired} (weighted :
  PreparedWeightedPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs.Weighted
  pairs) :
    Path.PairedIncrementArea.total ((run.fragments.map
      OwnedFragments.OwnedFragment.pair).map Prod.snd).flatten =
      Path.ConjugatePathReadback.conjugateDiagonal weighted.source.total := by
  rw [run.source_eq]
  exact
    Acquisition.ChildPairs.Weighted.source_run_total
    weighted run.chain

end SourceRun
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns
