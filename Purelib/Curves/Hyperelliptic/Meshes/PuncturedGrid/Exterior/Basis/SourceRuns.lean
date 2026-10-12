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

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {count : Nat} {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {sourceData : Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {cover :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover sourceData}
  {covers : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent} {minimum floor index
    depth : Nat}
  {common : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonCover cover covers minimum}
  {areaAllowance sourceTarget coefficientTarget : Normalization.InverseRootPolynomial.Coordinate}
  {request : Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest regular common
    areaAllowance sourceTarget coefficientTarget floor}
  {box : Rational.Box}
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}
  {originals : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers index}
  {cells : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank covers index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

open Purelib.Data.Rat.Fraction.Compatibility

variable {acquired :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest.Acquisition request
  polynomials originals cells coefficients depth}

variable {faceIndex : Nat} {data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData occurrence
  faceIndex}

set_option genInjectivity false in
/-- A complete physical run retains the exact source parameter chain.
No area estimate or analytic closeness is supplied by the caller. -/
structure SourceRun (acquired :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest.Acquisition request
  polynomials originals cells coefficients depth)
    {faceIndex : Nat} (data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData occurrence
      faceIndex) where
  /-- The complete original owned-fragment list for this physical parent run. -/ fragments : List
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals := originals)
    (coefficients := coefficients) data)
  /-- The original physical source parameter chain. -/ points : List Normalization.InverseRootPolynomial.Coordinate
  /-- The retained source increments are exactly the conjugate primitive increments on this parameter chain. -/
    source_eq : ((fragments.map Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.pair).map
    Prod.snd).flatten =
    Path.Dyadic.SourceListResampling.increments
      (fun t => Path.ConjugatePathReadback.conjugateDiagonal
        (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
        originals coefficients t)) 0 points
  /-- The original parameter chain traverses the complete unit interval. -/ chain : Path.Dyadic.SourceResampling.Chain 0
    points 1
  /-- The common bound on the actual source parameter steps. -/ width : Normalization.InverseRootPolynomial.Coordinate
  /-- Every original parameter step satisfies the retained width bound. -/ steps : Path.Dyadic.SourceResampling.widths 0
    points width

constructive_injectivity SourceRun

namespace SourceRun

/-- Compute the full owned-fragment and source-resampling area error against the cached parent summary.

The actual fragment errors, physical width, common primitive slope and retained reference depth all remain explicit. -/
@[expose] def error (run : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns.SourceRun acquired data) :
  Coordinate :=
  2 * (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentBlocks.fragmentBlockError (acquired := acquired)
    run.fragments +
    16 * (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers)^2 *
      (max run.width ((1 / 2 : Normalization.InverseRootPolynomial.Coordinate)^(common.depth + acquired.extraDepth)))^2)

/-- All fragment areas, owner junctions and source resampling costs remain
in this bound against the actual cached parent source summary. -/
theorem cached_source_area_bound (run : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns.SourceRun acquired
  data)
    {pairs :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs
      acquired} (weighted :
      Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs.Weighted
      pairs) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area ((run.fragments.map
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.pair).map Prod.fst).flatten -
      weighted.source.area) ≤ run.error * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 :=
        open Purelib.Data.Rat in by
  have owned := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentBlocks.owned_fragments_area_bound (acquired :=
    acquired) run.fragments
  rw [run.source_eq] at owned
  have source :=
    Acquisition.ChildPairs.Weighted.source_run_bound
    weighted run.chain run.steps
  have bounded := (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct owned
      source) (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2))
  rw [sub_add_sub_cancel] at bounded
  exact bounded.trans_eq (by unfold Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns.SourceRun.error; ring1)

/-- The resampled source total belongs to this parent's cached summary. -/
theorem source_total (run : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns.SourceRun acquired data) {pairs
  : Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs
  acquired} (weighted :
  Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs.Weighted
  pairs) :
    Path.PairedIncrementArea.total ((run.fragments.map
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.pair).map Prod.snd).flatten =
      Path.ConjugatePathReadback.conjugateDiagonal weighted.source.total := by
  rw [run.source_eq]
  exact
    Acquisition.ChildPairs.Weighted.source_run_total
    weighted run.chain

end SourceRun
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns
