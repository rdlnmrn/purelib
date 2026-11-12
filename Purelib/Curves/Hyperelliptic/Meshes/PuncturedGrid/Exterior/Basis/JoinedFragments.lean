module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.CenteredPathIncrements
import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Integration.Path.JoinedTrace
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalFragments
public import Purelib.Integration.Polynomial.Rectangle.SampleReadback
public import Purelib.Integration.Polynomial.Rectangle.JoinedSampleBlocks
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Meshes.PuncturedGridFaces

open Purelib.Integration.Polynomial.Rectangle

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Integration.Path.CenteredPathIncrements

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

public section

/-! Read complete cached physical paths through their common-source fragments. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments

open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest (ownedValue)

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Differentials.Basic.Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {regular : Disk.RegularBounds.Data cap} {domains :
    Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {count : Nat} {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {sourceData : UniformReciprocalModels.Data patch count} {cover :
    UniformReciprocalCover.Cover sourceData}
  {covers : Disk.Basis.SourceLocations.BasisSourceCovers parent} {minimum floor index
    depth : Nat}
  {common : Disk.Basis.CommonCover.BasisCommonCover cover covers minimum}
  {areaAllowance sourceTarget coefficientTarget : InverseRootPolynomial.Coordinate}
  {request : Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest regular common
    areaAllowance sourceTarget coefficientTarget floor}
  {box : Rational.Box}
  {polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box}
  {originals : Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers index}
  {cells : Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank covers index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

open Purelib.Data.Rat.Fraction.Compatibility

variable {acquired :
  Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest.Acquisition request
  polynomials originals cells coefficients depth}

variable {faceIndex : Nat} {data : FragmentQueries.RowData occurrence
  faceIndex}

set_option genInjectivity false in
/-- A common-basis owned fragment with an exact cached sample readback on the supplied vertex values.

Equality of the complete increment lists preserves the original fragment path and coefficient-weighted point readings.
-/
structure SampledFragment {count : Nat} (values : Fin (count + 1) → Topology.Polygon.Stokes.PrimitivePoint) where
  /-- The original coefficient-weighted common-basis owned fragment. -/ fragment :
    OwnedFragments.OwnedFragment (originals := originals)
    (coefficients := coefficients) data
  /-- The cached centered sample of the supplied vertex values. -/ reading : Periods.CenteredBilinearPath.Sample values
  /-- The sample's increments are exactly the original fragment's cached owned increments. -/ increments_eq :
    Sample.increments reading = Sample.increments fragment.owned

constructive_injectivity SampledFragment

namespace SampledFragment

/-- Exact increment readback preserves the original fragment's centered area. -/
theorem reading_area {count : Nat} {values : Fin (count + 1) → Topology.Polygon.Stokes.PrimitivePoint}
    (certified : SampledFragment (originals :=
      originals) (coefficients := coefficients) (data := data) values) :
    certified.reading.centeredArea = certified.fragment.owned.centeredArea :=
  (Sample.increments_area certified.reading).symm.trans
    ((congrArg Path.PairedIncrementArea.area certified.increments_eq).trans
      (Sample.increments_area certified.fragment.owned))

/-- Transport the original common-basis fragment sample through the retained count and value equalities. -/
@[expose] def ofReadback (fragment : OwnedFragments.OwnedFragment
  (originals := originals) (coefficients := coefficients) data) {count : Nat}
    (equalCount : fragment.vertices = count) (values : Fin (count + 1) → Topology.Polygon.Stokes.PrimitivePoint)
    (equal : ∀ vertex, Path.ConjugateIncrementComparison.conjugateFirst (⟨ownedValue fragment.readings coefficients
      (Fin.cast (congrArg (· + 1) equalCount.symm) vertex),
        OwnerRequest.ownedValue fragment.readings coefficients
          (Fin.cast (congrArg (· + 1) equalCount.symm) vertex)⟩ : Topology.Polygon.Stokes.PrimitivePoint) = values
          vertex) :
    SampledFragment (originals := originals)
      (coefficients := coefficients) (data := data) values :=
  ⟨fragment, SampleReadback.Sample.readback (SampleReadback.Sample.castCount
    equalCount fragment.owned) equal,
    SampleReadback.Sample.castCount_increments equalCount fragment.owned⟩

/-- Transport the certified sample to the vertex trace built from the original index map. -/
@[expose] def ofIndexed {Vertex : Type} {count : Nat} (vertices : Fin (count + 1) → Vertex) (values : Vertex →
  Topology.Polygon.Stokes.PrimitivePoint)
    (original : SampledFragment (originals :=
      originals) (coefficients := coefficients) (data := data)
      (fun vertex => values (vertices vertex))) :
    SampledFragment (originals := originals)
      (coefficients := coefficients) (data := data)
      (fun vertex => values ((Path.JoinedTrace.VertexTrace.ofIndexed vertices).indexed vertex)) :=
  ⟨original.fragment, SampleReadback.VertexTrace.ofIndexedSample vertices values original.reading,
    (SampleReadback.VertexTrace.ofIndexedSample_increments vertices values original.reading).trans
      original.increments_eq⟩

end SampledFragment

/-- Interleave the original piece fragments with one retained owner junction between adjacent pieces. -/
@[expose] def interleaveFragments : {count : Nat} →
    (Fin (count + 1) → OwnedFragments.OwnedFragment (originals :=
      originals) (coefficients := coefficients) data) →
    (Fin count → OwnedFragments.OwnedFragment (originals := originals)
      (coefficients := coefficients) data) → List
      (OwnedFragments.OwnedFragment (originals := originals)
      (coefficients := coefficients) data)
  | 0, pieces, _ => [pieces 0]
  | _ + 1, pieces, junctions => pieces 0 :: junctions 0 ::
      JoinedFragments.interleaveFragments (fun position
        => pieces position.succ) (fun position => junctions position.succ)

/-- The interleaved owned increment blocks equal the original certified piece and junction sample blocks. -/
theorem interleave_owned {Vertex : Type} (values : Vertex → Topology.Polygon.Stokes.PrimitivePoint) {count : Nat}
    (traces : Fin (count + 1) → Path.JoinedTrace.VertexTrace Vertex)
    (pieces : (position : Fin (count + 1)) →
      SampledFragment (originals := originals)
      (coefficients := coefficients) (data := data)
      (fun vertex => values ((traces position).indexed vertex)))
    (junctions : (position : Fin count) →
      SampledFragment (originals := originals)
      (coefficients := coefficients) (data := data)
      (JoinedSampleBlocks.JunctionValues values (traces position.castSucc) (traces position.succ)))
        :
    ((JoinedFragments.interleaveFragments (fun position => (pieces
      position).fragment) (fun position => (junctions position).fragment)).map
      OwnedFragments.OwnedFragment.pair).map Prod.fst =
      JoinedSampleBlocks.sampledBlocks values traces (fun position => (pieces position).reading)
        (fun position => (junctions position).reading) := by
  induction count with
  | zero => exact congrArg (fun block => [block]) (pieces 0).increments_eq.symm
  | succ count ih =>
    change Sample.increments (pieces 0).fragment.owned ::
      Sample.increments (junctions 0).fragment.owned :: _ =
      Sample.increments (pieces 0).reading :: Sample.increments
        (junctions 0).reading :: _
    exact congrArg₂ List.cons (pieces 0).increments_eq.symm
      (congrArg₂ List.cons (junctions 0).increments_eq.symm
        (ih (fun position => traces position.succ) (fun position => pieces position.succ) (fun position => junctions
          position.succ)))

/-- The error controls the original whole-side cached area, including all
owner junctions and the cross-fragment polygon. No whole-path equality or
analytic estimate is supplied by the caller. -/
theorem joined_fragments_area_bound {Vertex : Type} (values : Vertex → Topology.Polygon.Stokes.PrimitivePoint) {count :
  Nat}
    (traces : Fin (count + 1) → Path.JoinedTrace.VertexTrace Vertex)
    (pieces : (position : Fin (count + 1)) →
      SampledFragment (originals := originals)
      (coefficients := coefficients) (data := data)
      (fun vertex => values ((traces position).indexed vertex)))
    (junctions : (position : Fin count) →
      SampledFragment (originals := originals)
      (coefficients := coefficients) (data := data)
      (JoinedSampleBlocks.JunctionValues values (traces position.castSucc) (traces position.succ)))
    {whole : Path.JoinedTrace.VertexTrace Vertex} (original : Periods.CenteredBilinearPath.Sample (fun vertex => values
      (whole.indexed vertex)))
    (traceEq : whole = Path.JoinedTrace.VertexTrace.concatenate traces) :
    let fragments := JoinedFragments.interleaveFragments (fun position
      => (pieces position).fragment) (fun position => (junctions position).fragment)
    Gaussian.Norm.Basic.normSq (original.centeredArea - Path.PairedIncrementArea.area ((fragments.map
      OwnedFragments.OwnedFragment.pair).map Prod.snd).flatten) ≤
      FragmentBlocks.fragmentBlockError (acquired := acquired)
        fragments * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  intro fragments
  have bound := FragmentBlocks.owned_fragments_area_bound (acquired :=
    acquired) fragments
  have owned := JoinedFragments.interleave_owned values traces pieces
    junctions
  change (fragments.map OwnedFragments.OwnedFragment.pair).map
    Prod.fst = _ at owned
  rw [owned, JoinedSampleBlocks.sampledBlocks_flatten values traces _ _ original traceEq,
    (Sample.increments_area original)] at bound
  exact bound

/-- Compare the cached whole physical sample directly with this parent's
cached common source polygon. Both readbacks preserve the complete path. -/
theorem joined_cached_source_area_bound {Vertex : Type} (values : Vertex → Topology.Polygon.Stokes.PrimitivePoint)
  {count : Nat}
    (traces : Fin (count + 1) → Path.JoinedTrace.VertexTrace Vertex)
    (pieces : (position : Fin (count + 1)) →
      SampledFragment (originals := originals)
      (coefficients := coefficients) (data := data)
      (fun vertex => values ((traces position).indexed vertex)))
    (junctions : (position : Fin count) →
      SampledFragment (originals := originals)
      (coefficients := coefficients) (data := data)
      (JoinedSampleBlocks.JunctionValues values (traces position.castSucc) (traces position.succ)))
    {whole : Path.JoinedTrace.VertexTrace Vertex} (original : Periods.CenteredBilinearPath.Sample (fun vertex => values
      (whole.indexed vertex)))
    (traceEq : whole = Path.JoinedTrace.VertexTrace.concatenate traces)
    (chain : SourceChains.SourceChain
      (JoinedFragments.interleaveFragments (fun position => (pieces
        position).fragment) (fun position => (junctions position).fragment)) 0 1)
    {pairs :
      Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs
      acquired} (weighted :
      Disk.Basis.PreparedWeightedPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs.Weighted
      pairs) :
    let run := SourceChains.SourceRun.ofChain (acquired := acquired)
      (JoinedFragments.interleaveFragments (fun position => (pieces
        position).fragment) (fun position => (junctions position).fragment)) chain
    Gaussian.Norm.Basic.normSq (original.centeredArea - weighted.source.area) ≤ run.error *
      (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  intro run
  have bound := run.cached_source_area_bound weighted
  have owned := JoinedFragments.interleave_owned values traces pieces
    junctions
  change (run.fragments.map OwnedFragments.OwnedFragment.pair).map
    Prod.fst = _ at owned
  rw [owned, JoinedSampleBlocks.sampledBlocks_flatten values traces _ _ original traceEq,
    (Sample.increments_area original)] at bound
  exact bound

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments
