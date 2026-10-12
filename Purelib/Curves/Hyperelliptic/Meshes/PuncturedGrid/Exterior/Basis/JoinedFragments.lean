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
/-- A common-basis owned fragment with an exact cached sample readback on the supplied vertex values.

Equality of the complete increment lists preserves the original fragment path and coefficient-weighted point readings.
-/
structure SampledFragment {count : Nat} (values : Fin (count + 1) → Topology.Polygon.Stokes.PrimitivePoint) where
  /-- The original coefficient-weighted common-basis owned fragment. -/ fragment :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals := originals)
    (coefficients := coefficients) data
  /-- The cached centered sample of the supplied vertex values. -/ reading : Periods.CenteredBilinearPath.Sample values
  /-- The sample's increments are exactly the original fragment's cached owned increments. -/ increments_eq :
    Path.CenteredPathIncrements.Sample.increments reading = Path.CenteredPathIncrements.Sample.increments fragment.owned

constructive_injectivity SampledFragment

namespace SampledFragment

/-- Exact increment readback preserves the original fragment's centered area. -/
theorem reading_area {count : Nat} {values : Fin (count + 1) → Topology.Polygon.Stokes.PrimitivePoint}
    (certified : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments.SampledFragment (originals :=
      originals) (coefficients := coefficients) (data := data) values) :
    certified.reading.centeredArea = certified.fragment.owned.centeredArea :=
  (Path.CenteredPathIncrements.Sample.increments_area certified.reading).symm.trans
    ((congrArg Path.PairedIncrementArea.area certified.increments_eq).trans
      (Path.CenteredPathIncrements.Sample.increments_area certified.fragment.owned))

/-- Transport the original common-basis fragment sample through the retained count and value equalities. -/
@[expose] def ofReadback (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment
  (originals := originals) (coefficients := coefficients) data) {count : Nat}
    (equalCount : fragment.vertices = count) (values : Fin (count + 1) → Topology.Polygon.Stokes.PrimitivePoint)
    (equal : ∀ vertex, Path.ConjugateIncrementComparison.conjugateFirst (⟨ownedValue fragment.readings coefficients
      (Fin.cast (congrArg (· + 1) equalCount.symm) vertex),
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest.ownedValue fragment.readings coefficients
          (Fin.cast (congrArg (· + 1) equalCount.symm) vertex)⟩ : Topology.Polygon.Stokes.PrimitivePoint) = values
          vertex) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments.SampledFragment (originals := originals)
      (coefficients := coefficients) (data := data) values :=
  ⟨fragment, Polynomial.Rectangle.SampleReadback.Sample.readback (Polynomial.Rectangle.SampleReadback.Sample.castCount
    equalCount fragment.owned) equal,
    Polynomial.Rectangle.SampleReadback.Sample.castCount_increments equalCount fragment.owned⟩

/-- Transport the certified sample to the vertex trace built from the original index map. -/
@[expose] def ofIndexed {Vertex : Type} {count : Nat} (vertices : Fin (count + 1) → Vertex) (values : Vertex →
  Topology.Polygon.Stokes.PrimitivePoint)
    (original : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments.SampledFragment (originals :=
      originals) (coefficients := coefficients) (data := data)
      (fun vertex => values (vertices vertex))) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments.SampledFragment (originals := originals)
      (coefficients := coefficients) (data := data)
      (fun vertex => values ((Path.JoinedTrace.VertexTrace.ofIndexed vertices).indexed vertex)) :=
  ⟨original.fragment, Polynomial.Rectangle.SampleReadback.VertexTrace.ofIndexedSample vertices values original.reading,
    (Polynomial.Rectangle.SampleReadback.VertexTrace.ofIndexedSample_increments vertices values original.reading).trans
      original.increments_eq⟩

end SampledFragment

/-- Interleave the original piece fragments with one retained owner junction between adjacent pieces. -/
@[expose] def interleaveFragments : {count : Nat} →
    (Fin (count + 1) → Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals :=
      originals) (coefficients := coefficients) data) →
    (Fin count → Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals := originals)
      (coefficients := coefficients) data) → List
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals := originals)
      (coefficients := coefficients) data)
  | 0, pieces, _ => [pieces 0]
  | _ + 1, pieces, junctions => pieces 0 :: junctions 0 ::
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments.interleaveFragments (fun position
        => pieces position.succ) (fun position => junctions position.succ)

/-- The interleaved owned increment blocks equal the original certified piece and junction sample blocks. -/
theorem interleave_owned {Vertex : Type} (values : Vertex → Topology.Polygon.Stokes.PrimitivePoint) {count : Nat}
    (traces : Fin (count + 1) → Path.JoinedTrace.VertexTrace Vertex)
    (pieces : (position : Fin (count + 1)) →
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments.SampledFragment (originals := originals)
      (coefficients := coefficients) (data := data)
      (fun vertex => values ((traces position).indexed vertex)))
    (junctions : (position : Fin count) →
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments.SampledFragment (originals := originals)
      (coefficients := coefficients) (data := data)
      (Polynomial.Rectangle.JoinedSampleBlocks.JunctionValues values (traces position.castSucc) (traces position.succ)))
        :
    ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments.interleaveFragments (fun position => (pieces
      position).fragment) (fun position => (junctions position).fragment)).map
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.pair).map Prod.fst =
      Polynomial.Rectangle.JoinedSampleBlocks.sampledBlocks values traces (fun position => (pieces position).reading)
        (fun position => (junctions position).reading) := by
  induction count with
  | zero => exact congrArg (fun block => [block]) (pieces 0).increments_eq.symm
  | succ count ih =>
    change Path.CenteredPathIncrements.Sample.increments (pieces 0).fragment.owned ::
      Path.CenteredPathIncrements.Sample.increments (junctions 0).fragment.owned :: _ =
      Path.CenteredPathIncrements.Sample.increments (pieces 0).reading :: Path.CenteredPathIncrements.Sample.increments
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
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments.SampledFragment (originals := originals)
      (coefficients := coefficients) (data := data)
      (fun vertex => values ((traces position).indexed vertex)))
    (junctions : (position : Fin count) →
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments.SampledFragment (originals := originals)
      (coefficients := coefficients) (data := data)
      (Polynomial.Rectangle.JoinedSampleBlocks.JunctionValues values (traces position.castSucc) (traces position.succ)))
    {whole : Path.JoinedTrace.VertexTrace Vertex} (original : Periods.CenteredBilinearPath.Sample (fun vertex => values
      (whole.indexed vertex)))
    (traceEq : whole = Path.JoinedTrace.VertexTrace.concatenate traces) :
    let fragments := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments.interleaveFragments (fun position
      => (pieces position).fragment) (fun position => (junctions position).fragment)
    Data.Gaussian.Norm.Basic.normSq (original.centeredArea - Path.PairedIncrementArea.area ((fragments.map
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.pair).map Prod.snd).flatten) ≤
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentBlocks.fragmentBlockError (acquired := acquired)
        fragments * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  intro fragments
  have bound := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentBlocks.owned_fragments_area_bound (acquired :=
    acquired) fragments
  have owned := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments.interleave_owned values traces pieces
    junctions
  change (fragments.map Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.pair).map
    Prod.fst = _ at owned
  rw [owned, Polynomial.Rectangle.JoinedSampleBlocks.sampledBlocks_flatten values traces _ _ original traceEq,
    (Path.CenteredPathIncrements.Sample.increments_area original)] at bound
  exact bound

/-- Compare the cached whole physical sample directly with this parent's
cached common source polygon. Both readbacks preserve the complete path. -/
theorem joined_cached_source_area_bound {Vertex : Type} (values : Vertex → Topology.Polygon.Stokes.PrimitivePoint)
  {count : Nat}
    (traces : Fin (count + 1) → Path.JoinedTrace.VertexTrace Vertex)
    (pieces : (position : Fin (count + 1)) →
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments.SampledFragment (originals := originals)
      (coefficients := coefficients) (data := data)
      (fun vertex => values ((traces position).indexed vertex)))
    (junctions : (position : Fin count) →
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments.SampledFragment (originals := originals)
      (coefficients := coefficients) (data := data)
      (Polynomial.Rectangle.JoinedSampleBlocks.JunctionValues values (traces position.castSucc) (traces position.succ)))
    {whole : Path.JoinedTrace.VertexTrace Vertex} (original : Periods.CenteredBilinearPath.Sample (fun vertex => values
      (whole.indexed vertex)))
    (traceEq : whole = Path.JoinedTrace.VertexTrace.concatenate traces)
    (chain : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains.SourceChain
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments.interleaveFragments (fun position => (pieces
        position).fragment) (fun position => (junctions position).fragment)) 0 1)
    {pairs :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs
      acquired} (weighted :
      Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs.Weighted
      pairs) :
    let run := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains.SourceRun.ofChain (acquired := acquired)
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments.interleaveFragments (fun position => (pieces
        position).fragment) (fun position => (junctions position).fragment)) chain
    Data.Gaussian.Norm.Basic.normSq (original.centeredArea - weighted.source.area) ≤ run.error *
      (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  intro run
  have bound := run.cached_source_area_bound weighted
  have owned := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments.interleave_owned values traces pieces
    junctions
  change (run.fragments.map Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.pair).map
    Prod.fst = _ at owned
  rw [owned, Polynomial.Rectangle.JoinedSampleBlocks.sampledBlocks_flatten values traces _ _ original traceEq,
    (Path.CenteredPathIncrements.Sample.increments_area original)] at bound
  exact bound

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments
