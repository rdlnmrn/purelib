module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest
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
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.Dyadic.SourceListResampling
import Purelib.Integration.Path.Dyadic.SourceResampling
import Purelib.Integration.Path.Dyadic.SourceSampleResampling
import Purelib.Integration.Path.PairedAreaReversal
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains
public import Purelib.Integration.Path.Dyadic.SourceReversal
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Reverse cached common-source parameters without reevaluating primitives. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments

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

namespace OwnedFragment

/-- The original fragment's retained source parameter list ends at its actual last sampled parameter. -/
theorem source_parameters_terminal (fragment :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals := originals) (coefficients
  := coefficients) data) :
    Path.Dyadic.SourceListResampling.terminal (fragment.parameters 0) fragment.sourceParameters =
      fragment.parameters (Fin.last fragment.vertices) :=
  Path.Dyadic.SourceListResampling.terminal_ofFn fragment.parameters

/-- Compute the maximum reverse step of the original retained source parameters. -/
def reverseSourceWidth (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment
  (originals := originals) (coefficients := coefficients) data) : Coordinate :=
  Path.Dyadic.SourceSampleResampling.meshWidth fragment.parameters false

/-- Reverse the original source parameter list while retaining its initial endpoint. -/
def reversedSourceParameters (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment
  (originals := originals) (coefficients := coefficients) data) : List Coordinate :=
  Path.Dyadic.SourceReversal.reverseParameters (fragment.parameters 0) fragment.sourceParameters

/-- Read the ascending reverse path from the existing cached source sample. -/
theorem reversed_source_increments (fragment :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals := originals) (coefficients
  := coefficients) data) :
    Path.PairedAreaReversal.reverseIncrements fragment.pair.2 =
      Path.Dyadic.SourceListResampling.increments (fun t => Path.ConjugatePathReadback.conjugateDiagonal
        (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
        originals coefficients t))
        (fragment.parameters (Fin.last fragment.vertices)) fragment.reversedSourceParameters := by
  have reversed := Path.Dyadic.SourceReversal.increments_reverseParameters
    (fun t => Path.ConjugatePathReadback.conjugateDiagonal
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
      originals coefficients t)) (fragment.parameters 0) fragment.sourceParameters
  rw [fragment.source_parameters_terminal] at reversed
  rw [fragment.source_increments]
  exact reversed.symm

/-- Reverse the actual descending parameter chain, retaining constant steps. -/
theorem reversed_source_chain (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment
  (originals := originals) (coefficients := coefficients) data)
    (descending : ∀ edge : Fin fragment.vertices,
      fragment.parameters edge.succ ≤ fragment.parameters edge.castSucc) :
    Path.Dyadic.SourceResampling.Chain (fragment.parameters (Fin.last fragment.vertices))
      fragment.reversedSourceParameters (fragment.parameters 0) := open Purelib.Data.Rat in by
  apply Path.Dyadic.SourceReversal.reverseParameters_chain
  rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.sourceParameters,
    Data.List.OfFn.Basic.map_ofFn]
  apply Path.Dyadic.SourceResampling.chain_ofFn (fun vertex => -fragment.parameters vertex)
  intro edge
  exact Fraction.Order.Arithmetic.neg_le_neg_direct (descending edge)

/-- A bound on each original descending step bounds the complete reversed source parameter list. -/
theorem reversed_source_widths (fragment :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals := originals) (coefficients
  := coefficients) data)
    (width : Normalization.InverseRootPolynomial.Coordinate)
    (bounded : ∀ edge : Fin fragment.vertices,
      fragment.parameters edge.castSucc - fragment.parameters edge.succ ≤ width) :
    Path.Dyadic.SourceResampling.widths (fragment.parameters (Fin.last fragment.vertices))
      fragment.reversedSourceParameters width := by
  have signed : Path.Dyadic.SourceResampling.widths (-fragment.parameters 0)
      (fragment.sourceParameters.map (fun point => -point)) width := by
    rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.sourceParameters,
      Data.List.OfFn.Basic.map_ofFn]
    apply Path.Dyadic.SourceResampling.widths_ofFn (fun vertex => -fragment.parameters vertex) width
    intro edge
    exact (show -fragment.parameters edge.succ - -fragment.parameters edge.castSucc =
      fragment.parameters edge.castSucc - fragment.parameters edge.succ by ring1).trans_le (bounded edge)
  have reversed := Path.Dyadic.SourceReversal.reverseParameters_widths signed
  rw [fragment.source_parameters_terminal] at reversed
  exact reversed

end OwnedFragment
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
