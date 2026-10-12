module
import Purelib.Data.List.Reverse
import Purelib.Data.List.Map
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
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
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseParameters
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces

public section

open Purelib.Curves
open Purelib.Geometry
open Purelib.Integration
open Purelib
open Purelib.Riemann

/-! Complete reversed common-source paths from retained descending fragment chains. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains

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

/-- Descending parameter chains also retain constant owner-junction steps,
regardless of the fragment's direction tag. -/
inductive ReverseSourceChain : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment
  (originals := originals) (coefficients := coefficients) data) →
    Normalization.InverseRootPolynomial.Coordinate → Normalization.InverseRootPolynomial.Coordinate → Prop where
  /-- An empty descending fragment chain starts and ends at the same retained parameter. -/ | nil (point :
    Normalization.InverseRootPolynomial.Coordinate) :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains.ReverseSourceChain [] point
    point
  /-- Prepend an original descending fragment whose last parameter is the tail's first parameter. -/ | cons (fragment :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals := originals)
    (coefficients := coefficients) data)
      {rest : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals :=
        originals) (coefficients := coefficients) data)} {last : Normalization.InverseRootPolynomial.Coordinate}
      (descending : ∀ edge : Fin fragment.vertices, fragment.parameters edge.succ ≤ fragment.parameters edge.castSucc)
      (tail : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains.ReverseSourceChain
        rest (fragment.parameters (Fin.last fragment.vertices)) last) :
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains.ReverseSourceChain (fragment
        :: rest) (fragment.parameters 0) last

namespace ReverseSourceChain

/-- Assemble the reversed original parameter lists in reverse fragment order. -/
@[expose] def parameters : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment
  (originals := originals) (coefficients := coefficients) data) → List Normalization.InverseRootPolynomial.Coordinate
  | [] => []
  | fragment :: rest =>
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains.ReverseSourceChain.parameters
    rest ++ fragment.reversedSourceParameters

variable {fragments : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals :=
  originals) (coefficients := coefficients) data)}
  {first last width : Normalization.InverseRootPolynomial.Coordinate}

/-- The reversed parameters form an ascending chain between the original terminal and initial parameters. -/
theorem parameters_chain (chain :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains.ReverseSourceChain fragments first last) :
    Path.Dyadic.SourceResampling.Chain last
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains.ReverseSourceChain.parameters fragments)
      first := by
  induction chain with
  | nil point => exact .nil point
  | cons fragment descending tail ih =>
    exact Path.Dyadic.SourceListResampling.Chain.append ih (fragment.reversed_source_chain descending)

/-- A common bound on all original reverse fragment widths bounds the complete reversed parameter chain. -/
theorem parameter_widths (chain :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains.ReverseSourceChain fragments first last)
    (bounded : ∀ fragment ∈ fragments, fragment.reverseSourceWidth ≤ width) :
    Path.Dyadic.SourceResampling.widths last
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains.ReverseSourceChain.parameters fragments)
      width := by
  induction chain with
  | nil point => trivial
  | cons fragment descending tail ih =>
    apply Path.Dyadic.SourceListResampling.widths_append (ih (fun found member => bounded found (List.mem_cons_of_mem _
      member)))
    rw [Path.Dyadic.SourceListResampling.Chain.terminal_eq tail.parameters_chain]
    apply fragment.reversed_source_widths width
    intro edge
    exact (Path.Dyadic.SourceSampleResampling.step_le_meshWidth fragment.parameters false edge).trans
      (bounded fragment List.mem_cons_self)

/-- Reversing concatenated paired increments reverses their block order and each original block. -/
private theorem reverse_append (left right : List Topology.Polygon.Stokes.PrimitivePoint) :
    Path.PairedAreaReversal.reverseIncrements (left ++ right) =
      Path.PairedAreaReversal.reverseIncrements right ++ Path.PairedAreaReversal.reverseIncrements left := by
  simp only [Path.PairedAreaReversal.reverseIncrements, Data.List.Reverse.reverse_append, Data.List.Map.map_append,
    -eq_self, -iff_self]
  rfl

/-- Reverse the complete cached source path, preserving every junction and
all cross-fragment joining contributions. -/
theorem source_readback (chain :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains.ReverseSourceChain fragments first last) :
    Path.PairedAreaReversal.reverseIncrements ((fragments.map
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.pair).map Prod.snd).flatten =
      Path.Dyadic.SourceListResampling.increments
        (fun t => Path.ConjugatePathReadback.conjugateDiagonal
          (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
          originals coefficients t)) last
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains.ReverseSourceChain.parameters
          fragments) := by
  induction chain with
  | nil point => rfl
  | @cons fragment rest last descending tail ih =>
    change Path.PairedAreaReversal.reverseIncrements
      (fragment.pair.2 ++ ((rest.map
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.pair).map Prod.snd).flatten) =
      Path.Dyadic.SourceListResampling.increments _ last
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains.ReverseSourceChain.parameters rest ++
        fragment.reversedSourceParameters)
    rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains.ReverseSourceChain.reverse_append,
      Path.Dyadic.SourceListResampling.increments_append, Path.Dyadic.SourceListResampling.Chain.terminal_eq
      tail.parameters_chain,
      ih, fragment.reversed_source_increments]

end ReverseSourceChain

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains
