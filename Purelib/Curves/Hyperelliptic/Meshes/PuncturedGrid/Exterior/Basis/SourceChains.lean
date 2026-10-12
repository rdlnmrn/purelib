module
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.CenteredPathIncrements
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.Dyadic.SourceListResampling
import Purelib.Integration.Path.Dyadic.SourceResampling
public import Purelib.Integration.Path.Dyadic.SourceSampleResampling
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes

open Purelib.Curves

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Construct complete source-run readbacks from the retained fragment geometry. -/
section

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

section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment

/-- Read the original fragment's parameter list after its first vertex. -/
def
  sourceParameters
  (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals := originals)
  (coefficients := coefficients) data) : List Coordinate :=
  List.ofFn (fun edge : Fin fragment.vertices => fragment.parameters edge.succ)

/-- Compute the maximum forward step in the original source parameter sample. -/
def sourceWidth
  (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals := originals)
  (coefficients := coefficients) data) : Coordinate :=
  Path.Dyadic.SourceSampleResampling.meshWidth fragment.parameters true

/-- The cached source increment list is exactly the original conjugate primitive's increments on the retained
parameters. -/
theorem
  source_increments
  (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals := originals)
  (coefficients := coefficients) data) :
    fragment.pair.2 = Path.Dyadic.SourceListResampling.increments
      (fun t => Path.ConjugatePathReadback.conjugateDiagonal
        (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
        originals coefficients t))
      (fragment.parameters 0) fragment.sourceParameters := by
  change Path.CenteredPathIncrements.Sample.increments fragment.source = _
  rw [Path.CenteredPathIncrements.Sample.increments_raw fragment.source]
  exact (Path.Dyadic.SourceListResampling.increments_ofFn
    (fun t => Path.ConjugatePathReadback.conjugateDiagonal
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
      originals coefficients t)) fragment.parameters).symm

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment

end

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains

/-- Every junction shares the source parameter, but may retain different
physical point owners. The empty tail records its actual terminal parameter. -/
inductive SourceChain : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals
  := originals) (coefficients := coefficients) data) →
    Normalization.InverseRootPolynomial.Coordinate → Normalization.InverseRootPolynomial.Coordinate → Prop where
  /-- An empty retained fragment chain begins and ends at the same parameter. -/ | nil (point :
    Normalization.InverseRootPolynomial.Coordinate) :
    SourceChain [] point point
  /-- Prepend an ordered original fragment whose last parameter is the tail's first parameter. -/ | cons (fragment :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals := originals)
    (coefficients := coefficients) data)
      {rest : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals :=
        originals) (coefficients := coefficients) data)} {last : Normalization.InverseRootPolynomial.Coordinate}
      (ordered : ∀ edge : Fin fragment.vertices, fragment.parameters edge.castSucc ≤ fragment.parameters edge.succ)
      (tail : SourceChain rest
        (fragment.parameters (Fin.last fragment.vertices)) last) :
      SourceChain (fragment :: rest)
        (fragment.parameters 0) last

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains

section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains.SourceChain

/-- Flatten the original fragment parameter lists in retained chain order. -/
def parameters (fragments : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment
  (originals := originals) (coefficients := coefficients) data)) : List Coordinate :=
  (fragments.map
    OwnedFragments.OwnedFragment.sourceParameters).flatten

/-- The complete original fragment chain induces the corresponding ordered scalar parameter chain. -/
theorem parameter_chain : {fragments : List
  (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals := originals) (coefficients
  := coefficients) data)} →
    {first last : Normalization.InverseRootPolynomial.Coordinate} →
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains.SourceChain fragments first last →
      Path.Dyadic.SourceResampling.Chain first
      (parameters fragments) last
  | _, _, _, .nil point => .nil point
  | _, _, _, .cons fragment ordered tail =>
      Path.Dyadic.SourceListResampling.Chain.append (Path.Dyadic.SourceResampling.chain_ofFn fragment.parameters
        ordered)
        (parameter_chain tail)

/-- The retained source blocks flatten to the original primitive's increments on the complete parameter chain. -/
theorem source_path : {fragments : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment
  (originals := originals) (coefficients := coefficients) data)} →
    {first last : Normalization.InverseRootPolynomial.Coordinate} →
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains.SourceChain fragments first last →
    ((fragments.map Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.pair).map
      Prod.snd).flatten =
      Path.Dyadic.SourceListResampling.increments
        (fun t => Path.ConjugatePathReadback.conjugateDiagonal
          (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
          originals coefficients t)) first
          (parameters fragments)
  | _, _, _, .nil _ => rfl
  | _, _, _, .cons fragment ordered tail => by
      change fragment.pair.2 ++ _ = Path.Dyadic.SourceListResampling.increments _ _ (fragment.sourceParameters ++ _)
      rw [Path.Dyadic.SourceListResampling.increments_append, fragment.source_increments]
      have terminal := Path.Dyadic.SourceListResampling.terminal_ofFn fragment.parameters
      change Path.Dyadic.SourceListResampling.terminal (fragment.parameters 0) fragment.sourceParameters = _ at terminal
      rw [terminal,
        source_path tail]
      rfl

/-- A common bound on every original fragment mesh width bounds the complete parameter chain. -/
theorem widths {width : Normalization.InverseRootPolynomial.Coordinate} :
    {fragments : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals :=
      originals) (coefficients := coefficients) data)} →
    {first last : Normalization.InverseRootPolynomial.Coordinate} →
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains.SourceChain fragments first last →
    (∀ fragment ∈ fragments, fragment.sourceWidth ≤ width) →
    Path.Dyadic.SourceResampling.widths first
      (parameters fragments) width
  | _, _, _, .nil _, _ => trivial
  | _, _, _, .cons fragment ordered tail, bounded => by
      have head := Path.Dyadic.SourceResampling.widths_ofFn fragment.parameters width (fun edge =>
        (Path.Dyadic.SourceSampleResampling.step_le_meshWidth fragment.parameters true edge).trans
          (bounded fragment List.mem_cons_self))
      have rest := widths tail
        (fun value member => bounded value (List.mem_cons_of_mem _ member))
      have terminal := Path.Dyadic.SourceListResampling.terminal_ofFn fragment.parameters
      apply Path.Dyadic.SourceListResampling.widths_append head
      rw [terminal]
      exact rest

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains.SourceChain

end

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains.SourceRun

/-- Reuse the fragment samples and derive the complete readback and mesh width
from their parameter chain. No source primitive is reevaluated. -/
def ofChain (fragments : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment
  (originals := originals) (coefficients := coefficients) data))
    (chain : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains.SourceChain fragments 0 1) :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns.SourceRun acquired data :=
  { fragments := fragments
    points := SourceChains.SourceChain.parameters fragments
    source_eq := chain.source_path
    chain := chain.parameter_chain
    width := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum
      OwnedFragments.OwnedFragment.sourceWidth fragments
    steps := chain.widths (fun _ member => Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum _
      member) }

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains.SourceRun

end
