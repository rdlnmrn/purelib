module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalRunBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseParameters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.CenteredBilinearPath

open Purelib.Curves

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Read each physical run on its certified canonical source index. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns

open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments (OwnedFragment)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

variable (retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared)
  {index : Nat} (inputs : retained.Inputs index)
  (outer : Fin prepared.occurrences.length) {faceIndex : Nat}
  (data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer) faceIndex)
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)

variable {retained inputs outer data coefficients}

namespace ParentFragment
variable {first last : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
  prepared.occurrences outer).compared.entered.cache.parents.length}
  (same : first = last) (fragments : List
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.ParentFragment retained inputs outer data
    coefficients first))

/-- Reindex the complete cached list by equality; no fragment is reconstructed. -/
def castList : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.ParentFragment retained inputs
  outer data coefficients last) :=
  Eq.mp (congrArg (fun position => List
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.ParentFragment retained inputs outer data
    coefficients position)) same) fragments

/-- Transport along equality of parent indices preserves every retained physical/source pair. -/
theorem castList_pairs : (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns.ParentFragment.castList
  same fragments).map Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.pair =
  fragments.map OwnedFragment.pair := by
  cases same
  rfl

/-- Transporting the retained fragment list to an equal parent index preserves its length. -/
theorem castList_length : (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns.ParentFragment.castList
  same fragments).length = fragments.length := by
  cases same
  rfl

/-- Transport along equality of parent indices preserves the complete forward source-chain certificate. -/
theorem castList_chain {start finish : Normalization.InverseRootPolynomial.Coordinate} (chain :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains.SourceChain fragments start finish) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains.SourceChain
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns.ParentFragment.castList same fragments) start
      finish := by
  cases same
  exact chain

/-- Transport along equality of parent indices preserves the complete reverse source-chain certificate. -/
theorem castList_reverse_chain {start finish : Normalization.InverseRootPolynomial.Coordinate} (chain :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains.ReverseSourceChain fragments start finish) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains.ReverseSourceChain
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns.ParentFragment.castList same fragments) start
      finish := by
  cases same
  exact chain

/-- Transporting the retained fragment list to an equal parent index preserves its pointwise forward-width bound. -/
theorem castList_width {width : Normalization.InverseRootPolynomial.Coordinate}
    (bounded : ∀ fragment ∈ fragments, fragment.sourceWidth ≤ width) :
    ∀ fragment ∈ Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns.ParentFragment.castList same
      fragments, fragment.sourceWidth ≤ width := by
  cases same
  exact bounded

/-- Transporting the retained fragment list to an equal parent index preserves its pointwise reverse-width bound. -/
theorem castList_reverse_width {width : Normalization.InverseRootPolynomial.Coordinate}
    (bounded : ∀ fragment ∈ fragments, fragment.reverseSourceWidth ≤ width) :
    ∀ fragment ∈ Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns.ParentFragment.castList same
      fragments, fragment.reverseSourceWidth ≤ width := by
  cases same
  exact bounded

/-- Transporting the retained fragment list to an equal parent index preserves every allowance and tolerance bound. -/
theorem castList_budget {allowance tolerance : Normalization.InverseRootPolynomial.Coordinate}
    (bounded : ∀ fragment ∈ fragments, fragment.allowance ≤ allowance ∧ fragment.budget.tolerance ≤ tolerance) :
    ∀ fragment ∈ Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns.ParentFragment.castList same
      fragments, fragment.allowance ≤ allowance ∧ fragment.budget.tolerance ≤ tolerance := by
  cases same
  exact bounded

end ParentFragment
namespace ParentOrderedRuns
variable (ordered : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns.ParentOrderedRuns retained
  inputs outer data coefficients)
  (position : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer).compared.entered.cache.parents.length)

/-- The retained parent-index certificate fixes the dependent numerical owner. -/
def fragments : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.ParentFragment retained inputs
  outer data coefficients position) :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns.ParentFragment.castList (ordered.runAt_parent
    position) (ordered.runAt position).fragments

/-- The source-indexed fragment list reads exactly the pairs of its selected original run. -/
theorem fragments_pairs : (ordered.fragments position).map
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.pair =
    (ordered.runAt position).fragments.map OwnedFragment.pair :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns.ParentFragment.castList_pairs _ _

/-- The source-indexed fragment list has exactly the length of its selected original run. -/
theorem fragments_length : (ordered.fragments position).length = (ordered.runAt position).fragments.length :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns.ParentFragment.castList_length _ _

/-- Read the full physical path, not merely the sum of its increments. -/
theorem fragments_physical : (((ordered.fragments position).map
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.pair).map Prod.fst).flatten =
    ordered.physical position :=
  congrArg (fun pairs : List (List Topology.Polygon.Stokes.PrimitivePoint × List Topology.Polygon.Stokes.PrimitivePoint)
    => (pairs.map Prod.fst).flatten)
    (ordered.fragments_pairs position)

end ParentOrderedRuns
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns
