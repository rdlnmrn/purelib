module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalRunBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseParameters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.PairedAreaReversal
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentFragmentReadback
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentRunSchedule
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RetainedFragmentBudgets
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HierarchicalRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Topology.Polygon.Stokes

open Purelib.Curves

open Purelib.Integration

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Apply synchronized requests to the exact source-indexed physical runs. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ScheduledPhysicalRuns

open Purelib.Riemann.Normalization

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

variable {retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared}
  {index : Nat} {inputs : retained.Inputs index}
  {outer : Fin prepared.occurrences.length} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
  {faceIndex depth capacity minimum : Nat} {sideArea : Normalization.InverseRootPolynomial.Gaussian} {requested
    allowance tolerance : Normalization.InverseRootPolynomial.Coordinate}

namespace PhysicalRunBank
variable (bank : PhysicalRunBank retained inputs outer
  coefficients faceIndex depth capacity sideArea allowance tolerance)
  (position : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer).compared.entered.cache.parents.length)

/-- The selected original parent run has at most the retained physical capacity many fragments. -/
private theorem runAt_capacity : (bank.ordered.runAt position).fragments.length ≤ capacity :=
  bank.capacity_bound _ (bank.ordered.runAt_mem position)

/-- A forward bank gives a source chain from zero to one on the selected original run. -/
private theorem runAt_forward_chain (forward : bank.forward = true) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains.SourceChain (bank.ordered.runAt position).fragments 0
      1 := by
  have chains := bank.chains
  unfold PhysicalRunBank.Chains at chains
  rw [forward] at chains
  exact chains _ (bank.ordered.runAt_mem position)

/-- A reverse bank gives a source chain from one to zero on the selected original run. -/
private theorem runAt_reverse_chain (reverse : bank.forward = false) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains.ReverseSourceChain (bank.ordered.runAt
      position).fragments 1 0 := by
  have chains := bank.chains
  unfold PhysicalRunBank.Chains at chains
  rw [reverse] at chains
  exact chains _ (bank.ordered.runAt_mem position)

/-- Every fragment in the selected forward run satisfies the retained dyadic width bound. -/
private theorem runAt_forward_width (forward : bank.forward = true)
    (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals :=
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs.parentInput retained inputs outer
      (bank.ordered.runAt position).parent).numerical.originals)
      (coefficients := coefficients) bank.data)
    (member : fragment ∈ (bank.ordered.runAt position).fragments) :
    fragment.sourceWidth ≤ (1 / 2 : Normalization.InverseRootPolynomial.Coordinate)^depth := by
  have widths := bank.widths
  unfold PhysicalRunBank.Widths at widths
  rw [forward] at widths
  exact (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.sourceWidth member).trans
    (widths _ (bank.ordered.runAt_mem position))

/-- Every fragment in the selected reverse run satisfies the retained dyadic reverse-width bound. -/
private theorem runAt_reverse_width (reverse : bank.forward = false)
    (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals :=
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs.parentInput retained inputs outer
      (bank.ordered.runAt position).parent).numerical.originals)
      (coefficients := coefficients) bank.data)
    (member : fragment ∈ (bank.ordered.runAt position).fragments) :
    fragment.reverseSourceWidth ≤ (1 / 2 : Normalization.InverseRootPolynomial.Coordinate)^depth := by
  have widths := bank.widths
  unfold PhysicalRunBank.Widths at widths
  rw [reverse] at widths
  exact (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.reverseSourceWidth member).trans
    (widths _ (bank.ordered.runAt_mem position))

/-- The canonically indexed original fragment list satisfies the retained capacity bound. -/
theorem fragments_capacity : (bank.ordered.fragments position).length ≤ capacity :=
  (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns.ParentOrderedRuns.fragments_length bank.ordered
    position).trans_le
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ScheduledPhysicalRuns.PhysicalRunBank.runAt_capacity bank
    position)

/-- The canonically indexed forward fragments form a source chain from zero to one. -/
theorem fragments_forward_chain (forward : bank.forward = true) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains.SourceChain (bank.ordered.fragments position) 0 1 :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns.ParentFragment.castList_chain _ _
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ScheduledPhysicalRuns.PhysicalRunBank.runAt_forward_chain bank
    position forward)

/-- The canonically indexed reverse fragments form a source chain from one to zero. -/
theorem fragments_reverse_chain (reverse : bank.forward = false) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains.ReverseSourceChain (bank.ordered.fragments
      position) 1 0 :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns.ParentFragment.castList_reverse_chain _ _
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ScheduledPhysicalRuns.PhysicalRunBank.runAt_reverse_chain bank
    position reverse)

/-- The canonically indexed forward fragments satisfy the retained dyadic width bound. -/
theorem fragments_forward_width (forward : bank.forward = true) :
    ∀ fragment ∈ bank.ordered.fragments position, fragment.sourceWidth ≤ (1 / 2 :
      Normalization.InverseRootPolynomial.Coordinate)^depth :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns.ParentFragment.castList_width _ _
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ScheduledPhysicalRuns.PhysicalRunBank.runAt_forward_width bank
    position forward)

/-- The canonically indexed reverse fragments satisfy the retained dyadic reverse-width bound. -/
theorem fragments_reverse_width (reverse : bank.forward = false) :
    ∀ fragment ∈ bank.ordered.fragments position, fragment.reverseSourceWidth ≤ (1 / 2 :
      Normalization.InverseRootPolynomial.Coordinate)^depth :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns.ParentFragment.castList_reverse_width _ _
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ScheduledPhysicalRuns.PhysicalRunBank.runAt_reverse_width bank
    position reverse)

/-- Each canonically indexed original fragment retains the bank allowance and tolerance bounds. -/
theorem fragments_budget : ∀ fragment ∈ bank.ordered.fragments position,
    fragment.allowance ≤ allowance ∧ fragment.budget.tolerance ≤ tolerance :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns.ParentFragment.castList_budget _ _ (bank.budgets _
    (bank.ordered.runAt_mem position))

/-- Attach the request on the canonical parent index, preserving the original list. -/
def certifyRun {target : Normalization.InverseRootPolynomial.Coordinate}
    (selected : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks.BlockRequest
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer)
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs.parentInput retained inputs outer
        position).sources capacity target)
    (allowancePaid : allowance ≤ 1) (tolerancePaid : tolerance ≤ selected.budget.tolerance) :
    selected.RetainedFragments (bank.ordered.fragments position) :=
  selected.certifyFragments _ (fun fragment member =>
    let bounds :=
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ScheduledPhysicalRuns.PhysicalRunBank.fragments_budget bank
      position fragment member
    ⟨bounds.1.trans allowancePaid, bounds.2.trans tolerancePaid⟩)

/-- A forward bank reads exactly the flattened physical increments of its original parent fragments. -/
theorem forward_physical (forward : bank.forward = true) : bank.physical position =
    (((bank.ordered.fragments position).map
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.pair).map Prod.fst).flatten := by
  change (if bank.forward then bank.ordered.physical position else
    Path.PairedAreaReversal.reverseIncrements (bank.ordered.physical position)) = _
  rw [forward]
  exact (bank.ordered.fragments_physical position).symm

/-- A reverse bank reads the reversed increments of its original flattened parent fragments. -/
theorem reverse_physical (reverse : bank.forward = false) : bank.physical position =
    Path.PairedAreaReversal.reverseIncrements
      (((bank.ordered.fragments position).map
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.pair).map Prod.fst).flatten := by
  change (if bank.forward then bank.ordered.physical position else
    Path.PairedAreaReversal.reverseIncrements (bank.ordered.physical position)) = _
  rw [reverse]
  exact congrArg Path.PairedAreaReversal.reverseIncrements (bank.ordered.fragments_physical position).symm

variable (schedule :
  ParentRunSchedule retained
  inputs outer capacity requested minimum)

/-- A forward fragment satisfies its retained parent request width once the scheduled depth is paid. -/
theorem scheduled_forward_width (forward : bank.forward = true) (later : schedule.depth ≤ depth)
    (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals :=
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs.parentInput retained inputs outer
      position).numerical.originals)
      (coefficients := coefficients) bank.data)
    (member : fragment ∈ bank.ordered.fragments position) :
    fragment.sourceWidth ≤ (schedule.requests.get position).refinement.width :=
  (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ScheduledPhysicalRuns.PhysicalRunBank.fragments_forward_width bank
    position forward fragment member).trans (schedule.width_le position later)

/-- A reverse fragment satisfies its retained parent request width once the scheduled depth is paid. -/
theorem scheduled_reverse_width (reverse : bank.forward = false) (later : schedule.depth ≤ depth)
    (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals :=
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs.parentInput retained inputs outer
      position).numerical.originals)
      (coefficients := coefficients) bank.data)
    (member : fragment ∈ bank.ordered.fragments position) :
    fragment.reverseSourceWidth ≤ (schedule.requests.get position).refinement.width :=
  (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ScheduledPhysicalRuns.PhysicalRunBank.fragments_reverse_width bank
    position reverse fragment member).trans (schedule.width_le position later)

end PhysicalRunBank
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ScheduledPhysicalRuns
