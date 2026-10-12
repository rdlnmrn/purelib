module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalRunBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedReverseRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ScheduledPhysicalRuns
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RetainedRunAcquisition
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedSelection
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonDepthRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentFragmentReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.QuerySchedule
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOwners
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RetainedFragmentBudgets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseParameters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches

open Purelib.Curves

open Purelib.Geometry

open Purelib.Riemann

public section

/-! Certify each actual physical run against its retained prepared parent source. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PreparedPhysicalRuns

open Purelib

open Purelib.Data.Rat

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

variable {bounds : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {sourceAllowance coefficientTarget : Normalization.InverseRootPolynomial.Coordinate} {coverFloor floor : Nat}
  {box : Rational.Box} {polynomials :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}

namespace PhysicalRunBank
variable (bank : PhysicalRunBank retained inputs outer
  coefficients faceIndex depth capacity sideArea allowance tolerance)
  (position : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer).compared.entered.cache.parents.length)
  (source : Charts.Reciprocal.Disk.Basis.PreparedSelection
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs.parentInput retained inputs outer position)
    basis sourceAllowance coefficientTarget coverFloor floor polynomials coefficients)

set_option genInjectivity false in
/-- The certified samples retain their traversal and exact physical fragments.
Both cases compare with the same prepared source, selected by the canonical index. -/
inductive PreparedRun (target : Normalization.InverseRootPolynomial.Coordinate) : Type 3 where
  /-- A certified forward run retaining the original fragment list and its traversal witness. -/ | forward (direction :
    bank.forward = true)
      (certified : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns.CertifiedRun source.integrals
        bank.data target)
      (fragments : certified.run.fragments = bank.ordered.fragments position)
  /-- A certified reverse run retaining the original fragment list and its traversal witness. -/ | reverse (direction :
    bank.forward = false)
      (certified : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns.CertifiedReverseRun source.integrals
        bank.data target)
      (fragments : certified.run.fragments = bank.ordered.fragments position)

constructive_injectivity PreparedRun

variable {target : Normalization.InverseRootPolynomial.Coordinate}
  (runRequest : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns.RunRequest
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer)
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs.parentInput retained inputs outer position).sources
      capacity target minimum)
  {vertices : Fin capacity → Nat} (owners : runRequest.blocks.OwnerPreparation vertices)
  (allowancePaid : allowance ≤ 1) (tolerancePaid : tolerance ≤ runRequest.blocks.budget.tolerance)
  (sourcePaid : runRequest.blocks.queries.sourceMinimum ≤ index) (facePaid : owners.faceIndex ≤ faceIndex)
  (meshPaid : (1 / 2 : Normalization.InverseRootPolynomial.Coordinate) ^ depth ≤ runRequest.refinement.width)
  (depthPaid : runRequest.refinement.depth ≤ source.entry.common.depth + source.integrals.extraDepth)

/-- Acquisition only adds certificates to the retained numerical payloads. -/
@[expose] def prepareRun :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PreparedPhysicalRuns.PhysicalRunBank.PreparedRun bank position
  source target := by
  let fragments := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ScheduledPhysicalRuns.PhysicalRunBank.certifyRun
    bank position runRequest.blocks allowancePaid tolerancePaid
  cases direction : bank.forward with
  | false =>
    have widths : ∀ fragment ∈ bank.ordered.fragments position,
        fragment.reverseSourceWidth ≤ runRequest.refinement.width :=
      fun fragment member =>
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ScheduledPhysicalRuns.PhysicalRunBank.fragments_reverse_width
        bank position direction fragment member).trans meshPaid
    let certified := runRequest.acquireRetainedReverse (acquired := source.integrals) owners fragments
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ScheduledPhysicalRuns.PhysicalRunBank.fragments_capacity bank
        position)
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ScheduledPhysicalRuns.PhysicalRunBank.fragments_reverse_chain
        bank position direction) sourcePaid facePaid widths depthPaid
    exact .reverse direction certified
      (runRequest.acquireRetainedReverse_fragments owners fragments
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ScheduledPhysicalRuns.PhysicalRunBank.fragments_capacity bank
        position)
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ScheduledPhysicalRuns.PhysicalRunBank.fragments_reverse_chain
          bank position direction) sourcePaid facePaid widths depthPaid)
  | true =>
    have widths : ∀ fragment ∈ bank.ordered.fragments position,
        fragment.sourceWidth ≤ runRequest.refinement.width :=
      fun fragment member =>
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ScheduledPhysicalRuns.PhysicalRunBank.fragments_forward_width
        bank position direction fragment member).trans meshPaid
    let certified := runRequest.acquireRetained (acquired := source.integrals) owners fragments
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ScheduledPhysicalRuns.PhysicalRunBank.fragments_capacity bank
        position)
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ScheduledPhysicalRuns.PhysicalRunBank.fragments_forward_chain
        bank position direction) sourcePaid facePaid widths depthPaid
    exact .forward direction certified
      (runRequest.acquireRetained_fragments owners fragments
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ScheduledPhysicalRuns.PhysicalRunBank.fragments_capacity bank
        position)
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ScheduledPhysicalRuns.PhysicalRunBank.fragments_forward_chain
          bank position direction) sourcePaid facePaid widths depthPaid)

end PhysicalRunBank
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PreparedPhysicalRuns
