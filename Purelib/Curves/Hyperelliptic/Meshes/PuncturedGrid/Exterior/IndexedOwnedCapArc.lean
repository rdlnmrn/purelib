module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OwnedCapArcComparison
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedFragmentChains
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Integration.Path.JoinedTrace
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedParentOrder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RequestedOwnedCapArc
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches

public section

/-! The whole-side cap estimate constructs and certifies its own parent
runs from the original indexed fragment word. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedOwnedCapArc

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedFragmentChains
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedParentOrder
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OwnedCapArcComparison
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RequestedOwnedCapArc
open Purelib.Integration.Path
open Purelib.Integration.Path.JoinedTrace
open Purelib.Riemann.Periods
open Purelib.Topology.Polygon
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences (PairedSourcePlan)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan
  (ParentEvaluation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues (FirstData SecondData)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies (JoinedFragmentFamily)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping (IndexedOwnedFragment
  IndexedOwnedGrouping)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OwnedCapArcComparison (GroupedSourceFragments)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement (sourceRunDensity)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior (SourceRunRefinement)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open Purelib.Data.Rat.Fraction.Compatibility
variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Riemann.Meshes.LiftedPuncturedGrid base} {differential other :
    Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential} {target : Riemann.Normalization.InverseRootPolynomial.Coordinate} {minimum stage fine
    index : Nat}
  {box otherBox : Purelib.Geometry.Rational.Box}
  {sample : Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {plan : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan occurrence other
    target minimum}

variable {evaluated :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan
  sample otherSample fine}
  {data : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.FirstData occurrence index} {otherData
    : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.SecondData occurrence other index}

open Purelib.Integration.Path.PairedIncrementArea (area)
open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst)

/-- No caller grouping or source-area identity remains: the executable index grouping and its geometric word
certificates supply both internally. -/
theorem JoinedFragmentFamily.conjugate_cap_arc_of_indexed {Vertex : Type} {count : Nat}
    {values : Vertex → Stokes.PrimitivePoint} {traces : Fin (count + 1) → JoinedTrace.VertexTrace Vertex}
    (family : FragmentFamilies.JoinedFragmentFamily (evaluated := evaluated) (data := data) (otherData := otherData)
      values traces)
    (items : List (IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData))
    (readback : items.map IndexedOwnedFragment.fragment = family.fragments)
    {whole : JoinedTrace.VertexTrace Vertex}
    (original : CenteredBilinearPath.Sample (fun vertex => ConjugateIncrementComparison.conjugateFirst (values
      (whole.indexed vertex))))
    (traceEq : whole = VertexTrace.concatenate traces) (later : plan.parents.index ≤ stage)
    {requested : InverseRootPolynomial.Coordinate} {floor : Nat}
    (request : SourceRunRefinement plan.parents.plans.length (SourceRunRefinement.sourceRunDensity
      plan) (requested / 8) floor)
    (word : IndexedOwnedFragment.Word items) (parentWord : IndexedOwnedFragment.ParentWord items)
    (fineEnough : ∀ item ∈ items, IndexedOwnedFragment.FineEnough item request.width)
    (refined : request.depth ≤ plan.parents.depth + fine)
    (ownerPaid : family.error ≤ requested / 8) (capPaid : target ≤ requested / 4) :
    Data.Gaussian.Norm.Basic.normSq (original.centeredArea -
      (Bilinear.arcArea
        (fun point => ConjugateIncrementComparison.conjugateFirst ⟨sample.primitive.value.eval point,
          otherSample.primitive.value.eval point⟩)
        (occurrence.piece.mesh.depth + (plan.parents.depth + fine)) occurrence.start occurrence.finish -
      Stokes.edgeArea
        (ConjugateIncrementComparison.conjugateFirst ⟨sample.primitive.value.eval occurrence.start⁻¹,
          otherSample.primitive.value.eval occurrence.start⁻¹⟩)
        (ConjugateIncrementComparison.conjugateFirst ⟨sample.primitive.value.eval occurrence.finish⁻¹,
          otherSample.primitive.value.eval occurrence.finish⁻¹⟩))) < requested := by
  let grouped := IndexedOwnedGrouping.build items
  let groups := IndexedOwnedGrouping.certify grouped request.width word fineEnough
  have partition : (groups.map GroupedSourceFragments.fragments).flatten = family.fragments :=
    (IndexedOwnedGrouping.certify_partition grouped request.width word fineEnough).trans readback
  have parentOrder : groups.map GroupedSourceFragments.entry = evaluated.retained :=
    IndexedOwnedGrouping.certify_parent_order grouped request.width word fineEnough parentWord
  have widths : ∀ group ∈ groups, group.width ≤ request.width :=
    fun group member => (IndexedOwnedGrouping.certify_widths grouped request.width word fineEnough group member).le
  exact JoinedFragmentFamily.conjugate_cap_arc_requested family groups partition parentOrder original traceEq later
    request
    widths refined ownerPaid capPaid

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedOwnedCapArc
