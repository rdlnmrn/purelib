module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Vertices
public import Purelib.Riemann.RootContinuation.RootOwnerCommonRefinement
import Purelib.Geometry.Path.Gaussian.Lifted.Basic

/-! # Actual common refinements for original source branches

The existing finite common-owner procedure selects a refinement of the
second original owner with strict inclusions into both input boxes.
Its complete cache and factory identity are retained before the original
RootBranch view consumes those same geometric certificates.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.RootBranch

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.RootContinuation

variable {parameter point : Canonical} {firstCount lastCount : Nat}
variable {firstPatch : ContinuedNeighborhood (Paths.polynomial parameter) firstCount}
variable {lastPatch : ContinuedNeighborhood (Paths.polynomial parameter) lastCount}
variable {first : ContinuedNeighborhood.Point firstPatch point}
variable {last : ContinuedNeighborhood.Point lastPatch point}

/-- The operational comparison of two original continued root Point names.

The complete input Points remain the indices of this exact comparison
type, including their original owners and certificates.
-/
@[expose] def Comparison (first : ContinuedNeighborhood.Point firstPatch point)
    (last : ContinuedNeighborhood.Point lastPatch point) :=
  NamedEquivalent first.certificate.value.name last.certificate.value.name

/-- The original common-refinement cache supplies both strict geometric witnesses of a source branch. -/
def ofCommonRefinement (common : RootOwnerCommonRefinement.CommonRefinement first.owner last.owner) :
    RootBranch first last :=
  ⟨common.owner, common.strictFirst, common.strictSecond⟩

/-- The branch keeps the exact selected common owner of the original refinement cache. -/
theorem ofCommonRefinement_common (common : RootOwnerCommonRefinement.CommonRefinement first.owner last.owner) :
    (ofCommonRefinement common).common = common.owner := by rfl

/-- A complete actual refinement cache and its original geometric branch view.

The original owner-name comparison remains an index. Both the actual
refinement index and its second-owner factory equation stay in the existing
CommonRefinement record; the branch retains that same common owner.
-/
@[expose] def Refinement (first : ContinuedNeighborhood.Point firstPatch point)
    (last : ContinuedNeighborhood.Point lastPatch point)
    (equivalent : Comparison first last) :=
  (common : { retained : RootOwnerCommonRefinement.CommonRefinement first.owner last.owner //
    retained = RootOwnerCommonRefinement.acquire first.owner last.owner equivalent }) ×
  { branch : RootBranch first last // branch = ofCommonRefinement common.val }

/-- Construct the actual common refinement once and retain its original source-branch view without choosing an owner. -/
def acquire (first : ContinuedNeighborhood.Point firstPatch point)
    (last : ContinuedNeighborhood.Point lastPatch point)
    (equivalent : NamedEquivalent first.certificate.value.name last.certificate.value.name) :
    Refinement first last equivalent :=
  let common := RootOwnerCommonRefinement.acquire first.owner last.owner equivalent
  ⟨⟨common, rfl⟩, ⟨ofCommonRefinement common, rfl⟩⟩

namespace Refinement

variable {liftedPoint : LiftedPoint 2} {sourceCount : Nat}
    {sourcePatch : ContinuedNeighborhood (Paths.polynomial parameter) sourceCount}

/-- Transport the complete retained refinement through exact source Point, target Vertex and comparison identities.

The selected Common, original acquire equation, branch and branch factory
law are the same supplied cache. Only their original indices change;
no root refinement or branch acquisition is executed.
-/
def castVertex
    (firstVertex lastVertex : Vertex parameter liftedPoint)
    (firstSource lastSource : ContinuedNeighborhood.Point sourcePatch liftedPoint.coordinate)
    (firstEquivalent : NamedEquivalent firstSource.certificate.value.name firstVertex.sample.certificate.value.name)
    (lastEquivalent : NamedEquivalent lastSource.certificate.value.name lastVertex.sample.certificate.value.name)
    (sources : firstSource = lastSource) (vertices : firstVertex = lastVertex)
    (comparisons : HEq firstEquivalent lastEquivalent)
    (retained : Refinement firstSource firstVertex.sample firstEquivalent) :
    Refinement lastSource lastVertex.sample lastEquivalent := by
  cases sources
  cases vertices
  have exactComparison : firstEquivalent = lastEquivalent := eq_of_heq comparisons
  cases exactComparison
  exact retained

/-- Exact endpoint-index transport retains the entire original refinement cache heterogeneously. -/
theorem castVertex_heq
    (firstVertex lastVertex : Vertex parameter liftedPoint)
    (firstSource lastSource : ContinuedNeighborhood.Point sourcePatch liftedPoint.coordinate)
    (firstEquivalent : NamedEquivalent firstSource.certificate.value.name firstVertex.sample.certificate.value.name)
    (lastEquivalent : NamedEquivalent lastSource.certificate.value.name lastVertex.sample.certificate.value.name)
    (sources : firstSource = lastSource) (vertices : firstVertex = lastVertex)
    (comparisons : HEq firstEquivalent lastEquivalent)
    (retained : Refinement firstSource firstVertex.sample firstEquivalent) :
    HEq (castVertex firstVertex lastVertex firstSource lastSource firstEquivalent lastEquivalent
      sources vertices comparisons retained) retained := by
  cases sources
  cases vertices
  have exactComparison : firstEquivalent = lastEquivalent := eq_of_heq comparisons
  cases exactComparison
  unfold castVertex
  rfl

end Refinement

end Purelib.Curves.Legendre.Periods.Jets.Source.RootBranch

end
