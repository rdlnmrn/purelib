module

public import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Curves.Hyperelliptic.Differentials.PreparedModels
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

/-! # Uniform patch readings at the literal moving trace endpoint Owners

The original patch retains its aligned seed and common winding-one bridge.
Its endpoint samples are compared with the actual cached prepared source
and actual transported target of the same original accepted spatial edge.
No new continuation, seed, point query or root Owner is constructed.
-/

public section

namespace Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
variable {parent : CenteredEdge curve differential}

/-- Compare an original patch-point certificate with the SAME literal moving source Owner.

The cached prepared Owner is the actual source of the moving trace link.
Its zero-fraction query comparison and the patch's original common seed
bridge supply operational agreement. Both input owners remain unchanged.
-/
def sourceEquivalent (patch : PreparedPatch parent) (count : Nat)
    (sample : ContinuedNeighborhood.Point (patch.neighborhood count)
      (parent.edge.segment.pointAt parent.edge.left.parameter)) :
    NamedEquivalent
      (ownerRootName parent.edge.cached.preparedOwner.parameterNonzero parent.edge.cached.preparedOwner)
      sample.certificate.value.name := by
  have sourceInside := patch.start_inside count
  rewrite [parent.edge.point_zero] at sourceInside
  have query := patch.point_equivalent_at count 0 parent.edge.baseInside parent.edge.point_zero
    sourceInside sample
  have cachedName :
      ownerRootName parent.edge.cached.preparedOwner.parameterNonzero parent.edge.cached.preparedOwner =
        parent.edge.preparedRootName := by
    rewrite [parent.edge.cached.preparedOwner_eq]
    unfold Integration.PreparedConstantModels.PreparedEdge.preparedRootName
      PreparedSheetContinuation.preparedRootName ownerRootName
    rfl
  exact (NamedEquivalent.transport cachedName.symm rfl parent.edge.preparedRootEquivalent_baseQuery).trans query

/-- Compare an original patch-point certificate with the SAME literal moving target Owner.

The endpoint query name reads the original transported Owner. Composing
that exact readback with the retained patch bridge preserves the actual
transport and sample, including their separate preparation caches.
-/
def targetEquivalent (patch : PreparedPatch parent) (count : Nat)
    (covered : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    (sample : ContinuedNeighborhood.Point (patch.neighborhood count)
      (parent.edge.segment.pointAt parent.edge.request.endpoint.parameter)) :
    NamedEquivalent
      (ownerRootName
        (PreparedSheetContinuation.transported parent.edge.segment parent.edge.within parent.edge.left
          parent.edge.owner parent.edge.request parent.edge.small).parameterNonzero
        (PreparedSheetContinuation.transported parent.edge.segment parent.edge.within parent.edge.left
          parent.edge.owner parent.edge.request parent.edge.small)) sample.certificate.value.name := by
  have targetInside := covered
  rewrite [parent.edge.point_one] at targetInside
  have query := patch.point_equivalent_at count 1 (of_decide_eq_true rfl) parent.edge.point_one
    targetInside sample
  have targetName : parent.edge.rootName 1 (of_decide_eq_true rfl) =
      ownerRootName
        (PreparedSheetContinuation.transported parent.edge.segment parent.edge.within parent.edge.left
          parent.edge.owner parent.edge.request parent.edge.small).parameterNonzero
        (PreparedSheetContinuation.transported parent.edge.segment parent.edge.within parent.edge.left
          parent.edge.owner parent.edge.request parent.edge.small) := by
    unfold Integration.PreparedConstantModels.PreparedEdge.rootName
    exact PreparedModels.rootAtCached_one_name_eq_transportedRootName curve parent.edge.segment
      parent.edge.within parent.edge.left parent.edge.owner parent.edge.request parent.edge.cached
      parent.edge.ordered parent.edge.small (of_decide_eq_true rfl)
  exact NamedEquivalent.transport targetName rfl query

/-- Compare a cached source sample after transporting only its exact physical-coordinate index.

The complete original Point is retained by the original castPoint operation.
The returned comparison reads that same old certificate name, not a newly
acquired sample at an equal coordinate.
-/
def sourceEquivalentAt (patch : PreparedPatch parent) (count : Nat)
    {point : Data.Gaussian.Basic.Canonical}
    (point_eq : parent.edge.segment.pointAt parent.edge.left.parameter = point)
    (sample : ContinuedNeighborhood.Point (patch.neighborhood count) point) :
    NamedEquivalent
      (ownerRootName parent.edge.cached.preparedOwner.parameterNonzero parent.edge.cached.preparedOwner)
      sample.certificate.value.name :=
  NamedEquivalent.transport rfl (ContinuedNeighborhood.Point.castPoint_name point_eq sample)
    (patch.sourceEquivalent count (ContinuedNeighborhood.Point.castPoint point_eq sample))

/-- Compare a cached target sample while preserving its full Point and actual transported endpoint Owner.

Only the exact coordinate index crosses the supplied scalar equality. The
old root state and seed refinement remain those of the original sample.
-/
def targetEquivalentAt (patch : PreparedPatch parent) (count : Nat)
    (covered : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    {point : Data.Gaussian.Basic.Canonical}
    (point_eq : parent.edge.segment.pointAt parent.edge.request.endpoint.parameter = point)
    (sample : ContinuedNeighborhood.Point (patch.neighborhood count) point) :
    NamedEquivalent
      (ownerRootName
        (PreparedSheetContinuation.transported parent.edge.segment parent.edge.within parent.edge.left
          parent.edge.owner parent.edge.request parent.edge.small).parameterNonzero
        (PreparedSheetContinuation.transported parent.edge.segment parent.edge.within parent.edge.left
          parent.edge.owner parent.edge.request parent.edge.small)) sample.certificate.value.name :=
  NamedEquivalent.transport rfl (ContinuedNeighborhood.Point.castPoint_name point_eq sample)
    (patch.targetEquivalent count covered (ContinuedNeighborhood.Point.castPoint point_eq sample))

end Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch

end
