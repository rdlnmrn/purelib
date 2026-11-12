module

public import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance

/-! # Exact endpoint names of original cached prepared-edge queries

At zero the existing reserved transport selects its unchanged-source branch.
At one the original cached-query law reads the accepted moving Owner. These
are exact name readbacks of the original evaluator, rather than new queries
or occurrence comparisons.
-/

public section

namespace Purelib.Riemann.Integration.PreparedConstantModels.PreparedEdge

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Riemann.Branches
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.RootIsolation.SquareRoot.Clearance

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt

/-- The original zero-fraction query reads exactly the same cached prepared Owner's root name. -/
theorem rootName_zero_eq_cached (edge : PreparedEdge curve differential) :
    edge.rootName 0 edge.baseInside = ownerRootName edge.cached.preparedOwner.parameterNonzero
      edge.cached.preparedOwner := by
  unfold rootName
  rewrite [PreparedModels.rootAtCached_zero_name_eq_zeroMoveRootName]
  let source := PreparedSheetContinuation.prepared edge.segment edge.left edge.owner edge.request
  have fixed : ExactQuadraticOwnerClearance.reservedTransport source source.parameterNonzero
      (PreparedSheetContinuation.samePointSmall source)
      (PreparedSheetContinuation.transportReserve edge.segment edge.left edge.request) = source := by
    unfold ExactQuadraticOwnerClearance.reservedTransport
    exact dif_pos rfl
  have same := congrArg (fun owner => ownerRootName owner.parameterNonzero owner) fixed
  exact same.trans (congrArg (fun owner => ownerRootName owner.parameterNonzero owner)
    edge.cached.preparedOwner_eq).symm

/-- The original one-fraction query reads the exact original accepted moving Owner's root name. -/
theorem rootName_one_eq_transported (edge : PreparedEdge curve differential) :
    edge.rootName 1 (by decide) = ownerRootName
      (PreparedSheetContinuation.transported edge.segment edge.within edge.left edge.owner edge.request
        edge.small).parameterNonzero
      (PreparedSheetContinuation.transported edge.segment edge.within edge.left edge.owner edge.request
        edge.small) := by
  unfold rootName
  exact PreparedModels.rootAtCached_one_name_eq_transportedRootName curve edge.segment edge.within edge.left
    edge.owner edge.request edge.cached edge.ordered edge.small (by decide)

end Purelib.Riemann.Integration.PreparedConstantModels.PreparedEdge

end
