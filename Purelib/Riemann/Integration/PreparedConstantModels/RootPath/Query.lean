module

public import Purelib.Riemann.Integration.PreparedConstantModels.RootPath
public import Purelib.Riemann.Integration.PreparedConstantModels.Query
public import Purelib.Riemann.RootContinuation.FixedRootBoxPath.At
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

/-! # Actual interior query comparison on the same cached accepted-edge RootPath

The original two budgets and complete PathData are retained. A derived
prepared-source/reference comparison is propagated to actual interior
Owners using their separate original-box refinements. A retained direct
query then gives the original evaluator-name comparison by exact readback.
No final query agreement, transport replay or same-sign label is assumed.
-/

public section

namespace Purelib.Riemann.Integration.PreparedConstantModels.PreparedEdge.RootPath

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.FixedRootBoxPath (Inside)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.RootIsolation.SquareRoot.Owner.Transport (castOwnerParameter castOwnerParameter_initial_box)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
    {edge : PreparedEdge curve differential} {source : Canonical} {owner : Owner source}
    {second : FixedRootBoxBudget.Budget owner}
    {movement : ∀ time : Rational, Inside time →
      Purelib.Data.Gaussian.Norm.Basic.normSq (source - curve.polynomial.eval (edge.point time)) ≤ second.movement}
    (retained : RootPath edge second movement)

/-- Derive same-point signed agreement of two actual interior Owners using the SAME cached two-budget path.

The prepared-start comparison is assembly evidence on the actual cached
source and independent initial reference. The interior comparison is the
conclusion. Four exact index casts retain all supplied Owners and their
separate refinements; no original input Owner or source preparation is reconstructed.
-/
def retainedAtEquivalent (time : Rational) (inside : Inside time)
    (firstReference : Owner (curve.polynomial.eval (edge.segment.pointAt edge.left.parameter)))
    (firstRefines : firstReference.track.initial.box.Refines owner.track.initial.box)
    (start : NamedEquivalent (ownerRootName edge.cached.preparedOwner.parameterNonzero edge.cached.preparedOwner)
      (ownerRootName firstReference.parameterNonzero firstReference))
    (actual reference : Owner (curve.polynomial.eval (edge.point time)))
    (actualRefines : actual.track.initial.box.Refines edge.cached.preparedOwner.track.initial.box)
    (referenceRefines : reference.track.initial.box.Refines owner.track.initial.box) :
    NamedEquivalent (ownerRootName actual.parameterNonzero actual)
      (ownerRootName reference.parameterNonzero reference) := by
  let firstStart := castOwnerParameter retained.source_eq.symm edge.cached.preparedOwner
  let secondStart := castOwnerParameter retained.source_eq.symm firstReference
  let firstAt := castOwnerParameter (retained.point_eq time).symm actual
  let secondAt := castOwnerParameter (retained.point_eq time).symm reference
  have initial : NamedEquivalent (ownerRootName firstStart.parameterNonzero firstStart)
      (ownerRootName secondStart.parameterNonzero secondStart) :=
    NamedEquivalent.transport
      (SquareRootTrackEquivalence.ownerRootName_castOwnerParameter retained.source_eq.symm
        edge.cached.preparedOwner).symm
      (SquareRootTrackEquivalence.ownerRootName_castOwnerParameter retained.source_eq.symm firstReference).symm start
  have firstStartRefines : firstStart.track.initial.box.Refines edge.cached.preparedOwner.track.initial.box := by
    unfold firstStart
    rewrite [castOwnerParameter_initial_box]
    exact Geometry.Rational.Box.refines_refl _
  have secondStartRefines : secondStart.track.initial.box.Refines owner.track.initial.box := by
    unfold secondStart
    rewrite [castOwnerParameter_initial_box]
    exact firstRefines
  have firstAtRefines : firstAt.track.initial.box.Refines edge.cached.preparedOwner.track.initial.box := by
    unfold firstAt
    rewrite [castOwnerParameter_initial_box]
    exact actualRefines
  have secondAtRefines : secondAt.track.initial.box.Refines owner.track.initial.box := by
    unfold secondAt
    rewrite [castOwnerParameter_initial_box]
    exact referenceRefines
  let compared := retained.path.retainedEquivalentAt time inside firstStart secondStart firstStartRefines
    secondStartRefines initial firstAt secondAt firstAtRefines secondAtRefines
  exact NamedEquivalent.transport
    (SquareRootTrackEquivalence.ownerRootName_castOwnerParameter (retained.point_eq time).symm actual)
    (SquareRootTrackEquivalence.ownerRootName_castOwnerParameter (retained.point_eq time).symm reference) compared

/-- Compare the actual original edge-query name with an independent same-point reference using its retained query cache.

The query's original reserved-transport refinement is derived internally,
including its recentered branch. The same reference and start comparison
are consumed by retainedAtEquivalent; exact query-name readback attaches
that derived result to the original evaluator without replacing a reading.
-/
def queryEquivalent {time : Rational} {inside : Inside time} (query : PreparedEdge.Query edge time inside)
    (firstReference : Owner (curve.polynomial.eval (edge.segment.pointAt edge.left.parameter)))
    (firstRefines : firstReference.track.initial.box.Refines owner.track.initial.box)
    (start : NamedEquivalent (ownerRootName edge.cached.preparedOwner.parameterNonzero edge.cached.preparedOwner)
      (ownerRootName firstReference.parameterNonzero firstReference))
    (reference : Owner (curve.polynomial.eval (edge.point time)))
    (referenceRefines : reference.track.initial.box.Refines owner.track.initial.box) :
    NamedEquivalent (edge.rootName time inside) (ownerRootName reference.parameterNonzero reference) :=
  NamedEquivalent.transport query.name_eq.symm rfl
    (retained.retainedAtEquivalent time inside firstReference firstRefines start query.owner reference
      query.refines referenceRefines)

end Purelib.Riemann.Integration.PreparedConstantModels.PreparedEdge.RootPath

end
