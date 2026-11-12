module

public import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
public import Purelib.Riemann.Integration.PreparedConstantModels.Query
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.CheckedPrimitiveNeighborhoods
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

/-! # Uniform patch agreement consuming an already retained direct-edge query

The original direct Query is an input with its actual Owner, complete factory
identity, name and initial-box refinement. The original patch's common seed
bridge constructs the signed sample comparison without another direct-query
transport, source preparation or point acquisition.
-/

public section

namespace Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Branches
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods (Bounds)
open Purelib.Riemann.Integration.CheckedPrimitiveNeighborhoods (grow grow_base)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
    {parent : CenteredEdge curve differential}

/-- Derive signed patch-sample agreement using the SAME already retained direct-query Owner.

The original Query supplies its complete name readback and source-box
refinement, including the reserved recentering branch. The original edge
movement payment and patch seed bridge derive the comparison. Exact point
transport retains the supplied sample; no direct Query is executed here.
-/
def retainedQueryEquivalent (patch : PreparedPatch parent) (count : Nat)
    (fraction : Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1)
    (query : PreparedEdge.Query parent.edge fraction inside) {point : Canonical}
    (point_eq : parent.edge.point fraction = point)
    (pointInside : (patch.neighborhood count).box.Contains point)
    (sample : ContinuedNeighborhood.Point (patch.neighborhood count) point) :
    NamedEquivalent (parent.edge.rootName fraction inside) sample.certificate.value.name := by
  subst point
  have small : Canonical.normSq
      (curve.polynomial.eval (parent.edge.segment.pointAt parent.edge.left.parameter) -
        curve.polynomial.eval (parent.edge.point fraction)) <
        parent.edge.cached.preparedOwner.track.initial.clearance.bound := by
    rewrite [← parent.edge.directQueryParameter_eq fraction, parent.edge.cached.preparedOwner_eq]
    exact Eq.mp (congrArg (fun bound => bound <
      (PreparedSheetContinuation.prepared parent.edge.segment parent.edge.left parent.edge.owner
        parent.edge.request).track.initial.clearance.bound)
      (Norm.Basic.normSq_eq_canonical _))
      (PreparedSheetContinuation.pointNormSmall parent.edge.segment parent.edge.within parent.edge.left
        parent.edge.owner parent.edge.request parent.edge.ordered parent.edge.small fraction inside)
  have sampleRefines := sample.refines
  change sample.owner.track.initial.box.Refines
    (grow (patch.seed.neighborhood count)).base.seed.owner.track.initial.box at sampleRefines
  rewrite [grow_base] at sampleRefines
  have movement := (patch.neighborhood count).parameter_movement pointInside
  change Canonical.normSq (curve.polynomial.eval (grow (patch.seed.neighborhood count)).base.site.center - _) <
    (grow (patch.seed.neighborhood count)).base.seed.owner.track.initial.clearance.bound at movement
  rewrite [grow_base] at movement
  let compared := Bounds.PreparedSeed.ownerEquivalent patch.seed query.owner query.refines small
    sample.owner sampleRefines movement
  exact NamedEquivalent.transport query.name_eq.symm rfl compared

end Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch

end
