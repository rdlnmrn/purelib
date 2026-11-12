module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
public import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConjugateRibbon
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConjugateRibbon

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon

open Purelib.Data.List

open Purelib.Integration.Path

open Purelib.Riemann.Periods

@[expose] public section

/-! Complete common-cover conjugate ribbon bounds on the existing cached
source and reciprocal-cap models. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConjugateRibbonFamily
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive CellPrimitive)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover (CommonInterval CommonCover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples (Data Sample)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SheetAlignment (RegularAlignment)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon (PairedRibbonRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbon (evaluateCommon)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest (Entry Evaluation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon.RegularAlignment (pairedSourceValues
  pairedCapValues)
variable {genus count otherCount : Nat} {curve : HyperellipticCurve genus}
  {differential other : Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : CenteredEdge curve differential} {patch :
    PreparedPatch parent}
  {otherPatch : PreparedPatch
    (recastCenteredEdge other parent)}
  {data : UniformReciprocalModels.Data patch count} {otherData :
    UniformReciprocalModels.Data otherPatch otherCount}
  {firstCover : Cover data} {secondCover :
    Cover otherData}
  {regular : RegularBounds.Data cap}

namespace CommonRibbonRequest
variable {common : CommonCover firstCover
  secondCover} {target : Coordinate} {minimum : Nat}

variable {stage depth : Nat} {box otherBox : Geometry.Rational.Box}
  {sample : Cap.Primitives.Sample cap differential stage box}
  {otherSample : Cap.Primitives.Sample cap other stage otherBox}
  {source : SourcePrimitive data stage}
    {otherSource : SourcePrimitive otherData
    stage}
  {request : CommonRibbonRequest regular common
    target minimum}

/-- The conjugate ribbon uses the already retained source polynomials and signed cap alignments. Its endpoint correction
is part of the expression. -/
def Entry.conjugateRemainder (entry : Entry request sample otherSample source otherSource depth) :
  Gaussian :=
  DyadicBilinearBoundaryRibbon.dyadicDifference
    (fun parameter => ConjugateIncrementComparison.conjugateFirst
      (RegularAlignment.pairedSourceValues (edge := entry.plan.interval.first.owner)
        (otherEdge := entry.plan.interval.second.owner) source otherSource parameter))
    (fun parameter => ConjugateIncrementComparison.conjugateFirst
      (RegularAlignment.pairedCapValues entry.left entry.right parameter))
    depth entry.plan.interval.edge.left.parameter entry.plan.interval.edge.right.parameter

/-- The original retained conjugate ribbon remainder satisfies its paid per-interval allowance. -/
theorem Entry.conjugate_accurate (entry : Entry request sample otherSample source otherSource depth)
  :
    normSq
      (Entry.conjugateRemainder
      entry) < request.allowance :=
  PairedRibbonRequest.conjugate_accurate_at entry.plan.request source otherSource entry.left entry.right
    entry.evaluated.later entry.evaluated.leftLower entry.evaluated.leftUpper
    entry.evaluated.rightLower entry.evaluated.rightUpper entry.evaluated.ordered depth

/-- The original retained conjugate ribbon remainder satisfies its paid per-interval allowance. -/
theorem Evaluation.conjugate_accurate
    (evaluated : Evaluation request sample otherSample source otherSource depth) :
    normSq (gaussianSum (evaluated.entries.map
      Entry.conjugateRemainder)) <
      target := by
  have bound := Data.Gaussian.Norm.Sum.Bounds.normSq_sum_le
    (evaluated.entries.map
      Entry.conjugateRemainder)
      request.allowance (by
      intro value member
      obtain ⟨entry, _, rfl⟩ := Map.mem_map.mp member
      exact
        (Entry.conjugate_accurate
        entry).le)
  have length : evaluated.entries.length = request.count := by
    have first := congrArg List.length evaluated.plans_eq
    have second := congrArg List.length request.intervals_eq
    rw [Map.length_map] at first second
    exact (first.trans second).trans request.count_eq.symm
  rw [Map.length_map, length] at bound
  exact bound.trans_lt request.paid

end CommonRibbonRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConjugateRibbonFamily
