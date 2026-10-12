module
import Purelib.Topology.Surface.Sewing.SewnFaceAreaComparison
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Polygon.Stokes
import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction

import Purelib.Integration.Path.AreaComparison
import Purelib.Tactic.Ring

@[expose] public section

namespace Purelib.Examples.Topology.Surface.Sewing.ComposedArea

open Purelib.Data.Gaussian.Basic (Canonical conj)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Norm.Basic (normSq normSq_eq_canonical)
open Purelib.Integration

/-! The unit imaginary coefficient is a small exact fixture. Its contribution
is normSq coefficient = 1, giving the original factor four. This numerical
law is used by mixed source/chart realizations only with their retained signed
chart witnesses and two actual reading parents. It does not replace those
geometric premises. -/
/-- Conjugate-plus-imaginary mixed errors each bounded by one allowance give squared norm at most four allowances. -/
example (left right : Canonical) {allowance : Rational}
    (leftBound : normSq left ≤ allowance) (rightBound :
      normSq right ≤ allowance) :
    normSq (conj left + (⟨0, 1⟩ :
      Canonical) * right) ≤ 4 * allowance := by
  have estimate := Path.AreaComparison.mixed_error
    left right (⟨0, 1⟩ : Canonical)
      (by simpa only [normSq_eq_canonical] using leftBound)
      (by simpa only [normSq_eq_canonical] using rightBound)
  rw [← normSq_eq_canonical, ← normSq_eq_canonical] at estimate
  rw [show normSq (⟨0, 1⟩ : Canonical) = 1 by
    decide] at estimate
  exact estimate.trans_eq (by ring1)

/-! The two source areas occur identically in the outward chart comparison,
opposite-sheet comparison and return chart comparison. Three paid tenth
budgets compose to one target by the original scalar law. Geometry supplies
the three premises; this step neither rebuilds a polygon nor selects a stage. -/
/-- Three retained outward, seam and return bounds at one tenth of the target compose to the full chart comparison
bound. -/
example (chart source opposite otherChart : Canonical) (target :
  Rational)
    (outward : normSq (source - chart) ≤ target / 10)
    (seam : normSq (source - opposite) ≤ target / 10)
    (returning : normSq (opposite - otherChart) ≤ target / 10) :
    normSq (chart - otherChart) ≤ target := by
  rw [normSq_eq_canonical]
  exact (Path.AreaComparison.stem_chain chart source opposite otherChart
    (by simpa only [normSq_eq_canonical] using outward)
    (by simpa only [normSq_eq_canonical] using seam)
    (by simpa only [normSq_eq_canonical] using returning)).trans_eq
    (Path.AreaComparison.stem_tenth_payment target)

section Faces

open Purelib.Topology.Polygon
open Purelib.Topology.Surface.Sewing
open Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces

/-- Sew the original primitive values once, retain selected local areas and pay their actual discrepancy.

Selection preserves the ordered original face traces. The local area reads those same traces and the sewing request
allocates its original magnitude and face-count allowance without rebuilding the surface. -/
example {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
    {localValues : Fin faceCount → PrimitiveSewing.PrimitiveValues 3} {patch : SewingTree.SewnPatch faces}
    (keep : Fin faceCount → Bool)
    (magnitude target : Rational) (nonnegative : 0 ≤ magnitude) (positive : 0 < target)
    (bounded : ∀ source index, normSq (localValues source index - localValues source 0) ≤ magnitude)
    (locallyAccurate : SewnPrimitiveRequests.LocalAccuracy
      (SewnFaceAreaComparison.FaceAreaRequest.build patch.assembly magnitude target nonnegative
        positive).sewing.tolerance
      (SewnPrimitiveSamples.CachedSample.build patch localValues).sewn.readings) :
    let sample := SewnPrimitiveSamples.CachedSample.build patch localValues
    let request := SewnFaceAreaComparison.FaceAreaRequest.build patch.assembly magnitude target nonnegative positive
    let selected := CachedSample.FaceSelection.build sample keep
    let localArea := CachedSample.FaceSelection.LocalArea.build selected
    0 < request.error ∧ normSq (selected.area - localArea.value) < target := by
  let sample := SewnPrimitiveSamples.CachedSample.build patch localValues
  let request := SewnFaceAreaComparison.FaceAreaRequest.build patch.assembly magnitude target nonnegative positive
  let selected := CachedSample.FaceSelection.build sample keep
  let localArea := CachedSample.FaceSelection.LocalArea.build selected
  exact ⟨request.sewing.target_positive, request.accurate sample selected localArea bounded locallyAccurate⟩

end Faces

end Purelib.Examples.Topology.Surface.Sewing.ComposedArea
