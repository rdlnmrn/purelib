module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter.Shifted
public import Purelib.Curves.Legendre.Paths.Frame.Clearance
import Purelib.Curves.Legendre.PicardFuchs.Clearance.Increment

/-! # One regular shifted-parameter allocation for the retained covered family

The same cached finite patch bound is tightened by the original frame's
two singular-value distances. This one positive scalar continues every
original query, pays changed-polynomial clearance on every identical box,
and constructs a genuine regular frame at the same shifted parameter.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ParameterRange

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.PicardFuchs.Clearance (ParameterClearance)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {count : Nat} {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count parents} (ranges : ParameterRange covered)

/-- Tighten the actual cached whole-cover bound by the identical source frame's positive singular-value allocation. -/
@[expose] def regularBound : Rational :=
  min ranges.shiftedBound (ParameterClearance.ofFrame frame).incrementBound

/-- The whole-cover regular allocation is strictly positive and independent of every source/query stage. -/
theorem regularBound_positive : 0 < ranges.regularBound :=
  Order.Basic.lt_min ranges.shiftedBound_positive (ParameterClearance.ofFrame frame).incrementBound_positive

/-- The regular allocation pays all retained shifted box clearances and original query/endpoint continuations. -/
theorem regularBound_le_shiftedBound : ranges.regularBound ≤ ranges.shiftedBound := Order.Basic.min_le_left _ _

/-- The same allocation pays the two actual parameter distances supplied by the original source frame. -/
theorem regularBound_le_parameterBound :
    ranges.regularBound ≤ (ParameterClearance.ofFrame frame).incrementBound := Order.Basic.min_le_right _ _

/-- Derive positive zero/one clearance for the actual shifted parameter from the common retained finite allocation. -/
def targetClearance (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ ranges.regularBound) :
    ParameterClearance (parameter + increment) :=
  (ParameterClearance.ofFrame frame).shifted increment (admitted.trans ranges.regularBound_le_parameterBound)

/-- The whole derived target-clearance certificate uses the exact original frame and admitted common allocation. -/
theorem targetClearance_eq (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ ranges.regularBound) :
    ranges.targetClearance increment admitted = (ParameterClearance.ofFrame frame).shifted increment
      (admitted.trans ranges.regularBound_le_parameterBound) := by
  rfl

/-- Construct the original regular target frame at the exact same increment admitted by every retained physical patch.

The original frame's distance allocation derives both exclusions. This
runs the existing target frame factory once; it does not replay any
source preparation or construct geometric continuation/period evidence.
-/
def targetFrame (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ ranges.regularBound) :
    Paths.Frame (parameter + increment) :=
  frame.ofIncrement increment (admitted.trans ranges.regularBound_le_parameterBound)

/-- The complete target frame consumes precisely the derived same-increment parameter-clearance certificate. -/
theorem targetFrame_eq (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ ranges.regularBound) :
    ranges.targetFrame increment admitted = Paths.Frame.ofClearance (ranges.targetClearance increment admitted) := by
  unfold targetFrame
  exact (frame.ofIncrement_eq increment (admitted.trans ranges.regularBound_le_parameterBound)).trans
    (congrArg (fun target : ParameterClearance (parameter + increment) => Paths.Frame.ofClearance target)
      (ranges.targetClearance_eq increment admitted).symm)

/-- Equal admitted increments give the same complete original target frame after exact parameter transport.

Both frames use this same original range and source frame. Only the
increment equality is eliminated; no frame, branch owner or source
factory is replayed, and proof-only admission data remain irrelevant.
-/
theorem targetFrame_castParameter {first last : Canonical}
    (firstAdmitted : Norm.Basic.normSq first ≤ ranges.regularBound)
    (lastAdmitted : Norm.Basic.normSq last ≤ ranges.regularBound) (equal : first = last) :
    (ranges.targetFrame first firstAdmitted).castParameter
      (congrArg (fun increment : Canonical => parameter + increment) equal) =
      ranges.targetFrame last lastAdmitted := by
  cases equal
  rfl

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ParameterRange

end
