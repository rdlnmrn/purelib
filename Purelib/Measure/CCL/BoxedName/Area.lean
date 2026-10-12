module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Rational.Budget.Square
public import Purelib.Approximation.Bound.Operational
import Purelib.Approximation.Bound.Process
public import Purelib.Approximation.Box.Content
public import Purelib.Data.CCL.Name.Boxed.Process
import Purelib.Data.CCL.Name.Boxed.Refinement
import Purelib.Geometry.Rational.Box.Content
public import Purelib.Measure.Box.Cover
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.CCL.Name.Boxed.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Box.Basic
import Mathlib.Order.Basic

open Purelib.Measure.Box.Cover (BoxCover)

section
@[expose] public section

/-!
# Finite measure observations of boxed CCL names

This module turns each boxed CCL certificate into a generic finite
observation and supplies arbitrarily small rational-area observations of a
progressive site.  The possible predicate is deliberately allowed to refine:
no intersection of all cylinders and no completed point is asserted.
-/

namespace Purelib.Measure.CCL.BoxedName

namespace ProgressiveName

open Purelib.Approximation.Rational in
open Purelib.Data.CCL.Name in
open Purelib.Data.Rat in
/-- Request the exact progressive boxed name at the radius computed from the positive target area.

The returned certificate comes from the original supplied state and retains the name's own refinement and realization
data. -/
def areaCertificate (name : Boxed.Process.ProgressiveName) (state :
  name.State)
    (target : Fraction.Rational) (positive : 0 < target) : Boxed.Basic.Certificate :=
  name.certificate
    (name.request state (Budget.Square.radius target) (Budget.Square.radius_pos positive))

open Purelib.Approximation.Rational in
open Purelib.Data.CCL.Name in
open Purelib.Data.Rat in
open Purelib.Measure in
/-- The requested area certificate refines the exact certificate of the original supplied state. -/
theorem areaCertificate_refines (name :
  Boxed.Process.ProgressiveName)
    (state : name.State) (target : Fraction.Rational) (positive : 0 < target) :
    Boxed.Refinement.Refines ((areaCertificate name) state target positive)
      (name.certificate state) :=
  name.request_refines state (Budget.Square.radius target) (Budget.Square.radius_pos
    positive)

open Purelib.Data.CCL.Name in
open Purelib.Data.Rat in
open Purelib.Measure in
/-- The singleton cover of the requested certificate's box covers every point possible for that same certificate. -/
theorem areaCertificate_cover (name :
  Boxed.Process.ProgressiveName)
    (state : name.State) (target : Fraction.Rational) (positive : 0 < target) :
    (BoxCover.mk
      [((areaCertificate name) state target positive).box]).Covers
      ((areaCertificate name) state target positive).Possible := by
  intro point possible
  exact ⟨((areaCertificate name) state target positive).box,
    List.mem_cons_self,
    ((areaCertificate name) state target positive).possible_inside possible⟩

open Purelib.Approximation.Rational in
open Purelib.Data.CCL.Name in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Measure in
/-- The exact requested area certificate's box has rectangular content strictly below the supplied positive target. -/
theorem areaCertificate_content_lt (name :
  Boxed.Process.ProgressiveName)
    (state : name.State) (target : Fraction.Rational) (positive : 0 < target) :
    Box.Content.boxContent
      ((areaCertificate name) state target positive).box < target := by
  apply Box.Content.boxContent_lt_of_diagonalSq_lt
  exact (name.accurate state (Budget.Square.radius target)
    (Budget.Square.radius_pos positive)).trans_lt (Budget.Square.radius_sq_lt positive)

open Purelib.Data.CCL.Name in
open Purelib.Data.Rat in
open Purelib.Measure in
/-- The singleton cover of the exact requested certificate has content below the positive target. -/
theorem areaCover_content_lt (name : Boxed.Process.ProgressiveName)
    (state : name.State) (target : Fraction.Rational) (positive : 0 < target) :
    BoxCover.content
      (BoxCover.mk
        [((areaCertificate name) state target positive).box]) <
      target := by
  simpa only [BoxCover.content, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero] using
      (areaCertificate_content_lt name) state target positive

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Data.CCL.Name in
open Purelib.Measure in
/-- Read the original boxed-name states as an area-bound process, translating each area request to its certified radius
request.

The original state type, initial state and certificate boxes remain unchanged, and each resulting content interval
refines the preceding one. -/
def toAreaProcess (name : Boxed.Process.ProgressiveName) :
    Approximation.BoundProcess where
  State := name.State
  bound state := Approximation.Box.Content.boxContentBound
    (name.certificate state).box
  initial := name.initial
  request state target positive :=
    name.request state (Budget.Square.radius target) (Budget.Square.radius_pos positive)
  request_refines state target positive := by
    apply Approximation.Box.Content.boxContentBound_refines
    exact (name.request_refines state (Budget.Square.radius target)
      (Budget.Square.radius_pos positive)).box
  accurate state target positive := by
    rw [Approximation.Box.Content.boxContentBound_width]
    exact (areaCertificate_content_lt name) state target positive
  refinesInitial state := by
    apply Approximation.Box.Content.boxContentBound_refines
    exact (name.refinesInitial state).box

open Purelib.Data.CCL.Name in
open Purelib.Geometry.Rational in
open Purelib.Measure in
/-- Every interval of the exact area process contains zero. -/
theorem toAreaProcess_anchored (name :
  Boxed.Process.ProgressiveName) :
    (toAreaProcess name).AnchoredAt 0 := by
  intro state
  exact ⟨le_rfl,
    Box.Content.boxContent_nonneg (name.certificate state).box⟩

open Purelib in
open Purelib.Data.CCL.Name in
open Purelib.Measure in
/-- The original boxed name's area process is operationally equivalent to the exact-zero bound process. -/
theorem toAreaProcess_operationallyEquivalent_zero (name :
  Boxed.Process.ProgressiveName) :
    Approximation.OperationallyEquivalent (toAreaProcess name)
      (Approximation.BoundProcess.exact 0) :=
  Approximation.operationallyEquivalent_exact_of_anchoredAt
    (toAreaProcess name) 0 (toAreaProcess_anchored name)

end ProgressiveName
end Purelib.Measure.CCL.BoxedName

end
