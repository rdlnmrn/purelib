module

public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Robust.Homography
public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Robust.Run
import Purelib.Data.List.Map
public import Purelib.Data.List.Append
import Purelib.Data.List.Membership
import Purelib.Data.List.Pairwise
import Purelib.Data.Nat.Order
import Purelib.Geometry.Rational.Box.Refinement

/-!
# Unreserved finite histories of robust sharpness windows

Every segment retains its original run and numerical caches. A history keeps
their ordered window records and a proper box on which all their complete
consecutive-best and threshold-violation certificates hold. An extension
places additional windows beyond every earlier upper scale inside that box,
then retains a proper strict subbox and the exact earlier window prefix.
-/

public section

namespace Purelib.NumberTheory.Approximation.Dirichlet.Critical.Robust

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.NumberTheory.Approximation
open Purelib.NumberTheory.Approximation.Dirichlet.Critical

namespace WindowHistory

/-- A window retains its original requested-scale index and original bad-window record. -/
abbrev Entry (threshold : Fraction.Rational) := Σ requestedScale : Nat, Sharpness.BadWindow threshold requestedScale

set_option genInjectivity false in
/-- An original robust run or a placed robust run retained as one history segment.

Each constructor keeps the complete original nominal run, its requested
scale and count. Placed segments also keep their original outer box and all
matrix, window and clearance caches through the placed-run owner.
-/
inductive Segment (threshold : Fraction.Rational) (certificate : Sharpness.IsSharperWindowThreshold threshold) where
  /-- Retain an existing fully robust finite run as an original segment. -/
  | original (requestedScale count : Nat) (run : Run.FullyRobustRun threshold requestedScale count)
  /-- Retain a placed robust run with its actual original outer box. -/
  | placed (requestedScale count : Nat) (outer : Box)
      (run : PlacedRun threshold certificate requestedScale count outer)

namespace Segment

variable {threshold : Fraction.Rational} {certificate : Sharpness.IsSharperWindowThreshold threshold}

/-- Read the original requested scale of a retained segment. -/
@[expose] def requestedScale : Segment threshold certificate → Nat
  | .original requestedScale _ _ => requestedScale
  | .placed requestedScale _ _ _ => requestedScale

/-- Read the original window count of a retained segment. -/
@[expose] def count : Segment threshold certificate → Nat
  | .original _ count _ => count
  | .placed _ count _ _ => count

/-- Read the exact robust box of a retained segment. -/
@[expose] def box : Segment threshold certificate → Box
  | .original _ _ run => run.box
  | .placed _ _ _ run => run.box

/-- Read the original ordered window records without changing their requested-scale indices or sources. -/
@[expose] def entries : Segment threshold certificate → List (Entry threshold)
  | .original requestedScale _ run => run.exact.windows.map (fun window => ⟨requestedScale, window.1⟩)
  | .placed requestedScale _ _ run => run.placement.run.windows.map (fun window => ⟨requestedScale, window.1⟩)

/-- The retained entry list has exactly the segment's original requested count. -/
theorem entries_length (segment : Segment threshold certificate) : segment.entries.length = segment.count := by
  cases segment with
  | original requestedScale count run =>
      exact (List.Map.length_map _ run.exact.windows).trans run.exact.length_eq
  | placed requestedScale count outer run =>
      exact (List.Map.length_map _ run.placement.run.windows).trans run.placement.run.length_eq

/-- The segment's original strict upper-denominator order is retained by its entry list. -/
theorem scalesStrict (segment : Segment threshold certificate) : segment.entries.Pairwise fun first second =>
    Best.Error.denominatorQuadrance first.2.upper < Best.Error.denominatorQuadrance second.2.upper := by
  cases segment with
  | original requestedScale count run =>
      exact List.Pairwise.pairwise_map.mpr run.exact.scalesStrict
  | placed requestedScale count outer run =>
      exact List.Pairwise.pairwise_map.mpr run.placement.run.scalesStrict

/-- Every original entry lies strictly beyond the segment's retained requested scale. -/
theorem beyondScale (segment : Segment threshold certificate) (entry : Entry threshold)
    (member : entry ∈ segment.entries) : segment.requestedScale < Best.Error.denominatorQuadrance entry.2.upper := by
  cases segment with
  | original requestedScale count run =>
      rcases List.Map.mem_map.mp member with ⟨window, _, equal⟩
      rewrite [← equal]
      exact window.1.beyondScale
  | placed requestedScale count outer run =>
      rcases List.Map.mem_map.mp member with ⟨window, _, equal⟩
      rewrite [← equal]
      exact window.1.beyondScale

/-- Every segment entry has its complete consecutive-best certificate throughout the original segment box. -/
theorem uniformConsecutive (segment : Segment threshold certificate) (sample : Gaussian.Basic.Canonical)
    (inside : segment.box.Contains sample) (entry : Entry threshold) (member : entry ∈ segment.entries) :
    Best.Consecutive.Basic.AreConsecutiveBest sample entry.2.lower entry.2.upper := by
  cases segment with
  | original requestedScale count run =>
      rcases List.Map.mem_map.mp member with ⟨window, windowMember, equal⟩
      rewrite [← equal]
      exact run.uniformConsecutive sample inside window windowMember
  | placed requestedScale count outer run =>
      rcases List.Map.mem_map.mp member with ⟨window, windowMember, equal⟩
      rewrite [← equal]
      exact run.uniformConsecutive sample inside window windowMember

/-- Every segment entry keeps its strict threshold violation throughout the original segment box. -/
theorem uniformViolation (segment : Segment threshold certificate) (sample : Gaussian.Basic.Canonical)
    (inside : segment.box.Contains sample) (entry : Entry threshold) (member : entry ∈ segment.entries) :
    1 < threshold * Dirichlet.Window.SourceBound.dirichletWindowQuadrance sample entry.2.lower entry.2.upper := by
  cases segment with
  | original requestedScale count run =>
      rcases List.Map.mem_map.mp member with ⟨window, windowMember, equal⟩
      rewrite [← equal]
      exact run.uniformViolation sample inside window windowMember
  | placed requestedScale count outer run =>
      rcases List.Map.mem_map.mp member with ⟨window, windowMember, equal⟩
      rewrite [← equal]
      exact run.uniformWindowViolation sample inside window windowMember

end Segment

/-- Concatenate the original entry lists of an ordered finite segment history. -/
@[expose] def entriesOfSegments {threshold : Fraction.Rational}
    {certificate : Sharpness.IsSharperWindowThreshold threshold} :
    List (Segment threshold certificate) → List (Entry threshold)
  | [] => []
  | segment :: remaining => segment.entries ++ entriesOfSegments remaining

/-- Concatenating histories preserves the exact ordered entry lists of both original inputs. -/
theorem entriesOfSegments_append {threshold : Fraction.Rational}
    {certificate : Sharpness.IsSharperWindowThreshold threshold}
    (left right : List (Segment threshold certificate)) :
    entriesOfSegments (left ++ right) = entriesOfSegments left ++ entriesOfSegments right := by
  induction left with
  | nil => rfl
  | cons segment remaining inductionHypothesis =>
      change segment.entries ++ entriesOfSegments (remaining ++ right) =
        (segment.entries ++ entriesOfSegments remaining) ++ entriesOfSegments right
      rewrite [inductionHypothesis]
      exact (List.Append.append_assoc _ _ _).symm

/-- Compute the largest actual upper-denominator quadrance in an ordered window list, with zero for an empty list. -/
@[expose] def maximumUpperQuadrance {threshold : Fraction.Rational} : List (Entry threshold) → Nat
  | [] => 0
  | entry :: remaining => Nat.max (Best.Error.denominatorQuadrance entry.2.upper) (maximumUpperQuadrance remaining)

/-- Every original window occurrence is bounded by the computed largest upper-denominator quadrance. -/
theorem upperQuadrance_le_maximum_of_mem {threshold : Fraction.Rational}
    (entries : List (Entry threshold)) (entry : Entry threshold) (member : entry ∈ entries) :
    Best.Error.denominatorQuadrance entry.2.upper ≤ maximumUpperQuadrance entries := by
  induction entries with
  | nil => cases member
  | cons head tail inductionHypothesis =>
      cases member with
      | head => exact Nat.Order.le_max_left _ _
      | tail _ tailMember =>
          exact (inductionHypothesis tailMember).trans (Nat.Order.le_max_right _ _)

end WindowHistory

set_option genInjectivity false in
/-- Retain an ordered finite window history and one proper box preserving all its complete certificates.

The segments retain the actual original runs and their numerical caches.
The entry list keeps every original window and scale index in order. Its
strict scale order and both uniform laws concern this same retained list
and the same current rational box.
-/
structure WindowHistory (threshold : Fraction.Rational)
    (certificate : Sharpness.IsSharperWindowThreshold threshold) where
  /-- The original chronological run segments and their retained caches. -/ segments :
    List (WindowHistory.Segment threshold certificate)
  /-- The cached complete ordered list of original indexed window records. -/ windows :
    List (WindowHistory.Entry threshold)
  /-- The window cache is exactly the original segment concatenation. -/ windowsSpec :
    windows = WindowHistory.entriesOfSegments segments
  /-- The current common robust box. -/ box : Box
  /-- The current box has positive width and height. -/ proper : box.Proper
  /-- Actual upper-denominator quadrances increase strictly across the entire retained list. -/ scalesStrict :
    windows.Pairwise fun first second =>
      Best.Error.denominatorQuadrance first.2.upper < Best.Error.denominatorQuadrance second.2.upper
  /-- Every actual earlier window remains completely consecutive best throughout the current box. -/
  uniformConsecutive : ∀ sample : Gaussian.Basic.Canonical, box.Contains sample →
    ∀ entry ∈ windows, Best.Consecutive.Basic.AreConsecutiveBest sample entry.2.lower entry.2.upper
  /-- Every actual earlier window keeps its strict threshold violation throughout the current box. -/
  uniformViolation : ∀ sample : Gaussian.Basic.Canonical, box.Contains sample →
    ∀ entry ∈ windows, 1 < threshold *
      Dirichlet.Window.SourceBound.dirichletWindowQuadrance sample entry.2.lower entry.2.upper

namespace WindowHistory

variable {threshold : Fraction.Rational} {certificate : Sharpness.IsSharperWindowThreshold threshold}

/-- Start an empty robust window history inside one retained proper box. -/
def ofBox (certificate : Sharpness.IsSharperWindowThreshold threshold) (box : Box) (proper : box.Proper) :
    WindowHistory threshold certificate where
  segments := []
  windows := []
  windowsSpec := rfl
  box := box
  proper := proper
  scalesStrict := List.Pairwise.nil
  uniformConsecutive := by intro sample inside entry member; cases member
  uniformViolation := by intro sample inside entry member; cases member

/-- Start a history with an existing fully robust run, retaining its exact original owner and window records. -/
@[expose] def ofRobustRun (certificate : Sharpness.IsSharperWindowThreshold threshold) {requestedScale count : Nat}
    (run : Run.FullyRobustRun threshold requestedScale count) : WindowHistory threshold certificate := by
  let segment : Segment threshold certificate := Segment.original requestedScale count run
  exact
    { segments := [segment]
      windows := segment.entries
      windowsSpec := (List.Append.append_nil _).symm
      box := run.box
      proper := run.proper
      scalesStrict := segment.scalesStrict
      uniformConsecutive := segment.uniformConsecutive
      uniformViolation := segment.uniformViolation }

/-- The initial history retains the exact original fully robust run as its sole segment. -/
theorem ofRobustRun_segments (certificate : Sharpness.IsSharperWindowThreshold threshold) {requestedScale count : Nat}
    (run : Run.FullyRobustRun threshold requestedScale count) :
    (ofRobustRun certificate run).segments = [Segment.original requestedScale count run] := rfl

/-- The initial history retains the exact original run's indexed window entries. -/
theorem ofRobustRun_windows (certificate : Sharpness.IsSharperWindowThreshold threshold) {requestedScale count : Nat}
    (run : Run.FullyRobustRun threshold requestedScale count) :
    (ofRobustRun certificate run).windows =
      (Segment.original (certificate := certificate) requestedScale count run).entries := rfl

/-- The initial history retains the same actual proper box as its original fully robust run. -/
theorem ofRobustRun_box (certificate : Sharpness.IsSharperWindowThreshold threshold) {requestedScale count : Nat}
    (run : Run.FullyRobustRun threshold requestedScale count) : (ofRobustRun certificate run).box = run.box := rfl

/-- The initial history has exactly the original run's requested window count. -/
theorem ofRobustRun_length (certificate : Sharpness.IsSharperWindowThreshold threshold) {requestedScale count : Nat}
    (run : Run.FullyRobustRun threshold requestedScale count) : (ofRobustRun certificate run).windows.length = count :=
  (Segment.original (certificate := certificate) requestedScale count run).entries_length

set_option genInjectivity false in
/-- Retain a proper-box refinement of one original window history without changing any segment or window cache.

The original history and exact child box index the refinement. Its result
keeps all original run owners, window records and strict scale certificates;
both complete uniform window laws are transported to that same child box.
-/
structure Refinement (previous : WindowHistory threshold certificate) (inner : Box) where
  /-- The actual refined robust history. -/ next : WindowHistory threshold certificate
  /-- All original nominal run owners and numerical caches are retained. -/ segmentsEq :
    next.segments = previous.segments
  /-- All actual original indexed window records are retained in their original order. -/ windowsEq :
    next.windows = previous.windows
  /-- The result uses exactly the supplied child box. -/ boxEq : next.box = inner
  /-- The same child box refines the original retained robust box. -/ refines : inner.Refines previous.box

/-- Refine the robust history to an exact proper child box, reusing all original segments, windows and scale data.

The builder copies references to the actual retained caches. Only the
current box and its containment transports change; no homography, clearance,
window or encoding is recomputed.
-/
def refine (previous : WindowHistory threshold certificate) (inner : Box) (proper : inner.Proper)
    (refines : inner.Refines previous.box) : Refinement previous inner := by
  let next : WindowHistory threshold certificate :=
    { segments := previous.segments
      windows := previous.windows
      windowsSpec := previous.windowsSpec
      box := inner
      proper := proper
      scalesStrict := previous.scalesStrict
      uniformConsecutive := fun sample inside entry member =>
        previous.uniformConsecutive sample (refines.contains inside) entry member
      uniformViolation := fun sample inside entry member =>
        previous.uniformViolation sample (refines.contains inside) entry member }
  exact ⟨next, rfl, rfl, rfl, refines⟩

namespace Refinement

/-- Every original window occurrence remains in the exact refined history. -/
theorem earlier_mem {previous : WindowHistory threshold certificate} {inner : Box}
    (refinement : Refinement previous inner) (entry : Entry threshold) (member : entry ∈ previous.windows) :
    entry ∈ refinement.next.windows := refinement.windowsEq.symm ▸ member

/-- Every earlier complete consecutive-best certificate holds throughout the actual refined box. -/
theorem earlierConsecutive {previous : WindowHistory threshold certificate} {inner : Box}
    (refinement : Refinement previous inner) (sample : Gaussian.Basic.Canonical)
    (inside : refinement.next.box.Contains sample) (entry : Entry threshold) (member : entry ∈ previous.windows) :
    Best.Consecutive.Basic.AreConsecutiveBest sample entry.2.lower entry.2.upper :=
  previous.uniformConsecutive sample (refinement.refines.contains (refinement.boxEq ▸ inside)) entry member

/-- Every earlier strict threshold violation holds throughout the actual refined box. -/
theorem earlierViolation {previous : WindowHistory threshold certificate} {inner : Box}
    (refinement : Refinement previous inner) (sample : Gaussian.Basic.Canonical)
    (inside : refinement.next.box.Contains sample) (entry : Entry threshold) (member : entry ∈ previous.windows) :
    1 < threshold * Dirichlet.Window.SourceBound.dirichletWindowQuadrance sample entry.2.lower entry.2.upper :=
  previous.uniformViolation sample (refinement.refines.contains (refinement.boxEq ▸ inside)) entry member

end Refinement

/-- Pay a new scale request and every earlier actual upper-denominator scale with one explicit natural maximum. -/
@[expose] def extensionScale (previous : WindowHistory threshold certificate) (requestedScale : Nat) : Nat :=
  Nat.max requestedScale (maximumUpperQuadrance previous.windows)

set_option genInjectivity false in
/-- Retain one requested finite extension together with its exact previous history and nested robust result.

The additional segment's matrix pays the requested scale and every earlier
upper scale. The resulting history keeps the original segment and window
prefixes literally, adds exactly the requested number of windows, and
retains a proper strict subbox of the previous robust box.
-/
structure Extension (previous : WindowHistory threshold certificate) (requestedScale additionalCount : Nat) where
  /-- The new placed segment and all its actual numerical caches. -/ addition :
    PlacedRun threshold certificate (previous.extensionScale requestedScale) additionalCount previous.box
  /-- The complete retained extended history. -/ next : WindowHistory threshold certificate
  /-- Every original segment is retained before the new placed segment. -/ segmentsEq :
    next.segments = previous.segments ++
      [Segment.placed (previous.extensionScale requestedScale) additionalCount previous.box addition]
  /-- Every original window record is retained before the new placed windows. -/ windowsEq :
    next.windows = previous.windows ++
      (Segment.placed (previous.extensionScale requestedScale) additionalCount previous.box addition).entries
  /-- The resulting history retains the actual newly computed robust box. -/ boxEq : next.box = addition.box
  /-- The number of newly added windows equals the original finite increment request. -/ countEq :
    next.windows.length = previous.windows.length + additionalCount
  /-- The resulting proper box lies strictly inside the previous retained box. -/ nested :
    next.box.StrictInterior previous.box

/-- Extend a retained robust history by every requested finite increment without a fixed reserve endpoint.

The constructor uses one new homographic placement inside the previous
proper box. Its scale payment dominates every previous upper quadrance.
The existing windows and segments are retained unchanged, and their full
uniform certificates are transported through the actual box refinement.
-/
def extend (previous : WindowHistory threshold certificate) (requestedScale additionalCount : Nat) :
    Extension previous requestedScale additionalCount := by
  let scale := previous.extensionScale requestedScale
  let addition := placedRobustRunInBox certificate scale additionalCount previous.box previous.proper
  let segment := Segment.placed scale additionalCount previous.box addition
  have refines : addition.box.Refines previous.box :=
    Box.Refinement.StrictInterior.refines addition.nested
  let next : WindowHistory threshold certificate :=
    { segments := previous.segments ++ [segment]
      windows := previous.windows ++ segment.entries
      windowsSpec := by
        rewrite [entriesOfSegments_append]
        change previous.windows ++ segment.entries = entriesOfSegments previous.segments ++ (segment.entries ++ [])
        rewrite [← previous.windowsSpec, List.Append.append_nil]
        rfl
      box := addition.box
      proper := addition.proper
      scalesStrict := by
        apply List.Pairwise.pairwise_append previous.scalesStrict segment.scalesStrict
        intro earlier earlierMember later laterMember
        exact ((upperQuadrance_le_maximum_of_mem previous.windows earlier earlierMember).trans
          (Nat.Order.le_max_right _ _)).trans_lt (segment.beyondScale later laterMember)
      uniformConsecutive := by
        intro sample inside entry member
        rcases List.Membership.mem_append.mp member with earlierMember | laterMember
        · exact previous.uniformConsecutive sample (refines.contains inside) entry earlierMember
        · exact segment.uniformConsecutive sample inside entry laterMember
      uniformViolation := by
        intro sample inside entry member
        rcases List.Membership.mem_append.mp member with earlierMember | laterMember
        · exact previous.uniformViolation sample (refines.contains inside) entry earlierMember
        · exact segment.uniformViolation sample inside entry laterMember }
  refine
    { addition := addition
      next := next
      segmentsEq := rfl
      windowsEq := rfl
      boxEq := rfl
      countEq := ?_
      nested := addition.nested }
  exact (List.Append.length_append _ _).trans (congrArg (Nat.add previous.windows.length) segment.entries_length)

namespace Extension

/-- Every original window occurrence remains in the exact extended window list. -/
theorem earlier_mem {previous : WindowHistory threshold certificate} {requestedScale additionalCount : Nat}
    (extension : Extension previous requestedScale additionalCount) (entry : Entry threshold)
    (member : entry ∈ previous.windows) : entry ∈ extension.next.windows := by
  rewrite [extension.windowsEq]
  exact List.Membership.mem_append.mpr (Or.inl member)

/-- The original complete consecutive-best certificate remains valid at every sample in the nested result box. -/
theorem earlierConsecutive {previous : WindowHistory threshold certificate} {requestedScale additionalCount : Nat}
    (extension : Extension previous requestedScale additionalCount) (sample : Gaussian.Basic.Canonical)
    (inside : extension.next.box.Contains sample) (entry : Entry threshold) (member : entry ∈ previous.windows) :
    Best.Consecutive.Basic.AreConsecutiveBest sample entry.2.lower entry.2.upper :=
  previous.uniformConsecutive sample
    ((Box.Refinement.StrictInterior.refines extension.nested).contains inside) entry member

/-- The original threshold-violation certificate remains valid at every sample in the nested result box. -/
theorem earlierViolation {previous : WindowHistory threshold certificate} {requestedScale additionalCount : Nat}
    (extension : Extension previous requestedScale additionalCount) (sample : Gaussian.Basic.Canonical)
    (inside : extension.next.box.Contains sample) (entry : Entry threshold) (member : entry ∈ previous.windows) :
    1 < threshold * Dirichlet.Window.SourceBound.dirichletWindowQuadrance sample entry.2.lower entry.2.upper :=
  previous.uniformViolation sample
    ((Box.Refinement.StrictInterior.refines extension.nested).contains inside) entry member

end Extension

set_option genInjectivity false in
/-- A finite history-extension request gives the new scale floor and number of additional windows. -/
structure Request where
  /-- The requested lower floor for the new upper-denominator scales. -/ requestedScale : Nat
  /-- The exact number of additional windows requested. -/ additionalCount : Nat

/-- Compute the exact total number of additional windows in the original finite request list. -/
@[expose] def requestedWindowCount : List Request → Nat
  | [] => 0
  | request :: remaining => request.additionalCount + requestedWindowCount remaining

set_option genInjectivity false in
/-- Retain a finite path of requested extensions from one exact original robust history.

The cached added windows and segments describe the exact suffixes of the
resulting history. Its count pays every original increment, its box refines
the original box, and a nonempty path gives strict interior containment.
-/
structure ExtensionPath (previous : WindowHistory threshold certificate) (requests : List Request) where
  /-- The actual final robust history with all original and newly computed caches. -/ result :
    WindowHistory threshold certificate
  /-- The actual ordered window suffix added along this path. -/ addedWindows : List (Entry threshold)
  /-- The result keeps the exact original window list before that suffix. -/ windowsEq :
    result.windows = previous.windows ++ addedWindows
  /-- The actual ordered segment suffix added along this path. -/ addedSegments : List (Segment threshold certificate)
  /-- The result keeps the exact original segment list before that suffix. -/ segmentsEq :
    result.segments = previous.segments ++ addedSegments
  /-- The final box refines the original robust box. -/ refines : result.box.Refines previous.box
  /-- The final count pays the complete original finite increment list. -/ countEq :
    result.windows.length = previous.windows.length + requestedWindowCount requests
  /-- Every nonempty requested path gives a proper strict subbox of the original retained box. -/ strictWhenNonempty :
    requests ≠ [] → result.box.StrictInterior previous.box

/-- Execute the original finite request list by structural recurrence through the actual retained histories.

Each step consumes the previous proper box and preserves its complete
window certificates. The resulting suffix receipts and refinement laws
compose through the actual intermediate results; no final reserve is fixed.
-/
def extendRequests (previous : WindowHistory threshold certificate) (requests : List Request) :
    ExtensionPath previous requests :=
  match requests with
  | [] =>
      { result := previous
        addedWindows := []
        windowsEq := (List.Append.append_nil _).symm
        addedSegments := []
        segmentsEq := (List.Append.append_nil _).symm
        refines := Box.refines_refl previous.box
        countEq := rfl
        strictWhenNonempty := fun impossible => (impossible rfl).elim }
  | request :: remaining => by
      let first := previous.extend request.requestedScale request.additionalCount
      let rest := extendRequests first.next remaining
      let segment := Segment.placed (previous.extensionScale request.requestedScale)
        request.additionalCount previous.box first.addition
      refine
        { result := rest.result
          addedWindows := segment.entries ++ rest.addedWindows
          windowsEq := ?_
          addedSegments := segment :: rest.addedSegments
          segmentsEq := ?_
          refines := rest.refines.trans (Box.Refinement.StrictInterior.refines first.nested)
          countEq := ?_
          strictWhenNonempty := fun _ =>
            Box.Refinement.StrictInterior.of_refines first.nested rest.refines }
      · calc
          rest.result.windows = first.next.windows ++ rest.addedWindows := rest.windowsEq
          _ = (previous.windows ++ segment.entries) ++ rest.addedWindows :=
            congrArg (fun windows => windows ++ rest.addedWindows) first.windowsEq
          _ = previous.windows ++ (segment.entries ++ rest.addedWindows) := List.Append.append_assoc _ _ _
      · calc
          rest.result.segments = first.next.segments ++ rest.addedSegments := rest.segmentsEq
          _ = (previous.segments ++ [segment]) ++ rest.addedSegments :=
            congrArg (fun segments => segments ++ rest.addedSegments) first.segmentsEq
          _ = previous.segments ++ (segment :: rest.addedSegments) := List.Append.append_assoc _ _ _
      · rewrite [rest.countEq, first.countEq]
        exact Nat.add_assoc _ _ _
termination_by structural requests

namespace ExtensionPath

/-- Every original window occurrence remains in the final history of the actual finite extension path. -/
theorem earlier_mem {previous : WindowHistory threshold certificate} {requests : List Request}
    (path : ExtensionPath previous requests) (entry : Entry threshold) (member : entry ∈ previous.windows) :
    entry ∈ path.result.windows := by
  rewrite [path.windowsEq]
  exact List.Membership.mem_append.mpr (Or.inl member)

/-- Every original complete consecutive-best certificate holds throughout the final retained box. -/
theorem earlierConsecutive {previous : WindowHistory threshold certificate} {requests : List Request}
    (path : ExtensionPath previous requests) (sample : Gaussian.Basic.Canonical)
    (inside : path.result.box.Contains sample)
    (entry : Entry threshold) (member : entry ∈ previous.windows) :
    Best.Consecutive.Basic.AreConsecutiveBest sample entry.2.lower entry.2.upper :=
  previous.uniformConsecutive sample (path.refines.contains inside) entry member

/-- Every original threshold-violation certificate holds throughout the final retained box. -/
theorem earlierViolation {previous : WindowHistory threshold certificate} {requests : List Request}
    (path : ExtensionPath previous requests) (sample : Gaussian.Basic.Canonical)
    (inside : path.result.box.Contains sample)
    (entry : Entry threshold) (member : entry ∈ previous.windows) :
    1 < threshold * Dirichlet.Window.SourceBound.dirichletWindowQuadrance sample entry.2.lower entry.2.upper :=
  previous.uniformViolation sample (path.refines.contains inside) entry member

end ExtensionPath

end WindowHistory

end Purelib.NumberTheory.Approximation.Dirichlet.Critical.Robust
