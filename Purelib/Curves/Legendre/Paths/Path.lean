module

public import Purelib.Curves.Legendre.Paths.Frame
import Purelib.Curves.Legendre.Paths
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Topology.Knot.Braid.Event

/-!
# Finite folds of original Legendre segments and endpoint joins

A nonempty indexed family retains the source and target frame of every
original segment. The intervening original comparison segments join
consecutive endpoint frames, so the fold returns the existing `Path`.
-/

public section

namespace Purelib.Curves.Legendre.Paths.Path

/-- Transport an original certified path and its retained frames along equalities of both endpoint parameters.

Equality elimination preserves every original segment, overlap and
clearance while reindexing the same source and target frames.
-/
@[expose] def castParameters {source target start finish : Gaussian} {left : Frame source} {right : Frame target}
    (path : Path left right) (first : source = start) (last : target = finish) :
    Path (left.castParameter first) (right.castParameter last) := by
  subst start
  subst finish
  exact path

/-- Transporting endpoint parameter indices preserves the original certified path's step count. -/
theorem castParameters_stepCount {source target start finish : Gaussian} {left : Frame source} {right : Frame target}
    (path : Path left right) (first : source = start) (last : target = finish) :
    (path.castParameters first last).stepCount = path.stepCount := by
  subst start
  subst finish
  rfl

/-- Exact endpoint parameter transport preserves the complete original path word. -/
theorem castParameters_word {source target start finish : Gaussian} {left : Frame source} {right : Frame target}
    (path : Path left right) (first : source = start) (last : target = finish) :
    (path.castParameters first last).word = path.word := by
  subst start
  subst finish
  rfl

/-- Concatenating original certified paths adds their retained segment counts. -/
theorem append_stepCount {first middle last : Gaussian}
    {left : Frame first} {center : Frame middle} {right : Frame last}
    (initial : Path left center) (remaining : Path center right) :
    (initial.append remaining).stepCount = initial.stepCount + remaining.stepCount := by
  induction initial with
  | nil frame => exact (Nat.zero_add remaining.stepCount).symm
  | cons head tail inductionHypothesis =>
      change (tail.append remaining).stepCount + 1 = tail.stepCount + 1 + remaining.stepCount
      rewrite [inductionHypothesis]
      omega0

/-- Concatenating three original paths preserves the complete path independently of parenthesization. -/
theorem append_assoc {first middle following last : Gaussian}
    {left : Frame first} {center : Frame middle} {next : Frame following} {right : Frame last}
    (initial : Path left center) (second : Path center next) (remaining : Path next right) :
    (initial.append second).append remaining = initial.append (second.append remaining) := by
  induction initial with
  | nil frame => rfl
  | cons head tail inductionHypothesis => exact congrArg (Path.cons head) (inductionHypothesis second)

/-- Appending the empty path retains every original segment and endpoint frame. -/
theorem append_nil {start finish : Gaussian} {left : Frame start} {right : Frame finish}
    (path : Path left right) : path.append (Path.nil right) = path := by
  induction path with
  | nil frame => rfl
  | cons head tail inductionHypothesis => exact congrArg (Path.cons head) inductionHypothesis

/-- Reversal exchanges the order of the same two retained paths and reverses their original segments.

The shared endpoint frame remains the original middle frame. Structural
recursion retains every reversed segment without preparing another path
or replacing geometric data by its extracted word.
-/
theorem reverse_append {start middle finish : Gaussian}
    {left : Frame start} {center : Frame middle} {right : Frame finish}
    (initial : Path left center) (remaining : Path center right) :
    (initial.append remaining).reverse = remaining.reverse.append initial.reverse := by
  induction initial with
  | nil frame => exact (append_nil remaining.reverse).symm
  | cons head tail inductionHypothesis =>
      change (tail.append remaining).reverse.append (Path.cons head.reverse (Path.nil _)) =
        remaining.reverse.append (tail.reverse.append (Path.cons head.reverse (Path.nil _)))
      rewrite [inductionHypothesis, append_assoc]
      rfl

/-- Fold a nonempty finite family of original segments with the actual comparisons joining consecutive frames.

The first segment and its following join are retained in traversal order.
Structural recursion folds the successor-index tail with its original
parameter and frame families; no segment or comparison is reconstructed.
-/
@[expose] def ofJoinedSegments :
    (size : Nat) → (sources targets : Fin (size + 1) → Gaussian) →
    (left : (index : Fin (size + 1)) → Frame (sources index)) →
    (right : (index : Fin (size + 1)) → Frame (targets index)) →
    ((index : Fin (size + 1)) → Segment (left index) (right index)) →
    ((index : Fin size) → Segment (right index.castSucc) (left index.succ)) →
    Path (left 0) (right ⟨size, Nat.lt_succ_self size⟩)
  | 0, _, _, _, right, pieces, _ => .cons (pieces 0) (.nil (right 0))
  | size + 1, sources, targets, left, right, pieces, joins =>
    .cons (pieces 0) (.cons (joins 0)
      (ofJoinedSegments size (fun index => sources index.succ) (fun index => targets index.succ)
        (fun index => left index.succ) (fun index => right index.succ)
        (fun index => pieces index.succ) (fun index => joins index.succ)))

/-- The original joined-segment fold retains every moving piece and every intervening comparison exactly once. -/
theorem ofJoinedSegments_stepCount :
    (size : Nat) → (sources targets : Fin (size + 1) → Gaussian) →
    (left : (index : Fin (size + 1)) → Frame (sources index)) →
    (right : (index : Fin (size + 1)) → Frame (targets index)) →
    (pieces : (index : Fin (size + 1)) → Segment (left index) (right index)) →
    (joins : (index : Fin size) → Segment (right index.castSucc) (left index.succ)) →
    (ofJoinedSegments size sources targets left right pieces joins).stepCount = 2 * size + 1
  | 0, _, _, _, _, _, _ => rfl
  | size + 1, sources, targets, left, right, pieces, joins => by
    change (ofJoinedSegments size (fun index => sources index.succ) (fun index => targets index.succ)
      (fun index => left index.succ) (fun index => right index.succ)
      (fun index => pieces index.succ) (fun index => joins index.succ)).stepCount + 1 + 1 = _
    rewrite [ofJoinedSegments_stepCount]
    omega0

/-- Folding actual stationary pieces and endpoint comparisons contributes no braid crossing.

Each original stored segment and join has its own actual stationary event.
The structural fold keeps those exact inputs and their endpoint frames;
recursion consumes the same successor-index tail without reconstructing
any comparison or substituting a word for its geometric data.
-/
theorem ofJoinedSegments_word_nil :
    (size : Nat) → (sources targets : Fin (size + 1) → Gaussian) →
    (left : (index : Fin (size + 1)) → Frame (sources index)) →
    (right : (index : Fin (size + 1)) → Frame (targets index)) →
    (pieces : (index : Fin (size + 1)) → Segment (left index) (right index)) →
    (joins : (index : Fin size) → Segment (right index.castSucc) (left index.succ)) →
    (∀ index : Fin (size + 1), (pieces index).projection.event = .stationary) →
    (∀ index : Fin size, (joins index).projection.event = .stationary) →
    (ofJoinedSegments size sources targets left right pieces joins).word = []
  | 0, _, _, _, _, pieces, _, stationaryPieces, _ => by
      change (pieces 0).projection.event.word ++ [] = []
      rewrite [stationaryPieces 0]
      rfl
  | size + 1, sources, targets, left, right, pieces, joins, stationaryPieces, stationaryJoins => by
      change (pieces 0).projection.event.word ++ ((joins 0).projection.event.word ++
        (ofJoinedSegments size (fun index => sources index.succ) (fun index => targets index.succ)
          (fun index => left index.succ) (fun index => right index.succ)
          (fun index => pieces index.succ) (fun index => joins index.succ)).word) = []
      rewrite [stationaryPieces 0, stationaryJoins 0]
      rewrite [ofJoinedSegments_word_nil size (fun index => sources index.succ) (fun index => targets index.succ)
        (fun index => left index.succ) (fun index => right index.succ)
        (fun index => pieces index.succ) (fun index => joins index.succ)
        (fun index => stationaryPieces index.succ) (fun index => stationaryJoins index.succ)]
      rfl

end Purelib.Curves.Legendre.Paths.Path
