module

import Purelib.Curves.Legendre.Paths.Path
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Paths.Frame

/-! # Original finite segment folds preserve traversal order and complete retained entries -/

namespace TestPurelib.Curves.Legendre.Paths.Path

open Purelib.Curves.Legendre.Paths

/-- Exact parameter transport and its inverse retain the whole original frame, including owners and certificates. -/
example {source target : Gaussian} (frame : Frame source) (same : source = target) :
    (frame.castParameter same).castParameter same.symm = frame := frame.castParameter_inverse same

/-- Reflexive endpoint transport retains the complete original path. -/
example {source target : Gaussian} {left : Frame source} {right : Frame target} (path : Path left right) :
    path.castParameters rfl rfl = path := rfl

/-- Reindexing both endpoint parameters preserves the number of actual retained path steps. -/
example {source target start finish : Gaussian} {left : Frame source} {right : Frame target}
    (path : Path left right) (first : source = start) (last : target = finish) :
    (path.castParameters first last).stepCount = path.stepCount := path.castParameters_stepCount first last

/-- Exact endpoint reindexing retains the complete actual braid word. -/
example {source target start finish : Gaussian} {left : Frame source} {right : Frame target}
    (path : Path left right) (first : source = start) (last : target = finish) :
    (path.castParameters first last).word = path.word := path.castParameters_word first last

/-- A single-piece fold retains its complete original segment and terminal frame. -/
example (sources targets : Fin 1 → Gaussian) (left : (index : Fin 1) → Frame (sources index))
    (right : (index : Fin 1) → Frame (targets index)) (pieces : (index : Fin 1) → Segment (left index) (right index))
    (joins : (index : Fin 0) → Segment (right index.castSucc) (left index.succ)) :
    Path.ofJoinedSegments 0 sources targets left right pieces joins =
      .cons (pieces 0) (.nil (right 0)) := rfl

/-- A two-piece fold retains both complete original segments and their actual intervening comparison in order. -/
example (sources targets : Fin 2 → Gaussian) (left : (index : Fin 2) → Frame (sources index))
    (right : (index : Fin 2) → Frame (targets index)) (pieces : (index : Fin 2) → Segment (left index) (right index))
    (joins : (index : Fin 1) → Segment (right index.castSucc) (left index.succ)) :
    Path.ofJoinedSegments 1 sources targets left right pieces joins =
      .cons (pieces 0) (.cons (joins 0) (.cons (pieces 1) (.nil (right 1)))) := rfl

/-- Every finite original family contributes all its pieces and intervening comparisons to the same path. -/
example (size : Nat) (sources targets : Fin (size + 1) → Gaussian)
    (left : (index : Fin (size + 1)) → Frame (sources index))
    (right : (index : Fin (size + 1)) → Frame (targets index))
    (pieces : (index : Fin (size + 1)) → Segment (left index) (right index))
    (joins : (index : Fin size) → Segment (right index.castSucc) (left index.succ)) :
    (Path.ofJoinedSegments size sources targets left right pieces joins).stepCount = 2 * size + 1 :=
  Path.ofJoinedSegments_stepCount size sources targets left right pieces joins

/-- Actual stationary segments and joins retain their full data while their same finite fold has empty word. -/
example (size : Nat) (sources targets : Fin (size + 1) → Gaussian)
    (left : (index : Fin (size + 1)) → Frame (sources index))
    (right : (index : Fin (size + 1)) → Frame (targets index))
    (pieces : (index : Fin (size + 1)) → Segment (left index) (right index))
    (joins : (index : Fin size) → Segment (right index.castSucc) (left index.succ))
    (stationaryPieces : ∀ index : Fin (size + 1), (pieces index).projection.event = .stationary)
    (stationaryJoins : ∀ index : Fin size, (joins index).projection.event = .stationary) :
    (Path.ofJoinedSegments size sources targets left right pieces joins).word = [] :=
  Path.ofJoinedSegments_word_nil size sources targets left right pieces joins stationaryPieces stationaryJoins

end TestPurelib.Curves.Legendre.Paths.Path
