module

import Purelib.Curves.Legendre.Paths.SafePath.Preparation
import Purelib.Curves.Legendre.Paths.SafePath
import Purelib.Curves.Legendre.Paths.Path.Refinement
import Purelib.Curves.Legendre.Paths.Frame
import Purelib.Curves.Legendre.Paths
import Purelib.Data.Fin

/-! # Whole original finite-path preparation and its physical correspondence -/

namespace TestPurelib.Curves.Legendre.Paths.SafePath.Preparation

open Purelib.Curves.Legendre.Paths
open Purelib

/-- Cached reversal retains both original frame records and their actual reversed path. -/
example {start finish : Gaussian} {original : SafePath start finish} {slope : Coordinate}
    (prepared : original.PreparedPath slope) :
    prepared.reverse.sourceFrame = prepared.targetFrame ∧ prepared.reverse.targetFrame = prepared.sourceFrame ∧
      prepared.reverse.path = prepared.path.reverse :=
  ⟨prepared.reverse_frames.1, prepared.reverse_frames.2, prepared.reverse_path⟩

/-- The actual cached inverse preparation has a physical certificate for the same original reversed geometry. -/
example {start finish : Gaussian} {original : SafePath start finish} {slope : Coordinate}
    (prepared : original.PreparedPath slope) : prepared.reverse.path.RefinesSafePath original.reverse :=
  prepared.reverse.path_refinesSafePath

/-- A raw intrinsic preparation reuses its actual root owners and backward transport for the reversed path. -/
example (size : Nat) (points : Fin (size + 1) → Gaussian)
    (axes : (index : Fin size) → AxisSegment (points index.castSucc) (points index.succ))
    (avoidsZero : ∀ index : Fin size, (axes index).Avoids 0) (avoidsOne : ∀ index : Fin size, (axes index).Avoids 1)
    (nonzero : points 0 ≠ 0) (notOne : points 0 ≠ 1) :
    let prepared := (SafePath.prepareAxes size points axes avoidsZero avoidsOne nonzero notOne).preparation
    ∀ index : prepared.targetFrame.chamber.Index,
      prepared.reverse.path.ownerTransport.forward index = prepared.path.ownerTransport.backward index := by
  intro prepared index
  exact prepared.reverse_ownerTransport index

/-- A consumer of the original geometry retains all its physical points on the same cached reversed preparation. -/
example {start finish : Gaussian} {original : SafePath start finish} {slope : Coordinate}
    (prepared : original.PreparedPath slope) {point : Gaussian} (visited : original.Visits point) :
    prepared.reverse.path.Visits point := prepared.reverse_visits visited

/-- The original four-side meridian can be physically reversed through its retained preparation without fresh frames. -/
example :
    let prepared := RectangleExamples.zeroRectangle.preparePath (by decide +kernel) (by decide +kernel)
    prepared.reverse.path.RefinesSafePath RectangleExamples.zeroRectangle.reverse := by
  intro prepared
  exact prepared.reverse.path_refinesSafePath

/-- The actual whole path word agrees with its internal chart without a caller endpoint-reading or braid certificate. -/
example {start finish : Gaussian} (original : SafePath start finish) (slope : Coordinate)
    (nonzero : start ≠ 0) (notOne : start ≠ 1)
    (paid : ∀ index : Fin (original.stepCount + 1), Projection.slopeCost (original.vertices index) < slope) :
    (original.preparePathAt slope nonzero notOne
      (original.vertices_separated_of_slopeCost slope nonzero notOne paid)).path.word =
        (original.preparePath nonzero notOne).path.word :=
  original.preparePath_word_eq_of_slopeCost slope nonzero notOne paid

/-- The shared-chart head/tail constructor retains exactly both actual input words and its actual owner comparison. -/
example {start middle finish : Gaussian} (segment : AxisSegment start middle)
    (safe : AxisSegment.Safe segment) {tail : SafePath middle finish} {slope : Coordinate}
    {left : Frame start} {center : Frame middle} (head : Path left center)
    (sourceChart : left.InChart slope) (targetChart : center.InChart slope)
    (headRefinement : head.RefinesAxis segment 0 1) (remaining : tail.PreparedPath slope) :
    (SafePath.PreparedPath.prepend segment safe head sourceChart targetChart headRefinement remaining).path.word =
      head.word ++ remaining.path.word :=
  SafePath.PreparedPath.prepend_word segment safe head sourceChart targetChart headRefinement remaining

/-- Every original internally prepared finite safe path has the computed two-generators-per-axis bound. -/
example {start finish : Gaussian} (original : SafePath start finish) (nonzero : start ≠ 0) (notOne : start ≠ 1) :
    (original.preparePath nonzero notOne).path.word.length ≤ 2 * original.stepCount :=
  original.preparePath_word_length_le nonzero notOne

/-- Raw finite input derives its original two-generators-per-axis bound from intrinsic avoidance alone. -/
example (size : Nat) (points : Fin (size + 1) → Gaussian)
    (axes : (index : Fin size) → AxisSegment (points index.castSucc) (points index.succ))
    (avoidsZero : ∀ index : Fin size, (axes index).Avoids 0) (avoidsOne : ∀ index : Fin size, (axes index).Avoids 1)
    (nonzero : points 0 ≠ 0) (notOne : points 0 ≠ 1) :
    (SafePath.prepareAxes size points axes avoidsZero avoidsOne nonzero notOne).path.word.length ≤ 2 * size :=
  SafePath.prepareAxes_word_length_le size points axes avoidsZero avoidsOne nonzero notOne

/-- The geometry-only checked frontend proves the same actual bound on every returned successful preparation. -/
example (size : Nat) (points : Fin (size + 1) → Gaussian)
    (axes : (index : Fin size) → AxisSegment (points index.castSucc) (points index.succ)) :
    match SafePath.checkPrepareAxes size points axes with
    | .inl prepared => prepared.path.word.length ≤ 2 * size
    | .inr _ => True := SafePath.checkPrepareAxes_word_length_le size points axes

/-- Intrinsic finite input produces actual prepared frames and point coverage without a supplied safety cache. -/
example (size : Nat) (points : Fin (size + 1) → Gaussian)
    (axes : (index : Fin size) → AxisSegment (points index.castSucc) (points index.succ))
    (avoidsZero : ∀ index : Fin size, (axes index).Avoids 0) (avoidsOne : ∀ index : Fin size, (axes index).Avoids 1)
    (nonzero : points 0 ≠ 0) (notOne : points 0 ≠ 1) (index : Fin size) (parameter : Coordinate)
    (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    (SafePath.prepareAxes size points axes avoidsZero avoidsOne nonzero notOne).path.Visits
      ((axes index).pointAt parameter) :=
  (SafePath.prepareAxes size points axes avoidsZero avoidsOne nonzero notOne).path_visits_axis index parameter inside

/-- A checked success derives the complete physical relation to every original axis from raw geometric input alone. -/
example (size : Nat) (points : Fin (size + 1) → Gaussian)
    (axes : (index : Fin size) → AxisSegment (points index.castSucc) (points index.succ)) :
    match SafePath.checkPrepareAxes size points axes with
    | .inl prepared => prepared.original.stepCount = size ∧ ∀ index : Fin size, ∀ parameter : Coordinate,
        0 ≤ parameter → parameter ≤ 1 → prepared.path.Visits ((axes index).pointAt parameter)
    | .inr _ => True := by
  cases SafePath.checkPrepareAxes size points axes with
  | inl prepared =>
      exact ⟨prepared.original_stepCount, fun index parameter lower upper =>
        prepared.path_visits_axis index parameter ⟨lower, upper⟩⟩
  | inr invalid => exact True.intro

/-- The raw zero-collision example retains both original real-axis vertices. -/
def zeroPoints : Fin 2 → Gaussian := Data.Fin.cases (gaussian (-1) 0) (fun _ => gaussian 1 0)

/-- The raw original axis crosses zero at its exact unit midpoint. -/
def zeroAxes : (index : Fin 1) → AxisSegment (zeroPoints index.castSucc) (zeroPoints index.succ) :=
  Data.Fin.casesDependent (.horizontal (-1) 1 0) (fun index => Fin.elim0 index)

/-- The certificate-free checker identifies the original zero-collision axis and its exact interior parameter. -/
example :
    (match SafePath.checkPrepareAxes 1 zeroPoints zeroAxes with
    | .inl _ => false
    | .inr (.inl _) => false
    | .inr (.inr collision) => decide (collision.1 = 0) && match collision.2 with
        | .inl zero => decide (zero.parameter = 1 / 2)
        | .inr _ => false) = true := by decide +kernel

/-- The raw one-collision example retains both original regular real-axis vertices. -/
def onePoints : Fin 2 → Gaussian := Data.Fin.cases (gaussian (1 / 2) 0) (fun _ => gaussian (3 / 2) 0)

/-- The raw original axis crosses one at its exact unit midpoint. -/
def oneAxes : (index : Fin 1) → AxisSegment (onePoints index.castSucc) (onePoints index.succ) :=
  Data.Fin.casesDependent (.horizontal (1 / 2) (3 / 2) 0) (fun index => Fin.elim0 index)

/-- The same checker distinguishes the original one-collision from zero and retains its exact interior parameter. -/
example :
    (match SafePath.checkPrepareAxes 1 onePoints oneAxes with
    | .inl _ => false
    | .inr (.inl _) => false
    | .inr (.inr collision) => decide (collision.1 = 0) && match collision.2 with
        | .inl _ => false
        | .inr one => decide (one.parameter = 1 / 2)) = true := by decide +kernel

/-- Three original real vertices make the singular collision occur only on the second input axis. -/
def laterPoints : Fin 3 → Gaussian :=
  Data.Fin.cases (gaussian (-3) 0) (Data.Fin.cases (gaussian (-2) 0) (fun _ => gaussian 1 0))

/-- The original safe first axis precedes the original second zero-collision axis. -/
def laterAxes : (index : Fin 2) → AxisSegment (laterPoints index.castSucc) (laterPoints index.succ) :=
  Data.Fin.casesDependent (.horizontal (-3) (-2) 0)
    (Data.Fin.casesDependent (.horizontal (-2) 1 0) (fun index => Fin.elim0 index))

/-- Tail invalidity preserves the original input axis ordinal and the original local unit parameter. -/
example :
    (match SafePath.checkPrepareAxes 2 laterPoints laterAxes with
    | .inl _ => false
    | .inr (.inl _) => false
    | .inr (.inr collision) => decide (collision.1 = 1) && match collision.2 with
        | .inl zero => decide (zero.parameter = 2 / 3)
        | .inr _ => false) = true := by decide +kernel

/-- Both original vertices have zero real coordinate and a strictly positive imaginary coordinate. -/
def verticalPoints : Fin 2 → Gaussian := Data.Fin.cases (gaussian 0 1) (fun _ => gaussian 0 2)

/-- The original vertical axis is tied with the fixed zero branch in its unrotated real projection. -/
def verticalAxes : (index : Fin 1) → AxisSegment (verticalPoints index.castSucc) (verticalPoints index.succ) :=
  Data.Fin.casesDependent (.vertical 0 1 2) (fun index => Fin.elim0 index)

/-- Raw nongeneric geometry succeeds and computes its original shared chart without a supplied certificate. -/
example :
    (match SafePath.checkPrepareAxes 1 verticalPoints verticalAxes with
    | .inl prepared => decide (prepared.original.stepCount = 1) &&
        decide (prepared.original.projectionSlope = 5 / 2)
    | .inr _ => false) = true := by decide +kernel

/-- An empty raw family has no original axis to check or prepare. -/
def emptyAxes (points : Fin 1 → Gaussian) :
    (index : Fin 0) → AxisSegment (points index.castSucc) (points index.succ) := fun index => Fin.elim0 index

/-- Every intrinsic admissible finite family succeeds in the same checked preparation without an attempt certificate. -/
example (size : Nat) (points : Fin (size + 1) → Gaussian)
    (axes : (index : Fin size) → AxisSegment (points index.castSucc) (points index.succ))
    (avoidsZero : ∀ index : Fin size, (axes index).Avoids 0) (avoidsOne : ∀ index : Fin size, (axes index).Avoids 1)
    (nonzero : points 0 ≠ 0) (notOne : points 0 ≠ 1) :
    ∃ prepared : SafePath.PreparedAxes size points axes, SafePath.checkPrepareAxes size points axes = .inl prepared :=
  SafePath.checkPrepareAxes_succeeds size points axes avoidsZero avoidsOne nonzero notOne

/-- The checked empty regular family succeeds and retains its actual empty original and prepared paths. -/
example :
    (match SafePath.checkPrepareAxes 0 (fun _ => (2 : Gaussian)) (emptyAxes (fun _ => 2)) with
    | .inl prepared => decide (prepared.original.stepCount = 0) && decide (prepared.path.stepCount = 0)
    | .inr _ => false) = true := by decide +kernel

/-- The source check rejects even an empty singular input and identifies its actual excluded parameter. -/
example :
    (match SafePath.checkPrepareAxes 0 (fun _ => (0 : Gaussian)) (emptyAxes (fun _ => 0)) with
    | .inl _ => false
    | .inr (.inl invalid) => decide (invalid.val = 0)
    | .inr (.inr _) => false) = true := by decide +kernel

/-- The other singular source is distinguished without inventing an axis in the empty family. -/
example :
    (match SafePath.checkPrepareAxes 0 (fun _ => (1 : Gaussian)) (emptyAxes (fun _ => 1)) with
    | .inl _ => false
    | .inr (.inl invalid) => decide (invalid.val = 1)
    | .inr (.inr _) => false) = true := by decide +kernel

/-- Both actual output frames retain the same chart computed from the complete original vertex family. -/
example {start finish : Gaussian} (original : SafePath start finish) (nonzero : start ≠ 0) (notOne : start ≠ 1) :
    (original.preparePath nonzero notOne).sourceFrame.InChart original.projectionSlope ∧
      (original.preparePath nonzero notOne).targetFrame.InChart original.projectionSlope :=
  ⟨(original.preparePath nonzero notOne).sourceFrame_inChart,
    (original.preparePath nonzero notOne).targetFrame_inChart⟩

/-- The same actual stored output path physically refines every original retained head in its original order. -/
example {start finish : Gaussian} (original : SafePath start finish) (nonzero : start ≠ 0) (notOne : start ≠ 1) :
    (original.preparePath nonzero notOne).path.RefinesSafePath original :=
  (original.preparePath nonzero notOne).path_refinesSafePath

/-- Every original unit-axis or final-point membership transfers to the actual prepared whole path. -/
example {start finish : Gaussian} (original : SafePath start finish) (nonzero : start ≠ 0) (notOne : start ≠ 1)
    {point : Gaussian} (visited : original.Visits point) :
    (original.preparePath nonzero notOne).path.Visits point := (original.preparePath nonzero notOne).path_visits visited

/-- An original empty path at a regular point prepares no artificial segment. -/
example (point : Gaussian) (nonzero : point ≠ 0) (notOne : point ≠ 1) :
    ((SafePath.nil point).preparePath nonzero notOne).path.stepCount = 0 :=
  Path.RefinesSafePath.nil_data ((SafePath.nil point).preparePath nonzero notOne).path_refinesSafePath

/-- Preparation retains the original four-axis zero meridian without requesting any root frame or braid word. -/
def zeroRectangle := RectangleExamples.zeroRectangle.preparePath (by decide +kernel) (by decide +kernel)

/-- The whole actual prepared meridian retains physical correspondence with the same original rectangle owner. -/
example : zeroRectangle.path.RefinesSafePath RectangleExamples.zeroRectangle := zeroRectangle.path_refinesSafePath

/-- Each point on the original first meridian side belongs to the actual stored complete prepared loop. -/
example (parameter : Coordinate) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    zeroRectangle.path.Visits (RectangleExamples.zeroTop.pointAt parameter) :=
  zeroRectangle.path_visits (SafePath.Visits.cons_head RectangleExamples.zeroTop RectangleExamples.zeroTopSafe
    parameter inside rfl)

end TestPurelib.Curves.Legendre.Paths.SafePath.Preparation
