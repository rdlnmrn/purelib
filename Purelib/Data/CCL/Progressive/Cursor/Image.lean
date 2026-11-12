module
import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Encoding.Parser.State
public import Purelib.Data.CCL.Progressive.Cursor.Refinement
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.CCL.Transducer.Machine.Committed
import Purelib.Data.CCL.Transducer.Machine.Step
import Purelib.Data.CCL.Transducer.Emission.Step
import Purelib.Data.List.Append
import Purelib.Data.CCL.Transducer.Mode.Basic
import Purelib.Data.CCL.Transducer.Mode.Semantics
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Power
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Geometry.Projective.Line.Matrix.Gaussian

section
public section

/-!
# Persistent finite requests for progressive CCL cursors

The raw arithmetic cursor already extends one finite `List Bool` prefix.  This
module adds the missing accuracy operation: refine the finite enclosure carried
by its current quantitative mode without changing either exposed or buffered
bits.  The refined ball is transported through the exact current projective
chart, giving an arbitrarily small rational squared-chordal cylinder bound.

Everything here is a finite request on an explicit machine.  No stream, limit,
intersection, or completed value is formed.
-/

namespace Purelib.Data.CCL.Progressive.Cursor.Image

namespace Mode

open Purelib.Data.CCL.Transducer in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Projective in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Represent the retained mode's parser-tail normalization by its exact projective matrix.

Initial mode uses the identity; low and loop use inverse and forward gamma powers at their retained counts. Residual
mode uses the gamma inversion matrix, including tails represented homogeneously at zero. -/
@[expose] def tailMatrix :
    Transducer.Mode → LinearAlgebra.Coordinates2.Matrix.GaussianMatrix
  | .initial _ => Matrix2.identityMatrix
  | .low current =>
      Line.Matrix.scale
        (Power.natPow Basic.Canonical.gamma current.count)⁻¹
  | .loop current =>
      Line.Matrix.scale
        (Power.natPow Basic.Canonical.gamma current.count)
  | .residual _ => Line.Matrix.invert Basic.Canonical.gamma

section
open Purelib.Data.CCL.Progressive
open Purelib.Data.CCL.Transducer
open Purelib.Data.Gaussian
open Purelib.Geometry.Projective
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2
/-- Acting on a value's affine point by the exact mode tail matrix gives its retained parser tail. -/
theorem tailMatrix_act (mode : Transducer.Mode) (value : Basic.Canonical) :
    Line.Matrix.act (Cursor.Image.Mode.tailMatrix mode) (Line.Proj.affine value) =
      Purelib.Data.CCL.Transducer.Mode.Semantics.SemanticMode.parserTail mode value := by
  cases mode with
  | initial current =>
      apply Line.Proj.ext <;>
        simp [Cursor.Image.Mode.tailMatrix, Matrix2.identityMatrix,
          Line.Matrix.act, Line.Proj.affine,
          Purelib.Data.CCL.Transducer.Mode.Semantics.SemanticMode.parserTail, -eq_self, -iff_self ] <;> rfl
  | low current | loop current =>
      apply Line.Proj.ext <;>
        simp [Cursor.Image.Mode.tailMatrix, Line.Matrix.act, Line.Matrix.scale, Line.Proj.affine,
          Purelib.Data.CCL.Transducer.Mode.Semantics.SemanticMode.parserTail, -eq_self, -iff_self ] <;> rfl
  | residual current =>
      apply Line.Proj.ext <;>
        simp [Cursor.Image.Mode.tailMatrix, Line.Matrix.act, Line.Matrix.invert, Line.Proj.affine,
          Purelib.Data.CCL.Transducer.Mode.Semantics.SemanticMode.parserTail, -eq_self, -iff_self ] <;> rfl

/-- Every retained mode's exact tail matrix has nonzero determinant. -/
theorem tailMatrix_det_ne (mode : Transducer.Mode) :
    Matrix2.Matrix2.determinant (Cursor.Image.Mode.tailMatrix mode) ≠ 0 := by
  cases mode with
  | initial current =>
      dsimp only [tailMatrix, Matrix2.identityMatrix, Matrix2.Matrix2.determinant]
      rw [Basic.mul_one, Basic.zero_mul, Basic.sub_zero]
      decide
  | low current =>
      simp only [Cursor.Image.Mode.tailMatrix, Line.Matrix.scale,
        Matrix2.Matrix2.determinant,
        Basic.mul_one,
        Basic.zero_mul,
        Basic.sub_zero]
      exact Field.inv_ne_zero_direct
        (Power.natPow_ne_zero_direct Basic.Canonical.gamma
          (by decide) current.count)
  | loop current =>
      simp only [Cursor.Image.Mode.tailMatrix, Line.Matrix.scale,
        Matrix2.Matrix2.determinant,
        Basic.mul_one,
        Basic.zero_mul,
        Basic.sub_zero]
      exact Power.natPow_ne_zero_direct Basic.Canonical.gamma
        (by decide) current.count
  | residual current =>
      simp only [Cursor.Image.Mode.tailMatrix, Line.Matrix.invert,
        Matrix2.Matrix2.determinant,
        Basic.zero_mul,
        Basic.one_mul]
      exact Field.neg_ne_zero_direct
        (show Basic.Canonical.gamma ≠ 0 by decide)

end

open Purelib.Data.CCL.Progressive in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Rat in
/-- Refining a mode leaves its exact tail matrix unchanged. -/
@[simp] theorem refine_tailMatrix
    (mode : Transducer.Mode) (target : Fraction.Rational) (positive : 0 < target) :
    Cursor.Image.Mode.tailMatrix (Cursor.Refinement.Mode.refine mode target positive) = Cursor.Image.Mode.tailMatrix
      mode := by
  cases mode <;> rfl

end Mode

namespace Machine

open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Progressive in
open Purelib.Data.CCL.Transducer in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Multiply the committed parser matrix by the exact retained mode tail matrix. -/
@[expose] def imageMatrix (machine : Transducer.Machine) :
  LinearAlgebra.Coordinates2.Matrix.GaussianMatrix :=
  Matrix2.mul
    (Parser.State.parse
      (Transducer.Machine.committed
        machine)).matrix
    (Cursor.Image.Mode.tailMatrix machine.mode)

open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Projective in
/-- Apply the exact committed parser matrix to the retained mode's parser tail at the supplied value. -/
@[expose] def image (machine : Transducer.Machine) (value : Basic.Canonical) :
  Line.GaussianLine :=
  Line.Matrix.act
    (Parser.State.parse
      (Transducer.Machine.committed
        machine)).matrix
    (Purelib.Data.CCL.Transducer.Mode.Semantics.SemanticMode.parserTail machine.mode value)

open Purelib.Data.CCL.Progressive in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Projective in
/-- The retained machine image equals its combined image-matrix action on the value's affine point. -/
theorem image_eq_act_imageMatrix (machine : Transducer.Machine) (value : Basic.Canonical)
  :
    Cursor.Image.Machine.image machine value =
      Line.Matrix.act (Cursor.Image.Machine.imageMatrix machine) (Line.Proj.affine value) := by
  rw [Cursor.Image.Machine.image, Cursor.Image.Machine.imageMatrix, Line.Matrix.act_mul,
    Cursor.Image.Mode.tailMatrix_act]

open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Progressive in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Gaussian in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- The exact combined image matrix of every retained machine has nonzero determinant. -/
theorem imageMatrix_det_ne (machine : Transducer.Machine) :
    Matrix2.Matrix2.determinant (Cursor.Image.Machine.imageMatrix machine) ≠ 0 := by
  rw [Cursor.Image.Machine.imageMatrix, Matrix2.det_mul]
  exact Field.mul_ne_zero_direct
    (Parser.State.parse_det_ne
      (Transducer.Machine.committed machine))
    (Cursor.Image.Mode.tailMatrix_det_ne machine.mode)

open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Progressive in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Rat in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Refining a machine leaves its exact combined image matrix unchanged. -/
@[simp] theorem refine_imageMatrix
    (machine : Transducer.Machine) (target : Fraction.Rational) (positive : 0 < target) :
    Cursor.Image.Machine.imageMatrix (Refinement.Machine.refine machine target positive) =
      (Cursor.Image.Machine.imageMatrix machine) := by
  change Matrix2.mul
      (Parser.State.parse
        (Transducer.Machine.committed
          machine)).matrix
      (Cursor.Image.Mode.tailMatrix (Cursor.Refinement.Mode.refine machine.mode target positive)) =
    Matrix2.mul
      (Parser.State.parse
        (Transducer.Machine.committed
          machine)).matrix
      (Cursor.Image.Mode.tailMatrix machine.mode)
  rw [Cursor.Image.Mode.refine_tailMatrix]
end Machine

end Purelib.Data.CCL.Progressive.Cursor.Image

end

public section

namespace Purelib.Data.CCL.Progressive.Cursor.Image.Machine

open Purelib
open Purelib.Data.CCL.Encoding
open Purelib.Data.CCL.Progressive
open Purelib.Data.CCL.Transducer
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2

set_option genInjectivity false in
/-- Retain one cursor's actual parser, normalization matrix, combined image matrix and adjugate caches. -/
structure Frame (machine : Transducer.Machine) where
  /-- The original finite parser state cached for this same committed word. -/ parser : Parser.State
  /-- The cache is the actual parser of the retained committed word. -/ parserEq :
    parser = Parser.State.parse (Transducer.Machine.committed machine)
  /-- The mode's exact retained normalization matrix. -/ normalization : Matrix2.GaussianMatrix
  /-- This normalization cache belongs to the original mode and count. -/ normalizationEq :
    normalization = Cursor.Image.Mode.tailMatrix machine.mode
  /-- The combined image matrix computed once from the two retained factors. -/ matrix : Matrix2.GaussianMatrix
  /-- The combined cache consumes the exact retained parser and normalization factors. -/ factorsEq :
    matrix = Matrix2.mul parser.matrix normalization
  /-- The combined cache is the original cursor's image matrix. -/ matrixEq :
    matrix = Cursor.Image.Machine.imageMatrix machine
  /-- The exact inverse-chart adjugate computed once from this combined cache. -/ adjugate : Matrix2.GaussianMatrix
  /-- The adjugate consumes the same retained combined image matrix. -/ adjugateEq :
    adjugate = Matrix2.BoundaryAdjugate.adjugate matrix
  /-- This actual retained image chart is nonsingular. -/ determinantNonzero : Matrix2.Matrix2.determinant matrix ≠ 0

namespace Frame

/-- Cache a cursor frame from an already retained parser without reparsing its committed word. -/
def ofParser (machine : Transducer.Machine) (parser : Parser.State)
    (parsed : parser = Parser.State.parse (Transducer.Machine.committed machine)) : Frame machine := by
  let normalization : Matrix2.GaussianMatrix := Cursor.Image.Mode.tailMatrix machine.mode
  let matrix : Matrix2.GaussianMatrix := Matrix2.mul parser.matrix normalization
  have matrixEq : matrix = Cursor.Image.Machine.imageMatrix machine :=
    congrArg (fun (retained : Parser.State) => Matrix2.mul retained.matrix normalization) parsed
  have determinantNonzero : Matrix2.Matrix2.determinant matrix ≠ 0 := by
    rewrite [matrixEq]
    exact Cursor.Image.Machine.imageMatrix_det_ne machine
  exact
    { parser := parser
      parserEq := parsed
      normalization := normalization
      normalizationEq := rfl
      matrix := matrix
      factorsEq := rfl
      matrixEq := matrixEq
      adjugate := Matrix2.BoundaryAdjugate.adjugate matrix
      adjugateEq := rfl
      determinantNonzero := determinantNonzero }

/-- Parse a cursor's original committed word once and cache its complete image frame. -/
def ofMachine (machine : Transducer.Machine) : Frame machine :=
  let parser := Parser.State.parse (Transducer.Machine.committed machine)
  ofParser machine parser rfl

/-- The prepared-parser constructor retains the exact supplied parser cache. -/
private theorem ofParser_specification (machine : Transducer.Machine) (parser : Parser.State)
    (parsed : parser = Parser.State.parse (Transducer.Machine.committed machine)) :
    (ofParser machine parser parsed).parser = parser := rfl

/-- The frame constructor consumes the actual supplied parser instead of rebuilding its state. -/
theorem ofParser_parser (machine : Transducer.Machine) (parser : Parser.State)
    (parsed : parser = Parser.State.parse (Transducer.Machine.committed machine)) :
    (ofParser machine parser parsed).parser = parser := ofParser_specification machine parser parsed

/-- Transport the same four caches to a cursor with the same committed word and normalization matrix. -/
def transport {original : Transducer.Machine} (frame : Frame original) (next : Transducer.Machine)
    (committedEq : Transducer.Machine.committed next = Transducer.Machine.committed original)
    (normalizationEq : Cursor.Image.Mode.tailMatrix next.mode = Cursor.Image.Mode.tailMatrix original.mode) :
    Frame next := by
  have imageEq : Cursor.Image.Machine.imageMatrix next = Cursor.Image.Machine.imageMatrix original := by
    unfold Cursor.Image.Machine.imageMatrix
    rewrite [committedEq, normalizationEq]
    rfl
  exact
    { parser := frame.parser
      parserEq := frame.parserEq.trans (congrArg Parser.State.parse committedEq.symm)
      normalization := frame.normalization
      normalizationEq := frame.normalizationEq.trans normalizationEq.symm
      matrix := frame.matrix
      factorsEq := frame.factorsEq
      matrixEq := frame.matrixEq.trans imageEq.symm
      adjugate := frame.adjugate
      adjugateEq := frame.adjugateEq
      determinantNonzero := frame.determinantNonzero }

/-- Cache transport retains the four exact original data fields. -/
private theorem transport_specification {original : Transducer.Machine} (frame : Frame original)
    (next : Transducer.Machine)
    (committedEq : Transducer.Machine.committed next = Transducer.Machine.committed original)
    (normalizationEq : Cursor.Image.Mode.tailMatrix next.mode = Cursor.Image.Mode.tailMatrix original.mode) :
    let transported := frame.transport next committedEq normalizationEq
    transported.parser = frame.parser ∧ transported.normalization = frame.normalization ∧
      transported.matrix = frame.matrix ∧ transported.adjugate = frame.adjugate := ⟨rfl, rfl, rfl, rfl⟩

/-- Transport preserves the exact original parser, normalization, image and adjugate caches. -/
theorem transport_caches {original : Transducer.Machine} (frame : Frame original) (next : Transducer.Machine)
    (committedEq : Transducer.Machine.committed next = Transducer.Machine.committed original)
    (normalizationEq : Cursor.Image.Mode.tailMatrix next.mode = Cursor.Image.Mode.tailMatrix original.mode) :
    let transported := frame.transport next committedEq normalizationEq
    transported.parser = frame.parser ∧ transported.normalization = frame.normalization ∧
      transported.matrix = frame.matrix ∧ transported.adjugate = frame.adjugate :=
  transport_specification frame next committedEq normalizationEq

/-- Apply the exact retained image-matrix cache to a supplied rational tail. -/
@[expose] def image {machine : Transducer.Machine} (frame : Frame machine) (value : Basic.Canonical) :
    Line.GaussianLine := Line.Matrix.act frame.matrix (Line.Proj.affine value)

/-- Applying the retained matrix cache yields the original cursor image of the same supplied tail. -/
theorem imageEq {machine : Transducer.Machine} (frame : Frame machine) (value : Basic.Canonical) :
    frame.image value = Cursor.Image.Machine.image machine value :=
  (congrArg (fun matrix => Line.Matrix.act matrix (Line.Proj.affine value)) frame.matrixEq).trans
    (Cursor.Image.Machine.image_eq_act_imageMatrix machine value).symm

/-- Pull an image back using the exact retained adjugate cache. -/
@[expose] def pullback {machine : Transducer.Machine} (frame : Frame machine) (image : Line.GaussianLine) :
    Line.GaussianLine := Line.Matrix.act frame.adjugate image

/-- The retained adjugate operation is the mathematical pullback under the same retained matrix. -/
theorem pullbackEq {machine : Transducer.Machine} (frame : Frame machine) (image : Line.GaussianLine) :
    frame.pullback image = Line.Matrix.Gaussian.Mat2.pullback frame.matrix image :=
  congrArg (fun adjugate => Line.Matrix.act adjugate image) frame.adjugateEq

/-- Compute the affine quotient after one application of the retained inverse-chart cache. -/
@[expose] def affinePullback {machine : Transducer.Machine} (frame : Frame machine) (image : Line.GaussianLine) :
    Basic.Canonical :=
  let pulled := frame.pullback image
  Line.Gaussian.Proj.affineReading pulled

/-- The computed cached-chart quotient agrees with the mathematical affine pullback of that matrix. -/
theorem affinePullbackEq {machine : Transducer.Machine} (frame : Frame machine) (image : Line.GaussianLine) :
    frame.affinePullback image = Line.Matrix.Gaussian.Mat2.affinePullback frame.matrix image :=
  congrArg Line.Gaussian.Proj.affineReading (frame.pullbackEq image)

/-- Retain the original parser for a queued bit, or fold only the actual newly committed emission chunk. -/
@[expose] def followingParser {machine : Transducer.Machine} (frame : Frame machine)
    (result : Bool × Transducer.Machine) : Parser.State :=
  match machine.pending with
  | [] => (result.1 :: result.2.pending).foldl Parser.State.step frame.parser
  | _ :: _ => frame.parser

/-- Incremental parser preparation agrees with the actual next machine's complete committed-word parser. -/
private theorem followingParser_correct {machine : Transducer.Machine} (frame : Frame machine) :
    frame.followingParser (Transducer.Machine.Step.nextBit machine) =
      Parser.State.parse (Transducer.Machine.committed (Transducer.Machine.Step.nextBit machine).2) := by
  cases machine with
  | mk mode emitted pending =>
      cases pending with
      | cons bit rest =>
          change frame.parser = Parser.State.parse ((emitted ++ [bit]) ++ rest)
          rewrite [Data.List.Append.append_assoc]
          exact frame.parserEq
      | nil =>
          let emission := Emission.Step.step mode
          change ((Transducer.Machine.Step.consumeEmission emitted emission).1 ::
              (Transducer.Machine.Step.consumeEmission emitted emission).2.pending).foldl
                Parser.State.step frame.parser =
            Parser.State.parse (Transducer.Machine.committed
              (Transducer.Machine.Step.consumeEmission emitted emission).2)
          rewrite [Transducer.Machine.Step.consumeEmission_chunk,
            Transducer.Machine.Committed.consumeEmission_committed, Parser.State.parse_append]
          have parsed : frame.parser = Parser.State.parse emitted := by
            have original := frame.parserEq
            change frame.parser = Parser.State.parse (emitted ++ []) at original
            rewrite [Data.List.Append.append_nil] at original
            exact original
          exact congrArg (fun parser => emission.bits.foldl Parser.State.step parser) parsed

set_option genInjectivity false in
/-- One actual cached bit transition, retaining its original result and incrementally prepared next frame. -/
structure Step {machine : Transducer.Machine} (frame : Frame machine) where
  /-- The actual returned bit and same next machine, computed once. -/ result : Bool × Transducer.Machine
  /-- The result belongs to the original machine's actual next-bit procedure. -/ resultEq :
    result = Transducer.Machine.Step.nextBit machine
  /-- The next frame consumes this actual same returned machine. -/ after : Frame result.2
  /-- The parser is reused or folded only through this retained actual new chunk. -/ parserEq :
    after.parser = frame.followingParser result
  /-- A queued-bit transition retains every exact original chart cache. -/ pendingCaches : machine.pending ≠ [] →
    after.parser = frame.parser ∧ after.normalization = frame.normalization ∧
      after.matrix = frame.matrix ∧ after.adjugate = frame.adjugate

/-- Construct the next cached frame from one already retained original bit result.

The supplied complete result is consumed directly. A pending-bit transition
retains every chart cache; a new emission folds its exact returned chunk.
This constructor performs no source step or numerical source observation.
-/
def ofResult {machine : Transducer.Machine} (frame : Frame machine)
    (result : Bool × Transducer.Machine) (resultEq : result = Transducer.Machine.Step.nextBit machine) :
    Step frame := by
  cases pendingEq : machine.pending with
  | nil =>
      let parser := frame.followingParser result
      have parsed := ((congrArg frame.followingParser resultEq).trans (followingParser_correct frame)).trans
        (congrArg (fun returned : Bool × Transducer.Machine =>
          Parser.State.parse (Transducer.Machine.committed returned.2)) resultEq.symm)
      let after := ofParser result.2 parser parsed
      exact ⟨result, resultEq, after, ofParser_parser result.2 parser parsed,
        fun nonempty => (nonempty pendingEq).elim⟩
  | cons bit remaining =>
      have nonempty : machine.pending ≠ [] := by
        intro empty
        have impossible := pendingEq.symm.trans empty
        nomatch impossible
      have committedEq :=
        (congrArg (fun returned : Bool × Transducer.Machine => Transducer.Machine.committed returned.2) resultEq).trans
          (Transducer.Machine.Committed.nextBit_of_pending machine nonempty)
      have modeEq := (congrArg (fun returned : Bool × Transducer.Machine => returned.2.mode) resultEq).trans
        (Transducer.Machine.Step.nextBit_mode_of_pending machine nonempty)
      let normalizationEq := congrArg Cursor.Image.Mode.tailMatrix modeEq
      let after := frame.transport result.2 committedEq normalizationEq
      have retained := frame.transport_caches result.2 committedEq normalizationEq
      have parserEq : after.parser = frame.followingParser result := by
        unfold followingParser
        rewrite [pendingEq]
        exact retained.1
      exact ⟨result, resultEq, after, parserEq, fun _ => retained⟩

/-- Frame construction retains the supplied complete original bit result literally. -/
theorem ofResult_result {machine : Transducer.Machine} (frame : Frame machine)
    (result : Bool × Transducer.Machine) (resultEq : result = Transducer.Machine.Step.nextBit machine) :
    (frame.ofResult result resultEq).result = result := by
  cases machine with
  | mk mode emitted pending =>
      cases pending with
      | nil => rfl
      | cons bit remaining => rfl

/-- Execute one original next-bit procedure and consume its exact result in cached frame construction. -/
def nextBit {machine : Transducer.Machine} (frame : Frame machine) : Step frame :=
  let result := Transducer.Machine.Step.nextBit machine
  frame.ofResult result rfl

set_option genInjectivity false in
/-- One actual mode refinement retaining the original parser, normalization, image and adjugate caches. -/
structure Refinement {original : Transducer.Machine} (frame : Frame original)
    (target : Fraction.Rational) (positive : 0 < target) where
  /-- The actual refined original machine, computed once. -/ machine : Transducer.Machine
  /-- The retained machine is this same original refinement result. -/ machineEq :
    machine = Refinement.Machine.refine original target positive
  /-- The image frame belongs to the same retained refined machine. -/ after : Frame machine
  /-- The exact original parser is reused. -/ parserEq : after.parser = frame.parser
  /-- The exact original normalization factor is reused. -/ normalizationEq : after.normalization = frame.normalization
  /-- The exact original combined image matrix is reused. -/ matrixEq : after.matrix = frame.matrix
  /-- The exact original inverse-chart adjugate is reused. -/ adjugateEq : after.adjugate = frame.adjugate

/-- Reuse every original image-frame cache for the exact already returned machine refinement.

The complete supplied machine equality transports the original committed word
and normalization laws. This constructor performs no numerical source calls.
-/
def ofRefinement {machine : Transducer.Machine} (frame : Frame machine)
    (target : Fraction.Rational) (positive : 0 < target) (next : Transducer.Machine)
    (same : next = Refinement.Machine.refine machine target positive) : Refinement frame target positive := by
  let committedEq := (congrArg Transducer.Machine.committed same).trans
    (Refinement.Machine.refine_committed machine target positive)
  let normalizationEq := (congrArg (fun machine => Cursor.Image.Mode.tailMatrix machine.mode) same).trans
    (Cursor.Image.Mode.refine_tailMatrix machine.mode target positive)
  let after := frame.transport next committedEq normalizationEq
  have retained := frame.transport_caches next committedEq normalizationEq
  exact ⟨next, same, after, retained.1, retained.2.1, retained.2.2.1, retained.2.2.2⟩

/-- Refine the original mode once and reuse every unchanged retained image-frame cache. -/
def refine {machine : Transducer.Machine} (frame : Frame machine)
    (target : Fraction.Rational) (positive : 0 < target) : Refinement frame target positive :=
  frame.ofRefinement target positive (Refinement.Machine.refine machine target positive) rfl

/-- A frame rebuilt from an exact retained machine is the complete original refinement receipt. -/
theorem ofRefinement_eq {machine : Transducer.Machine} (frame : Frame machine)
    (target : Fraction.Rational) (positive : 0 < target) (next : Transducer.Machine)
    (same : next = Refinement.Machine.refine machine target positive) :
    frame.ofRefinement target positive next same = frame.refine target positive := by
  cases same
  rfl

end Frame

end Purelib.Data.CCL.Progressive.Cursor.Image.Machine

end
