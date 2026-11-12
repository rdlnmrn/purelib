module

public import Purelib.Data.CCL.Transducer.Mode.Exact
public import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.Data.CCL.Progressive.Cursor.Image
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.CCL.Transducer.Machine.Committed
import Purelib.Data.CCL.Transducer.Machine.Grammar.Basic

/-!
# Finite executable descriptions of retained rational cursors

The description stores finite mode code, both original words and the actual
parser, normalization, image and adjugate caches. Its interpreter and frame
projection consume those data directly. No original source, dependent state
type or source procedure is retained by the code.
-/

public section

namespace Purelib.Data.CCL.Transducer.Machine

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Data.CCL.Transducer
open Purelib.Data.CCL.Progressive
open Purelib.Data.CCL.Encoding
open Purelib.Data.Gaussian
open Purelib.Geometry.Projective
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2

set_option genInjectivity false in
/-- Finite numerical cursor code retains its exact words, phase description and all cached chart data. -/
structure Code where
  /-- The finite exact rational mode description. -/ mode : Mode.Code
  /-- The exact already exposed original word. -/ emitted : List Bool
  /-- The exact original queue waiting to be exposed. -/ pending : List Bool
  /-- The original committed-word parser cache. -/ parser : Parser.State
  /-- The original normalization-matrix cache. -/ normalization : Matrix2.GaussianMatrix
  /-- The original combined image-matrix cache. -/ matrix : Matrix2.GaussianMatrix
  /-- The original inverse-chart adjugate cache. -/ adjugate : Matrix2.GaussianMatrix
deriving @[expose] DecidableEq

namespace Code

/-- Equality of all finite description fields identifies the same cursor code. -/
theorem ext {left right : Code} (modeEq : left.mode = right.mode)
    (emittedEq : left.emitted = right.emitted) (pendingEq : left.pending = right.pending)
    (parserEq : left.parser = right.parser) (normalizationEq : left.normalization = right.normalization)
    (matrixEq : left.matrix = right.matrix) (adjugateEq : left.adjugate = right.adjugate) : left = right := by
  cases left
  cases right
  cases modeEq
  cases emittedEq
  cases pendingEq
  cases parserEq
  cases normalizationEq
  cases matrixEq
  cases adjugateEq
  rfl

set_option genInjectivity false in
/-- The numerical description certifies its mode bounds, exact original grammar and every retained cache. -/
structure Valid (code : Code) : Prop where
  /-- The finite mode description has its phase's required numerical payments. -/ modeValid : code.mode.Valid
  /-- The exact committed word owns the retained parser cache. -/ parserEq :
    code.parser = Parser.State.parse (code.emitted ++ code.pending)
  /-- The same interpreted mode owns the normalization cache. -/ normalizationEq :
    code.normalization = Cursor.Image.Mode.tailMatrix (code.mode.interpret modeValid)
  /-- The image cache consumes the exact retained two factors. -/ factorsEq :
    code.matrix = Matrix2.mul code.parser.matrix code.normalization
  /-- The adjugate consumes the exact retained image cache. -/ adjugateEq :
    code.adjugate = Matrix2.BoundaryAdjugate.adjugate code.matrix
  /-- The actual retained chart is nonsingular. -/ determinantNonzero : Matrix2.Matrix2.determinant code.matrix ≠ 0
  /-- The retained parser phase belongs to the same interpreted mode. -/ grammar :
    code.parser.phase = Mode.Grammar.modeRawPhase (code.mode.interpret modeValid)

/-- Interpret the original finite words and mode description without invoking any original source callback. -/
@[expose] def interpret (code : Code) (valid : Valid code) : Machine :=
  ⟨code.mode.interpret valid.modeValid, code.emitted, code.pending⟩

/-- Project the same retained parser and chart caches into the actual interpreted cursor frame. -/
def frame (code : Code) (valid : Valid code) : Cursor.Image.Machine.Frame (code.interpret valid) :=
  { parser := code.parser
    parserEq := valid.parserEq
    normalization := code.normalization
    normalizationEq := valid.normalizationEq
    matrix := code.matrix
    factorsEq := valid.factorsEq
    matrixEq := valid.factorsEq.trans
      (congrArg₂ Matrix2.mul (congrArg Parser.State.matrix valid.parserEq) valid.normalizationEq)
    adjugate := code.adjugate
    adjugateEq := valid.adjugateEq
    determinantNonzero := valid.determinantNonzero }

/-- Frame projection retains all four exact numerical caches from its finite code. -/
private theorem frame_specification (code : Code) (valid : Valid code) :
    let projected := code.frame valid
    projected.parser = code.parser ∧ projected.normalization = code.normalization ∧
      projected.matrix = code.matrix ∧ projected.adjugate = code.adjugate := ⟨rfl, rfl, rfl, rfl⟩

/-- The public interpreted-frame projection reuses every exact retained parser and chart cache. -/
theorem frame_caches (code : Code) (valid : Valid code) :
    let projected := code.frame valid
    projected.parser = code.parser ∧ projected.normalization = code.normalization ∧
      projected.matrix = code.matrix ∧ projected.adjugate = code.adjugate := frame_specification code valid

/-- The interpreted finite cursor has the exact retained committed-word grammar. -/
theorem grammar (code : Code) (valid : Valid code) : Machine.Grammar.Invariant (code.interpret valid) :=
  (congrArg Parser.State.phase valid.parserEq).symm.trans valid.grammar

/-- The finite interpreter's image consumes the exact retained matrix at every supplied rational coordinate. -/
theorem imageEq (code : Code) (valid : Valid code) (candidate : Basic.Canonical) :
    Cursor.Image.Machine.image (code.interpret valid) candidate =
      Line.Matrix.act code.matrix (Line.Proj.affine candidate) :=
  (Cursor.Image.Machine.image_eq_act_imageMatrix (code.interpret valid) candidate).trans
    (congrArg (fun matrix => Line.Matrix.act matrix (Line.Proj.affine candidate))
      ((code.frame valid).matrixEq.symm.trans (code.frame_caches valid).2.2.1))

/-- A finite valid cursor representing an affine rational reading has that exact singleton origin. -/
theorem exactCursor (code : Code) (valid : Valid code) (point : Basic.Canonical)
    (represented : (Line.Matrix.act code.matrix (Line.Proj.affine code.mode.value)).Equivalent
      (Line.Proj.affine point)) :
    Machine.Semantics.Basic.ExactCursor (Process.exact point) () (code.interpret valid) where
  grammar := code.grammar valid
  exact := by
    intro candidate possible
    have equal := (code.mode.interpret_possible valid.modeValid candidate).mp possible
    cases equal
    refine ⟨point, rfl, ?_⟩
    change (Cursor.Image.Machine.image (code.interpret valid) code.mode.value).Equivalent (Line.Proj.affine point)
    exact (code.imageEq valid code.mode.value).symm ▸ represented

set_option genInjectivity false in
/-- Retain original frame and mode-realization parents beside their finite numerical cursor description. -/
structure Description {original : Machine} (frame : Cursor.Image.Machine.Frame original)
    (realization : Mode.Exact.Realization original.mode) where
  /-- The actual finite description built from the original data. -/ code : Code
  /-- Complete mode, grammar and cache validity of that same description. -/ valid : Valid code
  /-- The original realized mode description is reused. -/ modeEq : code.mode = realization.code
  /-- The exact exposed word is retained. -/ emittedEq : code.emitted = original.emitted
  /-- The exact pending word is retained. -/ pendingEq : code.pending = original.pending
  /-- The exact original parser cache is retained. -/ parserEq : code.parser = frame.parser
  /-- The exact original normalization cache is retained. -/ normalizationEq : code.normalization = frame.normalization
  /-- The exact original image cache is retained. -/ matrixEq : code.matrix = frame.matrix
  /-- The exact original adjugate cache is retained. -/ adjugateEq : code.adjugate = frame.adjugate

/-- Describe an exact original cursor realization using its existing words, parser and chart caches. -/
def ofRealization {original : Machine} (frame : Cursor.Image.Machine.Frame original)
    (realization : Mode.Exact.Realization original.mode) (grammar : Machine.Grammar.Invariant original) :
    Description frame realization := by
  let code : Code :=
    ⟨realization.code, original.emitted, original.pending, frame.parser,
      frame.normalization, frame.matrix, frame.adjugate⟩
  have normalizationEq : code.normalization = Cursor.Image.Mode.tailMatrix (code.mode.interpret realization.valid) :=
    frame.normalizationEq.trans
      (realization.normalizationEq.symm.trans (congrArg Cursor.Image.Mode.tailMatrix realization.modeEq))
  have phaseEq : frame.parser.phase = Mode.Grammar.modeRawPhase (code.mode.interpret realization.valid) :=
    ((congrArg Parser.State.phase frame.parserEq).trans grammar).trans
      (realization.phaseEq.symm.trans (congrArg Mode.Grammar.modeRawPhase realization.modeEq))
  let valid : Valid code :=
    ⟨realization.valid, frame.parserEq, normalizationEq, frame.factorsEq,
      frame.adjugateEq, frame.determinantNonzero, phaseEq⟩
  exact ⟨code, valid, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

namespace Description

/-- Every possible interpreted tail is the same selected rational reading of the retained original realization. -/
theorem possible_value {original : Machine} {frame : Cursor.Image.Machine.Frame original}
    {realization : Mode.Exact.Realization original.mode} (description : Description frame realization)
    {candidate : Basic.Canonical}
    (possible : Mode.Semantics.SemanticMode.possible (description.code.interpret description.valid).mode candidate) :
    candidate = realization.value :=
  ((description.code.mode.interpret_possible description.valid.modeValid candidate).mp possible).trans
    ((congrArg Mode.Code.value description.modeEq).trans realization.codeValueEq)

/-- The interpreted cursor image uses the same retained original matrix cache at every supplied rational coordinate. -/
theorem imageEq {original : Machine} {frame : Cursor.Image.Machine.Frame original}
    {realization : Mode.Exact.Realization original.mode} (description : Description frame realization)
    (candidate : Basic.Canonical) :
    Cursor.Image.Machine.image (description.code.interpret description.valid) candidate = frame.image candidate :=
  (Cursor.Image.Machine.image_eq_act_imageMatrix (description.code.interpret description.valid) candidate).trans
    (congrArg (fun matrix => Line.Matrix.act matrix (Line.Proj.affine candidate))
      ((description.code.frame description.valid).matrixEq.symm.trans
        ((description.code.frame_caches description.valid).2.2.1.trans description.matrixEq)))

/-- A represented affine reading gives the finite-code cursor an exact singleton origin for all later advances. -/
theorem exactCursor {original : Machine} {frame : Cursor.Image.Machine.Frame original}
    {realization : Mode.Exact.Realization original.mode} (description : Description frame realization)
    (value : Basic.Canonical) (represented : (frame.image realization.value).Equivalent (Line.Proj.affine value)) :
    Machine.Semantics.Basic.ExactCursor (Process.exact value) () (description.code.interpret description.valid) where
  grammar := description.code.grammar description.valid
  exact := by
    intro candidate possible
    have equal := description.possible_value possible
    cases equal
    refine ⟨value, rfl, ?_⟩
    change (Cursor.Image.Machine.image (description.code.interpret description.valid) realization.value).Equivalent
      (Line.Proj.affine value)
    exact (description.imageEq realization.value).symm ▸ represented

end Description

end Code

end Purelib.Data.CCL.Transducer.Machine

end
