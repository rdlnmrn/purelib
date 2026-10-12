module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Data.ComplexContinuedFraction.CoordinateFloor.Transition
public import Purelib.Data.ContinuedFraction.Matrix
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.GaussianInt.Basic
public import Purelib.Data.GaussianInt.Cancellation
import Purelib.Data.GaussianInt.Constants
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.GaussianInt.Projective
public import Purelib.Geometry.Projective.GaussianInt.Embedding
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.LinearAlgebra.Coordinates2.Matrix

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.GaussianInt.Embedding
import Mathlib.Tactic.Ring
import Purelib.Data.Gaussian.Constants
public import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic.NormNum.Result
import Purelib.Tactic.Ring
public import Purelib.Data.ComplexContinuedFraction.CoordinateFloor.Contraction.Table

section
@[expose] public section

/-!
# Executable constructive coordinate-floor CCF encoder

The encoder groups at most three ordinary coordinate-floor clauses into one
well-founded recursive call.  Its measure is the natural squared norm of the
displayed uncancelled Gaussian denominator.
-/

namespace Purelib.Data.ComplexContinuedFraction.CoordinateFloor.Encoder

open Purelib in
open Purelib.Data in
open Purelib.Data.ContinuedFraction in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Construct the integral continued-fraction matrix with the supplied digit and integer gamma. -/
def digitMatrix (t : Data.GaussianInt) : (Matrix2
  Data.GaussianInt) := Matrix.cf t GaussianInt.gammaInt

open Purelib in
open Purelib.Data in
open Purelib.Data.ComplexContinuedFraction.CoordinateFloor in
open Purelib.Data.ContinuedFraction in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Projective in
/-- Embedding the integral digit matrix gives the canonical Gaussian continued-fraction matrix. -/
theorem map_digitMatrix (t : Data.GaussianInt) :
    GaussianInt.Embedding.mapMat (digitMatrix t) = Matrix.cf (GaussianInt.toGaussian t) Basic.Canonical.gamma :=
      by
  simp only [GaussianInt.Embedding.mapMat, digitMatrix, Matrix.cf,
    GaussianInt.toGaussian_gammaInt, GaussianInt.toGaussian_one, GaussianInt.toGaussian_zero,
    -eq_self, -iff_self]
  rfl

set_option genInjectivity false in
open Purelib in
open Purelib.Data in
open Purelib.Geometry.Projective in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Retain a finite coordinate-floor digit list and an integral matrix reconstructing its displayed source fraction.

The reconstruction acts on the projective point at infinity and retains equivalence to the original
numerator-denominator pair. The matrix and digit list are stored separately exactly as in the encoder contract. -/
structure DigitEncoding (fraction :
  GaussianInt.Fraction) where
  /-- The retained finite list of Gaussian-integer digits. -/ digits : List Data.GaussianInt
  /-- The retained integral reconstruction matrix. -/ matrix : Matrix2.SourceCCFEncoderIntegralMat2Alias
  /-- Evidence that this matrix sends infinity to the original displayed numerator-denominator pair. -/ reconstruct :
    (Line.Matrix.act matrix
      (Line.Proj.omega : Line.Basic.SourceCCFEncoderIntegralProjAlias)).Equivalent
      ⟨fraction.numerator, fraction.denominator⟩

constructive_injectivity DigitEncoding

section
open Purelib.Data
open Purelib.Data.ComplexContinuedFraction.CoordinateFloor
open Purelib.Data.ContinuedFraction
open Purelib.Geometry.Projective
/-- Construct the singleton digit encoding when the retained remainder is zero. -/
private def terminal (fraction :
  GaussianInt.Fraction)
    (remainderZero : Transition.remainder fraction = 0) : DigitEncoding fraction := by
  have numeratorIdentity : fraction.numerator = Transition.digit fraction * fraction.denominator := by
    rw [Transition.remainder] at remainderZero
    exact GaussianInt.eq_of_sub_eq_zero remainderZero
  refine ⟨[Transition.digit fraction], digitMatrix (Transition.digit fraction), ?_⟩
  rw [numeratorIdentity]
  dsimp only [digitMatrix, Line.Proj.Equivalent, Line.Matrix.act,
    Matrix.cf, Line.Proj.omega]
  ring1

/-- The current digit matrix maps the retained next fraction pair to an equivalent original fraction pair. -/
private theorem digit_step_reconstruct (fraction :
  GaussianInt.Fraction)
    (remainderNonzero : Transition.remainder fraction ≠ 0) :
    (Line.Matrix.act (digitMatrix (Transition.digit fraction))
      ⟨(Transition.next fraction remainderNonzero).numerator,
        (Transition.next fraction remainderNonzero).denominator⟩).Equivalent
      ⟨fraction.numerator, fraction.denominator⟩ := by
  dsimp only [digitMatrix, Line.Proj.Equivalent, Line.Matrix.act,
    Matrix.cf, Transition.next, Transition.remainder]
  apply GaussianInt.ext <;>
    simp only [GaussianInt.add_re,
      GaussianInt.add_im,
      GaussianInt.mul_re,
      GaussianInt.mul_im,
      GaussianInt.sub_re,
      GaussianInt.sub_im,
      GaussianInt.one_re,
      GaussianInt.one_im,
      GaussianInt.zero_re,
      GaussianInt.zero_im,
      GaussianInt.gammaInt] <;>
    ring1

/-- The current digit matrix maps a nonterminal next pair to a pair with nonzero denominator. -/
private theorem digit_step_den_ne (fraction :
  GaussianInt.Fraction)
    (remainderNonzero : Transition.remainder fraction ≠ 0) :
    (Line.Matrix.act (digitMatrix (Transition.digit fraction))
      ⟨(Transition.next fraction remainderNonzero).numerator,
        (Transition.next fraction remainderNonzero).denominator⟩).q ≠ 0 := by
  have denominatorIdentity :
      (Line.Matrix.act (digitMatrix (Transition.digit fraction))
        ⟨(Transition.next fraction remainderNonzero).numerator,
          (Transition.next fraction remainderNonzero).denominator⟩).q =
        GaussianInt.gammaInt * fraction.denominator := by
    dsimp only [digitMatrix, Line.Matrix.act, Matrix.cf, Transition.next]
    ring1
  rw [denominatorIdentity]
  exact GaussianInt.mul_ne_zero
    (show GaussianInt.gammaInt ≠ 0 by decide) fraction.denominatorNonzero

end

open Purelib.Data in
open Purelib.Data.ComplexContinuedFraction.CoordinateFloor in
open Purelib.Geometry.Projective in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Prepend the current digit and multiply its matrix by the retained tail matrix, preserving reconstruction. -/
private def prepend (fraction :
  GaussianInt.Fraction)
    (remainderNonzero : Transition.remainder fraction ≠ 0)
    (tail : DigitEncoding (Transition.next fraction remainderNonzero)) : DigitEncoding fraction :=
  let matrix := Matrix2.mul (digitMatrix (Transition.digit fraction)) tail.matrix
  ⟨Transition.digit fraction :: tail.digits, matrix, by
    dsimp only [matrix]
    rw [Line.Matrix.act_mul]
    have acted := Line.Matrix.act_respects_equivalent
      (digitMatrix (Transition.digit fraction)) tail.reconstruct
    exact GaussianInt.equivalent_trans_of_mid_q
      acted (digit_step_reconstruct fraction remainderNonzero)
      (digit_step_den_ne fraction remainderNonzero)⟩

open Purelib.Data in
open Purelib.Data.ComplexContinuedFraction.CoordinateFloor in
open Purelib.Data.ContinuedFraction in
open Purelib.Geometry.Projective in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Compute a finite coordinate-floor encoding with its integral reconstruction matrix.

Inspect up to three retained remainders before recurring on the third successor. Zero remainders produce terminal
digits; otherwise the original three-step denominator-norm descent supplies termination, and each preceding digit matrix
is retained in order. -/
def encodeResult (fraction : GaussianInt.Fraction)
  : DigitEncoding fraction :=
  let terminalHere : (current : GaussianInt.Fraction) → Transition.remainder current = 0 →
      DigitEncoding current := fun current remainderZero => by
    have numeratorIdentity : current.numerator = Transition.digit current * current.denominator := by
      rw [Transition.remainder] at remainderZero
      exact GaussianInt.eq_of_sub_eq_zero remainderZero
    refine ⟨[Transition.digit current], digitMatrix (Transition.digit current), ?_⟩
    rw [numeratorIdentity]
    dsimp only [digitMatrix, Line.Proj.Equivalent,
      Line.Matrix.act, Matrix.cf,
      Line.Proj.omega]
    ring1
  let prependHere : (current : GaussianInt.Fraction) →
      (remainderNonzero : Transition.remainder current ≠ 0) →
      DigitEncoding (Transition.next current remainderNonzero) → DigitEncoding current :=
    fun current remainderNonzero tail =>
      let matrix := Matrix2.mul
        (digitMatrix (Transition.digit current)) tail.matrix
      ⟨Transition.digit current :: tail.digits, matrix, by
        dsimp only [matrix]
        rw [Line.Matrix.act_mul]
        have acted := Line.Matrix.act_respects_equivalent
          (digitMatrix (Transition.digit current)) tail.reconstruct
        have stepReconstruct :
            (Line.Matrix.act (digitMatrix (Transition.digit current))
              ⟨(Transition.next current remainderNonzero).numerator,
                (Transition.next current remainderNonzero).denominator⟩).Equivalent
              ⟨current.numerator, current.denominator⟩ := by
          dsimp only [digitMatrix, Line.Proj.Equivalent,
            Line.Matrix.act,
            Matrix.cf, Transition.next, Transition.remainder]
          apply GaussianInt.ext <;>
            simp only [GaussianInt.add_re,
              GaussianInt.add_im,
              GaussianInt.mul_re,
              GaussianInt.mul_im,
              GaussianInt.sub_re,
              GaussianInt.sub_im,
              GaussianInt.one_re,
              GaussianInt.one_im,
              GaussianInt.zero_re,
              GaussianInt.zero_im,
              GaussianInt.gammaInt] <;>
            ring1
        have stepDenNonzero :
            (Line.Matrix.act (digitMatrix (Transition.digit current))
              ⟨(Transition.next current remainderNonzero).numerator,
                (Transition.next current remainderNonzero).denominator⟩).q ≠ 0 := by
          have denominatorIdentity :
              (Line.Matrix.act (digitMatrix (Transition.digit current))
                ⟨(Transition.next current remainderNonzero).numerator,
                  (Transition.next current remainderNonzero).denominator⟩).q =
                GaussianInt.gammaInt * current.denominator := by
            dsimp only [digitMatrix, Line.Matrix.act,
              Matrix.cf, Transition.next]
            ring1
          rw [denominatorIdentity]
          exact GaussianInt.mul_ne_zero
            (show GaussianInt.gammaInt ≠ 0 by decide) current.denominatorNonzero
        exact GaussianInt.equivalent_trans_of_mid_q
          acted stepReconstruct stepDenNonzero⟩
  if firstZero : Transition.remainder fraction = 0 then
    terminalHere fraction firstZero
  else
    let first := Transition.next fraction firstZero
    if secondZero : Transition.remainder first = 0 then
      prependHere fraction firstZero (terminalHere first secondZero)
    else
      let second := Transition.next first secondZero
      if thirdZero : Transition.remainder second = 0 then
        prependHere fraction firstZero
          (prependHere first secondZero (terminalHere second thirdZero))
      else
        let third := Transition.next second thirdZero
        prependHere fraction firstZero
          (prependHere first secondZero
            (prependHere second thirdZero (encodeResult
              third)))
termination_by GaussianInt.normNat fraction.denominator
decreasing_by exact Transition.three_den_descent fraction firstZero secondZero thirdZero

open Purelib in
open Purelib.Data in
open Purelib.Data.ComplexContinuedFraction.CoordinateFloor in
/-- Read the finite Gaussian-integer digit list from the certified coordinate-floor encoding. -/
def encode (fraction : GaussianInt.Fraction) : List
  Data.GaussianInt :=
  (encodeResult fraction).digits

open Purelib.Data in
open Purelib.Data.ComplexContinuedFraction.CoordinateFloor in
open Purelib.Geometry.Projective in
/-- The computed integral matrix sends infinity to a pair equivalent to the original displayed Gaussian fraction. -/
theorem encode_reconstruct_pair (fraction :
  GaussianInt.Fraction) :
    (Line.Matrix.act (encodeResult fraction).matrix
      (Line.Proj.omega : Line.Basic.SourceCCFEncoderIntegralProjAlias)).Equivalent
      ⟨fraction.numerator, fraction.denominator⟩ :=
  (encodeResult fraction).reconstruct

open Purelib.Data in
open Purelib.Data.ComplexContinuedFraction.CoordinateFloor in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Projective in
/-- Embedding the computed integral matrix sends infinity to the affine Gaussian readback of the source fraction. -/
theorem encode_reconstruct (fraction :
  GaussianInt.Fraction) :
    (Line.Matrix.act (GaussianInt.Embedding.mapMat (encodeResult fraction).matrix)
      (Line.Proj.omega : Line.Basic.SourceCCFEncoderProjAlias)).Equivalent
      (Line.Proj.affine fraction.value) := by
  have mapped := GaussianInt.Embedding.mapProj_equivalent (encodeResult fraction).reconstruct
  rw [GaussianInt.Embedding.mapProj_act, GaussianInt.Embedding.mapProj_omega] at mapped
  dsimp only [Line.Proj.Equivalent, GaussianInt.Embedding.mapProj, Line.Proj.affine] at mapped ⊢
  rw [Basic.mul_one]
  apply Field.mul_right_cancel_of_ne
    fraction.denominatorGaussianNonzero
  calc
    (Line.Matrix.act (GaussianInt.Embedding.mapMat (encodeResult fraction).matrix)
        (Line.Proj.omega : Line.Basic.SourceCCFEncoderProjAlias)).p * GaussianInt.toGaussian fraction.denominator =
        GaussianInt.toGaussian fraction.numerator *
          (Line.Matrix.act (GaussianInt.Embedding.mapMat (encodeResult fraction).matrix)
            (Line.Proj.omega : Line.Basic.SourceCCFEncoderProjAlias)).q := mapped
    _ = (fraction.value * GaussianInt.toGaussian fraction.denominator) *
          (Line.Matrix.act (GaussianInt.Embedding.mapMat (encodeResult fraction).matrix)
            (Line.Proj.omega : Line.Basic.SourceCCFEncoderProjAlias)).q := by rw [fraction.value_mul_denominator]
    _ = (fraction.value *
          (Line.Matrix.act (GaussianInt.Embedding.mapMat (encodeResult fraction).matrix)
            (Line.Proj.omega : Line.Basic.SourceCCFEncoderProjAlias)).q) * GaussianInt.toGaussian fraction.denominator
              := by
      rw [Basic.mul_assoc,
        Basic.mul_comm
          (GaussianInt.toGaussian fraction.denominator),
        ← Basic.mul_assoc]

end Purelib.Data.ComplexContinuedFraction.CoordinateFloor.Encoder

end
