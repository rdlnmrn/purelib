module

import Purelib.Data.Gaussian.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
public import Purelib.Integration.Polynomial.Gaussian.Cell.Reversal
public import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-!
# Progressive finite integration with Gaussian coefficients

This is the period-facing integration kernel.  Every model is still a finite
list of rationally parameterized cells, but its local polynomial coefficients
are Gaussian rationals.  Hence a cell can approximate a genuinely complex
coefficient before multiplication by the complex path displacement.
-/

namespace Purelib.Integration.Polynomial.Gaussian.Path
section PathModel

open Purelib.Integration.Polynomial.Gaussian.Cell in
set_option genInjectivity false in
/-- An ordered family of reversal certificates indexed by the exact original cell list. -/
inductive Basic.PathModel.ReversalCells : List Basic.CellModel ->
  Type
  /-- Reversal evidence for the exact empty cell list. -/ | nil :
    Basic.PathModel.ReversalCells []
  /-- Retain the original head-cell reversal certificate and the exact tail's reversal evidence. -/ | cons {cell :
    Basic.CellModel} {remaining : List Basic.CellModel}
      (head : Basic.CellModel.ReversalCertificate cell)
      (tail : Basic.PathModel.ReversalCells remaining) :
        Basic.PathModel.ReversalCells (cell :: remaining)

constructive_injectivity Basic.PathModel.ReversalCells

namespace Reversal.PathModel.ReversalCells

open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Reverse the retained cell order and each cell's orientation using its exact certificate. -/
def reversed : {cells : List
  Basic.CellModel} -> Basic.PathModel.ReversalCells cells -> List Basic.CellModel
  | [], .nil => []
  | _ :: _, .cons head tail =>
      (reversed tail) ++
        [Basic.CellModel.reverse _ head]

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The certified reversed cell list has integral sample equal to the negative original path sample. -/
theorem integralSample_reversed :
  forall {cells : List Basic.CellModel}
    (certificate : Basic.PathModel.ReversalCells cells),
    (Basic.PathModel.mk (reversed certificate)).integralSample =
      -(Basic.PathModel.mk cells).integralSample
  | [], .nil => by
      apply Basic.ext <;>
        simp only [reversed, Basic.PathModel.integralSample, List.foldr_nil,
          Basic.neg_re, Basic.neg_im,
          Basic.zero_re, Basic.zero_im] <;> ring1
  | cell :: remaining, .cons head tail => by
      change
        (Basic.PathModel.mk
          ((reversed tail) ++ [Basic.CellModel.reverse cell head])).integralSample =
          -(Basic.PathModel.mk (cell :: remaining)).integralSample
      rw [show Basic.PathModel.mk
          ((reversed tail) ++ [Basic.CellModel.reverse cell head]) =
          (Basic.PathModel.mk (reversed tail)).concat
            (Basic.PathModel.mk [Basic.CellModel.reverse cell head]) from rfl,
        Basic.PathModel.integralSample_concat,
          integralSample_reversed tail,
        Basic.PathModel.singleton_integralSample, Basic.CellModel.reverse_integralSample]
      change
        -(Basic.PathModel.mk remaining).integralSample + -cell.integralSample =
          -(cell.integralSample + (Basic.PathModel.mk remaining).integralSample)
      apply Basic.ext <;>
        simp only [Basic.add_re, Basic.add_im, Basic.neg_re, Basic.neg_im] <;> ring1

end Reversal.PathModel.ReversalCells

open Purelib.Integration.Polynomial.Gaussian.Path in
set_option genInjectivity false in
/-- Retained cell-reversal evidence for one exact original polynomial path. -/
structure Basic.PathModel.Reversal (path : Basic.PathModel) where
  /-- The retained reversal certificates for the original path's exact cell list. -/ cells :
    Basic.PathModel.ReversalCells path.cells

constructive_injectivity Basic.PathModel.Reversal

open Purelib.Integration.Polynomial.Gaussian.Path
/-- Read the original path's certified cells in reversed order and orientation. -/
def Basic.PathModel.reverse (path : Basic.PathModel) (certificate :
  Basic.PathModel.Reversal path) : Basic.PathModel :=
  ⟨(Reversal.PathModel.ReversalCells.reversed certificate.cells)⟩

/-- The certified reversed polynomial path has the negative exact original integral sample. -/
theorem Basic.PathModel.reverse_integralSample (path :
  Basic.PathModel)
    (certificate : Basic.PathModel.Reversal path) :
    (path.reverse certificate).integralSample = -path.integralSample :=
  Reversal.PathModel.ReversalCells.integralSample_reversed certificate.cells

end PathModel

end Purelib.Integration.Polynomial.Gaussian.Path

end
