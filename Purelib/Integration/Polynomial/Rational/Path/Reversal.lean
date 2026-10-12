module

import Purelib.Data.Gaussian.Basic
import Purelib.Integration.Polynomial.Rational.Cell.Basic
public import Purelib.Integration.Polynomial.Rational.Cell.Reversal
public import Purelib.Integration.Polynomial.Rational.Path.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Integration.Polynomial.Rational.Cell.Basic (CellModel)

section
@[expose] public section

/-!
# General certified integration by finite path refinements

An integrand is supplied operationally: at each natural refinement it returns
one finite path of rational polynomial cell models and finite rational sample
certificates.  The integration program sums the exact polynomial cell
integrals.  A rational geometric modulus and a finite later-refinement
certificate turn those displayed sums into an ordinary productive CCL name.

There is no measure, completed partition, function-as-an-infinite-set, or
infinitesimal.  The only universal refinements are natural-number calls to the
supplied finite program.
-/

namespace Purelib.Integration.Polynomial.Rational.Path
section PathModel

open Purelib.Integration.Polynomial in
set_option genInjectivity false in
/-- Integral-preserving polynomial reversal certificates indexed by the exact ordered cell list.

Each constructor retains the original head cell and a certificate for its own polynomial, followed by the dependent tail
certificates. -/
inductive Basic.PathModel.ReversalCells : List
  CellModel → Type
  /-- Reversal evidence for the empty cell list. -/ | nil :
    Basic.PathModel.ReversalCells []
  /-- The original head cell's reversal certificate followed by certificates for the exact tail. -/ | cons {cell :
    CellModel} {remaining : List CellModel}
      (head : Rational.Cell.Basic.CellModel.ReversalCertificate cell)
      (tail : Basic.PathModel.ReversalCells remaining) :
        Basic.PathModel.ReversalCells (cell :: remaining)

constructive_injectivity Basic.PathModel.ReversalCells

namespace Reversal.PathModel.ReversalCells

open Purelib.Integration.Polynomial in
/-- Read the certified cells in reverse order, reversing each original cell's endpoints with its own polynomial
certificate. -/
def reversed : {cells : List
  CellModel} → Rational.Path.Basic.PathModel.ReversalCells cells → List
  CellModel
  | [], .nil => []
  | _ :: _, .cons head tail => (reversed
    tail) ++ [CellModel.reverse _ head]

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial in
/-- The reversed certified cell list has the negative of the original path integral sample. -/
theorem integralSample_reversed : ∀
  {cells : List CellModel}
    (certificate : Rational.Path.Basic.PathModel.ReversalCells cells),
    (Rational.Path.Basic.PathModel.mk (reversed
      certificate)).integralSample =
      -(Rational.Path.Basic.PathModel.mk cells).integralSample
  | [], .nil => by
      apply Basic.ext <;>
        simp only [reversed,
          Rational.Path.Basic.PathModel.integralSample, List.foldr_nil, Basic.neg_re, Basic.neg_im,
          Basic.zero_re, Basic.zero_im] <;> ring1
  | cell :: remaining, .cons head tail => by
      change
        (Rational.Path.Basic.PathModel.mk ((reversed tail) ++
          [CellModel.reverse cell head])).integralSample =
          -(Rational.Path.Basic.PathModel.mk (cell :: remaining)).integralSample
      rw [show Rational.Path.Basic.PathModel.mk ((reversed tail) ++
        [CellModel.reverse cell head]) =
          (Rational.Path.Basic.PathModel.mk (reversed tail)).concat
            (Rational.Path.Basic.PathModel.mk [CellModel.reverse cell head]) from rfl,
        Rational.Path.Basic.PathModel.integralSample_concat,
          integralSample_reversed tail,
        Rational.Path.Basic.PathModel.singleton_integralSample, CellModel.reverse_integralSample]
      change
        -(Rational.Path.Basic.PathModel.mk remaining).integralSample + -cell.integralSample =
          -(cell.integralSample + (Rational.Path.Basic.PathModel.mk remaining).integralSample)
      apply Basic.ext <;>
        simp only [Basic.add_re, Basic.add_im, Basic.neg_re, Basic.neg_im] <;> ring1

end Reversal.PathModel.ReversalCells

open Purelib.Integration.Polynomial in
set_option genInjectivity false in
/-- A collection of cell reversal certificates indexed by the exact original path cells. -/
structure Basic.PathModel.Reversal (path :
  Rational.Path.Basic.PathModel) where
  /-- The reversal certificates indexed by this path's exact cell list. -/ cells :
    Basic.PathModel.ReversalCells path.cells

constructive_injectivity Basic.PathModel.Reversal

open Purelib.Integration.Polynomial
/-- Construct the reversed path from its retained cell-indexed reversal certificates. -/
def Basic.PathModel.reverse (path : Rational.Path.Basic.PathModel)
  (certificate : Basic.PathModel.Reversal path) : Rational.Path.Basic.PathModel :=
  ⟨(Reversal.PathModel.ReversalCells.reversed certificate.cells)⟩

/-- The certified reversed path's integral sample is the negative of the original sample. -/
theorem Basic.PathModel.reverse_integralSample (path :
  Rational.Path.Basic.PathModel)
    (certificate : Basic.PathModel.Reversal path) :
    (path.reverse certificate).integralSample = -path.integralSample :=
  (Reversal.PathModel.ReversalCells.integralSample_reversed certificate.cells)

end PathModel

end Purelib.Integration.Polynomial.Rational.Path

end
