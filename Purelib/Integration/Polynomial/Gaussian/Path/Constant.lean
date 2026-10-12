module

import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
public import Purelib.Integration.Polynomial.Gaussian.Cell.Constant
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
/-- An ordered list of cells with a retained constant-polynomial certificate for each cell. -/
inductive Basic.PathModel.ConstantCells : List Basic.CellModel ->
  Type
  /-- The empty cell list has a constant-cell certificate. -/ | nil :
    Basic.PathModel.ConstantCells []
  /-- Prepend the exact head cell's constant certificate to the retained tail certificate. -/ | cons {cell :
    Basic.CellModel} {cells : List Basic.CellModel}
      (head : cell.ConstantCertificate)
      (tail : Basic.PathModel.ConstantCells cells) :
        Basic.PathModel.ConstantCells (cell :: cells)

constructive_injectivity Basic.PathModel.ConstantCells

namespace Constant.PathModel.ConstantCells

open Purelib.Integration.Polynomial in
open Purelib.Integration.Polynomial.Gaussian.Cell in
/-- Append two retained constant-cell certificates in their original order. -/
def append : forall {first second :
  List Basic.CellModel},
    Gaussian.Path.Basic.PathModel.ConstantCells first -> Gaussian.Path.Basic.PathModel.ConstantCells second ->
      Gaussian.Path.Basic.PathModel.ConstantCells (first ++ second)
  | [], _, .nil, secondConstant => secondConstant
  | _ :: _, _, .cons head tail, secondConstant =>
      .cons head (append tail
        secondConstant)

end Constant.PathModel.ConstantCells
end PathModel

end Purelib.Integration.Polynomial.Gaussian.Path

end
