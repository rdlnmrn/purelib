module
public import Purelib.Approximation.Matrix.Operational.Integral.Action

import Purelib.Approximation.Gaussian.Vector.Operational.Basic
import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.LinearAlgebra.Matrix.Integral.Word
import Init.Prelude

namespace Purelib.Approximation.Matrix.Operational.Integral.Word

open Purelib
open Purelib.Approximation.Gaussian.Vector.Operational.Basic
open Purelib.Approximation.Matrix.Operational.Integral
open Purelib.LinearAlgebra.Matrix
open Purelib.LinearAlgebra.Matrix.Integral

public section

/-!
# Finite-word Legendre fractional transport

This module folds convention-locked integral matrices and their precisely
indexed denominator preparations.  It keeps the unconditional homogeneous
matrix product separate from stepwise productive division, then proves that a
fully prepared fold agrees with one prepared quotient by the folded matrix.
For period transport it also reverses the generator list while transposing
each homology matrix, and proves that this finite fold is exactly the dual
`periodMatrix` action.
-/

open Purelib.Riemann.Integration.LegendreGaussManin
open Purelib.Riemann.Integration.LegendreFractionalAction

/-- Apply each matrix in traversal order to a homogeneous vector. -/
@[expose] def blockAction : List LinearAlgebra.Matrix.Basic.IntegralMatrix ->
  RawPeriodVector -> RawPeriodVector
  | [], values => values
  | matrix :: remaining, values =>
      Purelib.Approximation.Matrix.Operational.Integral.Word.blockAction remaining (Action.matrixAction matrix values)

/-- A finite block action is operationally the action of its exact folded matrix, with the convention-locked
multiplication order. -/
@[expose] def matrixProduct_action : (matrices : List LinearAlgebra.Matrix.Basic.IntegralMatrix) ->
    (values : RawPeriodVector) ->
      VectorEquivalent (Action.matrixAction (Word.matrixProduct matrices) values)
        (Approximation.Matrix.Operational.Integral.Word.blockAction matrices values)
  | [], values => Action.matrixAction_identity values
  | matrix :: remaining, values =>
      VectorEquivalent.trans
        (Action.matrixAction_mul (Word.matrixProduct remaining) matrix values)
        (Purelib.Approximation.Matrix.Operational.Integral.Word.matrixProduct_action remaining (Action.matrixAction
          matrix values))

end

end Purelib.Approximation.Matrix.Operational.Integral.Word
