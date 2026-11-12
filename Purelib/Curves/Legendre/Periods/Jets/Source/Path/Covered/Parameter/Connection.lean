module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter.Strip
public import Purelib.Curves.Legendre.Periods.Jets.Connection.Matrix
import Purelib.Data.Gaussian.Norm.Basic

/-! # Connection coefficient bounds on the original retained common strip

The same original strip allocation pays the original frame's parameter
regularity request. The coefficient matrix therefore has a fixed rational
ceiling throughout the entire allocation, independent of source stages,
query requests, child counts and the admitted increment.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ParameterRange.StripAllocation

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Curves.Legendre.PicardFuchs.Clearance (ParameterClearance)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra
open Purelib.LinearAlgebra.Gaussian
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {count : Nat} {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count parents} {ranges : ParameterRange covered}

/-- Every increment admitted by the original common strip pays the original frame's parameter clearance allocation. -/
theorem parameter_admitted (allocation : StripAllocation ranges) (increment : Canonical)
    (admitted : Norm.Basic.normSq increment ≤ allocation.bound) :
    Norm.Basic.normSq increment ≤ (ParameterClearance.ofFrame frame).incrementBound :=
  admitted.trans (allocation.bound_le_regularBound.trans ranges.regularBound_le_parameterBound)

/-- The same strip payment derives one positive uniform denominator floor at the exact changed parameter. -/
theorem connectionDenominator_lower (allocation : StripAllocation ranges) (increment : Canonical)
    (admitted : Norm.Basic.normSq increment ≤ allocation.bound) :
    Connection.denominatorFloor (ParameterClearance.ofFrame frame) ≤
      Norm.Basic.normSq (ParameterClearance.connectionDenominator (parameter + increment)) :=
  Connection.denominatorFloor_le (ParameterClearance.ofFrame frame) increment
    (allocation.parameter_admitted increment admitted)

/-- The actual Legendre connection coefficient matrix has a fixed original-frame ceiling on this same common strip. -/
theorem connectionMatrix_le (allocation : StripAllocation ranges) (increment : Canonical)
    (admitted : Norm.Basic.normSq increment ≤ allocation.bound) :
    Norm.matrix (Connection.matrix (parameter + increment)) ≤
      Connection.matrixCeiling (ParameterClearance.ofFrame frame) :=
  Connection.matrix_le (ParameterClearance.ofFrame frame) increment
    (allocation.parameter_admitted increment admitted)

/-- The actual matrix-vector action retains its complete vector and the same fixed frame-derived coefficient ceiling. -/
theorem connectionMatrixVector_le (allocation : StripAllocation ranges) (increment : Canonical)
    (admitted : Norm.Basic.normSq increment ≤ allocation.bound) (values : Data.Vector Canonical 2) :
    Norm.vector (LinearAlgebra.Matrix.Multiplication.matrixVector
      (Connection.matrix (parameter + increment)) values) ≤
      2 * Connection.matrixCeiling (ParameterClearance.ofFrame frame) * Norm.vector values :=
  Connection.matrixVector_le (ParameterClearance.ofFrame frame) increment
    (allocation.parameter_admitted increment admitted) values

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ParameterRange.StripAllocation

end
