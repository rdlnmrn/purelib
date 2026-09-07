import FTA.LocalExtraction
import FTA.Winding
import CCL.RationalEncoder

/-!
# The cubic worked example

This file verifies the exact rational data from Section 12 of the paper for
`f(Z) = Z³ - (1 + i)`: a dense Bézout squarefreeness certificate, the three
displayed isolating boxes and centers, their winding values, and the complete
finite CCL words of the centers.
-/

namespace FTA.CubicExample

open CCL CCL.GaussianRat
open FTA.ComputablePolynomial
open ComputablePolynomial.DensePolynomial
open FTA.PathPolynomial
open FTA.GaussianDerivative
open FTA.LocalExtraction
open FTA.Winding

/-- The polynomial `Z³ - (1 + i)` used in Section 12. -/
def cubic : GaussianPolynomial :=
  ⟨[1, 0, 0, GaussianRat.mk (-1) (-1)]⟩

/-- The executable derivative of the cubic is exactly `3Z²`. -/
theorem derivative_cubic :
    derivative cubic = ⟨[GaussianRat.mk 3 0, 0, 0]⟩ := by
  native_decide

/-- The explicit left Bézout coefficient `-1 / (1 + i)`. -/
def bezoutLeft : GaussianPolynomial :=
  ⟨[GaussianRat.mk (-1 / 2) (1 / 2)]⟩

/-- The explicit right Bézout coefficient `Z / (3(1 + i))`. -/
def bezoutRight : GaussianPolynomial :=
  ⟨[GaussianRat.mk (1 / 6) (-1 / 6), 0]⟩

/-- The paper's finite squarefreeness certificate for `Z³ - (1 + i)`. -/
def squarefreeCertificate : GaussianSquarefreeCertificate cubic where
  left := bezoutLeft
  right := bezoutRight
  identity := by
    rw [derivative_cubic]
    simp [bezoutLeft, bezoutRight, cubic,
      DensePolynomial.toPolynomial_eq_foldl_horner]
    have hconstantScalar :
        GaussianRat.mk (-1 / 2) (1 / 2) * GaussianRat.mk (-1) (-1) = 1 := by
      apply GaussianRat.ext <;> norm_num
    have hvariableScalar :
        GaussianRat.mk (-1 / 2) (1 / 2) +
          GaussianRat.mk (1 / 6) (-1 / 6) * GaussianRat.mk 3 0 = 0 := by
      apply GaussianRat.ext <;> norm_num
    have hconstant :
        Polynomial.C (GaussianRat.mk (-1 / 2) (1 / 2)) *
          Polynomial.C (GaussianRat.mk (-1) (-1)) = 1 := by
      rw [← map_mul, hconstantScalar, map_one]
    have hvariable :
        Polynomial.C (GaussianRat.mk (-1 / 2) (1 / 2)) +
          Polynomial.C (GaussianRat.mk (1 / 6) (-1 / 6)) *
            Polynomial.C (GaussianRat.mk 3 0) = 0 := by
      rw [← map_mul, ← map_add, hvariableScalar, map_zero]
    calc
      _ =
          (Polynomial.C (GaussianRat.mk (-1 / 2) (1 / 2)) +
            Polynomial.C (GaussianRat.mk (1 / 6) (-1 / 6)) *
              Polynomial.C (GaussianRat.mk 3 0)) * Polynomial.X ^ 3 +
            Polynomial.C (GaussianRat.mk (-1 / 2) (1 / 2)) *
              Polynomial.C (GaussianRat.mk (-1) (-1)) := by ring_nf
      _ = 1 := by rw [hvariable, hconstant]; simp

/-- First isolating box from the worked example. -/
def boxOne : RatBox where
  xLower := 138 / 128
  xUpper := 140 / 128
  yLower := 36 / 128
  yUpper := 38 / 128
  x_valid := by norm_num
  y_valid := by norm_num

/-- Second isolating box from the worked example. -/
def boxTwo : RatBox where
  xLower := -102 / 128
  xUpper := -101 / 128
  yLower := 101 / 128
  yUpper := 102 / 128
  x_valid := by norm_num
  y_valid := by norm_num

/-- Third isolating box from the worked example. -/
def boxThree : RatBox where
  xLower := -38 / 128
  xUpper := -36 / 128
  yLower := -140 / 128
  yUpper := -138 / 128
  x_valid := by norm_num
  y_valid := by norm_num

/-- Rational center displayed for the first box. -/
def centerOne : QI := GaussianRat.mk (139 / 128) (37 / 128)

/-- Rational center displayed for the second box. -/
def centerTwo : QI := GaussianRat.mk (-203 / 256) (203 / 256)

/-- Rational center displayed for the third box. -/
def centerThree : QI := GaussianRat.mk (-37 / 128) (-139 / 128)

theorem centers_are_box_centers :
    boxOne.center = centerOne ∧
      boxTwo.center = centerTwo ∧
      boxThree.center = centerThree := by
  native_decide

theorem centers_strictly_inside :
    boxOne.StrictContains centerOne ∧
      boxTwo.StrictContains centerTwo ∧
      boxThree.StrictContains centerThree := by
  norm_num [RatBox.StrictContains, boxOne, boxTwo, boxThree,
    centerOne, centerTwo, centerThree]

theorem centers_nonzero :
    centerOne ≠ 0 ∧ centerTwo ≠ 0 ∧ centerThree ≠ 0 := by
  native_decide

/-- Regression for the executable gcd cancellation: the first center enters
the encoder with denominator norm `8192`, rather than the uncancelled norm
`268435456`. -/
theorem centerOne_reduced_fraction :
    (RationalEncoder.fraction centerOne).num = ⟨88, -51⟩ ∧
      (RationalEncoder.fraction centerOne).den = ⟨64, -64⟩ := by
  native_decide

/-- Readable notation for the paper's displayed raw bit strings. -/
def bits (s : String) : Prefix.Word :=
  s.toList.map (fun character => character = '1')

/-- The first displayed box has ordinary winding one. -/
theorem boxOne_winding : boxWinding cubic boxOne = 1 := by
  native_decide

/-- The second displayed box has ordinary winding one. -/
theorem boxTwo_winding : boxWinding cubic boxTwo = 1 := by
  native_decide

/-- The third displayed box has ordinary winding one. -/
theorem boxThree_winding : boxWinding cubic boxThree = 1 := by
  native_decide

/-- The signed-remainder engine stores twice the edge indices displayed in
the paper; the resulting four-entry list has sum four on the first box. -/
theorem boxOne_doubled_edge_indices :
    (boxBoundary cubic boxOne).map PolynomialEdge.doubledWinding =
      [0, 2, 0, 2] := by
  native_decide

/-- Exact doubled edge-index data for the second box. -/
theorem boxTwo_doubled_edge_indices :
    (boxBoundary cubic boxTwo).map PolynomialEdge.doubledWinding =
      [2, 0, 2, 0] := by
  native_decide

/-- Exact doubled edge-index data for the third box. -/
theorem boxThree_doubled_edge_indices :
    (boxBoundary cubic boxThree).map PolynomialEdge.doubledWinding =
      [0, 2, 0, 2] := by
  native_decide

/-- Exact residual norm at the first displayed center. -/
theorem centerOne_residual_norm :
    normSq (cubic.eval centerOne) = 39952889 / 549755813888 := by
  native_decide

/-- Exact residual norm at the second displayed center. -/
theorem centerTwo_residual_norm :
    normSq (cubic.eval centerTwo) = 537358761 / 35184372088832 := by
  native_decide

/-- Exact residual norm at the third displayed center. -/
theorem centerThree_residual_norm :
    normSq (cubic.eval centerThree) = 39952889 / 549755813888 := by
  native_decide

/-- Complete finite CCL word of the first rational center. -/
theorem encode_centerOne :
    RationalEncoder.encode centerOne centers_nonzero.1 =
      bits "0000011001110000111100101100101101010101" := by
  native_decide

/-- Complete finite CCL word of the second rational center. -/
theorem encode_centerTwo :
    RationalEncoder.encode centerTwo centers_nonzero.2.1 =
      bits "0001111011011101101110110111011011110101" := by
  native_decide

/-- Complete finite CCL word of the third rational center. -/
theorem encode_centerThree :
    RationalEncoder.encode centerThree centers_nonzero.2.2 =
      bits "0011011000110000111101001100101100010011" := by
  native_decide

end FTA.CubicExample
