import CCL.Boundary.Curve.Clear
import CCL.Boundary.Curve.CoordinateFactorization
import RFAP.Sturm.EventPartition

/-!
# Constructive root events on rationally parameterized curves

The constant-gcd branch of `CurveClear` excludes a polynomial
root everywhere on a rational curve.  This module handles the complementary
finite cases.  If both cleared coordinates vanish identically it records that
degeneracy explicitly.  Otherwise a nonconstant gcd is an ordinary nonzero
coordinate polynomial, so its derivative/gcd Sturm chain has the executable
event partition constructed in `ConstructiveSturmEventPartition`.
-/

namespace CCL.CurveEvents

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev CoordinatePolynomial :=
  RFAP.ComputablePolynomial.DensePolynomial Coordinate
abbrev RationalCurve := CCL.RationalCurve.RationalCurve
abbrev Cell := RFAP.SturmEventPartition.Cell
abbrev Factor := CCL.CoordinateFactorization.Factor
abbrev Decomposition := CCL.CoordinateFactorization.Decomposition
abbrev LocatedFactor :=
  CCL.CoordinateFactorization.LocatedFactor

open RFAP.ComputablePolynomial.DensePolynomial

/-- At least one denominator-cleared coordinate is a represented nonzero
polynomial. -/
structure Nontrivial
    (p : GaussianPolynomial) (curve : RationalCurve) : Prop where
  coordinateNonzero :
    (CCL.CurveClear.realPolynomial p curve).isZero = false ∨
      (CCL.CurveClear.imaginaryPolynomial p curve).isZero = false

namespace Nontrivial

theorem gcdNonzero
    {p : GaussianPolynomial} {curve : RationalCurve}
    (data : Nontrivial p curve) :
    (CCL.CurveClear.gcdPolynomial p curve).isZero = false :=
  RFAP.ComputableGCD.gcd_isZero_false data.coordinateNonzero

end Nontrivial

/-- Total finite outcome of the cleared-coordinate gcd calculation. -/
inductive Analysis (p : GaussianPolynomial) (curve : RationalCurve) where
  | identicallyZero
      (realZero :
        (CCL.CurveClear.realPolynomial p curve).isZero = true)
      (imaginaryZero :
        (CCL.CurveClear.imaginaryPolynomial p curve).isZero = true)
  | clear (certificate : CCL.CurveClear.GlobalClear p curve)
  | events (data : Nontrivial p curve)
      (gcdDegreePositive :
        0 < (CCL.CurveClear.gcdPolynomial p curve).natDegree)

/-- Execute the complete finite trichotomy: identically-zero restriction,
constant nonzero gcd, or nonconstant root-event polynomial. -/
def analyze (p : GaussianPolynomial) (curve : RationalCurve) :
    Analysis p curve := by
  by_cases realNonzero :
      (CCL.CurveClear.realPolynomial p curve).isZero = false
  · let data : Nontrivial p curve := ⟨Or.inl realNonzero⟩
    by_cases degreeZero :
        (CCL.CurveClear.gcdPolynomial p curve).natDegree = 0
    · exact .clear ⟨data.coordinateNonzero, degreeZero⟩
    · exact .events data (Nat.zero_lt_of_ne_zero degreeZero)
  · have realZero :
        (CCL.CurveClear.realPolynomial p curve).isZero = true := by
      cases value :
          (CCL.CurveClear.realPolynomial p curve).isZero <;>
        simp_all
    by_cases imaginaryNonzero :
        (CCL.CurveClear.imaginaryPolynomial p curve).isZero = false
    · let data : Nontrivial p curve := ⟨Or.inr imaginaryNonzero⟩
      by_cases degreeZero :
          (CCL.CurveClear.gcdPolynomial p curve).natDegree = 0
      · exact .clear ⟨data.coordinateNonzero, degreeZero⟩
      · exact .events data (Nat.zero_lt_of_ne_zero degreeZero)
    · have imaginaryZero :
          (CCL.CurveClear.imaginaryPolynomial p curve).isZero =
            true := by
        cases value :
            (CCL.CurveClear.imaginaryPolynomial p curve).isZero <;>
          simp_all
      exact .identicallyZero realZero imaginaryZero

/-- The executable gcd vanishes at a displayed parameter exactly when both
cleared coordinate polynomials vanish there. -/
theorem gcd_eval_eq_zero_iff
    (p : GaussianPolynomial) (curve : RationalCurve)
    (parameter : Coordinate) :
    (CCL.CurveClear.gcdPolynomial p curve).eval parameter = 0 ↔
      (CCL.CurveClear.realPolynomial p curve).eval parameter = 0 ∧
        (CCL.CurveClear.imaginaryPolynomial p curve).eval
          parameter = 0 := by
  constructor
  · intro gcdZero
    constructor
    · have identity := RFAP.ComputableGCD.leftFactor_eval_identity
          (CCL.CurveClear.realPolynomial p curve)
          (CCL.CurveClear.imaginaryPolynomial p curve) parameter
      change (CCL.CurveClear.realPolynomial p curve).eval parameter =
        (CCL.CurveClear.gcdPolynomial p curve).eval parameter * _
          at identity
      rw [gcdZero, RFAP.ConstructiveFraction.zero_mul_direct] at identity
      exact identity
    · have identity := RFAP.ComputableGCD.rightFactor_eval_identity
          (CCL.CurveClear.realPolynomial p curve)
          (CCL.CurveClear.imaginaryPolynomial p curve) parameter
      change
        (CCL.CurveClear.imaginaryPolynomial p curve).eval parameter =
          (CCL.CurveClear.gcdPolynomial p curve).eval parameter * _
            at identity
      rw [gcdZero, RFAP.ConstructiveFraction.zero_mul_direct] at identity
      exact identity
  · rintro ⟨realZero, imaginaryZero⟩
    rw [CCL.CurveClear.gcdPolynomial,
      RFAP.ComputableGCD.gcd_eval_identity, realZero, imaginaryZero]
    rw [RFAP.ConstructiveFraction.mul_zero_direct,
      RFAP.ConstructiveFraction.mul_zero_direct,
      RFAP.ConstructiveFraction.zero_add]

/-- Away from an explicitly excluded curve pole, the univariate gcd event is
exactly a zero of the original Gaussian polynomial on the curve. -/
theorem gcd_eval_eq_zero_iff_curve_root
    (p : GaussianPolynomial) (curve : RationalCurve)
    (parameter : Coordinate)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    (CCL.CurveClear.gcdPolynomial p curve).eval parameter = 0 ↔
      p.eval (curve.point parameter) = 0 :=
  (gcd_eval_eq_zero_iff p curve parameter).trans
    (CCL.RationalCurve.cleared_pair_zero_iff
      p curve parameter denominatorNonzero)

/-- Repeated parameter factors are split by finite derivative-gcd recursion
before boundary ownership.  Every returned occurrence is squarefree and the
displayed product is exactly the normalized curve gcd. -/
def eventDecomposition
    {p : GaussianPolynomial} {curve : RationalCurve}
    (data : Nontrivial p curve)
    (degreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p curve).natDegree) :
    Decomposition (CCL.CurveClear.gcdPolynomial p curve) := by
  apply CCL.CoordinateFactorization.decomposeNormalized
  · exact (RFAP.ComputableGCD.extendedGCD
      (CCL.CurveClear.realPolynomial p curve)
      (CCL.CurveClear.imaginaryPolynomial p curve)).normalized
  · exact data.gcdNonzero
  · exact degreePositive

/-- A displayed rational curve root is assigned by an executable finite scan
to its first squarefree parameter factor. -/
def locateFactorRoot
    {p : GaussianPolynomial} {curve : RationalCurve}
    (data : Nontrivial p curve)
    (degreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p curve).natDegree)
    (parameter : Coordinate)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0)
    (root : p.eval (curve.point parameter) = 0) :
    LocatedFactor (eventDecomposition data degreePositive).factors
      parameter :=
  (eventDecomposition data degreePositive).locateRoot parameter
    ((gcd_eval_eq_zero_iff_curve_root p curve parameter
      denominatorNonzero).2 root)

abbrev EventPartition
    (p : GaussianPolynomial) (curve : RationalCurve) (root : Cell) :=
  RFAP.SturmEventPartition.EventPartition
    (RFAP.ComputableDerivative.derivative
      (CCL.CurveClear.gcdPolynomial p curve))
    (CCL.CurveClear.gcdPolynomial p curve) root

/-- Classify every leaf of a nonconstant curve-gcd Sturm calculation. -/
def eventPartition
    {p : GaussianPolynomial} {curve : RationalCurve}
    (data : Nontrivial p curve) (root : Cell) :
    EventPartition p curve root :=
  RFAP.SturmEventPartition.classifyEvents
    (RFAP.ComputableDerivative.derivative
      (CCL.CurveClear.gcdPolynomial p curve))
    (CCL.CurveClear.gcdPolynomial p curve)
    data.gcdNonzero root

/-- The parent doubled Sturm count is exactly the finite sum of its classified
leaf counts. -/
theorem eventPartition_count_sum
    {p : GaussianPolynomial} {curve : RationalCurve}
    (data : Nontrivial p curve) (root : Cell) :
    RFAP.SturmRootCount.sturmRootCount2
        (CCL.CurveClear.gcdPolynomial p curve)
        root.interval.lower root.interval.upper =
      (((eventPartition data root).tree.leaves.map fun leaf =>
        RFAP.SturmRootCount.sturmRootCount2
          (CCL.CurveClear.gcdPolynomial p curve)
          leaf.interval.lower leaf.interval.upper).sum) := by
  exact RFAP.SturmEventPartition.eventSubdivision_cellIndex2_sum
    (RFAP.ComputableDerivative.derivative
      (CCL.CurveClear.gcdPolynomial p curve))
    (CCL.CurveClear.gcdPolynomial p curve)
    data.gcdNonzero root

end CCL.CurveEvents
