module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank
import Purelib.Curves.Hyperelliptic.Periods.Pairing
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
public import Purelib.LinearAlgebra.Gaussian.ImaginaryPositive
import Purelib.LinearAlgebra.Gaussian.QuadraticForm
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Rational.FiniteSum.Small
public import Purelib.LinearAlgebra.Rational.Vector.Ones
import Purelib.Riemann.Integration.PreparedRefinementPrograms
import Purelib.Riemann.Periods.PeriodMatrix
public import Purelib.Riemann.Periods.PeriodCurves
public import Purelib.Riemann.Periods.PeriodTheorem
import Purelib.Topology.BranchedCover.Double.Attachment
import Purelib.Topology.Surface.CellularHomology
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Data.Gaussian.Basic
import Purelib.Topology.BranchedCover
import Purelib.Curves.Hyperelliptic.Topology.Profile
import Purelib.Approximation.Gaussian.Name.Coherent
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Curves.Hyperelliptic.Periods.Pairing (StokesClosure)

section
@[expose] public section

/-!
# Worked finite hyperelliptic period examples

This module records explicit squarefree cyclic curves for the worked examples
of the finite period theorem.  Every polynomial is the concrete finite dense
power polynomial `Z^d - 1`.  Its nonzeroness, degree, and displayed Bézout
identity are proved by the finite power-monodromy algebra, so the examples
introduce no separate squarefreeness assumption.

The five nontrivial examples are

* `y² = x³ - 1` and `y² = x⁴ - 1` in genus one;
* `y² = x⁵ - 1` and `y² = x⁶ - 1` in genus two;
* `y² = x⁷ - 1` in genus three.

Two genus-zero controls, `y² = x - 1` and `y² = x² - 1`, exercise the
complete unconditional theorem and its genuinely empty period matrix.

The topology statements below compute the classical Euler characteristics
`0`, `-2`, and `-4` and expose the expected symplectic intersection basis.
The analytic period conclusions use the unconditional public theorem on
these same curves. The separate exact matrix examples below are algebraic
models, not period-program evaluations.
-/

namespace Purelib.Examples.Curves.Hyperelliptic.Periods.Worked

open Purelib.Data.Rat

open Purelib.Riemann.Periods
open Purelib.Examples
open Purelib.LinearAlgebra.Gaussian
open Purelib.Riemann.Integration
open Purelib.Curves.Hyperelliptic
open Purelib
open Purelib.Data

open Purelib.LinearAlgebra.Rational.Vector
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank (PairedPeriodBank)

open Purelib.Riemann.Periods.PeriodCurves

/-! ## Computed classical topology -/

/-- The displayed linear curve's original cell model has Euler characteristic 2. -/
theorem linear_eulerCharacteristic :
    linearCurve.cellModel.eulerCharacteristic = 2 := by
  exact linearCurve.cellModel_eulerCharacteristic.trans (by decide +kernel)

/-- The displayed quadratic curve's original cell model has Euler characteristic 2. -/
theorem quadratic_eulerCharacteristic :
    quadraticCurve.cellModel.eulerCharacteristic = 2 := by
  exact quadraticCurve.cellModel_eulerCharacteristic.trans (by decide +kernel)

/-- The displayed cubic curve's original cell model has Euler characteristic 0. -/
theorem cubic_eulerCharacteristic :
    cubicCurve.cellModel.eulerCharacteristic = 0 := by
  simpa using cubicCurve.cellModel_eulerCharacteristic

/-- The displayed quartic curve's original cell model has Euler characteristic 0. -/
theorem quartic_eulerCharacteristic :
    quarticCurve.cellModel.eulerCharacteristic = 0 := by
  simpa using quarticCurve.cellModel_eulerCharacteristic

/-- The displayed quintic curve's original cell model has Euler characteristic -2. -/
theorem quintic_eulerCharacteristic :
    quinticCurve.cellModel.eulerCharacteristic = -2 := by
  simpa using quinticCurve.cellModel_eulerCharacteristic

/-- The displayed sextic curve's original cell model has Euler characteristic -2. -/
theorem sextic_eulerCharacteristic :
    sexticCurve.cellModel.eulerCharacteristic = -2 := by
  simpa using sexticCurve.cellModel_eulerCharacteristic

/-- The displayed septic curve's original cell model has Euler characteristic -4. -/
theorem septic_eulerCharacteristic :
    septicCurve.cellModel.eulerCharacteristic = -4 := by
  simpa using septicCurve.cellModel_eulerCharacteristic

/-! ## Complete genus-zero controls -/

/-- The retained period-theorem result for the displayed linear curve.

Keeps the original curve, symplectic basis and certified normalized period construction at genus 0. -/
def linearPeriodTheorem :
    PeriodTheorem.Result linearCurve :=
  PeriodTheorem.riemann_period_theorem_genus_zero
    linearCurve

/-- The retained period-theorem result for the displayed quadratic curve.

Keeps the original curve, symplectic basis and certified normalized period construction at genus 0. -/
def quadraticPeriodTheorem :
    PeriodTheorem.Result quadraticCurve :=
  PeriodTheorem.riemann_period_theorem_genus_zero
    quadraticCurve

/-- The retained linear period-theorem basis has exactly 1 branch sites. -/
theorem linear_periodBranchPointCount :
    linearPeriodTheorem.basis.model.family.cuts.configuration.branches.siteCount =
      1 :=
  linearPeriodTheorem.branchPointCount.trans linear_degree

/-- The retained quadratic period-theorem basis has exactly 2 branch sites. -/
theorem quadratic_periodBranchPointCount :
    quadraticPeriodTheorem.basis.model.family.cuts.configuration.branches.siteCount
      =
      2 :=
  quadraticPeriodTheorem.branchPointCount.trans quadratic_degree

/-- The genus-zero linear curve has no normalized-period row index. -/
theorem linear_omega_index_impossible (row : Fin 0) : False
  :=
  Fin.elim0 row

/-- No genus-zero rational vector has a retained nonzero coefficient witness. -/
theorem quadratic_nonzero_vector_impossible
    (vector : QuadraticForm.RationalVector 0)
    (nonzero : QuadraticForm.NonzeroVector vector) : False :=
  Fin.elim0 nonzero.index

/-! ## Explicit symplectic bases -/

section
open Purelib.Curves.Hyperelliptic.Branches
/-- The original symplectic cut basis for the displayed cubic curve. -/
def cubicBasis := BranchCutLifts.symplecticBasis cubicCurve
/-- The original symplectic cut basis for the displayed quartic curve. -/
def quarticBasis := BranchCutLifts.symplecticBasis
  quarticCurve
/-- The original symplectic cut basis for the displayed quintic curve. -/
def quinticBasis := BranchCutLifts.symplecticBasis
  quinticCurve
/-- The original symplectic cut basis for the displayed sextic curve. -/
def sexticBasis := BranchCutLifts.symplecticBasis
  sexticCurve
/-- The original symplectic cut basis for the displayed septic curve. -/
def septicBasis := BranchCutLifts.symplecticBasis
  septicCurve

end

section
/-- The retained cubic cut basis has exactly 3 branch sites. -/
theorem cubic_branchPointCount :
    cubicBasis.family.cuts.configuration.branches.siteCount = 3 := by
  exact cubicBasis.family.cuts.configuration.branches.count_eq.trans
    cubic_degree

/-- The retained quartic cut basis has exactly 4 branch sites. -/
theorem quartic_branchPointCount :
    quarticBasis.family.cuts.configuration.branches.siteCount = 4 := by
  exact quarticBasis.family.cuts.configuration.branches.count_eq.trans
    quartic_degree

/-- The retained quintic cut basis has exactly 5 branch sites. -/
theorem quintic_branchPointCount :
    quinticBasis.family.cuts.configuration.branches.siteCount = 5 := by
  exact quinticBasis.family.cuts.configuration.branches.count_eq.trans
    quintic_degree

/-- The retained sextic cut basis has exactly 6 branch sites. -/
theorem sextic_branchPointCount :
    sexticBasis.family.cuts.configuration.branches.siteCount = 6 := by
  exact sexticBasis.family.cuts.configuration.branches.count_eq.trans
    sextic_degree

/-- The retained septic cut basis has exactly 7 branch sites. -/
theorem septic_branchPointCount :
    septicBasis.family.cuts.configuration.branches.siteCount = 7 := by
  exact septicBasis.family.cuts.configuration.branches.count_eq.trans
    septic_degree

open Purelib.Topology.Surface
/-- The original cubic basis a- and b-traces have intersection one. -/
theorem cubic_a_b_intersection :
    CellularHomology.intersection
      (cubicBasis.aTrace 0) (cubicBasis.bTrace
        0) = 1 := by
  exact (cubicBasis.a_b (0 : Fin 1) (0 : Fin 1)).trans
    (if_pos rfl)

/-- The original quartic basis a- and b-traces have intersection one. -/
theorem quartic_a_b_intersection :
    CellularHomology.intersection
      (quarticBasis.aTrace 0)
        (quarticBasis.bTrace 0) = 1 := by
  exact (quarticBasis.a_b (0 : Fin 1) (0 : Fin 1)).trans
    (if_pos rfl)

/-- The retained quintic a- and b-traces have the identity intersection matrix.

For the original genus-2 labels, matching indices intersect once and different indices have zero intersection. -/
theorem quintic_symplectic_intersections (left right : Fin
  2) :
    CellularHomology.intersection
        (quinticBasis.aTrace left)
          (quinticBasis.bTrace right) =
      if left = right then 1 else 0 :=
  quinticBasis.a_b left right

/-- The retained sextic a- and b-traces have the identity intersection matrix.

For the original genus-2 labels, matching indices intersect once and different indices have zero intersection. -/
theorem sextic_symplectic_intersections (left right : Fin 2)
  :
    CellularHomology.intersection
        (sexticBasis.aTrace left)
          (sexticBasis.bTrace right) =
      if left = right then 1 else 0 :=
  sexticBasis.a_b left right

/-- The retained septic a- and b-traces have the identity intersection matrix.

For the original genus-3 labels, matching indices intersect once and different indices have zero intersection. -/
theorem septic_symplectic_intersections (left right : Fin 3)
  :
    CellularHomology.intersection
        (septicBasis.aTrace left)
          (septicBasis.bTrace right) =
      if left = right then 1 else 0 :=
  septicBasis.a_b left right

/-! ## Analytic theorem entry points -/

end

/-- The automatically prepared standard period data for the original cubic curve. -/
def cubicStandardPeriodData :
    PeriodMatrix.PeriodData cubicCurve :=
  PreparedRefinementPrograms.automaticStandardPeriodData
    cubicCurve

/-- The automatically prepared standard period data for the original quartic curve. -/
def quarticStandardPeriodData :
    PeriodMatrix.PeriodData quarticCurve :=
  PreparedRefinementPrograms.automaticStandardPeriodData
    quarticCurve

/-- The automatically prepared standard period data for the original quintic curve. -/
def quinticStandardPeriodData :
    PeriodMatrix.PeriodData quinticCurve :=
  PreparedRefinementPrograms.automaticStandardPeriodData
    quinticCurve

/-- The automatically prepared standard period data for the original sextic curve. -/
def sexticStandardPeriodData :
    PeriodMatrix.PeriodData sexticCurve :=
  PreparedRefinementPrograms.automaticStandardPeriodData
    sexticCurve

/-- The standard cubic period cycles realize the original ordered cut basis.

Retains the actual paired period bank and its exact symplectic cycle-realization certificate. -/
theorem cubicStandardPeriodData_realizes_basis :
    PreparedRefinementPrograms.SymplecticCycleRealization
      cubicCurve cubicStandardPeriodData.cycles
      (PreparedRefinementPrograms.PeriodCycleBasis.ofOrdered
        (PairedPeriodBank.ofCurve cubicCurve)).cycles := by
  exact
    PreparedRefinementPrograms.automaticStandardPeriodData_realization
      cubicCurve

/-- The standard quartic period cycles realize the original ordered cut basis.

Retains the actual paired period bank and its exact symplectic cycle-realization certificate. -/
theorem quarticStandardPeriodData_realizes_basis :
    PreparedRefinementPrograms.SymplecticCycleRealization
      quarticCurve quarticStandardPeriodData.cycles
      (PreparedRefinementPrograms.PeriodCycleBasis.ofOrdered
        (PairedPeriodBank.ofCurve quarticCurve)).cycles := by
  exact
    PreparedRefinementPrograms.automaticStandardPeriodData_realization
      quarticCurve

/-- The standard quintic period cycles realize the original ordered cut basis.

Retains the actual paired period bank and its exact symplectic cycle-realization certificate. -/
theorem quinticStandardPeriodData_realizes_basis :
    PreparedRefinementPrograms.SymplecticCycleRealization
      quinticCurve quinticStandardPeriodData.cycles
      (PreparedRefinementPrograms.PeriodCycleBasis.ofOrdered
        (PairedPeriodBank.ofCurve quinticCurve)).cycles := by
  exact
    PreparedRefinementPrograms.automaticStandardPeriodData_realization
      quinticCurve

/-- The standard sextic period cycles realize the original ordered cut basis.

Retains the actual paired period bank and its exact symplectic cycle-realization certificate. -/
theorem sexticStandardPeriodData_realizes_basis :
    PreparedRefinementPrograms.SymplecticCycleRealization
      sexticCurve sexticStandardPeriodData.cycles
      (PreparedRefinementPrograms.PeriodCycleBasis.ofOrdered
        (PairedPeriodBank.ofCurve sexticCurve)).cycles := by
  exact
    PreparedRefinementPrograms.automaticStandardPeriodData_realization
      sexticCurve

/-- The genus-one Stokes closure for the supplied original cubic period data. -/
def cubicStokesClosure
    (data : PeriodMatrix.PeriodData cubicCurve) :
    StokesClosure data :=
  StokesClosure.genusOne data

/-- The genus-one Stokes closure for the supplied original quartic period data. -/
def quarticStokesClosure
    (data : PeriodMatrix.PeriodData quarticCurve) :
    StokesClosure data :=
  StokesClosure.genusOne data

/-! Unconditional named clients of the generic curve theorem. -/

/-- The retained period-theorem result for the displayed cubic curve.

Keeps the original curve, symplectic basis and certified normalized period construction at genus 1. -/
def cubicPeriodTheorem (_token : Unit) :
    PeriodTheorem.Result cubicCurve :=
  PeriodTheorem.riemann_period_theorem
    cubicCurve

/-- The retained period-theorem result for the displayed quartic curve.

Keeps the original curve, symplectic basis and certified normalized period construction at genus 1. -/
def quarticPeriodTheorem (_token : Unit) :
    PeriodTheorem.Result quarticCurve :=
  PeriodTheorem.riemann_period_theorem
    quarticCurve

/-- The retained period-theorem result for the displayed quintic curve.

Keeps the original curve, symplectic basis and certified normalized period construction at genus 2. -/
def quinticPeriodTheorem (_token : Unit) :
    PeriodTheorem.Result quinticCurve :=
  PeriodTheorem.riemann_period_theorem
    quinticCurve

/-- The retained period-theorem result for the displayed sextic curve.

Keeps the original curve, symplectic basis and certified normalized period construction at genus 2. -/
def sexticPeriodTheorem (_token : Unit) :
    PeriodTheorem.Result sexticCurve :=
  PeriodTheorem.riemann_period_theorem
    sexticCurve

/-- The retained period-theorem result for the displayed septic curve.

Keeps the original curve, symplectic basis and certified normalized period construction at genus 3. -/
def septicPeriodTheorem (_token : Unit) :
    PeriodTheorem.Result septicCurve :=
  PeriodTheorem.riemann_period_theorem
    septicCurve

/-! Each worked curve now exposes the two familiar conclusions through its
own theorem result: symmetry for every matrix entry, and a strictly positive
imaginary quadratic form for the displayed all-ones vector. -/

/-- Symmetry of the retained normalized cubic period entries.

Uses the original genus-1 period-theorem result at the supplied finite row and column indices. -/
def cubic_omega_symmetric
    (row column : Fin 1) :=
  (cubicPeriodTheorem ()).omega_symmetric row column

/-- Symmetry of the retained normalized quartic period entries.

Uses the original genus-1 period-theorem result at the supplied finite row and column indices. -/
def quartic_omega_symmetric
    (row column : Fin 1) :=
  (quarticPeriodTheorem ()).omega_symmetric row column

/-- Symmetry of the retained normalized quintic period entries.

Uses the original genus-2 period-theorem result at the supplied finite row and column indices. -/
def quintic_omega_symmetric
    (row column : Fin 2) :=
  (quinticPeriodTheorem ()).omega_symmetric row column

/-- Symmetry of the retained normalized sextic period entries.

Uses the original genus-2 period-theorem result at the supplied finite row and column indices. -/
def sextic_omega_symmetric
    (row column : Fin 2) :=
  (sexticPeriodTheorem ()).omega_symmetric row column

/-- Symmetry of the retained normalized septic period entries.

Uses the original genus-3 period-theorem result at the supplied finite row and column indices. -/
def septic_omega_symmetric
    (row column : Fin 3) :=
  (septicPeriodTheorem ()).omega_symmetric row column

/-- The retained cubic normalized period center has positive all-ones imaginary energy.

Uses its original nonzero 1-coordinate all-ones vector, unit target and exact requested refinement state. -/
theorem cubic_omega_positive :
    let result := cubicPeriodTheorem ()
    let request := result.omega_positive_request
      (Ones.onesVector 0) (Ones.onesVector_nonzero 0) 1 (by
        decide)
    0 < QuadraticForm.imaginaryQuadraticForm (Ones.onesVector 0)
      (LinearAlgebra.Matrix.matrixOfFn fun row column =>
        result.analytic.normalized.omegaCenter request.refinementTarget
          request.refinementPositive row column) := by
  exact (cubicPeriodTheorem ()).omega_center_imaginaryQuadraticForm_positive
    (Ones.onesVector 0) (Ones.onesVector_nonzero 0) 1 (by
      decide)

/-- The retained quartic normalized period center has positive all-ones imaginary energy.

Uses its original nonzero 1-coordinate all-ones vector, unit target and exact requested refinement state. -/
theorem quartic_omega_positive :
    let result := quarticPeriodTheorem ()
    let request := result.omega_positive_request
      (Ones.onesVector 0) (Ones.onesVector_nonzero 0) 1 (by
        decide)
    0 < QuadraticForm.imaginaryQuadraticForm (Ones.onesVector 0)
      (LinearAlgebra.Matrix.matrixOfFn fun row column =>
        result.analytic.normalized.omegaCenter request.refinementTarget
          request.refinementPositive row column) := by
  exact (quarticPeriodTheorem ()).omega_center_imaginaryQuadraticForm_positive
    (Ones.onesVector 0) (Ones.onesVector_nonzero 0) 1 (by
      decide)

/-- The retained quintic normalized period center has positive all-ones imaginary energy.

Uses its original nonzero 2-coordinate all-ones vector, unit target and exact requested refinement state. -/
theorem quintic_omega_positive :
    let result := quinticPeriodTheorem ()
    let request := result.omega_positive_request
      (Ones.onesVector 1) (Ones.onesVector_nonzero 1) 1 (by
        decide)
    0 < QuadraticForm.imaginaryQuadraticForm (Ones.onesVector 1)
      (LinearAlgebra.Matrix.matrixOfFn fun row column =>
        result.analytic.normalized.omegaCenter request.refinementTarget
          request.refinementPositive row column) := by
  exact (quinticPeriodTheorem ()).omega_center_imaginaryQuadraticForm_positive
    (Ones.onesVector 1) (Ones.onesVector_nonzero 1) 1 (by
      decide)

/-- The retained sextic normalized period center has positive all-ones imaginary energy.

Uses its original nonzero 2-coordinate all-ones vector, unit target and exact requested refinement state. -/
theorem sextic_omega_positive :
    let result := sexticPeriodTheorem ()
    let request := result.omega_positive_request
      (Ones.onesVector 1) (Ones.onesVector_nonzero 1) 1 (by
        decide)
    0 < QuadraticForm.imaginaryQuadraticForm (Ones.onesVector 1)
      (LinearAlgebra.Matrix.matrixOfFn fun row column =>
        result.analytic.normalized.omegaCenter request.refinementTarget
          request.refinementPositive row column) := by
  exact (sexticPeriodTheorem ()).omega_center_imaginaryQuadraticForm_positive
    (Ones.onesVector 1) (Ones.onesVector_nonzero 1) 1 (by
      decide)

/-- The retained septic normalized period center has positive all-ones imaginary energy.

Uses its original nonzero 3-coordinate all-ones vector, unit target and exact requested refinement state. -/
theorem septic_omega_positive :
    let result := septicPeriodTheorem ()
    let request := result.omega_positive_request
      (Ones.onesVector 2) (Ones.onesVector_nonzero 2) 1 (by
        decide)
    0 < QuadraticForm.imaginaryQuadraticForm (Ones.onesVector 2)
      (LinearAlgebra.Matrix.matrixOfFn fun row column =>
        result.analytic.normalized.omegaCenter request.refinementTarget
          request.refinementPositive row column) := by
  exact (septicPeriodTheorem ()).omega_center_imaginaryQuadraticForm_positive
    (Ones.onesVector 2) (Ones.onesVector_nonzero 2) 1 (by
      decide)

/-- The exact Gaussian rational imaginary unit. -/
def exactGaussianI : Gaussian := ⟨0, 1⟩
/-- The exact Gaussian rational twice the imaginary unit. -/
def exactGaussianTwoI : Gaussian := ⟨0, 2⟩

/-- The one-by-one exact Gaussian matrix with entry i. -/
def squareEllipticOmega : QuadraticForm.ExactGaussianMatrix
  1 :=
  LinearAlgebra.Matrix.matrixOfFn fun _ _ =>
    exactGaussianI

/-- The exact two-by-two matrix with diagonal 2i and off-diagonal i.

Keeps the original finite row/column equality test and both distinct Gaussian entries. -/
def coupledGenusTwoOmega : QuadraticForm.ExactGaussianMatrix
  2 :=
  LinearAlgebra.Matrix.matrixOfFn fun row column =>
    if row = column then exactGaussianTwoI else
      exactGaussianI

/-- Every entry of the retained one-by-one matrix is i. -/
@[simp] theorem squareEllipticOmega_apply (row column : Fin
  1) :
    squareEllipticOmega row column = exactGaussianI :=
  LinearAlgebra.Matrix.matrixOfFn_apply _ _ _

/-- The retained two-by-two matrix has its original diagonal/off-diagonal entries. -/
@[simp] theorem coupledGenusTwoOmega_apply (row column : Fin
  2) :
    coupledGenusTwoOmega row column =
      if row = column then exactGaussianTwoI else exactGaussianI :=
  LinearAlgebra.Matrix.matrixOfFn_apply _ _ _

open Purelib.Algebra in
/-- The one-dimensional imaginary energy is the square of its coefficient. -/
theorem squareEllipticOmega_form
    (vector : QuadraticForm.RationalVector 1) :
    QuadraticForm.imaginaryQuadraticForm vector
        squareEllipticOmega =
      (vector 0) ^ 2 := by
  unfold QuadraticForm.imaginaryQuadraticForm
  rw [FiniteSum.Fin.sumFin_succ]
  change FiniteSum.Fin.sumFin (fun column : Fin 1 =>
      vector 0 * (squareEllipticOmega 0 column).im * vector column) +
      FiniteSum.Fin.sumFin (fun row : Fin 0 =>
        FiniteSum.Fin.sumFin (fun column : Fin 1 =>
          vector row.succ * (squareEllipticOmega row.succ column).im *
            vector column)) = _
  rw [LinearAlgebra.Rational.FiniteSum.Small.exact_sumFin_fin_zero]
  rw [FiniteSum.Fin.sumFin_congr
    (right := fun column : Fin 1 =>
      vector 0 * exactGaussianI.im * vector column)
    (fun column => by rw [squareEllipticOmega_apply])]
  rw [FiniteSum.Fin.sumFin_succ]
  change vector 0 * (1 : Fraction.Rational) * vector 0 +
      FiniteSum.Fin.sumFin (fun column : Fin 0 =>
        vector 0 * exactGaussianI.im * vector column.succ) + 0 = _
  rw [LinearAlgebra.Rational.FiniteSum.Small.exact_sumFin_fin_zero, Fraction.Field.mul_one_direct,
    _root_.add_zero, _root_.add_zero, pow_two]

/-- The coupled matrix's imaginary energy is an explicit sum of three squares.

Retains the separate squared coordinates and the square of their sum using exact finite sums and rational arithmetic. -/
theorem coupledGenusTwoOmega_form
    (vector : QuadraticForm.RationalVector 2) :
    QuadraticForm.imaginaryQuadraticForm vector
        coupledGenusTwoOmega =
      (vector 0) ^ 2 + ((vector 1) ^ 2 + (vector 0 + vector 1) ^ 2) := by
  unfold QuadraticForm.imaginaryQuadraticForm
  rw [LinearAlgebra.Rational.FiniteSum.Small.exact_sumFin_fin_two]
  rw [LinearAlgebra.Rational.FiniteSum.Small.exact_sumFin_fin_two,
    LinearAlgebra.Rational.FiniteSum.Small.exact_sumFin_fin_two]
  rw [coupledGenusTwoOmega_apply,
    coupledGenusTwoOmega_apply,
    coupledGenusTwoOmega_apply,
      coupledGenusTwoOmega_apply]
  simp only [-eq_self, -iff_self, if_pos (rfl : (0 : Fin 2) = 0),
    if_pos (rfl : (1 : Fin 2) = 1), if_neg (by decide : (0 : Fin 2) ≠ 1),
    if_neg (by decide : (1 : Fin 2) ≠ 0), exactGaussianI,
    exactGaussianTwoI]
  ring1

/-- The exact one-by-one imaginary matrix is symmetric. -/
theorem squareEllipticOmega_symmetric (row column : Fin 1) :
    squareEllipticOmega row column =
      squareEllipticOmega column row := by
  unfold squareEllipticOmega
  rw [LinearAlgebra.Matrix.matrixOfFn_apply,
    LinearAlgebra.Matrix.matrixOfFn_apply]

/-- The coupled exact two-by-two imaginary matrix is symmetric. -/
theorem coupledGenusTwoOmega_symmetric (row column : Fin 2)
  :
    coupledGenusTwoOmega row column =
      coupledGenusTwoOmega column row := by
  unfold coupledGenusTwoOmega
  rw [LinearAlgebra.Matrix.matrixOfFn_apply,
    LinearAlgebra.Matrix.matrixOfFn_apply]
  by_cases equal : row = column
  · subst column
    rfl
  · rw [if_neg equal, if_neg (fun reverse => equal reverse.symm)]

/-- The one-dimensional imaginary energy is positive at every nonzero vector.

Uses the original finite nonzero-coordinate witness and direct rational square positivity. -/
theorem squareEllipticOmega_positive
    (vector : QuadraticForm.RationalVector 1)
    (nonzero : QuadraticForm.NonzeroVector vector) :
    0 < QuadraticForm.imaginaryQuadraticForm vector
      squareEllipticOmega := by
  rw [squareEllipticOmega_form]
  have indexZero : nonzero.index = (0 : Fin 1) :=
    Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ nonzero.index.isLt))
  have witness := nonzero.coefficient_nonzero
  rw [indexZero] at witness
  exact Fraction.Order.Arithmetic.exact_rational_sq_pos witness

/-- The coupled imaginary energy is positive at every nonzero rational vector.

Splits on the original nonzero coordinate and retains the other two nonnegative square contributions. -/
theorem coupledGenusTwoOmega_positive
    (vector : QuadraticForm.RationalVector 2)
    (nonzero : QuadraticForm.NonzeroVector vector) :
    0 < QuadraticForm.imaginaryQuadraticForm vector
      coupledGenusTwoOmega := by
  rw [coupledGenusTwoOmega_form]
  rcases Topology.BranchedCover.Double.Attachment.sheet_eq_zero_or_one nonzero.index with
    indexZero | indexOne
  · have firstNonzero : vector 0 ≠ 0 := by
      have indexLiteral : nonzero.index = (0 : Fin 2) :=
        indexZero.trans (by apply Fin.ext; rfl)
      have witness := nonzero.coefficient_nonzero
      rw [indexLiteral] at witness
      exact witness
    have tailNonnegative : 0 ≤ (vector 1) ^ 2 + (vector 0 + vector 1) ^ 2 :=
      calc
        0 = (0 : Fraction.Rational) + 0 := by decide +kernel
        _ ≤ (vector 1) ^ 2 + (vector 0 + vector 1) ^ 2 :=
          Fraction.Order.Arithmetic.add_le_add_direct
            (Fraction.Order.Arithmetic.sq_nonneg_direct (vector 1))
            (Fraction.Order.Arithmetic.sq_nonneg_direct (vector 0 + vector 1))
    exact Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct
      (Fraction.Order.Arithmetic.exact_rational_sq_pos firstNonzero) tailNonnegative
  · have secondNonzero : vector 1 ≠ 0 := by
      have indexLiteral : nonzero.index = (1 : Fin 2) :=
        indexOne.trans (by apply Fin.ext; rfl)
      have witness := nonzero.coefficient_nonzero
      rw [indexLiteral] at witness
      exact witness
    exact Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
      (Fraction.Order.Arithmetic.sq_nonneg_direct (vector 0))
      (Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct
        (Fraction.Order.Arithmetic.exact_rational_sq_pos secondNonzero)
        (Fraction.Order.Arithmetic.sq_nonneg_direct (vector 0 + vector 1)))

/-- The original one-by-one matrix with its symmetry and positivity certificates. -/
def squareEllipticMatrixWitness :
  ImaginaryPositive.RiemannMatrixWitness 1 where
  omega := squareEllipticOmega
  symmetric := squareEllipticOmega_symmetric
  positive := squareEllipticOmega_positive

/-- The original coupled matrix with its symmetry and positivity certificates. -/
def coupledGenusTwoMatrixWitness :
  ImaginaryPositive.RiemannMatrixWitness 2 where
  omega := coupledGenusTwoOmega
  symmetric := coupledGenusTwoOmega_symmetric
  positive := coupledGenusTwoOmega_positive

/-- The retained one-dimensional all-ones vector has energy one. -/
theorem squareElliptic_ones_energy :
    QuadraticForm.imaginaryQuadraticForm (Ones.onesVector 0)
      squareEllipticMatrixWitness.omega = 1 := by
  change QuadraticForm.imaginaryQuadraticForm (Ones.onesVector 0)
      squareEllipticOmega = 1
  rw [squareEllipticOmega_form]
  simp only [-eq_self, -iff_self, Ones.onesVector, Vector.Basic.vectorOfFn_apply]
  rfl

/-- The retained one-dimensional all-ones positivity margin is one half. -/
theorem squareElliptic_ones_margin :
    squareEllipticMatrixWitness.requestedMargin
      (Ones.onesVector 0) =
      (1 : Fraction.Rational) / 2 := by
  unfold ImaginaryPositive.RiemannMatrixWitness.requestedMargin
  rw [squareElliptic_ones_energy]

/-- The retained two-dimensional all-ones vector has energy six. -/
theorem coupledGenusTwo_ones_energy :
    QuadraticForm.imaginaryQuadraticForm (Ones.onesVector 1)
      coupledGenusTwoMatrixWitness.omega = 6 := by
  change QuadraticForm.imaginaryQuadraticForm (Ones.onesVector 1)
      coupledGenusTwoOmega = 6
  rw [coupledGenusTwoOmega_form]
  simp only [-eq_self, -iff_self, Ones.onesVector, Vector.Basic.vectorOfFn_apply]
  decide +kernel

/-- The retained two-dimensional all-ones positivity margin is three. -/
theorem coupledGenusTwo_ones_margin :
    coupledGenusTwoMatrixWitness.requestedMargin
      (Ones.onesVector 1) = 3 := by
  unfold ImaginaryPositive.RiemannMatrixWitness.requestedMargin
  rw [coupledGenusTwo_ones_energy]
  decide

end Purelib.Examples.Curves.Hyperelliptic.Periods.Worked

end
