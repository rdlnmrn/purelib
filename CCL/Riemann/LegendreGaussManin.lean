import CCL.Riemann.LegendreMonodromy
import CCL.Riemann.PeriodLinearity

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

namespace CCL.Riemann.LegendreGaussManin

open CCL.Riemann.LegendrePaths
open CCL.Riemann.AlgebraicDifferentials
open CCL.Riemann.PeriodMatrix

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev NamedEquivalent := CCL.OperationalEquivalence.NamedEquivalent
abbrev RefinementProgram :=
  CCL.ProgressiveGaussianIntegration.RefinementProgram
abbrev IntegralMatrix :=
  CCL.Riemann.LegendrePicardLefschetz.IntegralMatrix
abbrev RawPeriodVector := Fin 2 -> CoherentNamed
abbrev NamedMatrix := CCL.Riemann.PeriodMatrix.NamedMatrix 2
abbrev GeometricMatrix :=
  CCL.Riemann.FiniteMatrixApproximation.GeometricMatrix 2

private theorem fin_two_cases (index : Fin 2) :
    index = 0 ∨ index = 1 := by
  rcases index with ⟨value, bound⟩
  omega0

/-! ## Exact endpoint fibres -/

/-- The genus-one curve carried by one Legendre root frame.  Its finite
squarefree certificate is reused from the displayed simple-root chamber. -/
def frameCurve {parameter : Gaussian} (frame : Frame parameter) :
    HyperellipticCurve 1 where
  polynomial := LegendrePaths.polynomial parameter
  nonzero := LegendrePaths.polynomial_isZero parameter
  squarefree := by
    have certificate := frame.chamber.chamber.squarefree
    change RFAP.Squarefree.SquarefreeCertificate
      frame.chamber.polynomial at certificate
    rw [frame.polynomial_eq] at certificate
    exact certificate
  degreeShape := .odd (LegendrePaths.polynomial_natDegree parameter)

@[simp] theorem frameCurve_polynomial {parameter : Gaussian}
    (frame : Frame parameter) :
    (frameCurve frame).polynomial = LegendrePaths.polynomial parameter := rfl

/-- Certified raw periods on the exact fibre selected by one frame. -/
structure FibreData {parameter : Gaussian} (frame : Frame parameter) where
  periods : PeriodData (frameCurve frame)

namespace FibreData

/-- The `a` and `b` refinement programs in locked column-vector order. -/
def rawRefinement {parameter : Gaussian} {frame : Frame parameter}
    (data : FibreData frame) (coordinate : Fin 2) : RefinementProgram :=
  if coordinate = 0 then
    (data.periods.aProgram 0 0).integral
  else
    (data.periods.bProgram 0 0).integral

/-- The productive raw period vector in the same order. -/
def rawPeriods {parameter : Gaussian} {frame : Frame parameter}
    (data : FibreData frame) : RawPeriodVector :=
  fun coordinate => (data.rawRefinement coordinate).output

@[simp] theorem rawPeriods_apply {parameter : Gaussian}
    {frame : Frame parameter} (data : FibreData frame) (coordinate : Fin 2) :
    data.rawPeriods coordinate = (data.rawRefinement coordinate).output := rfl

/-- The first raw coordinate is exactly the certified genus-one `a` period. -/
theorem rawRefinement_zero {parameter : Gaussian} {frame : Frame parameter}
    (data : FibreData frame) :
    data.rawRefinement 0 = (data.periods.aProgram 0 0).integral := rfl

/-- The second raw coordinate is exactly the certified genus-one `b` period. -/
theorem rawRefinement_one {parameter : Gaussian} {frame : Frame parameter}
    (data : FibreData frame) :
    data.rawRefinement 1 = (data.periods.bProgram 0 0).integral := by
  unfold rawRefinement
  rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]

end FibreData

/-! ## The same integral matrix acting on productive period names -/

/-- Embed an integer as an exact Gaussian rational. -/
def integralGaussian (value : Int) : Gaussian := ⟨(value : Coordinate), 0⟩

/-- Exact synchronized geometric matrix underlying an integral homology
matrix. -/
def integralGeometricMatrix (matrix : IntegralMatrix) : GeometricMatrix :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
    CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.exact
      (integralGaussian (matrix row column))

/-- Productive exact CCL matrix carrying the same integral coefficients. -/
def integralNamedMatrix (matrix : IntegralMatrix) : NamedMatrix :=
  CCL.Riemann.PeriodMatrix.ScaledInverseCertificate.geometricNamedMatrix
    (integralGeometricMatrix matrix)

/-- Repeat a period vector as both columns of a square named matrix.  This
lets the existing synchronized square-matrix algebra act on a vector without
introducing a second matrix representation. -/
def replicatedPeriods (periods : RawPeriodVector) : NamedMatrix :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row _ => periods row

/-- Apply exactly the integral homology matrix to a raw period vector.  The
first column is selected only after synchronized named-matrix multiplication;
both replicated columns carry the same vector. -/
def matrixAction (matrix : IntegralMatrix) (periods : RawPeriodVector) :
    RawPeriodVector := fun row =>
  CCL.Riemann.PeriodMatrix.matrixMul
    (integralNamedMatrix matrix) (replicatedPeriods periods) row 0

/-- Pointwise operational equality of raw period vectors. -/
def VectorEquivalent (left right : RawPeriodVector) : Type :=
  forall coordinate, NamedEquivalent (left coordinate).name
    (right coordinate).name

namespace VectorEquivalent

def refl (periods : RawPeriodVector) : VectorEquivalent periods periods :=
  fun coordinate =>
    CCL.OperationalEquivalence.NamedEquivalent.refl (periods coordinate).name

def symm {left right : RawPeriodVector}
    (equivalent : VectorEquivalent left right) : VectorEquivalent right left :=
  fun coordinate =>
    CCL.OperationalEquivalence.NamedEquivalent.symm (equivalent coordinate)

def trans {first second third : RawPeriodVector}
    (firstSecond : VectorEquivalent first second)
    (secondThird : VectorEquivalent second third) :
    VectorEquivalent first third := fun coordinate =>
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (firstSecond coordinate) (secondThird coordinate)

end VectorEquivalent

@[simp] theorem integralNamedMatrix_apply (matrix : IntegralMatrix)
    (row column : Fin 2) :
    integralNamedMatrix matrix row column =
      CCL.Riemann.PeriodMatrix.geometricNamed
        (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.exact
          (integralGaussian (matrix row column))) := by
  rw [integralNamedMatrix,
    CCL.Riemann.PeriodMatrix.ScaledInverseCertificate.geometricNamedMatrix_apply,
    integralGeometricMatrix,
    RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply]

@[simp] theorem replicatedPeriods_apply (periods : RawPeriodVector)
    (row column : Fin 2) : replicatedPeriods periods row column = periods row :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply _ _ _

private theorem sumFin_empty_gaussian (values : Fin 0 -> Gaussian) :
    RFAP.ConstructiveFiniteMatrix.sumFin values = 0 := by
  calc
    RFAP.ConstructiveFiniteMatrix.sumFin values =
        RFAP.ConstructiveFiniteMatrix.sumFin
          (fun _ : Fin 0 => (0 : Gaussian)) :=
      RFAP.ConstructiveFiniteMatrix.sumFin_congr
        (fun index => Fin.elim0 index)
    _ = 0 := RFAP.ConstructiveFiniteMatrix.sumFin_zero

private theorem sumFin_two_gaussian (values : Fin 2 -> Gaussian) :
    RFAP.ConstructiveFiniteMatrix.sumFin values = values 0 + values 1 := by
  rw [RFAP.ConstructiveFiniteMatrix.sumFin_succ,
    RFAP.ConstructiveFiniteMatrix.sumFin_succ, sumFin_empty_gaussian]
  rw [show (Fin.succ 0 : Fin 2) = 1 by rfl]
  rw [RFAP.ConstructiveGaussian.Gaussian.add_zero]

/-- Casting a two-term integral dot product into exact Gaussian rationals
commutes with the displayed finite sum. -/
theorem integralGaussian_sumFin_two
    (left right : IntegralMatrix) (row column : Fin 2) :
    RFAP.ConstructiveFiniteMatrix.sumFin (fun middle =>
        integralGaussian (left row middle) *
          integralGaussian (right middle column)) =
      integralGaussian
        (RFAP.ConstructiveFiniteMatrix.sumFin fun middle =>
          left row middle * right middle column) := by
  rw [sumFin_two_gaussian,
    CCL.Riemann.LegendrePicardLefschetz.sumFin_two]
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · simp only [integralGaussian,
      RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveFraction.intCast_add_direct,
      RFAP.ConstructiveFraction.intCast_mul_direct]
    ring1
  · simp only [integralGaussian,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_im]
    ring1

/-- Entrywise casting commutes with exact two-by-two integer matrix
multiplication. -/
theorem integralGaussian_matrix_mul_entry
    (left right : IntegralMatrix) (row column : Fin 2) :
    RFAP.ConstructiveFiniteMatrix.mul
        (RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
          integralGaussian (left row column))
        (RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
          integralGaussian (right row column)) row column =
      integralGaussian
        (RFAP.ConstructiveFiniteMatrix.mul left right row column) := by
  rw [RFAP.ConstructiveFiniteMatrix.mul_apply]
  rw [RFAP.ConstructiveFiniteMatrix.sumFin_congr
    (right := fun middle =>
      integralGaussian (left row middle) *
        integralGaussian (right middle column))
    (fun middle => by
      rw [RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply,
        RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply])]
  rw [RFAP.ConstructiveFiniteMatrix.mul_apply]
  exact integralGaussian_sumFin_two left right row column

theorem sample_integralGeometricMatrix_apply
    (matrix : IntegralMatrix) (index : Nat) (row column : Fin 2) :
    CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
        (integralGeometricMatrix matrix) index row column =
      integralGaussian (matrix row column) := by
  rw [CCL.Riemann.FiniteMatrixApproximation.sampleMatrix_apply,
    integralGeometricMatrix,
    RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply]
  exact CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.exact_sample
    _ _

/-- Productive exact integral matrices multiply like their finite integer
matrices, entry by entry, at the operational layer. -/
def integralNamedMatrix_mul (left right : IntegralMatrix) :
    CCL.Riemann.PeriodMatrix.MatrixEquivalent
      (CCL.Riemann.PeriodMatrix.matrixMul
        (integralNamedMatrix left) (integralNamedMatrix right))
      (integralNamedMatrix
        (RFAP.ConstructiveFiniteMatrix.mul left right)) := by
  let leftGeometric := integralGeometricMatrix left
  let rightGeometric := integralGeometricMatrix right
  let productGeometric :=
    CCL.Riemann.PeriodMatrix.ScaledInverseCertificate.geometricProductMatrix
      leftGeometric rightGeometric
  have normalize : CCL.Riemann.PeriodMatrix.MatrixEquivalent
      (CCL.Riemann.PeriodMatrix.matrixMul
        (integralNamedMatrix left) (integralNamedMatrix right))
      (CCL.Riemann.PeriodMatrix.ScaledInverseCertificate.geometricNamedMatrix
        productGeometric) :=
    CCL.Riemann.PeriodMatrix.ScaledInverseCertificate.matrixMul_equivalent_geometricProductMatrix
      (integralNamedMatrix left) (integralNamedMatrix right)
      leftGeometric rightGeometric
      (fun row column => by
        dsimp only [leftGeometric]
        rw [integralNamedMatrix_apply, integralGeometricMatrix,
          RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply]
        exact CCL.OperationalEquivalence.NamedEquivalent.refl _)
      (fun row column => by
        dsimp only [rightGeometric]
        rw [integralNamedMatrix_apply, integralGeometricMatrix,
          RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply]
        exact CCL.OperationalEquivalence.NamedEquivalent.refl _)
  apply CCL.Riemann.PeriodMatrix.MatrixEquivalent.trans normalize
  intro row column
  rw [CCL.Riemann.PeriodMatrix.ScaledInverseCertificate.geometricNamedMatrix_apply,
    integralNamedMatrix_apply]
  apply CCL.Riemann.PeriodMatrix.ScaledInverseCertificate.geometricNamed_equivalent_of_samples
  intro index
  rw [show (productGeometric row column).sample index =
      RFAP.ConstructiveFiniteMatrix.mul
        (CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
          leftGeometric index)
        (CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
          rightGeometric index) row column by
    dsimp only [productGeometric]
    rw [CCL.Riemann.PeriodMatrix.ScaledInverseCertificate.geometricProductMatrix_apply]
    exact CCL.Riemann.PeriodMatrix.ScaledInverseCertificate.geometricProductEntry_sample
      leftGeometric rightGeometric row column index]
  rw [RFAP.ConstructiveFiniteMatrix.mul_apply]
  rw [RFAP.ConstructiveFiniteMatrix.sumFin_congr
    (right := fun middle =>
      integralGaussian (left row middle) *
        integralGaussian (right middle column))
    (fun middle => by
      rw [sample_integralGeometricMatrix_apply,
        sample_integralGeometricMatrix_apply])]
  rw [CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.exact_sample]
  rw [RFAP.ConstructiveFiniteMatrix.mul_apply]
  exact integralGaussian_sumFin_two left right row column

/-- Replicating pointwise equivalent period vectors gives equivalent named
matrices. -/
def replicatedPeriods_respects {left right : RawPeriodVector}
    (equivalent : VectorEquivalent left right) :
    CCL.Riemann.PeriodMatrix.MatrixEquivalent
      (replicatedPeriods left) (replicatedPeriods right) := by
  intro row column
  rw [replicatedPeriods_apply, replicatedPeriods_apply]
  exact equivalent row

/-- Integral matrix action respects pointwise operational equality. -/
def matrixAction_respects (matrix : IntegralMatrix)
    {left right : RawPeriodVector} (equivalent : VectorEquivalent left right) :
    VectorEquivalent (matrixAction matrix left) (matrixAction matrix right) := by
  let matrixEquivalent := CCL.Riemann.PeriodMatrix.matrixMul_respects
    (integralNamedMatrix matrix) (integralNamedMatrix matrix)
    (replicatedPeriods left) (replicatedPeriods right)
    (CCL.Riemann.PeriodMatrix.MatrixEquivalent.refl
      (integralNamedMatrix matrix))
    (replicatedPeriods_respects equivalent)
  intro coordinate
  exact matrixEquivalent coordinate 0

/-- Replicating an already acted-on vector agrees with retaining either
column of the corresponding named matrix product. -/
def replicatedPeriods_matrixAction (matrix : IntegralMatrix)
    (periods : RawPeriodVector) :
    CCL.Riemann.PeriodMatrix.MatrixEquivalent
      (replicatedPeriods (matrixAction matrix periods))
      (CCL.Riemann.PeriodMatrix.matrixMul
        (integralNamedMatrix matrix) (replicatedPeriods periods)) := by
  intro row column
  rw [replicatedPeriods_apply]
  unfold matrixAction
  rw [CCL.Riemann.PeriodMatrix.matrixMul_apply,
    CCL.Riemann.PeriodMatrix.matrixMul_apply]
  apply CCL.Riemann.PeriodMatrix.sumNamed_respects
  intro middle
  rw [replicatedPeriods_apply, replicatedPeriods_apply]
  exact CCL.OperationalEquivalence.NamedEquivalent.refl _

/-- Successive raw actions compose with exactly the same multiplication order
as the locked homology matrices. -/
def matrixAction_mul (left right : IntegralMatrix)
    (periods : RawPeriodVector) :
    VectorEquivalent
      (matrixAction (RFAP.ConstructiveFiniteMatrix.mul left right) periods)
      (matrixAction left (matrixAction right periods)) := by
  let raw := replicatedPeriods periods
  let leftNamed := integralNamedMatrix left
  let rightNamed := integralNamedMatrix right
  let productNamed := integralNamedMatrix
    (RFAP.ConstructiveFiniteMatrix.mul left right)
  have exposeProduct : CCL.Riemann.PeriodMatrix.MatrixEquivalent
      (CCL.Riemann.PeriodMatrix.matrixMul productNamed raw)
      (CCL.Riemann.PeriodMatrix.matrixMul
        (CCL.Riemann.PeriodMatrix.matrixMul leftNamed rightNamed) raw) :=
    CCL.Riemann.PeriodMatrix.matrixMul_respects productNamed
      (CCL.Riemann.PeriodMatrix.matrixMul leftNamed rightNamed) raw raw
      (CCL.Riemann.PeriodMatrix.MatrixEquivalent.symm
        (integralNamedMatrix_mul left right))
      (CCL.Riemann.PeriodMatrix.MatrixEquivalent.refl raw)
  have associate := CCL.Riemann.PeriodMatrix.ScaledInverseCertificate.matrixMul_assoc
    leftNamed rightNamed raw
  have replaceRight : CCL.Riemann.PeriodMatrix.MatrixEquivalent
      (CCL.Riemann.PeriodMatrix.matrixMul leftNamed
        (CCL.Riemann.PeriodMatrix.matrixMul rightNamed raw))
      (CCL.Riemann.PeriodMatrix.matrixMul leftNamed
        (replicatedPeriods (matrixAction right periods))) :=
    CCL.Riemann.PeriodMatrix.matrixMul_respects leftNamed leftNamed
      (CCL.Riemann.PeriodMatrix.matrixMul rightNamed raw)
      (replicatedPeriods (matrixAction right periods))
      (CCL.Riemann.PeriodMatrix.MatrixEquivalent.refl leftNamed)
      (CCL.Riemann.PeriodMatrix.MatrixEquivalent.symm
        (replicatedPeriods_matrixAction right periods))
  intro coordinate
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (exposeProduct coordinate 0)
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      (associate coordinate 0) (replaceRight coordinate 0))

private def integralNamedMatrix_identity_scaleIdentity :
    CCL.Riemann.PeriodMatrix.MatrixEquivalent
      (integralNamedMatrix RFAP.ConstructiveFiniteMatrix.identity)
      (CCL.Riemann.PeriodMatrix.scaleIdentity
        (CCL.ProgressiveCoherence.CoherentNamed.exact 1)) := by
  intro row column
  rw [integralNamedMatrix_apply,
    CCL.Riemann.PeriodMatrix.scaleIdentity_apply]
  by_cases equal : row = column
  · subst column
    rw [if_pos rfl]
    change NamedEquivalent
      (CCL.Riemann.PeriodMatrix.geometricNamed
        (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.exact
          (integralGaussian
            (RFAP.ConstructiveFiniteMatrix.identity row row)))).name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 1).name
    have diagonal :
        (RFAP.ConstructiveFiniteMatrix.identity : IntegralMatrix) row row =
          (1 : Int) := by
      unfold RFAP.ConstructiveFiniteMatrix.identity
      rw [RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply, if_pos rfl]
    rw [diagonal]
    have oneEqual : integralGaussian 1 = (1 : Gaussian) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [integralGaussian, Int.cast_one,
          RFAP.ConstructiveGaussian.Gaussian.one_re,
          RFAP.ConstructiveGaussian.Gaussian.one_im]
    rw [oneEqual]
    exact CCL.Riemann.FiniteBilinear.geometricExact_equivalent_exact
      (1 : Gaussian)
  · rw [if_neg equal]
    have offDiagonal :
        (RFAP.ConstructiveFiniteMatrix.identity : IntegralMatrix) row column =
          (0 : Int) := by
      unfold RFAP.ConstructiveFiniteMatrix.identity
      rw [RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply, if_neg equal]
    rw [offDiagonal]
    exact CCL.OperationalEquivalence.NamedEquivalent.refl _

/-- The identity homology matrix acts identically on raw productive periods. -/
def matrixAction_identity (periods : RawPeriodVector) :
    VectorEquivalent
      (matrixAction RFAP.ConstructiveFiniteMatrix.identity periods) periods := by
  let raw := replicatedPeriods periods
  let one := CCL.ProgressiveCoherence.CoherentNamed.exact 1
  have replaceIdentity : CCL.Riemann.PeriodMatrix.MatrixEquivalent
      (CCL.Riemann.PeriodMatrix.matrixMul
        (integralNamedMatrix RFAP.ConstructiveFiniteMatrix.identity) raw)
      (CCL.Riemann.PeriodMatrix.matrixMul
        (CCL.Riemann.PeriodMatrix.scaleIdentity one) raw) :=
    CCL.Riemann.PeriodMatrix.matrixMul_respects
      (integralNamedMatrix RFAP.ConstructiveFiniteMatrix.identity)
      (CCL.Riemann.PeriodMatrix.scaleIdentity one) raw raw
      integralNamedMatrix_identity_scaleIdentity
      (CCL.Riemann.PeriodMatrix.MatrixEquivalent.refl raw)
  have exposeScalar :=
    CCL.Riemann.PeriodMatrix.ScaledInverseCertificate.scaleIdentity_mul one raw
  intro coordinate
  apply CCL.OperationalEquivalence.NamedEquivalent.trans
    (replaceIdentity coordinate 0)
  apply CCL.OperationalEquivalence.NamedEquivalent.trans
    (exposeScalar coordinate 0)
  rw [CCL.Riemann.PeriodMatrix.ScaledInverseCertificate.scalarMul_apply,
    replicatedPeriods_apply]
  exact CCL.OperationalFieldLaws.coherentMul_one_left (periods coordinate)

/-! ## Finite endpoint continuation and the dual period action -/

/-- Actual endpoint period programs together with the source fibre whose
displayed homology basis is transported along a finite parameter path.  No
claim equates periods on the two different endpoint curves. -/
structure EndpointContinuation {start finish : Gaussian}
    {left : Frame start} {right : Frame finish}
    (path : Path left right) where
  source : FibreData left
  target : FibreData right

namespace EndpointContinuation

/-- Endpoint periods evaluated on the transported source-labelled homology
basis.  Since `wordMatrix` acts on homology coordinate columns, the period
column carries its exact transpose. -/
def periods {start finish : Gaussian}
    {left : Frame start} {right : Frame finish}
    {path : Path left right} (continuation : EndpointContinuation path) :
    RawPeriodVector :=
  matrixAction
    (CCL.Riemann.LegendrePicardLefschetz.periodMatrix path.word)
    continuation.target.rawPeriods

/-- The coefficient used for an output basis period is exactly the
corresponding column coefficient of direct homology transport. -/
@[simp] theorem period_coefficient {start finish : Gaussian}
    {left : Frame start} {right : Frame finish}
    {path : Path left right} (_continuation : EndpointContinuation path)
    (output input : Fin 2) :
    CCL.Riemann.LegendrePicardLefschetz.periodMatrix path.word output input =
      CCL.Riemann.LegendrePicardLefschetz.wordMatrix path.word input output :=
  CCL.Riemann.LegendrePicardLefschetz.transpose_apply _ _ _

/-- The empty path leaves the actual endpoint period column unchanged. -/
def nil_periods {parameter : Gaussian} {frame : Frame parameter}
    (data : FibreData frame) :
    VectorEquivalent
      (({ source := data, target := data } :
        EndpointContinuation (.nil frame)).periods)
      data.rawPeriods := by
  change VectorEquivalent
    (matrixAction
      (CCL.Riemann.LegendrePicardLefschetz.periodMatrix []) data.rawPeriods)
    data.rawPeriods
  rw [CCL.Riemann.LegendrePicardLefschetz.periodMatrix_nil]
  exact matrixAction_identity data.rawPeriods

/-- The exact dual matrix for an appended path acts in the order forced by
pairing endpoint periods with the composed homology transport. -/
def append_periods {start middle finish : Gaussian}
    {left : Frame start} {center : Frame middle} {right : Frame finish}
    (first : Path left center) (second : Path center right)
    (source : FibreData left) (target : FibreData right) :
    let appended : EndpointContinuation (first.append second) :=
      { source := source, target := target }
    VectorEquivalent appended.periods
      (matrixAction
        (CCL.Riemann.LegendrePicardLefschetz.periodMatrix first.word)
        (matrixAction
          (CCL.Riemann.LegendrePicardLefschetz.periodMatrix second.word)
          target.rawPeriods)) := by
  intro appended
  change VectorEquivalent
    (matrixAction
      (CCL.Riemann.LegendrePicardLefschetz.periodMatrix
        (first.append second).word) target.rawPeriods)
    (matrixAction
      (CCL.Riemann.LegendrePicardLefschetz.periodMatrix first.word)
      (matrixAction
        (CCL.Riemann.LegendrePicardLefschetz.periodMatrix second.word)
        target.rawPeriods))
  rw [CCL.Riemann.LegendrePaths.Path.word_append,
    CCL.Riemann.LegendrePicardLefschetz.periodMatrix_append]
  exact matrixAction_mul _ _ target.rawPeriods

/-- Applying the reverse dual action after the forward one returns the
canonical endpoint period column operationally. -/
def reverse_undoes_periods {start finish : Gaussian}
    {left : Frame start} {right : Frame finish}
    (path : Path left right) (target : FibreData right) :
    VectorEquivalent
      (matrixAction
        (CCL.Riemann.LegendrePicardLefschetz.periodMatrix path.reverse.word)
        (matrixAction
          (CCL.Riemann.LegendrePicardLefschetz.periodMatrix path.word)
          target.rawPeriods))
      target.rawPeriods := by
  rw [CCL.Riemann.LegendrePaths.Path.word_reverse]
  have inverse :=
    (CCL.Riemann.LegendrePicardLefschetz.periodMatrix_inverse_identities
      path.word).2
  apply VectorEquivalent.trans
    (VectorEquivalent.symm
      (matrixAction_mul
        (CCL.Riemann.LegendrePicardLefschetz.periodMatrix path.word.inverse)
        (CCL.Riemann.LegendrePicardLefschetz.periodMatrix path.word)
        target.rawPeriods))
  rw [inverse]
  exact matrixAction_identity target.rawPeriods

end EndpointContinuation

/-- Unconditional productive period columns for the three standard closed
loops.  These use actual base-fibre period programs and the dual action of the
certified homology matrices; no impossible equality between different fibres
is requested. -/
structure StandardLoopContinuations {parameter : Gaussian}
    {frame : Frame parameter}
    (loops : CCL.Riemann.LegendreMonodromy.StandardLoops frame) where
  base : FibreData frame

namespace StandardLoopContinuations

def zero {parameter : Gaussian} {frame : Frame parameter}
    {loops : CCL.Riemann.LegendreMonodromy.StandardLoops frame}
    (continuations : StandardLoopContinuations loops) : RawPeriodVector :=
  matrixAction
    (CCL.Riemann.LegendrePicardLefschetz.periodMatrix loops.zeroPath.word)
    continuations.base.rawPeriods

def one {parameter : Gaussian} {frame : Frame parameter}
    {loops : CCL.Riemann.LegendreMonodromy.StandardLoops frame}
    (continuations : StandardLoopContinuations loops) : RawPeriodVector :=
  matrixAction
    (CCL.Riemann.LegendrePicardLefschetz.periodMatrix loops.onePath.word)
    continuations.base.rawPeriods

def infinity {parameter : Gaussian} {frame : Frame parameter}
    {loops : CCL.Riemann.LegendreMonodromy.StandardLoops frame}
    (continuations : StandardLoopContinuations loops) : RawPeriodVector :=
  matrixAction
    (CCL.Riemann.LegendrePicardLefschetz.periodMatrix
      loops.infinityPath.word)
    continuations.base.rawPeriods

def product {parameter : Gaussian} {frame : Frame parameter}
    {loops : CCL.Riemann.LegendreMonodromy.StandardLoops frame}
    (continuations : StandardLoopContinuations loops) : RawPeriodVector :=
  matrixAction
    (CCL.Riemann.LegendrePicardLefschetz.periodMatrix loops.productPath.word)
    continuations.base.rawPeriods

def zero_explicit {parameter : Gaussian} {frame : Frame parameter}
    {loops : CCL.Riemann.LegendreMonodromy.StandardLoops frame}
    (continuations : StandardLoopContinuations loops) :
    VectorEquivalent continuations.zero
      (matrixAction CCL.Riemann.LegendreMonodromy.zeroPeriodMatrix
        continuations.base.rawPeriods) := by
  rw [zero, loops.zeroPath_periodMatrix]
  exact VectorEquivalent.refl _

def one_explicit {parameter : Gaussian} {frame : Frame parameter}
    {loops : CCL.Riemann.LegendreMonodromy.StandardLoops frame}
    (continuations : StandardLoopContinuations loops) :
    VectorEquivalent continuations.one
      (matrixAction CCL.Riemann.LegendreMonodromy.onePeriodMatrix
        continuations.base.rawPeriods) := by
  rw [one, loops.onePath_periodMatrix]
  exact VectorEquivalent.refl _

def infinity_explicit {parameter : Gaussian} {frame : Frame parameter}
    {loops : CCL.Riemann.LegendreMonodromy.StandardLoops frame}
    (continuations : StandardLoopContinuations loops) :
    VectorEquivalent continuations.infinity
      (matrixAction CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix
        continuations.base.rawPeriods) := by
  rw [infinity, loops.infinityPath_periodMatrix]
  exact VectorEquivalent.refl _

def product_identity {parameter : Gaussian} {frame : Frame parameter}
    {loops : CCL.Riemann.LegendreMonodromy.StandardLoops frame}
    (continuations : StandardLoopContinuations loops) :
    VectorEquivalent continuations.product continuations.base.rawPeriods := by
  rw [product, loops.productPath_periodMatrix]
  exact matrixAction_identity continuations.base.rawPeriods

end StandardLoopContinuations

/-- A deterministic common finite schedule.  Every request is advanced to
explicit source, target, and comparison indices, and each index stream is
monotone. -/
structure CommonSchedule where
  sourceIndex : Nat -> Nat
  targetIndex : Nat -> Nat
  comparisonIndex : Nat -> Nat
  source_ge : forall request, request ≤ sourceIndex request
  target_ge : forall request, request ≤ targetIndex request
  comparison_ge : forall request, request ≤ comparisonIndex request
  source_mono : forall {first second}, first ≤ second ->
    sourceIndex first ≤ sourceIndex second
  target_mono : forall {first second}, first ≤ second ->
    targetIndex first ≤ targetIndex second
  comparison_mono : forall {first second}, first ≤ second ->
    comparisonIndex first ≤ comparisonIndex second

namespace CommonSchedule

/-- The request itself is a deterministic common schedule. -/
def identity : CommonSchedule where
  sourceIndex := id
  targetIndex := id
  comparisonIndex := id
  source_ge := fun _ => le_rfl
  target_ge := fun _ => le_rfl
  comparison_ge := fun _ => le_rfl
  source_mono := fun order => order
  target_mono := fun order => order
  comparison_mono := fun order => order

@[simp] theorem identity_sourceIndex (request : Nat) :
    identity.sourceIndex request = request := rfl

@[simp] theorem identity_targetIndex (request : Nat) :
    identity.targetIndex request = request := rfl

@[simp] theorem identity_comparisonIndex (request : Nat) :
    identity.comparisonIndex request = request := rfl

end CommonSchedule

/-! ## Generic finite analytic bridge -/

private theorem quarterRadius_weighted_sum
    (left middle right : Coordinate) (index : Nat) :
    2 * (CCL.FiniteGeometric.quarterRadius left index +
      2 * (CCL.FiniteGeometric.quarterRadius middle index +
        CCL.FiniteGeometric.quarterRadius right index)) =
      CCL.FiniteGeometric.quarterRadius
        (2 * (left + 2 * (middle + right))) index := by
  simp only [CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
  ring1

private theorem quarterRadius_antitone {scale : Coordinate}
    (scaleNonnegative : 0 ≤ scale) {earlier later : Nat}
    (order : earlier ≤ later) :
    CCL.FiniteGeometric.quarterRadius scale later ≤
      CCL.FiniteGeometric.quarterRadius scale earlier := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le order
  rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
    CCL.FiniteGeometric.quarterRadius_eq_mul_pow, pow_add]
  have extraPowerLe : (1 / 4 : Coordinate) ^ extra ≤ 1 := by
    have powerOrder := RFAP.ConstructiveFraction.pow_le_pow_direct
      (show (0 : Coordinate) ≤ 1 / 4 by decide)
      (show (1 / 4 : Coordinate) ≤ 1 by decide) extra
    simpa only [one_pow] using powerOrder
  have earlierPowerNonnegative : 0 ≤ (1 / 4 : Coordinate) ^ earlier :=
    RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) _
  have scaledNonnegative :
      0 ≤ scale * (1 / 4 : Coordinate) ^ earlier :=
    RFAP.ConstructiveFraction.mul_nonneg_direct scaleNonnegative
      earlierPowerNonnegative
  calc
    scale * ((1 / 4 : Coordinate) ^ earlier *
        (1 / 4 : Coordinate) ^ extra) =
      (scale * (1 / 4 : Coordinate) ^ earlier) *
        (1 / 4 : Coordinate) ^ extra := by ring1
    _ ≤ (scale * (1 / 4 : Coordinate) ^ earlier) * 1 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        extraPowerLe scaledNonnegative
    _ = scale * (1 / 4 : Coordinate) ^ earlier := by ring1

private theorem normSq_sub_symm (left right : Gaussian) :
    RFAP.ConstructiveGaussian.Gaussian.normSq (left - right) =
      RFAP.ConstructiveGaussian.Gaussian.normSq (right - left) := by
  rw [show left - right = -(right - left) by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.neg_re,
        RFAP.ConstructiveGaussian.Gaussian.neg_im] <;> ring1,
    RFAP.ConstructiveGaussian.Gaussian.normSq_neg]

private theorem normSq_sub_le_weighted_sum
    (first second third fourth : Gaussian)
    (firstBound middleBound lastBound : Coordinate)
    (firstClose : RFAP.ConstructiveGaussian.Gaussian.normSq
      (first - second) ≤ firstBound)
    (middleClose : RFAP.ConstructiveGaussian.Gaussian.normSq
      (second - third) ≤ middleBound)
    (lastClose : RFAP.ConstructiveGaussian.Gaussian.normSq
      (third - fourth) ≤ lastBound) :
    RFAP.ConstructiveGaussian.Gaussian.normSq (first - fourth) ≤
      2 * (firstBound + 2 * (middleBound + lastBound)) := by
  have throughThird :=
    RFAP.ConstructiveGaussian.Gaussian.normSq_sub_le_via
      second third fourth
  have throughSecond :=
    RFAP.ConstructiveGaussian.Gaussian.normSq_sub_le_via
      first second fourth
  exact throughSecond.trans (by
    apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    · apply add_le_add firstClose
      exact throughThird.trans
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add middleClose lastClose) (by decide))
    · decide)

/-- A shrinking comparison on explicit, possibly different source and target
indices of one common schedule is sufficient for operational equality. -/
def scheduledProgram_output_equivalent
    (left right : RefinementProgram) (schedule : CommonSchedule)
    (bridgeScale : Coordinate) (bridgeScale_nonnegative : 0 ≤ bridgeScale)
    (samples : forall request,
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (((left.model (schedule.targetIndex request)).integralSample) -
            ((right.model (schedule.comparisonIndex request)).integralSample)) ≤
        CCL.FiniteGeometric.quarterRadius bridgeScale request) :
    NamedEquivalent left.output.name right.output.name := by
  let totalScale : Coordinate :=
    2 * (left.errorScale + 2 * (bridgeScale + right.errorScale))
  have totalScale_nonnegative : 0 ≤ totalScale :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg left.errorScale_nonneg
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          (add_nonneg bridgeScale_nonnegative right.errorScale_nonneg)))
  have equivalent : CCL.OperationalEquivalence.Equivalent
      left.approximation right.approximation := by
    refine { compare := ?_ }
    intro leftStart rightStart target positive
    let common := CCL.FiniteGeometric.firstQuarterBelow totalScale
      (max leftStart rightStart) target
    have common_ge_left : leftStart ≤ common :=
      (Nat.le_max_left leftStart rightStart).trans
        (CCL.FiniteGeometric.firstQuarterBelow_ge totalScale
          (max leftStart rightStart) target)
    have common_ge_right : rightStart ≤ common :=
      (Nat.le_max_right leftStart rightStart).trans
        (CCL.FiniteGeometric.firstQuarterBelow_ge totalScale
          (max leftStart rightStart) target)
    have totalSmall : CCL.FiniteGeometric.quarterRadius totalScale common <
        target :=
      CCL.FiniteGeometric.firstQuarterBelow_accurate totalScale
        totalScale_nonnegative (max leftStart rightStart) target positive
    exact
      { leftIndex := schedule.targetIndex common
        rightIndex := schedule.comparisonIndex common
        left_ge := common_ge_left.trans (schedule.target_ge common)
        right_ge := common_ge_right.trans (schedule.comparison_ge common)
        close := by
          intro leftLater rightLater leftOrder rightOrder
          let leftEarlier := schedule.targetIndex common
          let rightEarlier := schedule.comparisonIndex common
          have leftClose : RFAP.ConstructiveGaussian.Gaussian.normSq
              ((left.model leftLater).integralSample -
                (left.model leftEarlier).integralSample) ≤
              CCL.FiniteGeometric.quarterRadius left.errorScale common :=
            (left.later_close leftOrder).trans
              (quarterRadius_antitone left.errorScale_nonneg
                (schedule.target_ge common))
          have middleClose := samples common
          have rightForward := right.later_close rightOrder
          have rightClose : RFAP.ConstructiveGaussian.Gaussian.normSq
              ((right.model rightEarlier).integralSample -
                (right.model rightLater).integralSample) ≤
              CCL.FiniteGeometric.quarterRadius right.errorScale common := by
            rw [normSq_sub_symm]
            exact rightForward.trans
              (quarterRadius_antitone right.errorScale_nonneg
                (schedule.comparison_ge common))
          change RFAP.ConstructiveGaussian.Gaussian.normSq
              ((left.model leftLater).integralSample -
                (right.model rightLater).integralSample) < target
          apply (normSq_sub_le_weighted_sum
            (left.model leftLater).integralSample
            (left.model leftEarlier).integralSample
            (right.model rightEarlier).integralSample
            (right.model rightLater).integralSample
            (CCL.FiniteGeometric.quarterRadius left.errorScale common)
            (CCL.FiniteGeometric.quarterRadius bridgeScale common)
            (CCL.FiniteGeometric.quarterRadius right.errorScale common)
            leftClose middleClose rightClose).trans_lt
          rw [quarterRadius_weighted_sum]
          exact totalSmall }
  simpa only [CCL.ProgressiveGaussianIntegration.RefinementProgram.output,
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation] using
    CCL.TranscendentalCoherence.approximationEquivalent_toNamed equivalent

end CCL.Riemann.LegendreGaussManin
