module

public import Purelib.Algebra.Quadratic.Pair.Gaussian.Realization.Rational
public import Purelib.Riemann.RootContinuation.SquareRootSidecar
public import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
import Purelib.Riemann.RootContinuation.SquareRootProvenance
public import Purelib.Approximation.Gaussian.Provenance.Power.Factorization
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Finite admission of an original positive rational quadratic generator

The original supplied root sidecar remains the nominal source owner. Exact
coordinate inspection, positivity and finite rational-square inspection either
admit the positive nonsquare realization or retain the specific coefficient,
sign, zero or rational-square condition preventing that admission.
-/

public section

namespace Purelib.Algebra.Quadratic.Pair.Gaussian.Realization

open Purelib.Data.Rat.Fraction
open Purelib.Data.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Riemann.RootContinuation

/-- The original sidecar's square equation has the exact inspected real rational coefficient. -/
def rootEquation {generator : CoherentNamed} (root : SquareRootSidecar.Sidecar generator)
    (parameter : Rational) (same : root.parameter = Cast.CoordinateTaylor.ofCoordinate parameter) :
    PowerIdentity generator 2 (Cast.CoordinateTaylor.ofCoordinate parameter) := by
  have identity := PowerIdentity.ofSquare root.square
  rewrite [same] at identity
  exact identity

set_option genInjectivity false in
/-- A positive nonsquare rational realization retaining its entire original root owner and finite inspection. -/
structure Admission (generator : CoherentNamed) (root : SquareRootSidecar.Sidecar generator) where
  /-- The entire original supplied generator as executable data. -/
  source : CoherentNamed
  /-- The retained generator is exactly the original input. -/
  source_eq : source = generator
  /-- The entire original supplied root sidecar, including its optional isolation owner. -/
  origin : SquareRootSidecar.Sidecar generator
  /-- The retained root sidecar is the original nominal input owner. -/
  origin_eq : origin = root
  /-- The exact inspected rational square parameter. -/
  parameter : Rational
  /-- The inspected coefficient is the original sidecar's retained parameter. -/
  parameter_eq : root.parameter = Cast.CoordinateTaylor.ofCoordinate parameter
  /-- The original rational parameter is strictly positive. -/
  positive : 0 < parameter
  /-- The complete cached canonical rational-square inspection. -/
  inspection : Square.Inspection parameter
  /-- The inspection excludes every rational square root of the same parameter. -/
  missing : inspection.root? = none
  /-- The actual cached generic realization of the original nominal pair ring. -/
  realization : Realization Rational
  /-- The cached realization is built from the same original root equation and retained finite inspection. -/
  realization_eq : realization = rational parameter generator (rootEquation root parameter parameter_eq)
    inspection missing

constructive_injectivity Admission

/-- The admitted realization keeps the original negative rational pair parameter. -/
theorem Admission.realization_parameter {generator : CoherentNamed} {root : SquareRootSidecar.Sidecar generator}
    (admission : Admission generator root) : admission.realization.parameter = -admission.parameter :=
  (congrArg Realization.parameter admission.realization_eq).trans
    (rational_parameter admission.parameter generator (rootEquation root admission.parameter admission.parameter_eq)
      admission.inspection admission.missing)

/-- An admitted rational realization maps each original scalar to its exact real-axis coefficient. -/
theorem Admission.coefficient_eq {generator : CoherentNamed} {root : SquareRootSidecar.Sidecar generator}
    (admission : Admission generator root) (value : Rational) :
    admission.realization.coefficient value = Cast.CoordinateTaylor.ofCoordinate value :=
  (congrArg (fun owner => owner.coefficient value) admission.realization_eq).trans (Eq.refl _)

/-- The admitted realization keeps the exact original supplied coherent generator. -/
theorem Admission.realization_generator {generator : CoherentNamed} {root : SquareRootSidecar.Sidecar generator}
    (admission : Admission generator root) : admission.realization.generator = generator :=
  (congrArg Realization.generator admission.realization_eq).trans
    (rational_generator admission.parameter generator (rootEquation root admission.parameter admission.parameter_eq)
      admission.inspection admission.missing)

set_option genInjectivity false in
/-- Admitted positive nonsquare data or a specific original coefficient condition preventing that field admission. -/
inductive AdmissionOutcome (generator : CoherentNamed) (root : SquareRootSidecar.Sidecar generator) where
  /-- Retain the complete positive nonsquare admission and original root owner. -/
  | admitted (result : Admission generator root)
  /-- The original retained Gaussian coefficient has a nonzero imaginary coordinate. -/
  | nonreal (imaginary_ne : root.parameter.im ≠ 0)
  /-- The original rational coefficient is zero, with operational zero evidence at the unchanged generator. -/
  | zero (parameter : Rational) (parameter_eq : root.parameter = Cast.CoordinateTaylor.ofCoordinate parameter)
      (zero : parameter = 0) (evidence : RationalSidecar generator)
  /-- Retain the exact rational coefficient and the proved violated positivity condition. -/
  | nonpositive (parameter : Rational) (parameter_eq : root.parameter = Cast.CoordinateTaylor.ofCoordinate parameter)
      (nonzero : parameter ≠ 0) (not_positive : ¬ 0 < parameter)
  /-- Retain the completed rational-square inspection and its cached exact root reading. -/
  | square (parameter : Rational) (parameter_eq : root.parameter = Cast.CoordinateTaylor.ofCoordinate parameter)
      (positive : 0 < parameter) (inspection : Square.Inspection parameter)
      (candidate : Rational) (known : inspection.root? = some candidate)

constructive_injectivity AdmissionOutcome

set_option genInjectivity false in
/-- A finite admission check retaining the actual original root source and its entire typed outcome. -/
structure AdmissionCheck (generator : CoherentNamed) (root : SquareRootSidecar.Sidecar generator) where
  /-- The actual original coherent generator. -/
  source : CoherentNamed
  /-- The retained channel is exactly the original input. -/
  source_eq : source = generator
  /-- The actual original supplied root sidecar. -/
  origin : SquareRootSidecar.Sidecar generator
  /-- The retained root owner is the original input object. -/
  origin_eq : origin = root
  /-- Complete admission or the exact retained condition selecting a specialized route. -/
  outcome : AdmissionOutcome generator root

constructive_injectivity AdmissionCheck

/-- Inspect one supplied root owner using exact coordinate, positivity and canonical rational-square tests. -/
@[noinline, nospecialize] def inspectRoot {generator : CoherentNamed} (root : SquareRootSidecar.Sidecar generator) :
    AdmissionCheck generator root := by
  let outcome := match Cast.inspectReal root.parameter with
    | .complex imaginary => AdmissionOutcome.nonreal imaginary
    | .real parameter same =>
        if zero : parameter = 0 then
          AdmissionOutcome.zero parameter same zero (by
            have parameterZero : root.parameter = 0 := same.trans
              ((congrArg Cast.CoordinateTaylor.ofCoordinate zero).trans Cast.ofCoordinate_zero)
            have square := root.square
            rewrite [parameterZero] at square
            exact ⟨0, Purelib.Riemann.RootContinuation.SquareRootProvenance.zero_of_square square⟩)
        else if positive : 0 < parameter then
          let inspection := Square.inspect parameter
          match selected : inspection.root? with
          | some candidate => AdmissionOutcome.square parameter same positive inspection candidate selected
          | none =>
              let realization := rational parameter generator (rootEquation root parameter same) inspection selected
              AdmissionOutcome.admitted
                ⟨generator, rfl, root, rfl, parameter, same, positive, inspection, selected, realization, rfl⟩
        else AdmissionOutcome.nonpositive parameter same zero positive
  exact ⟨generator, rfl, root, rfl, outcome⟩

/-- The finite signed-reading certificate needed precisely by a retained rational-square admission outcome. -/
@[expose] def AdmissionOutcome.RationalCertificate {generator : CoherentNamed}
    {root : SquareRootSidecar.Sidecar generator} : AdmissionOutcome generator root → Type 1
  | .square _ _ _ _ candidate _ =>
      Power.SignedReading generator
        (Cast.CoordinateTaylor.ofCoordinate candidate)
  | _ => PUnit

/-- Inspect the same cached rational-square candidate to certify the original generator's exact signed reading. -/
@[noinline, nospecialize] def AdmissionOutcome.inspectRational {generator : CoherentNamed}
    {root : SquareRootSidecar.Sidecar generator} (outcome : AdmissionOutcome generator root) :
    outcome.RationalCertificate :=
  match outcome with
  | .square parameter parameter_eq positive inspection candidate known => by
      have square := inspection.square_of_root candidate known
      have candidateNonzero : candidate ≠ 0 := by
        intro zero
        rewrite [zero, zero_mul] at square
        rewrite [← square] at positive
        exact positive.2 positive.1
      have mappedNonzero : Cast.CoordinateTaylor.ofCoordinate candidate ≠ 0 := by
        intro zero
        exact candidateNonzero (Cast.ofCoordinate_injective (zero.trans Cast.ofCoordinate_zero.symm))
      have mappedSquare : Cast.CoordinateTaylor.ofCoordinate parameter =
          Cast.CoordinateTaylor.ofCoordinate candidate * Cast.CoordinateTaylor.ofCoordinate candidate :=
        (congrArg Cast.CoordinateTaylor.ofCoordinate square).symm.trans (Cast.ofCoordinate_mul candidate candidate)
      have identity := rootEquation root parameter parameter_eq
      rewrite [mappedSquare] at identity
      exact identity.rationalSquare (Cast.CoordinateTaylor.ofCoordinate candidate) mappedNonzero
  | .admitted _ => PUnit.unit
  | .nonreal _ => PUnit.unit
  | .zero _ _ _ _ => PUnit.unit
  | .nonpositive _ _ _ _ => PUnit.unit

/-- Read zero or signed rational evidence from the same retained admission and its already computed certificate. -/
@[expose, noinline, nospecialize] def AdmissionOutcome.rationalReading? {generator : CoherentNamed}
    {root : SquareRootSidecar.Sidecar generator} (outcome : AdmissionOutcome generator root)
    (certificate : outcome.RationalCertificate) : Option (RationalSidecar generator) :=
  match outcome, certificate with
  | .zero _ _ _ reading, _ => some reading
  | .square _ _ _ _ _ _, retained => some retained.2.val
  | .admitted _, _ => none
  | .nonreal _, _ => none
  | .nonpositive _ _ _ _, _ => none

/-- Every original zero-parameter root retains its exact zero outcome and original-channel rational evidence. -/
theorem inspectRoot_zero {generator : CoherentNamed} (root : SquareRootSidecar.Sidecar generator)
    (zero : root.parameter = 0) :
    ∃ evidence, (inspectRoot root).outcome = .zero 0 (zero.trans Cast.ofCoordinate_zero.symm) rfl evidence ∧
      evidence.value = 0 := by
  rcases root with ⟨parameter, square, owner⟩
  cases zero
  unfold inspectRoot Cast.inspectReal
  dsimp only
  rewrite [dif_pos (Eq.refl _)]
  dsimp only
  rewrite [dif_pos (Eq.refl _)]
  exact ⟨_, rfl, rfl⟩

/-- Every supplied positive nonsquare real rational parameter produces an admitted original realization. -/
theorem inspectRoot_positive {generator : CoherentNamed} (root : SquareRootSidecar.Sidecar generator)
    (parameter : Rational) (same : root.parameter = Cast.CoordinateTaylor.ofCoordinate parameter)
    (positive : 0 < parameter) (missing : (Square.inspect parameter).root? = none) :
    ∃ accepted, (inspectRoot root).outcome = .admitted accepted ∧ accepted.parameter = parameter := by
  have nonzero : parameter ≠ 0 := by
    intro zero
    rewrite [zero] at positive
    exact positive.2 positive.1
  unfold inspectRoot
  dsimp only
  cases inspected : Cast.inspectReal root.parameter with
  | complex imaginary =>
      have zero : root.parameter.im = 0 := congrArg Basic.im same
      exact False.elim (imaginary zero)
  | real coordinate coefficient_eq =>
      have coordinate_eq : coordinate = parameter :=
        Cast.ofCoordinate_injective (coefficient_eq.symm.trans same)
      cases coordinate_eq
      dsimp only
      rewrite [dif_neg nonzero, dif_pos positive]
      split
      · rename_i candidate selected
        cases selected.symm.trans missing
      · exact ⟨_, rfl, rfl⟩

end Purelib.Algebra.Quadratic.Pair.Gaussian.Realization

end
