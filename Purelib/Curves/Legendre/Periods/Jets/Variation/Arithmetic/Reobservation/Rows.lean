module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Arithmetic.Reobservation
public import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation
import Purelib.Data.Fin
import Purelib.Data.Fin.Two
import Purelib.Data.Vector.Basic

/-! # Four adjacent-derivative rows on the same independently paid arithmetic bank

The two derivative orders and two differential coordinates select the
original source, target and independent slope readings. All four actual
certificates use the one retained paid bank and its same scalar/root data.
Selection performs no query, reobservation or coefficient preparation.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Arithmetic.Reobservations

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Calculus.Jet
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation (Reading)
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.RootContinuation

variable {parameter increment point : Canonical}
    {source : CertifiedSquareRoot.Certificate (Polynomials.curveValue parameter point)}
    {target : CertifiedSquareRoot.Certificate (Polynomials.curveValue (parameter + increment) point)}
    {unit : Norm.Basic.normSq increment ≤ 1}
    {jet : Sampling.SampledJet parameter increment point source target unit}
    {observations : Observations jet} {spatial : AccuracyRequest}

/-- The exact original source, target and independent slope Reading types of one adjacent-derivative row.

All three have the identical whole spatial/parameter minimum request.
Source and target retain their distinct original root processes, selected
states and observations, with the original polynomial-indexed forms.
-/
@[expose] def RowNumerics (order coordinate : Fin 2) : Type 1 :=
  Reading (Specification.Table.forms parameter (Specification.Table.baseIndex order coordinate))
      point source.value source.apart jet.sourceSample.state jet.sourceSample.observation
      (spatial.minimum jet.accuracy) ×
    Reading (Specification.Table.forms (parameter + increment) (Specification.Table.baseIndex order coordinate))
      point target.value target.apart jet.targetSample.state jet.targetSample.observation
      (spatial.minimum jet.accuracy) ×
    Reading (Specification.Table.forms parameter (Specification.Table.slopeIndex order coordinate))
      point source.value source.apart jet.sourceSample.state jet.sourceSample.observation
      (spatial.minimum jet.accuracy)

/-- Select the SAME three already materialized actual Reading records without executing an evaluator or query. -/
@[expose] def rowNumerics (paid : Reobservations observations spatial) (order coordinate : Fin 2) :
    RowNumerics (jet := jet) (spatial := spatial) order coordinate :=
  Data.Fin.casesDependent
    (motive := fun order : Fin 2 => RowNumerics (jet := jet) (spatial := spatial) order coordinate)
    (Data.Fin.casesDependent
      (motive := fun coordinate : Fin 2 => RowNumerics (jet := jet) (spatial := spatial) 0 coordinate)
      ((paid.sourceValue.get 0).requested.original, (paid.targetValue.get 0).requested.original,
        (paid.sourceFirst.get 0).requested.original)
      (Data.Fin.casesDependent
        ((paid.sourceValue.get 1).requested.original, (paid.targetValue.get 1).requested.original,
          (paid.sourceFirst.get 1).requested.original)
        (fun index => Fin.elim0 index)) coordinate)
    (Data.Fin.casesDependent
      (motive := fun index : Fin 1 => RowNumerics (jet := jet) (spatial := spatial) index.succ coordinate)
      (Data.Fin.casesDependent
        (motive := fun coordinate : Fin 2 => RowNumerics (jet := jet) (spatial := spatial) 1 coordinate)
        ((paid.sourceFirst.get 0).requested.original, (paid.targetFirst.get 0).requested.original,
          (paid.sourceSecond.get 0).requested.original)
        (Data.Fin.casesDependent
          ((paid.sourceFirst.get 1).requested.original, (paid.targetFirst.get 1).requested.original,
            (paid.sourceSecond.get 1).requested.original)
          (fun index => Fin.elim0 index)) coordinate)
      (fun index => Fin.elim0 index)) order

/-- Construct the original value or first Taylor certificate on the SAME paid bank at the selected coordinate. -/
@[expose] def rowCertificate (paid : Reobservations observations spatial) (order coordinate : Fin 2) :
    Quadratic.Basic.Certificate increment :=
  Fin.cases (paid.valueCertificate coordinate)
    (Fin.cases (paid.firstCertificate coordinate) (fun index => Fin.elim0 index)) order

/-- Materialize each of the four original row certificates once in a two-by-two original finite vector.

The outer index is derivative order and the inner is the original
coordinate. Every certificate consumes the same retained paid bank; this
operation constructs no root, observation, evaluator or comparison.
-/
@[expose] def rowCertificates (paid : Reobservations observations spatial) :
    Data.Vector (Data.Vector (Quadratic.Basic.Certificate increment) 2) 2 :=
  Data.Vector.Basic.vectorOfFn (fun order : Fin 2 =>
    Data.Vector.Basic.vectorOfFn (fun coordinate : Fin 2 => paid.rowCertificate order coordinate))

/-- The stored two-by-two factory reads the identical selected original row certificate. -/
theorem rowCertificates_apply (paid : Reobservations observations spatial) (order coordinate : Fin 2) :
    paid.rowCertificates order coordinate = paid.rowCertificate order coordinate := by
  unfold rowCertificates
  rewrite [Data.Vector.Basic.vectorOfFn_apply]
  rewrite [Data.Vector.Basic.vectorOfFn_apply]
  rfl

/-- The selected certificate base is the same original source Reading displayed by the row view. -/
theorem rowCertificate_base (paid : Reobservations observations spatial) (order coordinate : Fin 2) :
    (paid.rowCertificate order coordinate).base = (paid.rowNumerics order coordinate).1.reading := by
  rcases Data.Fin.Two.finTwo_cases order with equal | equal
  · subst order
    rcases Data.Fin.Two.finTwo_cases coordinate with equal | equal
    · subst coordinate
      exact paid.valueCertificate_base 0
    · subst coordinate
      exact paid.valueCertificate_base 1
  · subst order
    rcases Data.Fin.Two.finTwo_cases coordinate with equal | equal
    · subst coordinate
      exact paid.firstCertificate_base 0
    · subst coordinate
      exact paid.firstCertificate_base 1

/-- The selected certificate output remains the independent original target Reading of that same row. -/
theorem rowCertificate_output (paid : Reobservations observations spatial) (order coordinate : Fin 2) :
    (paid.rowCertificate order coordinate).output = (paid.rowNumerics order coordinate).2.1.reading := by
  rcases Data.Fin.Two.finTwo_cases order with equal | equal
  · subst order
    rcases Data.Fin.Two.finTwo_cases coordinate with equal | equal
    · subst coordinate
      exact paid.valueCertificate_output 0
    · subst coordinate
      exact paid.valueCertificate_output 1
  · subst order
    rcases Data.Fin.Two.finTwo_cases coordinate with equal | equal
    · subst coordinate
      exact paid.firstCertificate_output 0
    · subst coordinate
      exact paid.firstCertificate_output 1

/-- The selected certificate slope retains the actual independent source-first or source-second Reading. -/
theorem rowCertificate_slope (paid : Reobservations observations spatial) (order coordinate : Fin 2) :
    (paid.rowCertificate order coordinate).slope = (paid.rowNumerics order coordinate).2.2.reading := by
  rcases Data.Fin.Two.finTwo_cases order with equal | equal
  · subst order
    rcases Data.Fin.Two.finTwo_cases coordinate with equal | equal
    · subst coordinate
      exact paid.valueCertificate_slope 0
    · subst coordinate
      exact paid.valueCertificate_slope 1
  · subst order
    rcases Data.Fin.Two.finTwo_cases coordinate with equal | equal
    · subst coordinate
      exact paid.firstCertificate_slope 0
    · subst coordinate
      exact paid.firstCertificate_slope 1

/-- Every selected actual Reading triple obeys its original numerical Taylor remainder on the SAME new bank. -/
theorem row_remainder_le (paid : Reobservations observations spatial) (order coordinate : Fin 2) :
    Canonical.normSq ((paid.rowNumerics order coordinate).2.1.reading -
      (paid.rowNumerics order coordinate).1.reading -
      increment * (paid.rowNumerics order coordinate).2.2.reading) ≤
      (paid.rowCertificate order coordinate).factor * Canonical.normSq increment ^ 2 := by
  have bound := (paid.rowCertificate order coordinate).remainder_le
  rewrite [← (paid.rowCertificate order coordinate).expansion, paid.rowCertificate_base order coordinate,
    paid.rowCertificate_output order coordinate, paid.rowCertificate_slope order coordinate] at bound
  exact bound

end Purelib.Curves.Legendre.Periods.Jets.Variation.Arithmetic.Reobservations

end
