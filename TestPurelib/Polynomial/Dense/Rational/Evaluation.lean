module

import Purelib.Polynomial.Dense.Rational.Nonzero.Search.Interval
import Purelib.Polynomial.Dense.Rational.Nonzero.Search.List
import Purelib.Polynomial.Dense.Rational.Evaluation
import Purelib.Polynomial.Dense.Integer.Homogeneous
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Variation
import Purelib.Polynomial.Elimination.Separated.Scalar
import scripts.checkpoint.Integration
import Init.Core
import Init.Data.Fin.Lemmas

namespace TestPurelib.Polynomial.Dense.Rational.Evaluation

open Purelib
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Dense.Rational.Basic (CoordinatePolynomial)
open Purelib.Polynomial.Dense.Rational
open Purelib.Polynomial.Dense.Rational.Evaluation
open IntegrationCheckpoint

example : (prepare ([1 / 2, -3 / 2, 1] : List Rational)).isZero 1 = true := by
  decide +kernel

example : (prepare ([1 / 2, -3 / 2, 1] : List Rational)).isZero 2 = true := by
  decide +kernel

example : (prepare ([1 / 2, -3 / 2, 1] : List Rational)).isZero 0 = false := by
  decide +kernel

example : Nonzero.Search.List.firstNonzeroPrepared
    (⟨[1 / 2, -3 / 2, 1]⟩ : CoordinatePolynomial) [1, 2, 2, 0] = some 0 := by
  decide +kernel

example : Nonzero.Search.List.firstNonzeroPrepared
    (⟨[0, 0]⟩ : CoordinatePolynomial) [1, -1, 0] = none := by
  decide +kernel

example : Nonzero.Search.List.firstNonzeroPrepared
    (⟨[]⟩ : CoordinatePolynomial) [] = none := by
  decide +kernel

/-- A small signed homogeneous residue remains reducible through the ordinary public imports. -/
example : (Polynomial.Dense.Integer.Homogeneous.modularEval 7 1 2
    (([1, -3, 2] : List Int).map fun value => (Fin.intCast value : Fin 7))).val = 3 := by
  decide +kernel

/-- A vanishing residue keeps exact fallback for a nonzero constant. -/
example : (match ((prepare ([7] : List Rational)).zeroTestUsing 7 [0] rfl 0).2 with
    | .isTrue _ => true
    | .isFalse _ => false) = false := by
  decide +kernel

/-- Read a retained numerator through an IO boundary so two forces stay separate native calls. -/
@[noinline] private def readCached (cached : Thunk Int) : IO Int := pure cached.get

/-- Check exact rational values, ordered scans and endpoint sign variations.

Fixed fractional and nonmonic tables include leading and all-zero inputs,
repeated coordinates, empty scans and all three endpoint signs. Runtime checks
compare complete caches and original formulas without supplying native proofs.
-/
public def check : IO Unit := do
  let multiple := Data.Rat.Fraction.Cast.fromInt ((2147483647 : Int) * 2 ^ 256)
  for coefficients in ([[], [0, 0], [1 / 2, -3 / 2, 1], [0, 0, 1 / 2, -1],
      [-3 / 5, 0, 12 / 5], [multiple], [multiple, -multiple]] : List (List Rational)) do
    let p : CoordinatePolynomial := ⟨coefficients⟩
    let cached := prepare p.coeffs
    for points in ([[], [1, 2, 2, 0], [-2, 2, 3], [2, 2, 2], [-3, 0, 1, 3],
        [1 / 3, 1 / 2, -2 / 3]] : List (List Rational)) do
      for point in points do
        let originalValue := p.eval point
        let preparedValue := cached.evaluate point
        unless preparedValue = originalValue do
          throw (IO.userError "prepared homogeneous evaluation changed an exact original rational value")
        unless cached.isZero point = decide (originalValue = 0) do
          throw (IO.userError "integer zero classifier changed an original rational evaluation decision")
        let actualZero := match cached.zeroDecision point with
          | .isTrue _ => true
          | .isFalse _ => false
        unless actualZero = decide (originalValue = 0) do
          throw (IO.userError "modular zero decision changed an original rational evaluation predicate")
      let actual := Nonzero.Search.List.scanWithPrepared cached points
      let original := Nonzero.Search.List.scan p points
      unless actual.result = original.result do
        throw (IO.userError "prepared retained scan changed the original stopping result")
      unless actual.evaluations = original.evaluations do
        throw (IO.userError "prepared retained scan changed original ordered rational evaluations")
      unless Nonzero.Search.List.firstNonzeroWithPrepared cached points = Nonzero.Search.List.firstNonzero p points do
        throw (IO.userError "prepared scan changed an original ordered first-success or failure result")
      let table := fun index : Fin points.length => points[index.val]'index.isLt
      let indexed := Nonzero.Search.List.scanOfFn cached table
      unless indexed.result = original.result ∧ indexed.evaluations = original.evaluations do
        throw (IO.userError "indexed scan changed its original complete result or ordered rational cache")
      unless Nonzero.Search.List.firstNonzeroOfFn cached table = original.result do
        throw (IO.userError "projected indexed search changed its first hit or finite exhaustion")
    for modulus in ([1, 2, 7, 31, 2147483647] : List Nat) do
      if nonzero : modulus ≠ 0 then
        letI : NeZero modulus := ⟨nonzero⟩
        let residues : List (Fin modulus) := cached.cleared.coefficients.map Fin.intCast
        for point in ([0, 1, -1, 1 / 7, 1 / Data.Rat.Fraction.Cast.fromInt 2147483647] : List Rational) do
          let tested := cached.zeroTestUsing modulus residues rfl point
          let first ← readCached tested.1.val
          let second ← readCached tested.1.val
          let exact := cached.numerator point
          unless first = exact ∧ second = exact do
            throw (IO.userError "retained numerator forces changed the original exact integer")
          let actualZero := match tested.2 with
            | .isTrue _ => true
            | .isFalse _ => false
          unless actualZero = decide (p.eval point = 0) do
            throw (IO.userError "zero residue fallback changed the original exact polynomial decision")
      else throw (IO.userError "finite residue fixture supplied a zero modulus")
  for modulus in ([1, 2, 7, 31, 2147483647] : List Nat) do
    if nonzero : modulus ≠ 0 then
      letI : NeZero modulus := ⟨nonzero⟩
      for coefficients in ([[], [0], [1, -3, 2], [0, 0, -2, 7]] : List (List Int)) do
        let residues : List (Fin modulus) := coefficients.map Fin.intCast
        for numerator in ([-5, 0, 7] : List Int) do
          for denominator in ([0, 1, 2, 11] : List Nat) do
            let actual := Polynomial.Dense.Integer.Homogeneous.modularEval modulus numerator denominator residues
            let original := Polynomial.Dense.Integer.Homogeneous.homogeneousEval numerator denominator coefficients
            unless actual = (Fin.intCast original : Fin modulus) do
              throw (IO.userError "shared modular accumulator changed an original homogeneous integer residue")
    else throw (IO.userError "homogeneous residue fixture supplied a zero modulus")
  let fractional := (prepare ([-3 / 5, 0, 12 / 5] : List Rational)).evaluate (1 / 3)
  unless fractional.num = 7 ∧ fractional.den = 3 do
    throw (IO.userError "prepared nonzero homogeneous quotient lost its exact canonical numerator/denominator")
  let leading := (prepare ([0, 0, 1 / 2, -1] : List Rational)).evaluate (1 / 2)
  unless leading.num = -3 ∧ leading.den = 4 do
    throw (IO.userError "prepared leading-zero quotient lost its exact signed rational value")
  let empty := (prepare ([] : List Rational)).evaluate (-3 / 7)
  unless empty.num = 0 ∧ empty.den = 1 do
    throw (IO.userError "prepared empty-table zero fast path lost canonical zero")
  let polynomial : CoordinatePolynomial := ⟨[1 / 2, -3 / 2, 1]⟩
  let ordered := Nonzero.Search.List.scanPrepared polynomial [1, 2, 2, 0, 3]
  unless ordered.result = some 0 ∧ ordered.evaluations = [(1, 0), (2, 0), (2, 0), (0, 1)] do
    throw (IO.userError "prepared retained scan lost a missed occurrence or evaluated beyond its first hit")
  let exhausted := Nonzero.Search.List.scanPrepared polynomial [2, 1, 2]
  unless exhausted.result = none ∧ exhausted.evaluations = [(2, 0), (1, 0), (2, 0)] do
    throw (IO.userError "prepared exhausted scan dropped an original zero evaluation")
  let coefficientChains : List (List (List Rational)) :=
    [[], [[0, 0]], [[1], [-1], [0], [1]], [[1, 0], [-1, 0], [0, 0], [1, 0]],
      [[0, 1 / 2, -1], [1 / 2, -3 / 2, 1], [], [-3 / 5, 0, 12 / 5]]]
  for coefficients in coefficientChains do
    let chain : List CoordinatePolynomial := coefficients.map (fun values => ⟨values⟩)
    for point in ([-2, -1, 0, 1 / 3, 1 / 2, 1, 2, 3] : List Rational) do
      let original := Data.Rat.Sign.Variation.variation2 (chain.map fun polynomial => polynomial.eval point)
      let actual := SignedRemainder.Variation.Sturm.endpointVariation2 chain point
      unless actual = original do
        throw (IO.userError "integer endpoint signs changed the original doubled variation or zero transitions")
  System.IO.println "rational-zero: exact prepared values, retained ordered scans, roots and exhaustion checked"

/-- Check zero discrimination at one retained original Gaussian-polynomial axis coordinate.

The saved polynomial and rational coordinate are decoded from their actual
records. Its unchanged original scalar eliminant is constructed once; either
the shared projected scan or original rational discrimination is then evaluated
at that same coordinate in a separate measurable stage.
-/
public def checkStored (path : System.FilePath) (original : Bool) : IO Unit := do
  let raw : Data.Json ← loadJson path
  let coefficients : List GaussianData ← match raw.getObjValAs? (List GaussianData) "polynomial" with
    | .ok value => pure value
    | .error error => throw (IO.userError error)
  let parameterData : FractionData ← match raw.getObjValAs? FractionData "parameter" with
    | .ok value => pure value
    | .error error => throw (IO.userError error)
  let coefficients ← checked "original axis coefficients" (coefficients.mapM decodeGaussian)
  let point ← checked "original axis coordinate" (decodeFraction parameterData)
  let p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial := ⟨coefficients⟩
  let eliminated := Polynomial.Elimination.Separated.Scalar.scalarEliminant p
  System.IO.println s!"rational-zero: original scalar eliminant degree {eliminated.natDegree} retained"
  (← IO.getStdout).flush
  let answer ← if original then
      System.IO.println "rational-zero: original rational discrimination starts"
      (← IO.getStdout).flush
      pure (decide (eliminated.eval point = 0))
    else do
      let cached := prepare eliminated.coeffs
      System.IO.println s!"rational-zero: integer coefficient clearance complete; \
        {cached.cleared.coefficients.length} slots"
      (← IO.getStdout).flush
      let selected := Nonzero.Search.List.firstNonzeroOfFn cached (fun _ : Fin 1 => point)
      match selected with
      | none => pure true
      | some actual =>
          unless actual = point do
            throw (IO.userError "projected scan changed the retained original coordinate")
          pure false
  unless answer = false do
    throw (IO.userError "retained original safe coordinate became a zero")
  System.IO.println "rational-zero: retained original safe coordinate is nonzero"

end TestPurelib.Polynomial.Dense.Rational.Evaluation
