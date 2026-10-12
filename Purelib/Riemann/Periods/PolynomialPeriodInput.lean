module
import Purelib.Data.List.Append
import Purelib.Data.List.Flatten
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.SquareFactor.Basic

public import Purelib.Curves.Hyperelliptic.Preparation.Polynomial
public import Purelib.Riemann.Periods.PeriodReplay

import Purelib.Elab.Deriving.Repr

public section

/-!
# Checked polynomial-first standard-period selections

The public constructor takes coefficients and raw finite indices.  Genus,
square-factor reduction and index validity are computed internally.  The
accepted entry retains a lazy canonical preparation of the reduced curve.
It denotes a normalized standard period, not an untransported `dx/y` on the
original possibly singular equation.
-/

namespace Purelib.Riemann.Periods.PolynomialPeriodInput

open _root_.Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial ->
  GaussianPolynomial

set_option genInjectivity false in
/-- The A- or B-cycle side of a standard period selection. -/
inductive Side where
  /-- Select the A-cycle family. -/ | a
  /-- Select the B-cycle family. -/ | b
deriving DecidableEq

constructive_injectivity Side

derive_exposed_repr Side

set_option genInjectivity false in
/-- Raw finite indices and an A/B side selecting one standard period. -/
structure Selection where
  /-- The requested A- or B-cycle family. -/ side : Side
  /-- The raw natural index of the requested standard differential. -/ differential : Nat
  /-- The raw natural index of the requested cycle. -/ cycle : Nat
deriving DecidableEq

constructive_injectivity Selection

derive_exposed_repr Selection

set_option genInjectivity false in
/-- Checked evidence that both raw selection indices fit the retained computed genus. -/
structure Bounds (selection : Selection) (genus : Nat) : Type where
  /-- The differential index is below the computed genus. -/ differential_lt : selection.differential < genus
  /-- The cycle index is below the computed genus. -/ cycle_lt : selection.cycle < genus

constructive_injectivity Bounds

open Purelib.Riemann in
/-- Convert the raw selection to a finite standard entry using its retained bounds. -/
@[expose] def Selection.entry (selection : Selection) {genus : Nat} (bounds : Bounds selection genus) :
    Periods.PeriodReplay.StandardEntry genus :=
  match selection.side with
  | .a => .a ⟨selection.differential, bounds.differential_lt⟩ ⟨selection.cycle, bounds.cycle_lt⟩
  | .b => .b ⟨selection.differential, bounds.differential_lt⟩ ⟨selection.cycle, bounds.cycle_lt⟩

set_option genInjectivity false in
/-- A certificate identifying the first out-of-range selection index.

The cycle-failure case retains successful differential validation, preserving the checker's branch order. -/
inductive IndexFailure (selection : Selection) (genus : Nat) where
  /-- The requested differential index is at least the computed genus. -/ | differential (outOfRange : genus ≤
    selection.differential)
  /-- The differential index is valid but the cycle index is at least the computed genus. -/ | cycle (differentialValid
    : selection.differential < genus) (outOfRange : genus ≤ selection.cycle)

constructive_injectivity IndexFailure

/-- Check both raw indices and return their bounds or the actual finite range obstruction. -/
@[expose] def checkIndices (selection : Selection) (genus : Nat) :
    Except (IndexFailure selection genus) (Bounds selection genus) :=
  if differential : selection.differential < genus then
    if cycle : selection.cycle < genus then .ok ⟨differential, cycle⟩
    else .error (.cycle differential (Nat.le_of_not_gt cycle))
  else .error (.differential (Nat.le_of_not_gt differential))

/-- A selection with valid retained bounds is accepted by the index checker. -/
theorem checkIndices_complete (selection : Selection) (genus : Nat)
    (bounds : Bounds selection genus) : checkIndices selection genus = .ok bounds := by
  rw [checkIndices, dif_pos bounds.differential_lt, dif_pos bounds.cycle_lt]

/-- A certified index failure excludes valid bounds for the same selection and genus. -/
theorem IndexFailure.excludes_bounds {selection : Selection} {genus : Nat}
    (failure : IndexFailure selection genus) (bounds : Bounds selection genus) : False := by
  cases failure with
  | differential outside => exact Nat.not_lt_of_ge outside bounds.differential_lt
  | cycle _ outside => exact Nat.not_lt_of_ge outside bounds.cycle_lt

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Polynomial in
set_option genInjectivity false in
/-- The computed regular curve and checked period selection with one shared preparation thunk.

The source polynomial is nonzero, both indices fit the computed genus, and the cached replay entry equals the canonical
preparation for that exact reduced curve. -/
structure PreparedEntry (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
  (selection : Selection)
  where
  /-- The original polynomial is certified nonzero. -/ sourceNonzero : polynomial.isZero = false
  /-- The retained regular-curve preparation of the original polynomial. -/ prepared :
    Hyperelliptic.Preparation.Polynomial.Prepared polynomial
  /-- Both selection indices fit the retained preparation's computed genus. -/ bounds : Bounds selection prepared.genus
  /-- The shared thunk retaining the selected canonical period entry. -/ entryCache : Thunk (Periods.PeriodReplay.Entry
    prepared.curve)
  /-- The cached entry is the canonical entry of the retained reduced curve and bounded selection. -/ entry_eq :
    entryCache.get = Periods.PeriodReplay.canonical prepared.curve (selection.entry bounds)

constructive_injectivity PreparedEntry

namespace PreparedEntry

open Purelib.Riemann in
open Purelib.Polynomial in
/-- Read the exact selected period entry from its retained shared thunk. -/
@[expose] def entry {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {selection : Selection}
    (prepared : PreparedEntry polynomial selection) :
    Periods.PeriodReplay.Entry prepared.prepared.curve := prepared.entryCache.get

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Polynomial in
/-- Retain an already computed regular curve and checked selection in a shared entry thunk. -/
@[expose] def ofCurve {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  (selection : Selection)
    (nonzero : polynomial.isZero = false) (prepared : Hyperelliptic.Preparation.Polynomial.Prepared polynomial)
    (bounds : Bounds selection prepared.genus) : PreparedEntry polynomial selection :=
  { sourceNonzero := nonzero
    prepared := prepared
    bounds := bounds
    entryCache := ⟨fun _ => Periods.PeriodReplay.canonical prepared.curve (selection.entry bounds)⟩
    entry_eq := rfl }

end PreparedEntry

open Purelib.Curves in
open Purelib.Polynomial in
set_option genInjectivity false in
/-- A certified finite polynomial or selection obstruction to a standard period entry.

The cases retain zero or degree evidence, the actual square-factor reduction when relevant, or the computed regular
curve with its invalid-index certificate. -/
inductive Failure (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (selection
  : Selection) where
  /-- The original polynomial is zero. -/ | zero (certificate : polynomial.isZero = true)
  /-- The nonzero input has degree zero and its retained reduced radicand also has degree zero. -/ | constantInput
    (nonzero : polynomial.isZero = false) (degreeZero : polynomial.natDegree = 0)
      (reduction : Dense.Gaussian.Squarefree.SquareFactor.Basic.Reduction polynomial)
      (radicandDegreeZero : reduction.radicand.natDegree = 0)
  /-- The positive-degree input's retained square-factor reduction has a constant radicand. -/ | squareTimesConstant
    (nonzero : polynomial.isZero = false) (degreePositive : 0 < polynomial.natDegree)
      (reduction : Dense.Gaussian.Squarefree.SquareFactor.Basic.Reduction polynomial)
      (radicandDegreeZero : reduction.radicand.natDegree = 0)
  /-- The actual regular-curve preparation has a certified out-of-range requested index. -/ | invalidIndex (prepared :
    Hyperelliptic.Preparation.Polynomial.Prepared polynomial)
      (failure : IndexFailure selection prepared.genus)

constructive_injectivity Failure

section
open Purelib.Curves
open Purelib.Polynomial
/-- Check the selection against an already computed regular curve and retain the accepted entry. -/
@[expose] def prepareRegular {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  (selection :
  Selection)
    (nonzero : polynomial.isZero = false) (prepared : Hyperelliptic.Preparation.Polynomial.Prepared polynomial) :
    Except (Failure polynomial selection) (PreparedEntry polynomial selection) :=
  match checkIndices selection prepared.genus with
  | .error failure => .error (.invalidIndex prepared failure)
  | .ok bounds => .ok (PreparedEntry.ofCurve selection nonzero prepared bounds)

/-- Compute a certified standard-period entry from polynomial coefficients and raw indices.

The finite preparation determines square-factor reduction, genus and curve validity, then checks both selection indices.
Every rejected branch retains its actual finite obstruction. -/
@[expose] def prepare (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
  (selection : Selection) :
    Except (Failure polynomial selection) (PreparedEntry polynomial selection) :=
  match Hyperelliptic.Preparation.Polynomial.prepare polynomial with
  | .zero certificate => .error (.zero certificate)
  | .constantInput nonzero degreeZero reduction reducedZero =>
      .error (.constantInput nonzero degreeZero reduction reducedZero)
  | .squareTimesConstant nonzero degreePositive reduction reducedZero =>
      .error (.squareTimesConstant nonzero degreePositive reduction reducedZero)
  | .regular nonzero prepared => prepareRegular selection nonzero prepared

/-- Valid bounds make regular-curve entry preparation return the retained prepared entry. -/
theorem prepareRegular_complete {polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (selection :
  Selection)
    (nonzero : polynomial.isZero = false) (prepared : Hyperelliptic.Preparation.Polynomial.Prepared polynomial)
    (bounds : Bounds selection prepared.genus) :
    prepareRegular selection nonzero prepared =
      .ok (PreparedEntry.ofCurve selection nonzero prepared bounds) := by
  rw [prepareRegular, checkIndices_complete selection prepared.genus bounds]

/-- Regular-curve entry preparation succeeds exactly when both raw indices fit its computed genus. -/
theorem prepareRegular_success_iff {polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (selection :
  Selection)
    (nonzero : polynomial.isZero = false) (prepared : Hyperelliptic.Preparation.Polynomial.Prepared polynomial) :
    (∃ entry, prepareRegular selection nonzero prepared = .ok entry) ↔
      selection.differential < prepared.genus ∧ selection.cycle < prepared.genus := by
  constructor
  · rintro ⟨entry, success⟩
    unfold prepareRegular at success
    cases checked : checkIndices selection prepared.genus with
    | error failure =>
        rw [checked] at success
        nomatch success
    | ok bounds => exact ⟨bounds.differential_lt, bounds.cycle_lt⟩
  · rintro ⟨differential, cycle⟩
    let bounds : Bounds selection prepared.genus := ⟨differential, cycle⟩
    exact ⟨PreparedEntry.ofCurve selection nonzero prepared bounds,
      prepareRegular_complete selection nonzero prepared bounds⟩

/-- The actual polynomial preparation yields a genus admitting both requested indices.

This proposition refers to the computed reduction and raw finite selection; it introduces no alternate genus or
executable preprocessing pass. -/
@[expose] def Admissible (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
  (selection : Selection)
  : Prop :=
  ∃ genus, (Hyperelliptic.Preparation.Polynomial.prepare polynomial).genus? = some genus ∧
    selection.differential < genus ∧ selection.cycle < genus

/-- Polynomial-first entry preparation succeeds exactly for admissible raw input and selection.

The characterization uses the actual computed regular genus, including the absence of valid standard entries at genus
zero. -/
theorem prepare_success_iff (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
  (selection :
  Selection) :
    (∃ entry, prepare polynomial selection = .ok entry) ↔ Admissible polynomial selection := by
  cases computed : Hyperelliptic.Preparation.Polynomial.prepare polynomial with
  | zero certificate =>
      constructor
      · rintro ⟨entry, success⟩
        rw [prepare, computed] at success
        nomatch success
      · rintro ⟨genus, present, _⟩
        rw [computed] at present
        nomatch present
  | constantInput nonzero degreeZero reduction reducedZero =>
      constructor
      · rintro ⟨entry, success⟩
        rw [prepare, computed] at success
        nomatch success
      · rintro ⟨genus, present, _⟩
        rw [computed] at present
        nomatch present
  | squareTimesConstant nonzero degreePositive reduction reducedZero =>
      constructor
      · rintro ⟨entry, success⟩
        rw [prepare, computed] at success
        nomatch success
      · rintro ⟨genus, present, _⟩
        rw [computed] at present
        nomatch present
  | regular nonzero prepared =>
      constructor
      · rintro ⟨entry, success⟩
        have accepted : prepareRegular selection nonzero prepared = .ok entry := by
          simpa only [prepare, computed, -eq_self, -iff_self] using success
        exact ⟨prepared.genus, by rw [computed]; rfl,
          (prepareRegular_success_iff selection nonzero prepared).mp ⟨entry, accepted⟩⟩
      · rintro ⟨genus, present, differential, cycle⟩
        have sameGenus : prepared.genus = genus := Option.some.inj (by
          simpa only [computed, Hyperelliptic.Preparation.Polynomial.Outcome.genus?, -eq_self, -iff_self] using present)
        have bounds : selection.differential < prepared.genus ∧ selection.cycle < prepared.genus := by
          rw [sameGenus]
          exact ⟨differential, cycle⟩
        obtain ⟨entry, success⟩ := (prepareRegular_success_iff selection nonzero prepared).mpr bounds
        exact ⟨entry, by simpa only [prepare, computed, -eq_self, -iff_self] using success⟩

end

end Purelib.Riemann.Periods.PolynomialPeriodInput

end
