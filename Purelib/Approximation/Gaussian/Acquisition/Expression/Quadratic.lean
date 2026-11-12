module

public import Purelib.Approximation.Gaussian.Acquisition.Expression.Coordinates
public import Purelib.Approximation.Gaussian.Acquisition.Expression.Realization
public import Purelib.Approximation.Gaussian.Provenance.Quadratic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Admission and pair inspection at original expression bindings

The actual root annotation supplies the generator owner. Admission inspects
its retained rational parameter once; admitted cases inspect the existing
polynomial cache. Rejected admission and unresolved coordinate inspections
remain available as typed data at the original source.
-/

public section

namespace Purelib.Approximation.Gaussian.Acquisition.Expression.Basic.Normalized

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Algebra.Quadratic.Pair.Gaussian (Realization)
open Purelib.Polynomial.Multivariate
open Purelib.Riemann.RootContinuation

variable {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}

/-- The pair check required precisely when the retained root admission succeeds. -/
@[expose] def RootCoordinates (normalized : Normalized environment expression)
    (index : Fin normalized.bindings.length)
    {root : SquareRootSidecar.Sidecar (Binding.channels normalized.bindings index)} :
    Realization.AdmissionOutcome (Binding.channels normalized.bindings index) root → Type 1
  | .admitted admission => Gaussian.Normalized.PairCheck normalized.polynomial index admission.parameter
  | _ => PUnit

set_option genInjectivity false in
/-- An original root occurrence with its complete admission and conditional cached pair inspection. -/
structure RootInspection (normalized : Normalized environment expression)
    (index : Fin normalized.bindings.length)
    (root : SquareRootSidecar.Sidecar (Binding.channels normalized.bindings index)) where
  /-- The entire original cached expression normalization. -/
  source : Normalized environment expression
  /-- The retained source is the actual original input, including its compilation and bindings. -/
  source_eq : source = normalized
  /-- The complete original supplied root owner. -/
  origin : SquareRootSidecar.Sidecar (Binding.channels normalized.bindings index)
  /-- The retained root owner is the original input sidecar. -/
  origin_eq : origin = root
  /-- The actual annotation at the requested original position supplies this exact root owner. -/
  selected : (Binding.read normalized.bindings index).annotation.provenance = some (.squareRoot root)
  /-- The complete cached parameter admission, including every rejected condition. -/
  admission : Realization.AdmissionCheck (Binding.channels normalized.bindings index) root
  /-- Admitted cases retain the actual pair check and all unresolved support or coefficient conditions. -/
  coordinates : RootCoordinates normalized index admission.outcome

constructive_injectivity RootInspection

/-- Inspect one actual supplied root without rebuilding its original expression, annotation or isolation. -/
@[noinline, nospecialize] def inspectRoot (normalized : Normalized environment expression)
    (index : Fin normalized.bindings.length)
    (root : SquareRootSidecar.Sidecar (Binding.channels normalized.bindings index))
    (selected : (Binding.read normalized.bindings index).annotation.provenance = some (.squareRoot root)) :
    RootInspection normalized index root :=
  let cached := normalized.inspections.get normalized.bindings index
  let admission := (cached.rootData root selected).1
  let coordinates : RootCoordinates normalized index admission.outcome := match admission.outcome with
    | .admitted accepted => normalized.polynomial.inspectPair index accepted.parameter
    | .nonreal _ => PUnit.unit
    | .zero _ _ _ _ => PUnit.unit
    | .nonpositive _ _ _ _ => PUnit.unit
    | .square _ _ _ _ _ _ => PUnit.unit
  ⟨normalized, rfl, root, rfl, selected, admission, coordinates⟩

/-- Attach a successful original pair reading while keeping every rejected inspection in its source certificate. -/
@[noinline, nospecialize] def RootInspection.evidence? {normalized : Normalized environment expression}
    {index : Fin normalized.bindings.length}
    {root : SquareRootSidecar.Sidecar (Binding.channels normalized.bindings index)}
    (inspection : RootInspection normalized index root) :
    Option (Quadratic.Sidecar normalized.compiled.annotation.channel) :=
  match inspection.admission.outcome, inspection.coordinates with
  | .admitted accepted, coordinates =>
      match coordinates.result with
      | .pair _ _ value _ reading reading_eq equivalent =>
          some (Quadratic.Sidecar.ofAdmission accepted value reading reading_eq equivalent)
      | .powers _ _ => none
      | .coefficients _ _ _ => none
  | .nonreal _, _ => none
  | .zero _ _ _ _, _ => none
  | .nonpositive _ _ _ _, _ => none
  | .square _ _ _ _ _ _, _ => none

set_option genInjectivity false in
/-- The exact original annotation class and every root inspection at a bounded binding position. -/
inductive GeneratorInspection (normalized : Normalized environment expression)
    (index : Fin normalized.bindings.length) where
  /-- The original annotation supplies no provenance for this generator. -/
  | absent (selected : (Binding.read normalized.bindings index).annotation.provenance = none)
  /-- The original annotation already supplies an exact rational value. -/
  | rational (sidecar : RationalSidecar (Binding.channels normalized.bindings index))
      (selected : (Binding.read normalized.bindings index).annotation.provenance = some (.rational sidecar))
  /-- Retain the original composite coordinates and complete cached interpretation attempt at their same owner. -/
  | composite (sidecar : Quadratic.Sidecar (Binding.channels normalized.bindings index))
      (selected : (Binding.read normalized.bindings index).annotation.provenance = some (.quadratic sidecar))
      (inspection : RealizationCheck normalized sidecar.admission.realization sidecar.admission.coefficient_eq
        (Binding.read normalized.bindings index))
  /-- Retain the actual supplied root, its annotation equation and the complete cached inspection. -/
  | root (sidecar : SquareRootSidecar.Sidecar (Binding.channels normalized.bindings index))
      (inspection : RootInspection normalized index sidecar)
  /-- Retain the original general root evidence without asserting quadratic coordinates. -/
  | polynomialRoot (sidecar : PolynomialRoot.Sidecar (Binding.channels normalized.bindings index))
      (selected : (Binding.read normalized.bindings index).annotation.provenance = some (.polynomialRoot sidecar))
  /-- Retain the original algebraic construction without asserting quadratic coordinates. -/
  | algebraic (sidecar : Algebraic.Sidecar (Binding.channels normalized.bindings index))
      (selected : (Binding.read normalized.bindings index).annotation.provenance = some (.algebraic sidecar))

constructive_injectivity GeneratorInspection

/-- Inspect the actual annotation at one original position, retaining the reason for every unsupported class. -/
@[expose, noinline, nospecialize] def inspectGenerator (normalized : Normalized environment expression)
    (index : Fin normalized.bindings.length) : GeneratorInspection normalized index :=
  match selected : (Binding.read normalized.bindings index).annotation.provenance with
  | none => .absent selected
  | some (.rational reading) => .rational reading selected
  | some (.squareRoot root) => .root root (normalized.inspectRoot index root selected)
  | some (.quadratic composite) =>
      .composite composite selected (normalized.inspectRealization composite.admission.realization
        composite.admission.coefficient_eq (Binding.read normalized.bindings index) composite.evidence)
  | some (.polynomialRoot root) => .polynomialRoot root selected
  | some (.algebraic sidecar) => .algebraic sidecar selected

/-- Read admitted evidence from a retained root attempt without repeating either inspection. -/
@[expose, noinline, nospecialize] def GeneratorInspection.evidence? {normalized : Normalized environment expression}
    {index : Fin normalized.bindings.length} (inspection : GeneratorInspection normalized index) :
    Option (Quadratic.Sidecar normalized.compiled.annotation.channel) :=
  match inspection with
  | .root _ retained => retained.evidence?
  | .absent _ => none
  | .rational _ _ => none
  | .polynomialRoot _ _ => none
  | .algebraic _ _ => none
  | .composite original _ retained =>
      match retained.evidence? with
      | some evidence => some (original.withEvidence evidence)
      | none => none

/-- Inspect every position in a bounded original prefix, in descending original-index order. -/
@[expose, noinline, nospecialize] def inspectPrefix (normalized : Normalized environment expression) :
    (count : Nat) → count ≤ normalized.bindings.length →
      List (Sigma (GeneratorInspection normalized))
  | 0, _ => []
  | count + 1, bound =>
      let index : Fin normalized.bindings.length := ⟨count, Nat.lt_of_lt_of_le (Nat.lt_succ_self count) bound⟩
      ⟨index, normalized.inspectGenerator index⟩ :: normalized.inspectPrefix count (Nat.le_of_succ_le bound)

/-- The original position list of a descending finite prefix. -/
@[expose] def prefixIndices : Nat → List Nat
  | 0 => []
  | count + 1 => count :: prefixIndices count

/-- Every requested original position is retained once, with no missing or unrelated binding index. -/
theorem inspectPrefix_indices (normalized : Normalized environment expression)
    (count : Nat) (bound : count ≤ normalized.bindings.length) :
    (normalized.inspectPrefix count bound).map (fun entry => entry.1.val) = prefixIndices count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      exact congrArg (fun tail => count :: tail) (ih (Nat.le_of_succ_le bound))

/-- Select the first admitted cached reading in the actual retained inspection order. -/
@[expose, noinline, nospecialize] def evidenceFrom {normalized : Normalized environment expression} :
    List (Sigma (GeneratorInspection normalized)) → Option (Quadratic.Sidecar normalized.compiled.annotation.channel)
  | [] => none
  | first :: remaining =>
      match first.2.evidence? with
      | some evidence => some evidence
      | none => evidenceFrom remaining

set_option genInjectivity false in
/-- A complete finite generator inspection with all outcomes and its cached admitted source evidence. -/
structure GeneratorCheck (normalized : Normalized environment expression) where
  /-- The entire original cached normalization. -/
  source : Normalized environment expression
  /-- The retained source is the actual input normalization. -/
  source_eq : source = normalized
  /-- All attempted original positions and their typed admission or coordinate outcomes. -/
  attempts : List (Sigma (GeneratorInspection normalized))
  /-- The attempts cover the complete original finite binding cache once in the stated order. -/
  indices_eq : attempts.map (fun entry => entry.1.val) = prefixIndices normalized.bindings.length
  /-- The actual cached admitted evidence, if one inspection succeeded. -/
  evidence : Option (Quadratic.Sidecar normalized.compiled.annotation.channel)
  /-- The cache is the result of reading those same retained attempts. -/
  evidence_eq : evidence = evidenceFrom attempts

constructive_injectivity GeneratorCheck

/-- Inspect the complete original binding cache once and retain every outcome together with any admitted reading. -/
@[expose, noinline, nospecialize] def inspectGenerators (normalized : Normalized environment expression) :
    GeneratorCheck normalized :=
  let attempts := normalized.inspectPrefix normalized.bindings.length (Nat.le_refl _)
  let evidence := evidenceFrom attempts
  ⟨normalized, rfl, attempts, normalized.inspectPrefix_indices _ (Nat.le_refl _), evidence, rfl⟩

/-- Enrich the original annotation using the cached admitted reading, preserving it when all attempts are unresolved. -/
@[expose] def GeneratorCheck.annotate {normalized : Normalized environment expression}
    (check : GeneratorCheck normalized) : Annotated :=
  match check.evidence with
  | some evidence => ⟨normalized.compiled.annotation.channel, some (.quadratic evidence)⟩
  | none => normalized.compiled.annotation

/-- Admission enrichment preserves the exact original numerical channel in every outcome. -/
theorem GeneratorCheck.annotate_channel {normalized : Normalized environment expression}
    (check : GeneratorCheck normalized) : check.annotate.channel = normalized.compiled.annotation.channel := by
  unfold GeneratorCheck.annotate
  cases check.evidence <;> rfl

/-- Attach a checked common-owner interpretation at the original source, preserving any already supplied provenance. -/
@[noinline, nospecialize] def RealizationCheck.annotate {normalized : Normalized environment expression}
    {basis : Binding environment} (origin : Quadratic.Sidecar basis.channel)
    (check : RealizationCheck normalized origin.admission.realization origin.admission.coefficient_eq basis) :
    Annotated :=
  match normalized.compiled.annotation.provenance with
  | some _ => normalized.compiled.annotation
  | none => match check.evidence? with
    | some evidence => ⟨normalized.compiled.annotation.channel, some (.quadratic (origin.withEvidence evidence))⟩
    | none => normalized.compiled.annotation

/-- Common-owner annotation retains the entire original source channel in every outcome. -/
theorem RealizationCheck.annotate_channel {normalized : Normalized environment expression}
    {basis : Binding environment} (origin : Quadratic.Sidecar basis.channel)
    (check : RealizationCheck normalized origin.admission.realization origin.admission.coefficient_eq basis) :
    (check.annotate origin).channel = normalized.compiled.annotation.channel := by
  unfold RealizationCheck.annotate
  split
  · rfl
  · split <;> rfl

/-- Already supplied original provenance is retained literally by common-owner annotation. -/
theorem RealizationCheck.annotate_preserves {normalized : Normalized environment expression}
    {basis : Binding environment} (origin : Quadratic.Sidecar basis.channel)
    (check : RealizationCheck normalized origin.admission.realization origin.admission.coefficient_eq basis)
    {provenance : Purelib.Approximation.Gaussian.Acquisition.Provenance normalized.compiled.annotation.channel}
    (known : normalized.compiled.annotation.provenance = some provenance) :
    check.annotate origin = normalized.compiled.annotation := by
  unfold RealizationCheck.annotate
  rewrite [known]
  rfl

end Purelib.Approximation.Gaussian.Acquisition.Expression.Basic.Normalized

end
