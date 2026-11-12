module

meta import Purelib.Approximation.Gaussian.Acquisition.Expression.Normalization
meta import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
meta import Purelib.Polynomial.Multivariate.Gaussian.Normalization
meta import Purelib.Data.Gaussian.Basic
meta import Purelib.Approximation.Gaussian.Name.Sampling
meta import Purelib.Data.Gaussian.Norm.Basic
meta import Lean.Elab.Command

/-!
# Separate finite operational normalization measurements

Repeated factors, dense cubic products and cancellation retain their original
opaque annotations. The observations separate original compilation, cached
normalization and an actual comparison request. Data counts describe finite
syntax and coefficient storage; schema node counts describe retained kernel
expressions, independently of checking and emission times in profiling receipts.
-/

meta section

namespace TestPurelib.Approximation.Gaussian.OperationalCosts

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Acquisition.Expression.Basic (Expr Compiled Normalized)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Name
open Purelib.Data.Gaussian

/-- Count original finite arithmetic syntax nodes, including repeated occurrences. -/
private def nodes : Expr arity → Nat
  | .atom _ | .rational _ | .root _ _ => 1
  | .neg input => 1 + nodes input
  | .add left right | .sub left right | .mul left right => 1 + nodes left + nodes right

/-- Read the original arithmetic degree before cancellation or coefficient reduction. -/
private def degree : Expr arity → Nat
  | .atom _ | .root _ _ => 1
  | .rational _ => 0
  | .neg input => degree input
  | .add left right | .sub left right => max (degree left) (degree right)
  | .mul left right => degree left + degree right

/-- Observe an original atom key in the finite syntax without identifying its numerical channel. -/
private def hasAtom (index : Nat) : Expr arity → Bool
  | .atom actual => actual.val == index
  | .rational _ | .root _ _ => false
  | .neg input => hasAtom index input
  | .add left right | .sub left right | .mul left right => hasAtom index left || hasAtom index right

/-- The largest decimal digit count of the original Gaussian coefficient's numerator or denominator coordinates. -/
private def coefficientDigits (value : Canonical) : Nat :=
  max (max (toString value.re.num.natAbs).length (toString value.re.den).length)
    (max (toString value.im.num.natAbs).length (toString value.im.den).length)

/-- The deterministic repeated-factor, dense-product and cancellation-heavy original syntax fixtures. -/
private def cases : List (String × Expr 3) :=
  let first : Expr 3 := .atom 0
  let second : Expr 3 := .atom 1
  let third : Expr 3 := .atom 2
  let shifted := Expr.add first (.rational 1)
  let sum := Expr.add (.add first second) third
  let permuted := Expr.add third (.add first second)
  let cubic := Expr.mul (.mul sum sum) sum
  let other := Expr.mul (.mul permuted permuted) permuted
  [("repeated-factor", .mul shifted shifted), ("dense-cubic", cubic),
    ("cubic-cancellation", .sub cubic other)]

/-- Execute original compilation inside the measured IO action, preserving its actual expression index. -/
@[noinline, nospecialize] private def compileFixture (environment : Fin 3 → Annotated) (expression : Expr 3) :
    (Compiled environment expression → IO Unit) → IO Unit :=
  fun observe => observe (expression.retain environment)

/-- Execute complete retained normalization inside the measured IO action. -/
@[noinline, nospecialize] private def normalizeFixture {environment : Fin 3 → Annotated} {expression : Expr 3}
    (compiled : Compiled environment expression) : (Normalized environment expression → IO Unit) → IO Unit :=
  fun observe => observe compiled.normalize

/-- Measure original compilation and coefficient/certificate normalization independently of comparison requests. -/
private def measure : IO Unit := do
  let environment : Fin 3 → Annotated := fun index =>
    Annotated.opaque (CoherentNamed.Coherence.exact (if index.val = 0 then 1 else if index.val = 1 then 2 else 3))
  for (label, expression) in cases do
    let started ← IO.monoNanosNow
    compileFixture environment expression fun compiled => do
      let afterCompilation ← IO.monoNanosNow
      normalizeFixture compiled fun normalized => do
        let afterNormalization ← IO.monoNanosNow
        let atomCount := (List.range 3).countP (fun index => hasAtom index expression)
        let terms := normalized.polynomial.form.terms
        let digits := terms.foldl (fun size term => max size (coefficientDigits term.coefficient)) 0
        IO.println s!"{label}: atoms={atomCount} degree={degree expression} syntax_nodes={nodes expression} \
          monomials={terms.length} coefficient_digits={digits} compilation_us={(afterCompilation - started) / 1000} \
          normalization_and_certificate_us={(afterNormalization - afterCompilation) / 1000}"

#eval measure

/-- Measure one actual atom-normalization comparison at its retained original and canonical channels. -/
private def measureComparison : IO Unit := do
  let channel := CoherentNamed.Coherence.exact 2
  let normalized := Purelib.Polynomial.Multivariate.Gaussian.Normalized.atom (fun _ : Fin 1 => channel) 0
  let started ← IO.monoNanosNow
  let comparison := normalized.equivalent.compare 0 0 1 (by decide +kernel)
  let finished ← IO.monoNanosNow
  IO.println s!"atom-comparison: atoms=1 degree=1 monomials=1 target=1 \
    comparison_us={(finished - started) / 1000} indices={comparison.leftIndex},{comparison.rightIndex}"

#eval measureComparison

/-- Measure the same repeated-factor request whose former sampled-name round trips were expensive. -/
private def measureRepeatedComparison : IO Unit := do
  let environment : Fin 3 → Annotated := fun index =>
    Annotated.opaque (CoherentNamed.Coherence.exact (if index.val = 0 then 1 else if index.val = 1 then 2 else 3))
  match cases with
  | [] => throw (IO.userError "missing original repeated-factor fixture")
  | (label, expression) :: _ =>
      compileFixture environment expression fun compiled => do
        normalizeFixture compiled fun normalized => do
          let started ← IO.monoNanosNow
          let comparison := normalized.polynomial.equivalent.compare 0 0 1 (by decide +kernel)
          let finished ← IO.monoNanosNow
          let original :=
            (Sampling.approximation normalized.compiled.annotation.channel.name).sample comparison.leftIndex
          let canonical := (Sampling.approximation normalized.polynomial.channel.name).sample comparison.rightIndex
          unless Norm.Basic.normSq (original - canonical) < 1 do
            throw (IO.userError "the original comparison's returned indices did not satisfy its actual sample bound")
          IO.println s!"{label}-comparison: target=1 comparison_us={(finished - started) / 1000} \
            indices={comparison.leftIndex},{comparison.rightIndex}"

#eval measureRepeatedComparison

end TestPurelib.Approximation.Gaussian.OperationalCosts

end

open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  for name in [``Purelib.Polynomial.Multivariate.Gaussian.Normalized.ofForm,
      ``Purelib.Polynomial.Multivariate.Gaussian.Normalized.add,
      ``Purelib.Polynomial.Multivariate.Gaussian.Normalized.mul] do
    let info ← getConstInfo name
    match info.value? with
    | some value =>
        logInfo m!"{name}: type_nodes={info.type.sizeWithoutSharing}, schema_nodes={value.sizeWithoutSharing}"
    | none => throwError "Missing exposed schema body for measurement: {name}"
  for (name, _) in environment.constants.map₂.toList do
    modifyEnv fun current => markMeta (setDeclMeta current name) name
