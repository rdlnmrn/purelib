module

public import Purelib.Polynomial.Laurent.Toeplitz
public import Purelib.Polynomial.Laurent.Circle.Deformation
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Actual recurrence boundary ledgers along certified Laurent deformations

One original finite schedule certifies the displayed coefficient path.
Endpoints and rational queries retain their own original normalization,
inventory, independent winding and actual recurrence boundary normal form.
The index comparison allows collisions and changes of degree or pole order.
-/

public section

namespace Purelib.Polynomial.Laurent.Toeplitz.Deformation

open Purelib.Data.Rat.Fraction (Rational)
open Circle.Deformation (Uniform)
open Path (Parameter)

set_option genInjectivity false in
/-- One actual parameter's original circle result and its own recurrence boundary ledger. -/
structure Evaluation {path : Path} (uniform : Uniform path) (parameter : Rational)
    (inside : Parameter parameter) where
  /-- The same original parameter symbol's normalization, full margin, inventory and independent winding. -/
  circle : Circle.Deformation.Evaluation uniform parameter inside
  /-- The actual parameter recurrence ledger consumes the retained original circle computation. -/
  result : Toeplitz.Comparison circle.normalized circle.paths circle.clearance
  /-- The complete parameter ledger extends that same cached original circle result. -/
  result_eq : result = Toeplitz.Comparison.ofCircle circle.result circle.result_eq

constructive_injectivity Evaluation

namespace Evaluation

variable {path : Path} {uniform : Uniform path} {parameter : Rational} {inside : Parameter parameter}

/-- Retain checked original parameter-circle and actual recurrence caches without replaying either producer. -/
@[expose] def ofCaches (circle : Circle.Deformation.Evaluation uniform parameter inside)
    (result : Toeplitz.Comparison circle.normalized circle.paths circle.clearance)
    (resultEq : result = Toeplitz.Comparison.ofCircle circle.result circle.result_eq) :
    Evaluation uniform parameter inside :=
  { circle, result, result_eq := resultEq }

/-- Extend one already computed original parameter result with its own actual recurrence ledger. -/
@[expose] def ofCircle (circle : Circle.Deformation.Evaluation uniform parameter inside) :
    Evaluation uniform parameter inside :=
  let result := Toeplitz.Comparison.ofCircle circle.result circle.result_eq
  ofCaches circle result rfl

/-- Construct an actual parameter's original circle comparison and recurrence ledger once. -/
@[expose] def prepare (uniform : Uniform path) (parameter : Rational) (inside : Parameter parameter) :
    Evaluation uniform parameter inside :=
  let circle := Circle.Deformation.Evaluation.prepare uniform parameter inside
  ofCircle circle

/-- The actual parameter ledger retains exactly its original cached circle comparison. -/
theorem result_circle (evaluation : Evaluation uniform parameter inside) :
    evaluation.result.circle = evaluation.circle.result :=
  (congrArg (fun result : Toeplitz.Comparison evaluation.circle.normalized
    evaluation.circle.paths evaluation.circle.clearance => result.circle) evaluation.result_eq).trans rfl

/-- The actual parameter's recurrence defect is the negative of its own independent original winding. -/
theorem index_eq_neg_winding (evaluation : Evaluation uniform parameter inside) :
    evaluation.result.index = -evaluation.circle.result.reading.winding :=
  evaluation.result.index_eq_neg_winding.trans
    (congrArg (fun circle => -circle.reading.winding) evaluation.result_circle)

/-- Checked complete parameter caches recover the same actual recurrence extension of the original circle result. -/
theorem ofCaches_eq_ofCircle (circle : Circle.Deformation.Evaluation uniform parameter inside)
    (result : Toeplitz.Comparison circle.normalized circle.paths circle.clearance)
    (resultEq : result = Toeplitz.Comparison.ofCircle circle.result circle.result_eq) :
    ofCaches circle result resultEq = ofCircle circle := by
  cases resultEq
  rfl

/-- Restore the same retained parameter construction without rebuilding its original circle result. -/
theorem restore (evaluation : Evaluation uniform parameter inside) : evaluation = ofCircle evaluation.circle := by
  cases evaluation with
  | mk circle result resultEq => exact ofCaches_eq_ofCircle circle result resultEq

end Evaluation

set_option genInjectivity false in
/-- The original sufficient deformation schedule and the two actual endpoint recurrence ledgers. -/
structure Comparison {path : Path} (uniform : Uniform path) where
  /-- The once-constructed original schedule and complete independent endpoint circle comparisons. -/
  circle : Circle.Deformation.Comparison uniform
  /-- The original comparison is the automatic sufficient constructor on this same certified path. -/
  circle_eq : circle = Circle.Deformation.Comparison.prepare uniform
  /-- The actual initial recurrence ledger extends the original cached initial circle result. -/
  initial : Evaluation uniform 0 ⟨by decide, by decide⟩
  /-- The complete initial extension reuses that same retained original initial result. -/
  initial_eq : initial = Evaluation.ofCircle circle.initial
  /-- The actual terminal recurrence ledger extends the original cached terminal circle result. -/
  terminal : Evaluation uniform 1 ⟨by decide, by decide⟩
  /-- The complete terminal extension reuses that same retained original terminal result. -/
  terminal_eq : terminal = Evaluation.ofCircle circle.terminal

constructive_injectivity Comparison

namespace Comparison

variable {path : Path} {uniform : Uniform path}

/-- Retain checked original deformation and actual endpoint caches without replaying their producers. -/
@[expose] def ofCaches (circle : Circle.Deformation.Comparison uniform)
    (circleEq : circle = Circle.Deformation.Comparison.prepare uniform)
    (initial : Evaluation uniform 0 ⟨by decide, by decide⟩)
    (initialEq : initial = Evaluation.ofCircle circle.initial)
    (terminal : Evaluation uniform 1 ⟨by decide, by decide⟩)
    (terminalEq : terminal = Evaluation.ofCircle circle.terminal) : Comparison uniform :=
  { circle, circle_eq := circleEq, initial, initial_eq := initialEq, terminal, terminal_eq := terminalEq }

/-- Construct one original deformation schedule and extend its cached endpoints with actual recurrence ledgers. -/
@[expose] def prepare (uniform : Uniform path) : Comparison uniform :=
  let circle := Circle.Deformation.Comparison.prepare uniform
  let initial := Evaluation.ofCircle circle.initial
  let terminal := Evaluation.ofCircle circle.terminal
  ofCaches circle rfl initial rfl terminal rfl

/-- Query one actual parameter ledger without rebuilding the cached schedule or either endpoint. -/
@[expose] def evaluate (comparison : Comparison uniform) (parameter : Rational) (inside : Parameter parameter) :
    Evaluation uniform parameter inside :=
  let circle := comparison.circle.evaluate parameter inside
  Evaluation.ofCircle circle

/-- The initial recurrence extension retains exactly the original initial parameter construction. -/
theorem initial_circle (comparison : Comparison uniform) : comparison.initial.circle = comparison.circle.initial :=
  (congrArg (fun evaluation : Evaluation uniform 0 ⟨by decide, by decide⟩ => evaluation.circle)
    comparison.initial_eq).trans rfl

/-- The terminal recurrence extension retains exactly the original terminal parameter construction. -/
theorem terminal_circle (comparison : Comparison uniform) : comparison.terminal.circle = comparison.circle.terminal :=
  (congrArg (fun evaluation : Evaluation uniform 1 ⟨by decide, by decide⟩ => evaluation.circle)
    comparison.terminal_eq).trans rfl

/-- The actual endpoint recurrence boundary defects agree through collisions and support changes. -/
theorem index_eq (comparison : Comparison uniform) :
    comparison.terminal.result.index = comparison.initial.result.index := by
  rewrite [comparison.terminal.index_eq_neg_winding, comparison.initial.index_eq_neg_winding,
    comparison.terminal_circle, comparison.initial_circle, comparison.circle.winding_eq]
  rfl

/-- Every actual parameter's recurrence boundary defect agrees with the same cached initial endpoint. -/
theorem evaluation_index_eq (comparison : Comparison uniform)
    {parameter : Rational} {inside : Parameter parameter} (evaluation : Evaluation uniform parameter inside) :
    evaluation.result.index = comparison.initial.result.index := by
  rewrite [evaluation.index_eq_neg_winding, comparison.initial.index_eq_neg_winding,
    comparison.initial_circle, comparison.circle.evaluation_winding_eq evaluation.circle]
  rfl

/-- Checked complete deformation caches recover the same automatic recurrence comparison. -/
theorem ofCaches_eq_prepare (circle : Circle.Deformation.Comparison uniform)
    (circleEq : circle = Circle.Deformation.Comparison.prepare uniform)
    (initial : Evaluation uniform 0 ⟨by decide, by decide⟩)
    (initialEq : initial = Evaluation.ofCircle circle.initial)
    (terminal : Evaluation uniform 1 ⟨by decide, by decide⟩)
    (terminalEq : terminal = Evaluation.ofCircle circle.terminal) :
    ofCaches circle circleEq initial initialEq terminal terminalEq = prepare uniform := by
  cases circleEq
  cases initialEq
  cases terminalEq
  rfl

/-- The complete retained deformation comparison restores its same automatic construction. -/
theorem restore (comparison : Comparison uniform) : comparison = prepare uniform := by
  cases comparison with
  | mk circle circleEq initial initialEq terminal terminalEq =>
      exact ofCaches_eq_prepare circle circleEq initial initialEq terminal terminalEq

end Comparison
end Purelib.Polynomial.Laurent.Toeplitz.Deformation

end
