module
public import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Geometric.Bounds
public import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Geometric.Evaluation
meta import Purelib.Elab.ConstructiveInjectivity

public section

namespace Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Geometric.Bounds

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Acquisition.Expression
open Purelib.Approximation.Gaussian.Geometric (Enclosure)
open Purelib.Approximation.Gaussian.Enclosure (Ball)

variable {arity : Nat} {environment : Fin arity → Annotated} {leafBalls : Basic.Leaf arity → Ball}

/-- Genuine geometry for exactly the used original compilation leaves with their same common-ball readbacks. -/
@[expose] def Inputs (leafBalls : Basic.Leaf arity → Ball) : {expression : Expr arity} →
    Admitted environment expression → Type
  | _, .base cached _ => {geometry : cached.compiled.Geometry //
      Basic.Construction.Geometry.Balls (construction := cached.compiled.construction) geometry leafBalls}
  | _, .unary _ child => Inputs leafBalls child
  | _, .inverse child => Inputs leafBalls child
  | _, .binary _ first second => Inputs leafBalls first × Inputs leafBalls second

/-- Project the same original optional geometry contract without compiling or reconstructing any leaf. -/
@[expose] def Inputs.geometry : {expression : Expr arity} → {admitted : Admitted environment expression} →
    Inputs leafBalls admitted → Geometric.Geometry admitted
  | _, .base _ _, inputs => some inputs.val
  | _, .unary _ child, inputs => Inputs.geometry (admitted := child) inputs
  | _, .inverse child, inputs => Inputs.geometry (admitted := child) inputs
  | _, .binary _ first second, inputs =>
      ⟨Inputs.geometry (admitted := first) inputs.1, Inputs.geometry (admitted := second) inputs.2⟩

/-- Supply the genuine empty geometric contract of the original exact constant compilation. -/
@[expose] def Inputs.rational (leafBalls : Basic.Leaf arity → Ball) (environment : Fin arity → Annotated)
    (value : Purelib.Data.Gaussian.Basic.Canonical) : Inputs leafBalls (Admitted.rational environment value) :=
  ⟨(), True.intro⟩

/-- Authenticate an original admitted atom's actual common enclosure at its same used bounded leaf. -/
@[expose] def Inputs.atom (leafBalls : Basic.Leaf arity → Ball) (environment : Fin arity → Annotated)
    (index : Fin arity) (sidecar : Purelib.Approximation.Gaussian.Provenance.Algebraic.Sidecar
      (environment index).channel) (enclosing : Enclosure (environment index).channel)
    (same : enclosing.ball = leafBalls (.atom index)) : Inputs leafBalls (Admitted.atom environment index sidecar) :=
  ⟨⟨⟨0, by change 0 < 1; exact Nat.zero_lt_succ 0⟩, rfl, enclosing⟩, same⟩

set_option genInjectivity false in
/-- An actual original checked realization consuming the same retained structural common programme. -/
structure Realized {expression : Expr arity} (common : Common leafBalls expression) where
  /-- The complete original common programme remains available beside its numerical caches. -/
  bounds : Common leafBalls expression
  /-- The retained programme is exactly the same supplied original common programme. -/
  bounds_eq : bounds = common
  /-- The actual original completed arithmetic, enclosure and existing child cache tree. -/
  value : Geometric.Realization environment expression
  /-- This actual parameter interpretation consumes that same retained common ball. -/
  ball_eq : value.enclosing.ball = bounds.ball

constructive_injectivity Realized

/-- The actual original realization has the same common ball as its authenticated original programme. -/
theorem Realized.common_ball {expression : Expr arity} {common : Common leafBalls expression}
    (realized : Realized (environment := environment) common) :
    realized.value.enclosing.ball = common.ball :=
  realized.ball_eq.trans (congrArg Common.ball realized.bounds_eq)

/-- Realize original admitted arithmetic using the retained common programme and genuine used-leaf geometry.

Each parameter specialization consumes the same cached balls directly. Existing
original completed children, arithmetic caches and paid reciprocal observations
remain in the original realization tree. All geometric-channel links are
operational comparisons, distinct from residual-program sample readback.
-/
@[expose] def realizeTree : {expression : Expr arity} → (admitted : Admitted environment expression) →
    {ball : Ball} → (tree : Tree leafBalls expression ball) →
    Inputs leafBalls admitted → Realized (environment := environment) ⟨ball, tree⟩
  | _, .base (expression := expression) cached admissions, _, .base .(expression) bounds, inputs =>
      let basic := cached.compiled.encloseBindingsFromBounds inputs.val bounds inputs.property
      let value : Geometric.Realization environment (.base expression) :=
        ⟨Checked.Completed.base cached admissions, basic.val.result,
          .base cached admissions inputs.val basic.val
            (cached.compiled.encloseBindingsFromBounds_computed inputs.val bounds inputs.property)⟩
      ⟨_, rfl, value, basic.ball_eq⟩
  | _, .unary .neg admitted, _, .neg child ball same, inputs =>
      let previous := realizeTree admitted child inputs
      let formula := same.trans (congrArg Ball.neg previous.common_ball).symm
      let value := previous.value.negFromBall ball formula
      ⟨_, rfl, value, previous.value.negFromBall_ball ball formula⟩
  | _, .unary .conj admitted, _, .conj child ball same, inputs =>
      let previous := realizeTree admitted child inputs
      let formula := same.trans (congrArg Ball.conj previous.common_ball).symm
      let value := previous.value.conjFromBall ball formula
      ⟨_, rfl, value, previous.value.conjFromBall_ball ball formula⟩
  | _, .unary (.pow _) admitted, _, .pow child exponent ball same, inputs =>
      let previous := realizeTree admitted child inputs
      let formula := same.trans (congrArg (fun original => original.pow exponent) previous.common_ball).symm
      let value := previous.value.powFromBall exponent ball formula
      ⟨_, rfl, value, previous.value.powFromBall_ball exponent ball formula⟩
  | _, .binary .add admittedFirst admittedSecond, _, .add first second ball same, inputs =>
      let firstValue := realizeTree admittedFirst first inputs.1
      let secondValue := realizeTree admittedSecond second inputs.2
      let formula := same.trans (congrArg₂ Ball.add firstValue.common_ball secondValue.common_ball).symm
      let value := firstValue.value.addFromBall secondValue.value ball formula
      ⟨_, rfl, value, firstValue.value.addFromBall_ball secondValue.value ball formula⟩
  | _, .binary .sub admittedFirst admittedSecond, _, .sub first second ball same, inputs =>
      let firstValue := realizeTree admittedFirst first inputs.1
      let secondValue := realizeTree admittedSecond second inputs.2
      let formula := same.trans (congrArg₂ Ball.sub firstValue.common_ball secondValue.common_ball).symm
      let value := firstValue.value.subFromBall secondValue.value ball formula
      ⟨_, rfl, value, firstValue.value.subFromBall_ball secondValue.value ball formula⟩
  | _, .binary .mul admittedFirst admittedSecond, _, .mul first second ball same, inputs =>
      let firstValue := realizeTree admittedFirst first inputs.1
      let secondValue := realizeTree admittedSecond second inputs.2
      let formula := same.trans (congrArg₂ Ball.mul firstValue.common_ball secondValue.common_ball).symm
      let value := firstValue.value.mulFromBall secondValue.value ball formula
      ⟨_, rfl, value, firstValue.value.mulFromBall_ball secondValue.value ball formula⟩
  | _, .inverse admitted, _, .inverse child _ apart _ ball same, inputs =>
      let previous := realizeTree admitted child inputs
      let adjusted : Ball.Apart previous.value.enclosing.ball :=
        Eq.ndrec (motive := fun original => Ball.Apart original) apart previous.common_ball.symm
      have formula : ball = (Ball.point 1).div previous.value.enclosing.ball adjusted :=
        same.trans ((Ball.point 1).div_cast previous.common_ball.symm apart).symm
      let value := previous.value.inverseFromBall adjusted ball formula
      ⟨_, rfl, value, previous.value.inverseFromBall_ball adjusted ball formula⟩

/-- Consume the same original common programme without rebuilding its finite structural bound tree. -/
@[expose] def Common.realize {expression : Expr arity} (common : Common leafBalls expression)
    (admitted : Admitted environment expression) (inputs : Inputs leafBalls admitted) :
    Realized (environment := environment) common := realizeTree admitted common.tree inputs

/-- Every actual parameter sample is contained in the same retained original common bound. -/
theorem Common.contains {expression : Expr arity} (common : Common leafBalls expression)
    (admitted : Admitted environment expression) (inputs : Inputs leafBalls admitted) (index : Nat) :
    common.ball.Contains ((common.realize admitted inputs).value.enclosing.source.sample index) := by
  let actual := common.realize admitted inputs
  exact actual.common_ball ▸ actual.value.enclosing.contains index

/-- Two independently owned original interpretations consume the same actual complete common ball. -/
theorem Common.same_ball {expression : Expr arity} (common : Common leafBalls expression)
    {other : Fin arity → Annotated} (first : Admitted environment expression) (firstInputs : Inputs leafBalls first)
    (second : Admitted other expression) (secondInputs : Inputs leafBalls second) :
    (common.realize first firstInputs).value.enclosing.ball =
      (common.realize second secondInputs).value.enclosing.ball :=
  (common.realize first firstInputs).common_ball.trans (common.realize second secondInputs).common_ball.symm

end Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Geometric.Bounds
end
