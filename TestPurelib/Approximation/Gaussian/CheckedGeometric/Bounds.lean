module
import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Geometric.Bounds.Evaluation
import Purelib.Approximation.Gaussian.Acquisition.Annotated.Basic
import Purelib.Approximation.Gaussian.Provenance.Algebraic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
import Purelib.System.IO

namespace TestPurelib.Approximation.Gaussian.CheckedGeometric.Bounds

open Purelib.Approximation.Gaussian.Acquisition.Expression
open Purelib.Approximation.Gaussian.Acquisition.Expression.Checked
open Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Geometric (Realization)
open Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Geometric.Bounds
open Purelib.Approximation.Gaussian.Enclosure (Ball)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Geometric (Enclosure)
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Approximation.Gaussian
open Purelib.Data.Gaussian

/-- Even exponent zero retains the exact earlier request at the same original denominator occurrence. -/
example {arity : Nat} {leafBalls : Basic.Leaf arity → Ball} {input : Expr arity}
    (request : Request leafBalls input) :
    (Outcome.requested request).unary (.pow 0) =
      .requested (.through (.unary (.pow 0) input) request) := rfl

/-- A right-side request retains the complete original left common programme unchanged. -/
example {arity : Nat} {leafBalls : Basic.Leaf arity → Ball} {left right : Expr arity}
    (operation : Binary) (first : Common leafBalls left) (remaining : Request leafBalls right) :
    (Request.through (.right operation left first right) remaining).prefix = ⟨left, first⟩ :: remaining.prefix := by
  cases operation <;> rfl

/-- An unresolved original left condition leaves the exact original right expression unvisited. -/
example {arity : Nat} {leafBalls : Basic.Leaf arity → Ball} {left right : Expr arity}
    (operation : Binary) (remaining : Request leafBalls left) :
    (Request.through (.left operation left right) remaining).unvisited = remaining.unvisited ++ [right] := by
  cases operation <;> rfl

/-- Every actual factory result carries its original procedure's exact computation certificate. -/
example {arity : Nat} {leafBalls : Basic.Leaf arity → Ball}
    {environment : Fin arity → Annotated}
    {expression : Expr arity} (outcome : Outcome leafBalls expression)
    (admitted : Admitted environment expression) (geometry : Inputs leafBalls admitted) :
    Computed outcome admitted geometry (outcome.specialize admitted geometry).result :=
  outcome.specialize_computed admitted geometry

/-- The specialization retains the exact original geometry object beside its original bound parent. -/
example {arity : Nat} {leafBalls : Basic.Leaf arity → Ball}
    {environment : Fin arity → Annotated}
    {expression : Expr arity} (outcome : Outcome leafBalls expression)
    (admitted : Admitted environment expression) (geometry : Inputs leafBalls admitted) :
    (outcome.specialize admitted geometry).bounds = outcome ∧
      (outcome.specialize admitted geometry).input.geometry = geometry :=
  ⟨outcome.specialize_bounds admitted geometry, outcome.specialize_geometry admitted geometry⟩

/-- The actual completed output stays in the original common ball at every sample index.

This consumes an arbitrary stored specialization and its own completed result,
including independently supplied geometry and positive programme evidence.
-/
example {arity : Nat} {leafBalls : Basic.Leaf arity → Ball}
    {environment : Fin arity → Annotated} {expression : Expr arity}
    {outcome : Outcome leafBalls expression} {admitted : Admitted environment expression}
    (actual : Specialization outcome admitted) {common : Common leafBalls expression}
    (positive : outcome = .prepared common) {value : Realization environment expression}
    (completed : actual.result = .completed value) (stage : Nat) :
    common.ball.Contains (value.enclosing.source.sample stage) :=
  actual.completed_ball positive completed ▸ value.enclosing.contains stage

/-- Exercise full common bounds, nested reciprocal domains and exact ordered prefix retention. -/
public def check : IO Unit := do
  let leafBalls : Basic.Leaf 0 → Ball := fun _ => Ball.point 0
  let three : Expr 0 := .rational 3
  let nonreal : Expr 0 := .rational (⟨1, 1⟩ : Canonical)
  let positive : Expr 0 := .add (.inverse three) (.conj (.pow (.mul three nonreal) 2))
  match inspect leafBalls positive with
  | .requested _ => throw (IO.userError "The positive nested common programme lost its computed separation")
  | .prepared common =>
      unless common.ball.center == (⟨1 / 3, -18⟩ : Canonical) && common.ball.radiusSq == 0 do
        throw (IO.userError "The structural common programme changed an original operation bound")
  let zero : Expr 0 := .rational 0
  let invalid : Expr 0 := .add (Expr.rational 7) (.pow (.inverse zero) 0)
  match inspect leafBalls invalid with
  | .prepared _ => throw (IO.userError "Exponent zero erased its original denominator domain condition")
  | .requested remaining =>
      unless remaining.denominator.child.ball.center == 0 && remaining.prefix.length == 1 &&
          remaining.unvisited.length == 0 do
        throw (IO.userError "A failed reciprocal discarded its original bound or completed left prefix")
      match remaining.prefix with
      | [⟨_, first⟩] =>
          unless first.ball.center == 7 do
            throw (IO.userError "The right request replaced its retained original left common bound")
      | _ => throw (IO.userError "The exact original completed prefix was lost")
  let leftFirst : Expr 0 := .mul (.inverse zero) (.pow (.inverse three) 0)
  match inspect leafBalls leftFirst with
  | .prepared _ => throw (IO.userError "The first insufficient denominator bound was skipped")
  | .requested remaining =>
      unless remaining.prefix.length == 0 && remaining.unvisited.length == 1 do
        throw (IO.userError "The left request visited or discarded the original right expression")
  let retained : Expr 0 := .pow (.inverse three) 0
  match inspect leafBalls retained with
  | .requested _ => throw (IO.userError "A genuine inverse child lost its original positive common margin")
  | .prepared common =>
      let tree : Tree leafBalls (.pow (.inverse three) 0) common.ball := common.tree
      match tree with
      | .pow (.inverse ..) 0 _ _ => pure ()
      | _ => throw (IO.userError "A zero exponent discarded its original successful inverse child programme")
  let environment : Fin 0 → Annotated := Fin.elim0
  let originalThree := Admitted.rational environment 3
  let originalNonreal := Admitted.rational environment (⟨1, 1⟩ : Canonical)
  let admitted : Admitted environment positive :=
    (Admitted.inverse originalThree).add ((originalThree.mul originalNonreal).pow 2).conj
  let inputs : Inputs leafBalls admitted :=
    ⟨Inputs.rational leafBalls environment 3,
      Inputs.rational leafBalls environment 3, Inputs.rational leafBalls environment ⟨1, 1⟩⟩
  match inspect leafBalls positive with
  | .requested _ => throw (IO.userError "The retained positive common programme became inconclusive")
  | .prepared common =>
      let actual := common.realize admitted inputs
      unless actual.value.enclosing.source.sample 7 == (⟨1 / 3, -18⟩ : Canonical) &&
          actual.value.enclosing.ball.center == common.ball.center &&
          actual.value.enclosing.ball.radiusSq == common.ball.radiusSq do
        throw (IO.userError "Actual original arithmetic did not consume its retained common programme")
  let prepared := (inspect leafBalls positive).specialize admitted inputs
  match completed : prepared.result with
  | .completed actual =>
      unless actual.enclosing.source.sample 7 == (⟨1 / 3, -18⟩ : Canonical) do
        throw (IO.userError "The retained original specialization changed its formal programme")
      match positiveResult : prepared.bounds with
      | .prepared common =>
          let retained : {ball : Ball // ball = actual.enclosing.ball} :=
            ⟨common.ball, (prepared.completed_ball (prepared.bounds_eq.symm.trans positiveResult) completed).symm⟩
          unless retained.val.Contains (actual.enclosing.source.sample 7) ∧
              actual.enclosing.ball.center = retained.val.center ∧
              actual.enclosing.ball.radiusSq = retained.val.radiusSq do
            throw (IO.userError "The actual specialization lost its original common bound")
      | .requested _ => throw (IO.userError "A completed specialization retained an unresolved common programme")
  | _ => throw (IO.userError "The positive retained programme lost its actual numerical completion")
  let originalZero := Admitted.rational environment 0
  let originalSeven := Admitted.rational environment 7
  let invalidAdmission : Admitted environment invalid :=
    originalSeven.add ((Admitted.inverse originalZero).pow 0)
  let invalidInputs : Inputs leafBalls invalidAdmission :=
    ⟨Inputs.rational leafBalls environment 7, Inputs.rational leafBalls environment 0⟩
  let invalidActual := (inspect leafBalls invalid).specialize invalidAdmission invalidInputs
  match invalidActual.result with
  | .invalid stopped =>
      let ⟨_, denominator, _, _⟩ := stopped.denominator
      unless denominator.enclosing.source.sample 0 == 0 && stopped.prefix.length == 1 do
        throw (IO.userError "The exact zero lost its actual denominator or completed original prefix")
  | _ => throw (IO.userError "An actual inverse-zero under exponent zero lost its original domain obstruction")
  match (inspect leafBalls positive).prepare admitted none with
  | .specialized _ => throw (IO.userError "Missing actual geometry was fabricated")
  | .missing request =>
      let supplied : Inputs leafBalls request.original :=
        Eq.ndrec (motive := fun original => Inputs leafBalls original) inputs request.original_eq.symm
      let resumed := request.resume supplied
      match resumed.result with
      | .completed actual =>
          unless actual.enclosing.source.sample 7 == (⟨1 / 3, -18⟩ : Canonical) do
            throw (IO.userError "Filling geometry changed the original retained bound programme")
      | _ => throw (IO.userError "Filling actual geometry lost the retained original construction")
  let atomIndex : Fin 1 := ⟨0, by decide +kernel⟩
  let atomEnvironment : Fin 1 → Annotated :=
    fun _ => Annotated.rational 3
  let sidecar := Algebraic.Sidecar.ofRational
    (RationalSidecar.exact 3)
  let coarse : Enclosure (atomEnvironment atomIndex).channel :=
    { source := (Enclosure.exact 3).source
      equivalent := (Enclosure.exact 3).equivalent
      ball := ⟨0, 9, by decide +kernel⟩
      contains := fun stage => by
        rewrite [Enclosure.exact_sample]
        change Norm.Basic.normSq ((3 : Canonical) - 0) ≤ 9
        decide +kernel }
  let coarseBalls : Basic.Leaf 1 → Ball := fun _ => coarse.ball
  let atomAdmission := Admitted.atom atomEnvironment atomIndex sidecar
  let atomInputs := Inputs.atom coarseBalls atomEnvironment atomIndex sidecar coarse rfl
  let inverseAdmission := Admitted.inverse atomAdmission
  let insufficient := (inspect coarseBalls (.inverse (Expr.atom atomIndex))).specialize inverseAdmission atomInputs
  match insufficient.result with
  | .requested _ => pure ()
  | _ => throw (IO.userError "A coarse nonzero denominator bound became a global pole or false clearance")
  Purelib.System.IO.println "Uniform checked bounds: ordered domains, prefixes and every zero-power child retained"

end TestPurelib.Approximation.Gaussian.CheckedGeometric.Bounds
