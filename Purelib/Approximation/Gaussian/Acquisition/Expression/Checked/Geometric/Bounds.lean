module
import Purelib.Approximation.Gaussian.Acquisition.Expression.Basic
public import Purelib.Approximation.Gaussian.Acquisition.Expression.Enclosure
public import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Admission
public import Purelib.Approximation.Gaussian.Geometric.Preparation
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Division
import Purelib.Approximation.Gaussian.Enclosure.Residual
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

public section

namespace Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Geometric.Bounds

open Purelib.Approximation.Gaussian.Acquisition.Expression
open Purelib.Approximation.Gaussian.Enclosure (Ball)
open Purelib.Approximation.Gaussian.Geometric
open Purelib.Approximation.Gaussian.Enclosure

variable {arity : Nat} {leafBalls : Basic.Leaf arity → Ball}

set_option genInjectivity false in
/-- Original finite expression bounds retaining every child and each once-computed operation ball.

The tree keeps the original syntax, including every child of exponent zero.
An inverse node retains its computed positive separation and exact division
bound. Base nodes retain the original total-expression bound programme.
-/
inductive Tree (leafBalls : Basic.Leaf arity → Ball) : Expr arity → Ball → Type where
  /-- The original total base bound programme is retained in full. -/
  | base (expression : Basic.Expr arity) (bounds : Basic.Expr.Bounds leafBalls expression) :
      Tree leafBalls (.base expression) bounds.ball
  /-- Retain the actual original negative child and its exact bound. -/
  | neg {input : Expr arity} {childBall : Ball} (child : Tree leafBalls input childBall)
      (ball : Ball) (same : ball = childBall.neg) : Tree leafBalls (.neg input) ball
  /-- Retain both ordered original addition children and the exact common sum bound. -/
  | add {left right : Expr arity} {leftBall rightBall : Ball}
      (first : Tree leafBalls left leftBall) (second : Tree leafBalls right rightBall)
      (ball : Ball) (same : ball = leftBall.add rightBall) : Tree leafBalls (.add left right) ball
  /-- Retain both ordered original subtraction children and the exact common difference bound. -/
  | sub {left right : Expr arity} {leftBall rightBall : Ball}
      (first : Tree leafBalls left leftBall) (second : Tree leafBalls right rightBall)
      (ball : Ball) (same : ball = leftBall.sub rightBall) : Tree leafBalls (.sub left right) ball
  /-- Retain both original product occurrences even when their result may collide with zero. -/
  | mul {left right : Expr arity} {leftBall rightBall : Ball}
      (first : Tree leafBalls left leftBall) (second : Tree leafBalls right rightBall)
      (ball : Ball) (same : ball = leftBall.mul rightBall) : Tree leafBalls (.mul left right) ball
  /-- Every natural power retains its original child and that child's domain obligations. -/
  | pow {input : Expr arity} {childBall : Ball} (child : Tree leafBalls input childBall) (exponent : Nat)
      (ball : Ball) (same : ball = childBall.pow exponent) : Tree leafBalls (.pow input exponent) ball
  /-- Conjugation keeps the original child programme and its exact conjugate bound. -/
  | conj {input : Expr arity} {childBall : Ball} (child : Tree leafBalls input childBall)
      (ball : Ball) (same : ball = childBall.conj) : Tree leafBalls (.conj input) ball
  /-- Reciprocal bounds consume the actual positive separation computed at the same child ball. -/
  | inverse {input : Expr arity} {childBall : Ball} (child : Tree leafBalls input childBall)
      (separated : Preparation.Separated childBall) (apart : Ball.Apart childBall)
      (computed : apart = Residual.apartOfCenter childBall separated)
      (ball : Ball) (same : ball = (Ball.point 1).div childBall apart) : Tree leafBalls (.inverse input) ball

constructive_injectivity Tree

set_option genInjectivity false in
/-- A retained original common ball and its complete structural bound programme. -/
structure Common (leafBalls : Basic.Leaf arity → Ball) (expression : Expr arity) where
  /-- The actual common ball computed for this original expression. -/
  ball : Ball
  /-- Its complete original child programme and exact operation readbacks. -/
  tree : Tree leafBalls expression ball

constructive_injectivity Common

namespace Common

/-- Compute and retain the complete original total base bound programme once. -/
@[expose] def base (expression : Basic.Expr arity) (leafBalls : Basic.Leaf arity → Ball) :
    Common leafBalls (.base expression) :=
  let bounds := expression.bounds leafBalls
  ⟨bounds.ball, .base expression bounds⟩

/-- Compute a unary common bound after retaining the complete original child. -/
@[expose] def unary (operation : Unary) {input : Expr arity} (child : Common leafBalls input) :
    Common leafBalls (operation.expression input) :=
  match operation with
  | .neg => let ball := child.ball.neg; ⟨ball, .neg child.tree ball rfl⟩
  | .pow exponent => let ball := child.ball.pow exponent; ⟨ball, .pow child.tree exponent ball rfl⟩
  | .conj => let ball := child.ball.conj; ⟨ball, .conj child.tree ball rfl⟩

/-- Compute an ordered binary common bound from the same two retained child programmes. -/
@[expose] def binary (operation : Binary) {left right : Expr arity}
    (first : Common leafBalls left) (second : Common leafBalls right) :
    Common leafBalls (operation.expression left right) :=
  match operation with
  | .add => let ball := first.ball.add second.ball; ⟨ball, .add first.tree second.tree ball rfl⟩
  | .sub => let ball := first.ball.sub second.ball; ⟨ball, .sub first.tree second.tree ball rfl⟩
  | .mul => let ball := first.ball.mul second.ball; ⟨ball, .mul first.tree second.tree ball rfl⟩

/-- Compute the original reciprocal margin and common division bound once after its finite separation test. -/
@[expose] def inverse {input : Expr arity} (child : Common leafBalls input)
    (separated : Preparation.Separated child.ball) : Common leafBalls (.inverse input) :=
  let apart := Residual.apartOfCenter child.ball separated
  let ball := (Ball.point 1).div child.ball apart
  ⟨ball, .inverse child.tree separated apart rfl ball rfl⟩

end Common

set_option genInjectivity false in
/-- An original bound context retaining earlier common programmes and every unvisited right expression. -/
inductive Frame (leafBalls : Basic.Leaf arity → Ball) : Expr arity → Expr arity → Type where
  /-- Retain the original unfinished negative child. -/
  | neg (input : Expr arity) : Frame leafBalls input (.neg input)
  /-- Retain the original unfinished power child and its literal exponent. -/
  | pow (input : Expr arity) (exponent : Nat) : Frame leafBalls input (.pow input exponent)
  /-- Retain the original unfinished conjugate child. -/
  | conj (input : Expr arity) : Frame leafBalls input (.conj input)
  /-- Retain the exact original unfinished denominator. -/
  | inverse (input : Expr arity) : Frame leafBalls input (.inverse input)
  /-- A left addition request keeps the original unvisited right occurrence. -/
  | addLeft (left right : Expr arity) : Frame leafBalls left (.add left right)
  /-- A left subtraction request keeps the original unvisited right occurrence. -/
  | subLeft (left right : Expr arity) : Frame leafBalls left (.sub left right)
  /-- A left product request keeps the original unvisited right occurrence. -/
  | mulLeft (left right : Expr arity) : Frame leafBalls left (.mul left right)
  /-- A right addition request keeps its actual completed original left programme. -/
  | addRight (left : Expr arity) (first : Common leafBalls left) (right : Expr arity) :
      Frame leafBalls right (.add left right)
  /-- A right subtraction request keeps its actual completed original left programme. -/
  | subRight (left : Expr arity) (first : Common leafBalls left) (right : Expr arity) :
      Frame leafBalls right (.sub left right)
  /-- A right product request keeps its actual completed original left programme. -/
  | mulRight (left : Expr arity) (first : Common leafBalls left) (right : Expr arity) :
      Frame leafBalls right (.mul left right)

constructive_injectivity Frame

/-- Retain the exact total unary context with its original constructor index. -/
@[expose] def Frame.unary (operation : Unary) (input : Expr arity) :
    Frame leafBalls input (operation.expression input) :=
  match operation with
  | .neg => .neg input
  | .pow exponent => .pow input exponent
  | .conj => .conj input

/-- Retain an exact ordered left context without entering the original right expression. -/
@[expose] def Frame.left (operation : Binary) (left right : Expr arity) :
    Frame leafBalls left (operation.expression left right) :=
  match operation with
  | .add => .addLeft left right
  | .sub => .subLeft left right
  | .mul => .mulLeft left right

/-- Retain an exact ordered right context with its actual original completed left programme. -/
@[expose] def Frame.right (operation : Binary) (left : Expr arity) (first : Common leafBalls left)
    (right : Expr arity) : Frame leafBalls right (operation.expression left right) :=
  match operation with
  | .add => .addRight left first right
  | .sub => .subRight left first right
  | .mul => .mulRight left first right

set_option genInjectivity false in
/-- A finite insufficient denominator bound with the original prefix and all surrounding syntax.

Failure of this sufficient spatial condition proves no operational zero or
path-wide pole. The original numerical admission and genuine geometry must
specialize the request before an exact-zero decision can be read.
-/
inductive Request (leafBalls : Basic.Leaf arity → Ball) : Expr arity → Type where
  /-- The same retained denominator programme failed its actual finite common-ball test. -/
  | inverse {input : Expr arity} (child : Common leafBalls input)
      (failed : ¬ Preparation.Separated child.ball) : Request leafBalls (.inverse input)
  /-- Retain the exact original negative context. -/
  | neg {input : Expr arity} (first : Request leafBalls input) : Request leafBalls (.neg input)
  /-- Retain every original domain obligation below the literal exponent, including zero. -/
  | pow {input : Expr arity} (exponent : Nat) (first : Request leafBalls input) :
      Request leafBalls (.pow input exponent)
  /-- Retain the exact original conjugate context. -/
  | conj {input : Expr arity} (first : Request leafBalls input) : Request leafBalls (.conj input)
  /-- Retain an original outer inverse around the same unresolved child occurrence. -/
  | outerInverse {input : Expr arity} (first : Request leafBalls input) : Request leafBalls (.inverse input)
  /-- Retain the original right sum occurrence without visiting it. -/
  | addLeft {left : Expr arity} (right : Expr arity) (first : Request leafBalls left) :
      Request leafBalls (.add left right)
  /-- Retain the original right difference occurrence without visiting it. -/
  | subLeft {left : Expr arity} (right : Expr arity) (first : Request leafBalls left) :
      Request leafBalls (.sub left right)
  /-- Retain the original right product occurrence without visiting it. -/
  | mulLeft {left : Expr arity} (right : Expr arity) (first : Request leafBalls left) :
      Request leafBalls (.mul left right)
  /-- Retain the completed original left sum programme beside the same unresolved right child. -/
  | addRight {left right : Expr arity} (first : Common leafBalls left) (remaining : Request leafBalls right) :
      Request leafBalls (.add left right)
  /-- Retain the completed original left difference programme beside the same unresolved right child. -/
  | subRight {left right : Expr arity} (first : Common leafBalls left) (remaining : Request leafBalls right) :
      Request leafBalls (.sub left right)
  /-- Retain the completed original left product programme beside the same unresolved right child. -/
  | mulRight {left right : Expr arity} (first : Common leafBalls left) (remaining : Request leafBalls right) :
      Request leafBalls (.mul left right)

constructive_injectivity Request

/-- Retain a literal original bound context around its exact first unresolved occurrence. -/
@[expose] def Request.through {input output : Expr arity} (frame : Frame leafBalls input output)
    (remaining : Request leafBalls input) : Request leafBalls output :=
  match frame with
  | .neg _ => .neg remaining
  | .pow _ exponent => .pow exponent remaining
  | .conj _ => .conj remaining
  | .inverse _ => .outerInverse remaining
  | .addLeft _ right => .addLeft right remaining
  | .subLeft _ right => .subLeft right remaining
  | .mulLeft _ right => .mulLeft right remaining
  | .addRight _ first _ => .addRight first remaining
  | .subRight _ first _ => .subRight first remaining
  | .mulRight _ first _ => .mulRight first remaining

set_option genInjectivity false in
/-- The exact original denominator programme and proof of its actual failed finite ball test. -/
structure Failure (leafBalls : Basic.Leaf arity → Ball) where
  /-- The original first unresolved denominator syntax. -/
  input : Expr arity
  /-- Its complete retained common bound programme. -/
  child : Common leafBalls input
  /-- Its actual sufficient spatial condition failed. -/
  failed : ¬ Preparation.Separated child.ball

constructive_injectivity Failure

/-- Read the exact first unresolved denominator, common programme and actual failed finite condition. -/
@[expose] def Request.denominator {expression : Expr arity} : Request leafBalls expression → Failure leafBalls
  | .inverse child failed => ⟨_, child, failed⟩
  | .neg first | .pow _ first | .conj first | .outerInverse first |
      .addLeft _ first | .subLeft _ first | .mulLeft _ first |
      .addRight _ first | .subRight _ first | .mulRight _ first => first.denominator

/-- Read every original completed left bound programme preceding the first unresolved denominator. -/
@[expose] def Request.prefix {expression : Expr arity} : Request leafBalls expression →
    List ((input : Expr arity) × Common leafBalls input)
  | .inverse .. => []
  | @Request.addRight _ _ input _ first remaining | @Request.subRight _ _ input _ first remaining |
      @Request.mulRight _ _ input _ first remaining => ⟨input, first⟩ :: remaining.prefix
  | .neg first | .pow _ first | .conj first | .outerInverse first |
      .addLeft _ first | .subLeft _ first | .mulLeft _ first => first.prefix

/-- Read every original unvisited right occurrence surrounding the same unresolved condition. -/
@[expose] def Request.unvisited {expression : Expr arity} : Request leafBalls expression → List (Expr arity)
  | .inverse .. => []
  | .addLeft right first | .subLeft right first | .mulLeft right first => first.unvisited ++ [right]
  | .neg first | .pow _ first | .conj first | .outerInverse first |
      .addRight _ first | .subRight _ first | .mulRight _ first => first.unvisited

set_option genInjectivity false in
/-- A complete computed common bound or its first insufficient spatial condition with every original context. -/
inductive Outcome (leafBalls : Basic.Leaf arity → Ball) (expression : Expr arity) where
  /-- Every original domain obligation has a positive finite common-ball certificate. -/
  | prepared (common : Common leafBalls expression)
  /-- The actual first insufficient condition retains all computed prefixes and remaining syntax. -/
  | requested (request : Request leafBalls expression)

constructive_injectivity Outcome

namespace Outcome

/-- Read the actual original unresolved programme with its same-outcome branch certificate. -/
@[expose] def request {expression : Expr arity} (outcome : Outcome leafBalls expression) :
    Option { request : Request leafBalls expression // outcome = .requested request } :=
  match outcome with
  | .prepared _ => none
  | .requested request => some ⟨request, rfl⟩

/-- A proved requested branch exposes the same original unresolved programme and branch certificate. -/
theorem request_of_requested {expression : Expr arity} {outcome : Outcome leafBalls expression}
    {original : Request leafBalls expression} (same : outcome = .requested original) :
    outcome.request = some ⟨original, same⟩ := by
  cases same
  rfl

/-- A proved positive branch has no unresolved common-bound request. -/
theorem request_of_prepared {expression : Expr arity} {outcome : Outcome leafBalls expression}
    {common : Common leafBalls expression} (same : outcome = .prepared common) : outcome.request = none := by
  cases same
  rfl

/-- Apply a total unary operation only after its original child's complete domain check. -/
@[expose] def unary (operation : Unary) {input : Expr arity} : Outcome leafBalls input →
    Outcome leafBalls (operation.expression input)
  | .prepared child => .prepared (child.unary operation)
  | .requested first => .requested (.through (.unary operation input) first)

/-- Test the same original denominator's finite common bound after all of its original child obligations. -/
@[expose] def inverse {input : Expr arity} : Outcome leafBalls input → Outcome leafBalls (.inverse input)
  | .requested first => .requested (.through (.inverse input) first)
  | .prepared child =>
      if separated : Preparation.Separated child.ball then .prepared (child.inverse separated)
      else .requested (.inverse child separated)

/-- Retain the completed original left programme when an ordered right condition remains unresolved. -/
@[expose] def right (operation : Binary) {left right : Expr arity} (first : Common leafBalls left) :
    Outcome leafBalls right → Outcome leafBalls (operation.expression left right)
  | .prepared second => .prepared (first.binary operation second)
  | .requested remaining => .requested (.through (.right operation left first right) remaining)

/-- Check ordered children without entering the original right expression after a left-side request. -/
@[expose] def binary (operation : Binary) {left right : Expr arity} (first : Outcome leafBalls left)
    (second : Unit → Outcome leafBalls right) : Outcome leafBalls (operation.expression left right) :=
  match first with
  | .prepared original => (second ()).right operation original
  | .requested remaining => .requested (.through (.left operation left right) remaining)

end Outcome

/-- Compute finite structural common bounds in original expression order without evaluating any parameter cache.

The same exact leaf bounds feed every occurrence. Every original child remains
in its retained programme, including those under exponent zero. An insufficient
ball yields a typed finite request and never an asserted geometric pole.
-/
@[expose] def inspect (leafBalls : Basic.Leaf arity → Ball) (expression : Expr arity) :
    Outcome leafBalls expression :=
  match expression with
  | .base expression => .prepared (Common.base expression leafBalls)
  | .neg input => (inspect leafBalls input).unary .neg
  | .pow input exponent => (inspect leafBalls input).unary (.pow exponent)
  | .conj input => (inspect leafBalls input).unary .conj
  | .inverse input => (inspect leafBalls input).inverse
  | .add left right => (inspect leafBalls left).binary .add (fun _ => inspect leafBalls right)
  | .sub left right => (inspect leafBalls left).binary .sub (fun _ => inspect leafBalls right)
  | .mul left right => (inspect leafBalls left).binary .mul (fun _ => inspect leafBalls right)
termination_by sizeOf expression
decreasing_by
  all_goals
    simp only [Basic.Expr.neg.sizeOf_spec, Basic.Expr.pow.sizeOf_spec, Basic.Expr.conj.sizeOf_spec,
      Basic.Expr.inverse.sizeOf_spec, Basic.Expr.add.sizeOf_spec, Basic.Expr.sub.sizeOf_spec,
      Basic.Expr.mul.sizeOf_spec, -eq_self, -iff_self]
    omega0

end Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Geometric.Bounds
end
