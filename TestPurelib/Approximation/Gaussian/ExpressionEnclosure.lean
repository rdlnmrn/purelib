module
import Purelib.Approximation.Gaussian.Acquisition.Annotated.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Gaussian.Basic

public import Purelib.Approximation.Gaussian.Acquisition.Expression.Enclosure
import Purelib.Data.Gaussian.Field
import Purelib.System.IO
import Init.System.IOError

/-! # Original compiled construction and geometric observation caches -/

namespace TestPurelib.Approximation.Gaussian.ExpressionEnclosure

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Acquisition.Expression.Basic
open Purelib.Approximation.Gaussian.Geometric (Enclosure)
open Purelib.Approximation.Gaussian.Enclosure (Ball)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)

/-- The original syntax computes the complete actual interpreted ball from authenticated used leaves. -/
example {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (compiled : Compiled environment expression) (geometry : compiled.Geometry) (leafBalls : Leaf arity → Ball)
    (agreement : Construction.Geometry.Balls (construction := compiled.construction) geometry leafBalls) :
    (compiled.encloseBindings geometry).result.ball = expression.ball leafBalls :=
  compiled.encloseBindings_ball geometry leafBalls agreement

/-- Every original sample lies in the same syntax-computed common ball. -/
example {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (compiled : Compiled environment expression) (geometry : compiled.Geometry) (leafBalls : Leaf arity → Ball)
    (agreement : Construction.Geometry.Balls (construction := compiled.construction) geometry leafBalls)
    (index : Nat) : (expression.ball leafBalls).Contains
      ((compiled.encloseBindings geometry).result.source.sample index) := by
  have inside := (compiled.encloseBindings geometry).enclosed.contains index
  change (compiled.encloseBindings geometry).result.ball.Contains
    ((compiled.encloseBindings geometry).result.source.sample index) at inside
  rewrite [compiled.encloseBindings_ball geometry leafBalls agreement] at inside
  exact inside

/-- Independent original environments realize the same computed ball without identifying their samples or channels. -/
example {arity : Nat} {firstEnvironment secondEnvironment : Fin arity → Annotated} {expression : Expr arity}
    (first : Compiled firstEnvironment expression) (second : Compiled secondEnvironment expression)
    (firstGeometry : first.Geometry) (secondGeometry : second.Geometry) (leafBalls : Leaf arity → Ball)
    (firstAgreement : Construction.Geometry.Balls (construction := first.construction) firstGeometry leafBalls)
    (secondAgreement : Construction.Geometry.Balls (construction := second.construction) secondGeometry leafBalls) :
    (first.encloseBindings firstGeometry).result.ball = (second.encloseBindings secondGeometry).result.ball :=
  (first.encloseBindings_ball firstGeometry leafBalls firstAgreement).trans
    (second.encloseBindings_ball secondGeometry leafBalls secondAgreement).symm

/-- Every retained bound tree authenticates the complete original syntax-prescribed ball. -/
example {arity : Nat} (expression : Expr arity) (leafBalls : Leaf arity → Ball) :
    (expression.bounds leafBalls).ball = expression.ball leafBalls :=
  (expression.bounds leafBalls).ball_eq

/-- Cached node bounds preserve the complete original compiled result and its actual child cache. -/
example {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (compiled : Compiled environment expression) (geometry : compiled.Geometry) {leafBalls : Leaf arity → Ball}
    (bounds : Expr.Bounds leafBalls expression)
    (agreement : Construction.Geometry.Balls (construction := compiled.construction) geometry leafBalls) :
    (compiled.encloseBindingsFromBounds geometry bounds agreement).val = compiled.encloseBindings geometry :=
  compiled.encloseBindingsFromBounds_computed geometry bounds agreement

/-- Supplied bounds retain the complete original compilation and its actual binding spine. -/
example {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (compiled : Compiled environment expression) (geometry : compiled.Geometry) {leafBalls : Leaf arity → Ball}
    (bounds : Expr.Bounds leafBalls expression)
    (agreement : Construction.Geometry.Balls (construction := compiled.construction) geometry leafBalls) :
    let value := (compiled.encloseBindingsFromBounds geometry bounds agreement).val
    value.original = compiled ∧ value.table = compiled.bindings := by
  exact ⟨(compiled.encloseBindingsFromBounds geometry bounds agreement).val.original_eq,
    (compiled.encloseBindingsFromBounds geometry bounds agreement).val.table_eq⟩

/-- Every original formal observation lies in the same retained common node ball at every index. -/
example {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (compiled : Compiled environment expression) (geometry : compiled.Geometry) {leafBalls : Leaf arity → Ball}
    (bounds : Expr.Bounds leafBalls expression)
    (agreement : Construction.Geometry.Balls (construction := compiled.construction) geometry leafBalls)
    (index : Nat) : bounds.ball.Contains
      ((compiled.encloseBindingsFromBounds geometry bounds agreement).val.result.source.sample index) := by
  let bounded := compiled.encloseBindingsFromBounds geometry bounds agreement
  have inside := bounded.val.enclosed.contains index
  change bounded.val.result.ball.Contains (bounded.val.result.source.sample index) at inside
  rewrite [bounded.ball_eq] at inside
  exact inside

/-- Independent environments consume one bound tree without identifying their channels or observations. -/
example {arity : Nat} {firstEnvironment secondEnvironment : Fin arity → Annotated} {expression : Expr arity}
    (first : Compiled firstEnvironment expression) (second : Compiled secondEnvironment expression)
    (firstGeometry : first.Geometry) (secondGeometry : second.Geometry) {leafBalls : Leaf arity → Ball}
    (bounds : Expr.Bounds leafBalls expression)
    (firstAgreement : Construction.Geometry.Balls (construction := first.construction) firstGeometry leafBalls)
    (secondAgreement : Construction.Geometry.Balls (construction := second.construction) secondGeometry leafBalls) :
    (first.encloseBindingsFromBounds firstGeometry bounds firstAgreement).val.result.ball =
      (second.encloseBindingsFromBounds secondGeometry bounds secondAgreement).val.result.ball :=
  (first.encloseBindingsFromBounds firstGeometry bounds firstAgreement).ball_eq.trans
    (second.encloseBindingsFromBounds secondGeometry bounds secondAgreement).ball_eq.symm

/-- Shared cancellation authenticates its common bound through the one retained original child. -/
example {arity : Nat} {environment : Fin arity → Annotated} {bindings : List (Binding environment)}
    {input : Expr arity} {output : Annotated} (child : Annotated)
    (construction : Construction environment input child) (original : output = child.cancel)
    (geometry : construction.Geometry bindings) (leafBalls : Leaf arity → Ball)
    (agreement : Construction.Geometry.Balls (construction := construction) geometry leafBalls) :
    Construction.Geometry.Balls (construction := .addNeg child construction original) geometry leafBalls := agreement

/-- Shared self-subtraction needs no second geometric leaf-bound contract. -/
example {arity : Nat} {environment : Fin arity → Annotated} {bindings : List (Binding environment)}
    {input : Expr arity} {output : Annotated} (child : Annotated)
    (construction : Construction environment input child) (original : output = child.cancel)
    (geometry : construction.Geometry bindings) (leafBalls : Leaf arity → Ball)
    (agreement : Construction.Geometry.Balls (construction := construction) geometry leafBalls) :
    Construction.Geometry.Balls (construction := .subSelf child construction original) geometry leafBalls := agreement

/-- A shared square authenticates both formal multiplication occurrences through its same original child. -/
example {arity : Nat} {environment : Fin arity → Annotated} {bindings : List (Binding environment)}
    {input : Expr arity} {output : Annotated} (child : Annotated)
    (construction : Construction environment input child) (original : output = child.square)
    (geometry : construction.Geometry bindings) (leafBalls : Leaf arity → Ball)
    (agreement : Construction.Geometry.Balls (construction := construction) geometry leafBalls) :
    Construction.Geometry.Balls (construction := .square child construction true original)
      geometry leafBalls := agreement

example {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (compiled : Compiled environment expression) (geometry : compiled.Geometry) :
    (compiled.encloseBindings geometry).original = compiled := rfl

example {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (compiled : Compiled environment expression) (geometry : compiled.Geometry) :
    NamedEquivalent (expression.denote environment).name
      (compiled.encloseBindings geometry).result.source.toApproximation.toNamed :=
  (compiled.encloseBindings geometry).denoteEquivalent

example {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (compiled : Compiled environment expression) (geometry : compiled.Geometry) (index : Nat) :
    (compiled.encloseBindings geometry).result.ball.Contains
      ((compiled.encloseBindings geometry).result.source.sample index) :=
  (compiled.encloseBindings geometry).enclosed.contains index

example {arity : Nat} {environment : Fin arity → Annotated}
    {bindings : List (Binding environment)} {leaf : Leaf arity}
    (geometry : Binding.Geometry bindings leaf) (annotation : Annotated)
    (original : annotation = leaf.annotation environment) (index : Nat) :
    (geometry.enclose annotation original).source.sample index = geometry.enclosing.source.sample index :=
  geometry.enclosing.cast_sample _ index

example {arity : Nat} {environment : Fin arity → Annotated} {bindings : List (Binding environment)}
    {input : Expr arity} {output : Annotated} (child : Annotated)
    (construction : Construction environment input child) (original : output = child.cancel)
    (geometry : construction.Geometry bindings) :
    ((Construction.addNeg child construction original).enclose bindings geometry).cache.positions =
      (construction.enclose bindings geometry).cache.positions := rfl

example {arity : Nat} {environment : Fin arity → Annotated} {bindings : List (Binding environment)}
    {input : Expr arity} {output : Annotated} (child : Annotated)
    (construction : Construction environment input child) (original : output = child.cancel)
    (geometry : construction.Geometry bindings) :
    ((Construction.subSelf child construction original).enclose bindings geometry).cache.positions =
      (construction.enclose bindings geometry).cache.positions := rfl

example {arity : Nat} {environment : Fin arity → Annotated} {bindings : List (Binding environment)}
    {input : Expr arity} {output : Annotated} (child : Annotated)
    (construction : Construction environment input child) (original : output = child.square)
    (geometry : construction.Geometry bindings) :
    ((Construction.square child construction true original).enclose bindings geometry).cache.positions =
      (construction.enclose bindings geometry).cache.positions := rfl

example {arity : Nat} {environment : Fin arity → Annotated} {bindings : List (Binding environment)}
    (parameter : Canonical) (sheet : Fin 2) (annotation : Annotated)
    (original : annotation = Annotated.root parameter sheet)
    (geometry : Binding.Geometry bindings (.root parameter sheet)) :
    ((Construction.root parameter sheet annotation original).enclose bindings geometry).cache.positions =
      [geometry.position.val] := rfl

/-- Check a completed original construction using its cached output and actual ordered binding receipts. -/
private def checkResult {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    {bindings : List (Binding environment)} {compiled : Compiled environment expression}
    (cached : compiled.Enclosed bindings) (expected : Canonical) (positions : List Nat) : IO Unit := do
  let reading := cached.result.source.sample 0
  unless reading = expected ∧ cached.result.ball.Contains reading ∧
      cached.enclosed.cache.positions = positions do
    throw (IO.userError "original construction geometry changed its sample, enclosure or bounded occurrence order")

/-- Exercise original opaque atom constructions, shared children and unused binding slots.

The numerical input is the actual supplied original atom realization. The
fixture compiles each source once, then supplies geometry at its retained
bounded occurrences without consulting optimized output provenance.
-/
public def check (annotation : Annotated) (enclosing : Enclosure annotation.channel) : IO Unit := do
  let environment : Fin 2 → Annotated := fun index =>
    if index.val = 0 then annotation else Annotated.opaque (CoherentNamed.Coherence.exact 99)
  let index : Fin 2 := ⟨0, by decide⟩
  let atom : Expr 2 := .atom index
  let first := enclosing.source.sample 0
  let leafBalls : Leaf 2 → Ball := fun _ => enclosing.ball
  let cancellation := (Expr.add atom (.neg atom)).retain environment
  let cancelGeometry : cancellation.Geometry :=
    ⟨⟨0, by change 0 < 1; decide⟩, rfl, enclosing⟩
  let cancelBounds := (Expr.add atom (.neg atom)).bounds leafBalls
  let cancelBall := cancelBounds.ball
  have cancelAgreement : Construction.Geometry.Balls (construction := cancellation.construction)
      cancelGeometry leafBalls := rfl
  let cancelBounded := cancellation.encloseBindingsFromBounds cancelGeometry cancelBounds cancelAgreement
  let cancelCache := cancelBounded.val
  have cancelBall_eq : cancelCache.result.ball = cancelBall := cancelBounded.ball_eq
  checkResult cancelCache 0 [0]
  unless cancelCache.result.ball == cancelBall do
    throw (IO.userError "shared cancellation lost its procedure-computed common ball")
  unless 0 < cancelCache.result.ball.radiusSq do
    throw (IO.userError "shared cancellation replaced the actual input enclosure by an optimized zero ball")
  let subtraction := (Expr.sub atom atom).retain environment
  let subGeometry : subtraction.Geometry := ⟨⟨0, by change 0 < 1; decide⟩, rfl, enclosing⟩
  let subBounds := (Expr.sub atom atom).bounds leafBalls
  let subBall := subBounds.ball
  have subAgreement : Construction.Geometry.Balls (construction := subtraction.construction)
      subGeometry leafBalls := rfl
  let subBounded := subtraction.encloseBindingsFromBounds subGeometry subBounds subAgreement
  let subCache := subBounded.val
  have subBall_eq : subCache.result.ball = subBall := subBounded.ball_eq
  checkResult subCache 0 [0]
  unless subCache.result.ball == subBall do
    throw (IO.userError "shared self-subtraction lost its original common ball")
  let orderedSubtraction := (Expr.sub atom (.rational 1)).retain environment
  let orderedSubGeometry : orderedSubtraction.Geometry :=
    ⟨⟨⟨0, by change 0 < 1; decide⟩, rfl, enclosing⟩, ()⟩
  let orderedSubBounds := (Expr.sub atom (.rational 1)).bounds leafBalls
  let orderedSubBall := orderedSubBounds.ball
  have orderedSubAgreement : Construction.Geometry.Balls (construction := orderedSubtraction.construction)
      orderedSubGeometry leafBalls := ⟨rfl, True.intro⟩
  let orderedSubBounded :=
    orderedSubtraction.encloseBindingsFromBounds orderedSubGeometry orderedSubBounds orderedSubAgreement
  let orderedSubCache := orderedSubBounded.val
  have orderedSubBall_eq : orderedSubCache.result.ball = orderedSubBall := orderedSubBounded.ball_eq
  checkResult orderedSubCache (first - 1) [0]
  unless orderedSubCache.result.ball == orderedSubBall do
    throw (IO.userError "ordered subtraction lost the constant-and-original-input common bound")
  let squared := (Expr.mul atom atom).retain environment
  let squareGeometry : squared.Geometry := ⟨⟨0, by change 0 < 1; decide⟩, rfl, enclosing⟩
  let squareBounds := (Expr.mul atom atom).bounds leafBalls
  let squareBall := squareBounds.ball
  have squareAgreement : Construction.Geometry.Balls (construction := squared.construction)
      squareGeometry leafBalls := rfl
  let squareBounded := squared.encloseBindingsFromBounds squareGeometry squareBounds squareAgreement
  let squareCache := squareBounded.val
  have squareBall_eq : squareCache.result.ball = squareBall := squareBounded.ball_eq
  checkResult squareCache (first * first) [0]
  unless squareCache.result.ball == squareBall do
    throw (IO.userError "shared multiplication lost its single-child authenticated common ball")
  let nested := (Expr.add (.neg atom) (.mul atom (.rational 2))).retain environment
  let left : Binding.Geometry nested.bindings (.atom index) := ⟨⟨0, by change 0 < 2; decide⟩, rfl, enclosing⟩
  let right : Binding.Geometry nested.bindings (.atom index) := ⟨⟨1, by change 1 < 2; decide⟩, rfl, enclosing⟩
  let nestedGeometry : nested.Geometry := ⟨left, ⟨right, ()⟩⟩
  let nestedBounds := (Expr.add (.neg atom) (.mul atom (.rational 2))).bounds leafBalls
  let nestedBall := nestedBounds.ball
  have nestedAgreement : Construction.Geometry.Balls (construction := nested.construction)
      nestedGeometry leafBalls := ⟨rfl, rfl, True.intro⟩
  let nestedBounded := nested.encloseBindingsFromBounds nestedGeometry nestedBounds nestedAgreement
  let nestedCache := nestedBounded.val
  have nestedBall_eq : nestedCache.result.ball = nestedBall := nestedBounded.ball_eq
  checkResult nestedCache (-first + first * 2) [0, 1]
  unless nestedCache.result.ball == nestedBall do
    throw (IO.userError "nested repeated occurrences failed to share their procedure-computed common bound")
  let scalar := (Expr.rational (arity := 2) 7).retain environment
  let scalarBounds := (Expr.rational (arity := 2) 7).bounds leafBalls
  checkResult (scalar.encloseBindingsFromBounds () scalarBounds True.intro).val 7 []
  let originalAtom := atom.retain environment
  let unused : Binding environment := ⟨.atom ⟨1, by decide⟩, environment ⟨1, by decide⟩, rfl⟩
  let withUnused := originalAtom.bindings ++ [unused]
  let onlyUsed : originalAtom.construction.Geometry withUnused :=
    ⟨⟨0, by change 0 < 2; decide⟩, rfl, enclosing⟩
  let atomBounds := atom.bounds leafBalls
  have usedAgreement : Construction.Geometry.Balls (construction := originalAtom.construction)
      onlyUsed leafBalls := rfl
  let usedBounded := originalAtom.encloseFromBounds withUnused onlyUsed atomBounds usedAgreement
  let usedCache := usedBounded.val
  have usedBall_eq : usedCache.result.ball = atom.ball leafBalls :=
    usedBounded.ball_eq.trans atomBounds.ball_eq
  checkResult usedCache first [0]
  unless usedCache.result.ball == atom.ball leafBalls do
    throw (IO.userError "an unused original binding changed the authenticated used-leaf common bound")
  let _ := cancelBall_eq
  let _ := subBall_eq
  let _ := orderedSubBall_eq
  let _ := squareBall_eq
  let _ := nestedBall_eq
  let _ := usedBall_eq
  Purelib.System.IO.println
    "construction enclosure: original opaque input, shared caches, repeated bounded occurrences and unused slot checked"
  Purelib.System.IO.println
    "construction common balls: shared nodes, repeated occurrences and unused bindings authenticated"
  Purelib.System.IO.println
    "construction retained bounds: stored node balls consumed with original cubic children and occurrence caches"

end TestPurelib.Approximation.Gaussian.ExpressionEnclosure
