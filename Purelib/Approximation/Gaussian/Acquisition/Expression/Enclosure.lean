module
import Purelib.Approximation.Gaussian.Acquisition.Annotated.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Gaussian.Basic

public import Purelib.Approximation.Gaussian.Acquisition.Expression.Bindings
public import Purelib.Approximation.Gaussian.Geometric.Enclosure
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Spatial enclosures of original retained acquisition constructions -/

public section

namespace Purelib.Approximation.Gaussian.Acquisition.Expression.Basic

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Geometric (Enclosure)
open Purelib.Approximation.Gaussian.Enclosure (Ball)

namespace Expr

/-- Compute a common arithmetic ball from the original syntax and supplied original leaf balls.

The fold uses the same ordered point, negation, addition, subtraction and
multiplication operations as the geometric interpreter. Its finite output
can be retained outside a family of parameter-indexed interpretations.
-/
@[expose] def ball {arity : Nat} (expression : Expr arity) (leafBalls : Leaf arity → Ball) : Ball :=
  let Result : Mode → Type := fun mode => match mode with
    | .total => Ball
    | .checked => PUnit
  let rec compute {mode : Mode} (expression : Expr arity mode) : Result mode :=
    match expression with
    | .atom index => leafBalls (.atom index)
    | .rational value => Ball.point value
    | .root parameter sheet => leafBalls (.root parameter sheet)
    | .neg input =>
      match mode with
      | .total => (compute input).neg
      | .checked => PUnit.unit
    | .add left right =>
      match mode with
      | .total => (compute left).add (compute right)
      | .checked => PUnit.unit
    | .sub left right =>
      match mode with
      | .total => (compute left).sub (compute right)
      | .checked => PUnit.unit
    | .mul left right =>
      match mode with
      | .total => (compute left).mul (compute right)
      | .checked => PUnit.unit
    | .base _ | .pow _ _ | .conj _ | .inverse _ => PUnit.unit
  termination_by structural expression
  compute expression

set_option genInjectivity false in
/-- The actual finite common ball at every node of an original expression.

Each node retains its original children and its complete procedure-computed
ball. Scalar certificates authenticate every stored ball against the same
original syntax and leaf table; consuming the tree needs no ball arithmetic.
-/
inductive Bounds {arity : Nat} (leafBalls : Leaf arity → Ball) : Expr arity → Type where
  /-- Retain the supplied ball at the same original bounded atom. -/
  | atom (index : Fin arity) (ball : Ball) (same : ball = leafBalls (.atom index)) : Bounds leafBalls (.atom index)
  /-- Retain the computed exact point ball at the same original constant. -/
  | rational (value : Purelib.Data.Gaussian.Basic.Canonical) (ball : Ball) (same : ball = Ball.point value) :
      Bounds leafBalls (.rational value)
  /-- Retain the supplied ball at the same displayed root parameter and sheet. -/
  | root (parameter : Purelib.Data.Gaussian.Basic.Canonical) (sheet : Fin 2)
      (ball : Ball) (same : ball = leafBalls (.root parameter sheet)) : Bounds leafBalls (.root parameter sheet)
  /-- Retain the actual child and its computed negated ball. -/
  | neg {input : Expr arity} (child : Bounds leafBalls input) (ball : Ball)
      (same : ball = (Expr.neg input).ball leafBalls) : Bounds leafBalls (.neg input)
  /-- Retain both original ordered children and their computed sum ball. -/
  | add {left right : Expr arity} (first : Bounds leafBalls left) (second : Bounds leafBalls right)
      (ball : Ball) (same : ball = (Expr.add left right).ball leafBalls) : Bounds leafBalls (.add left right)
  /-- Retain both original ordered children and their computed difference ball. -/
  | sub {left right : Expr arity} (first : Bounds leafBalls left) (second : Bounds leafBalls right)
      (ball : Ball) (same : ball = (Expr.sub left right).ball leafBalls) : Bounds leafBalls (.sub left right)
  /-- Retain both original ordered children and their computed product ball. -/
  | mul {left right : Expr arity} (first : Bounds leafBalls left) (second : Bounds leafBalls right)
      (ball : Ball) (same : ball = (Expr.mul left right).ball leafBalls) : Bounds leafBalls (.mul left right)

constructive_injectivity Bounds

namespace Bounds

/-- Read the actual common ball retained at this original syntax node. -/
@[expose] def ball {arity : Nat} {leafBalls : Leaf arity → Ball} {expression : Expr arity} :
    Bounds leafBalls expression → Ball
  | .atom _ ball _ | .rational _ ball _ | .root _ _ ball _ | .neg _ ball _ |
      .add _ _ ball _ | .sub _ _ ball _ | .mul _ _ ball _ => ball

/-- Every cached node ball is exactly the original syntax's prescribed ball. -/
theorem ball_eq {arity : Nat} {leafBalls : Leaf arity → Ball} {expression : Expr arity}
    (bounds : Bounds leafBalls expression) : bounds.ball = expression.ball leafBalls :=
  match bounds with
  | .atom _ _ same | .rational _ _ same | .root _ _ _ same | .neg _ _ same |
      .add _ _ _ same | .sub _ _ _ same | .mul _ _ _ same => same

end Bounds

/-- Compute and retain every common node ball once from its actual stored child balls.

The result is independent of parameter-indexed numerical programs. Its scalar
readbacks let later interpreters consume the stored balls directly while
retaining the original construction, channels and geometric child caches.
-/
@[expose] def bounds {arity : Nat} (expression : Expr arity) (leafBalls : Leaf arity → Ball) :
    Bounds leafBalls expression :=
  let Result : (mode : Mode) → Expr arity mode → Type := fun mode => match mode with
    | .total => fun expression => Bounds leafBalls expression
    | .checked => fun _ => PUnit
  let rec compute {mode : Mode} (expression : Expr arity mode) : Result mode expression :=
    match expression with
    | .atom index => .atom index (leafBalls (.atom index)) rfl
    | .rational value => .rational value (Ball.point value) rfl
    | .root parameter sheet => .root parameter sheet (leafBalls (.root parameter sheet)) rfl
    | .neg input =>
      match mode with
      | .total =>
          let child := compute input
          .neg child child.ball.neg (congrArg Ball.neg child.ball_eq)
      | .checked => PUnit.unit
    | .add left right =>
      match mode with
      | .total =>
          let first := compute left
          let second := compute right
          .add first second (first.ball.add second.ball) (congrArg₂ Ball.add first.ball_eq second.ball_eq)
      | .checked => PUnit.unit
    | .sub left right =>
      match mode with
      | .total =>
          let first := compute left
          let second := compute right
          .sub first second (first.ball.sub second.ball) (congrArg₂ Ball.sub first.ball_eq second.ball_eq)
      | .checked => PUnit.unit
    | .mul left right =>
      match mode with
      | .total =>
          let first := compute left
          let second := compute right
          .mul first second (first.ball.mul second.ball) (congrArg₂ Ball.mul first.ball_eq second.ball_eq)
      | .checked => PUnit.unit
    | .base _ | .pow _ _ | .conj _ | .inverse _ => PUnit.unit
  termination_by structural expression
  compute expression

end Expr

namespace Binding

set_option genInjectivity false in
/-- A geometric realization of one checked occurrence in the original finite binding table.

The retained position and leaf equality authenticate the actual original
annotation. Geometry is required only for the leaf selected by this receipt.
-/
structure Geometry {arity : Nat} {environment : Fin arity → Annotated}
    (bindings : List (Binding environment)) (leaf : Leaf arity) where
  /-- The actual bounded original binding occurrence supplying this geometry. -/
  position : Fin bindings.length
  /-- The selected original occurrence has the requested source leaf. -/
  leaf_eq : (read bindings position).leaf = leaf
  /-- The geometric source and enclosure realize that same retained binding channel. -/
  enclosing : Enclosure (channels bindings position)

constructive_injectivity Geometry

namespace Geometry

/-- Read a leaf geometry from a complete finite table at its original located occurrence. -/
@[expose] def ofTable {arity : Nat} {environment : Fin arity → Annotated}
    (bindings : List (Binding environment))
    (entries : (index : Fin bindings.length) → Enclosure (channels bindings index))
    (leaf : Leaf arity) (present : Present leaf bindings) : Geometry bindings leaf :=
  let selected := locate leaf bindings present
  ⟨selected.val, selected.property, entries selected.val⟩

/-- Transport the actual selected binding geometry to its exact original leaf annotation.

The transport uses the complete retained annotation ownership equality and
preserves the selected source, ball and numerical observations.
-/
@[expose] def enclose {arity : Nat} {environment : Fin arity → Annotated}
    {bindings : List (Binding environment)} {leaf : Leaf arity}
    (geometry : Geometry bindings leaf) (annotation : Annotated)
    (original : annotation = leaf.annotation environment) : Enclosure annotation.channel :=
  geometry.enclosing.cast
    (congrArg Annotated.channel ((Lookup.annotation_eq geometry.position geometry.leaf_eq).trans original.symm))

/-- Authenticating an original bounded leaf preserves its complete supplied ball record. -/
theorem enclose_ball {arity : Nat} {environment : Fin arity → Annotated}
    {bindings : List (Binding environment)} {leaf : Leaf arity}
    (geometry : Geometry bindings leaf) (annotation : Annotated)
    (original : annotation = leaf.annotation environment) :
    (geometry.enclose annotation original).ball = geometry.enclosing.ball :=
  geometry.enclosing.cast_ball _

end Geometry

end Binding

namespace Construction

/-- Geometric inputs for exactly the original leaves used by a retained construction.

Ordered binary nodes retain two inputs. Shared cancellation and square nodes
retain one input tree, and exact constants introduce no binding obligation.
-/
@[expose] def Geometry {arity : Nat} {environment : Fin arity → Annotated}
    (bindings : List (Binding environment)) : {expression : Expr arity} → {annotation : Annotated} →
      Construction environment expression annotation → Type
  | _, _, .atom index _ _ => Binding.Geometry bindings (.atom index)
  | _, _, .rational _ _ _ => Unit
  | _, _, .root parameter sheet _ _ => Binding.Geometry bindings (.root parameter sheet)
  | _, _, .neg _ child _ => child.Geometry bindings
  | _, _, .add _ _ _ first second _ _ => first.Geometry bindings × second.Geometry bindings
  | _, _, .addNeg _ child _ => child.Geometry bindings
  | _, _, .sub _ _ _ first second _ _ => first.Geometry bindings × second.Geometry bindings
  | _, _, .subSelf _ child _ => child.Geometry bindings
  | _, _, .mul _ _ _ first second _ _ => first.Geometry bindings × second.Geometry bindings
  | _, _, .square _ child _ _ => child.Geometry bindings

namespace Geometry

/-- Authenticate each actually used bounded leaf's ball against the original syntax's common ball table.

The contract follows the original retained construction and its same supplied
geometry tree. Shared cancellation, subtraction and square nodes require only
their single original child; unused bindings impose no additional condition.
-/
@[expose] def Balls {arity : Nat} {environment : Fin arity → Annotated}
    {bindings : List (Binding environment)} :
    {expression : Expr arity} → {annotation : Annotated} →
    {construction : Construction environment expression annotation} →
      construction.Geometry bindings → (Leaf arity → Ball) → Prop
  | _, _, .atom index _ _, geometry, leafBalls => geometry.enclosing.ball = leafBalls (.atom index)
  | _, _, .rational _ _ _, _, _ => True
  | _, _, .root parameter sheet _ _, geometry, leafBalls => geometry.enclosing.ball = leafBalls (.root parameter sheet)
  | _, _, .neg _ child _, geometry, leafBalls => Balls (construction := child) geometry leafBalls
  | _, _, .add _ _ _ first second _ _, geometry, leafBalls =>
      Balls (construction := first) geometry.1 leafBalls ∧ Balls (construction := second) geometry.2 leafBalls
  | _, _, .addNeg _ child _, geometry, leafBalls => Balls (construction := child) geometry leafBalls
  | _, _, .sub _ _ _ first second _ _, geometry, leafBalls =>
      Balls (construction := first) geometry.1 leafBalls ∧ Balls (construction := second) geometry.2 leafBalls
  | _, _, .subSelf _ child _, geometry, leafBalls => Balls (construction := child) geometry leafBalls
  | _, _, .mul _ _ _ first second _ _, geometry, leafBalls =>
      Balls (construction := first) geometry.1 leafBalls ∧ Balls (construction := second) geometry.2 leafBalls
  | _, _, .square _ child _ _, geometry, leafBalls => Balls (construction := child) geometry leafBalls

/-- Select only used original leaf occurrences from a complete geometric binding table. -/
@[expose] def ofTable {arity : Nat} {environment : Fin arity → Annotated}
    (bindings : List (Binding environment))
    (entries : (index : Fin bindings.length) → Enclosure (Binding.channels bindings index)) :
    {expression : Expr arity} → {annotation : Annotated} →
      (construction : Construction environment expression annotation) → construction.Supported bindings →
        construction.Geometry bindings
  | _, _, .atom index _ _, supported => Binding.Geometry.ofTable bindings entries (.atom index) supported
  | _, _, .rational _ _ _, _ => ()
  | _, _, .root parameter sheet _ _, supported =>
      Binding.Geometry.ofTable bindings entries (.root parameter sheet) supported
  | _, _, .neg _ child _, supported => ofTable bindings entries child supported
  | _, _, .add _ _ _ first second _ _, supported =>
      ⟨ofTable bindings entries first supported.1, ofTable bindings entries second supported.2⟩
  | _, _, .addNeg _ child _, supported => ofTable bindings entries child supported
  | _, _, .sub _ _ _ first second _ _, supported =>
      ⟨ofTable bindings entries first supported.1, ofTable bindings entries second supported.2⟩
  | _, _, .subSelf _ child _, supported => ofTable bindings entries child supported
  | _, _, .mul _ _ _ first second _ _, supported =>
      ⟨ofTable bindings entries first supported.1, ofTable bindings entries second supported.2⟩
  | _, _, .square _ child _ _, supported => ofTable bindings entries child supported

end Geometry

set_option genInjectivity false in
/-- Cached geometric child results following an exact original retained construction.

Every constructor retains its actual original annotations, construction and
operation equality. Shared nodes store one child geometry and its cache while
using its same numerical source twice in the formal arithmetic result.
-/
inductive Interpretation {arity : Nat} {environment : Fin arity → Annotated}
    (bindings : List (Binding environment)) : {expression : Expr arity} → {annotation : Annotated} →
      Construction environment expression annotation → Enclosure annotation.channel → Type 1 where
  /-- Retain the selected bounded original atom occurrence and its actual geometry. -/
  | atom (index : Fin arity) (annotation : Annotated) (original : annotation = environment index)
      (geometry : Binding.Geometry bindings (.atom index)) :
      Interpretation bindings (.atom index annotation original) (geometry.enclose annotation original)
  /-- Retain the exact scalar annotation and its exact geometric source. -/
  | rational (value : Purelib.Data.Gaussian.Basic.Canonical) (annotation : Annotated)
      (original : annotation = Annotated.rational value) :
      Interpretation bindings (.rational value annotation original)
        ((Enclosure.exact value).cast (congrArg Annotated.channel original).symm)
  /-- Retain the displayed original root leaf and its selected original binding geometry. -/
  | root (parameter : Purelib.Data.Gaussian.Basic.Canonical) (sheet : Fin 2) (annotation : Annotated)
      (original : annotation = Annotated.root parameter sheet)
      (geometry : Binding.Geometry bindings (.root parameter sheet)) :
      Interpretation bindings (.root parameter sheet annotation original) (geometry.enclose annotation original)
  /-- Retain one original child and its geometric negation. -/
  | neg {input : Expr arity} {output : Annotated} (child : Annotated)
      (construction : Construction environment input child) (original : output = child.neg)
      (enclosing : Enclosure child.channel) (cache : Interpretation bindings construction enclosing) :
      Interpretation bindings (.neg child construction original)
        (enclosing.neg.cast (congrArg Annotated.channel original).symm)
  /-- Retain ordered original children and their geometric addition. -/
  | add {left right : Expr arity} {output : Annotated} (different : right ≠ .neg left)
      (first second : Annotated) (firstConstruction : Construction environment left first)
      (secondConstruction : Construction environment right second) (inferAlgebraic : Bool)
      (original : output = first.add second inferAlgebraic)
      (leftGeometry : Enclosure first.channel) (rightGeometry : Enclosure second.channel)
      (leftCache : Interpretation bindings firstConstruction leftGeometry)
      (rightCache : Interpretation bindings secondConstruction rightGeometry) :
      Interpretation bindings (.add different first second firstConstruction secondConstruction inferAlgebraic original)
        ((leftGeometry.add rightGeometry).cast (congrArg Annotated.channel original).symm)
  /-- Retain one child cache for both original signed cancellation occurrences. -/
  | addNeg {input : Expr arity} {output : Annotated} (child : Annotated)
      (construction : Construction environment input child) (original : output = child.cancel)
      (enclosing : Enclosure child.channel) (cache : Interpretation bindings construction enclosing) :
      Interpretation bindings (.addNeg child construction original)
        ((enclosing.add enclosing.neg).cast (congrArg Annotated.channel original).symm)
  /-- Retain ordered original children and their formal add-negation subtraction. -/
  | sub {left right : Expr arity} {output : Annotated} (different : left ≠ right)
      (first second : Annotated) (firstConstruction : Construction environment left first)
      (secondConstruction : Construction environment right second) (inferAlgebraic : Bool)
      (original : output = first.add second.neg inferAlgebraic)
      (leftGeometry : Enclosure first.channel) (rightGeometry : Enclosure second.channel)
      (leftCache : Interpretation bindings firstConstruction leftGeometry)
      (rightCache : Interpretation bindings secondConstruction rightGeometry) :
      Interpretation bindings (.sub different first second firstConstruction secondConstruction inferAlgebraic original)
        ((leftGeometry.sub rightGeometry).cast (congrArg Annotated.channel original).symm)
  /-- Retain one child cache for both original subtraction occurrences. -/
  | subSelf {input : Expr arity} {output : Annotated} (child : Annotated)
      (construction : Construction environment input child) (original : output = child.cancel)
      (enclosing : Enclosure child.channel) (cache : Interpretation bindings construction enclosing) :
      Interpretation bindings (.subSelf child construction original)
        ((enclosing.sub enclosing).cast (congrArg Annotated.channel original).symm)
  /-- Retain ordered original children and their geometric product. -/
  | mul {left right : Expr arity} {output : Annotated} (different : left ≠ right)
      (first second : Annotated) (firstConstruction : Construction environment left first)
      (secondConstruction : Construction environment right second) (inferAlgebraic : Bool)
      (original : output = first.mul second inferAlgebraic)
      (leftGeometry : Enclosure first.channel) (rightGeometry : Enclosure second.channel)
      (leftCache : Interpretation bindings firstConstruction leftGeometry)
      (rightCache : Interpretation bindings secondConstruction rightGeometry) :
      Interpretation bindings (.mul different first second firstConstruction secondConstruction inferAlgebraic original)
        ((leftGeometry.mul rightGeometry).cast (congrArg Annotated.channel original).symm)
  /-- Retain one child cache for both original square factors. -/
  | square {input : Expr arity} {output : Annotated} (child : Annotated)
      (construction : Construction environment input child) (inferAlgebraic : Bool)
      (original : output = child.square inferAlgebraic)
      (enclosing : Enclosure child.channel) (cache : Interpretation bindings construction enclosing) :
      Interpretation bindings (.square child construction inferAlgebraic original)
        ((enclosing.mul enclosing).cast (congrArg Annotated.channel original).symm)

constructive_injectivity Interpretation

namespace Interpretation

/-- Read the ordered original bounded leaf positions retained by an interpretation cache.

Shared nodes visit their one actual child cache once. Unshared ordered nodes
retain both source-occurrence lists even when their values happen to coincide.
-/
@[expose] def positions {arity : Nat} {environment : Fin arity → Annotated}
    {bindings : List (Binding environment)} : {expression : Expr arity} → {annotation : Annotated} →
      {construction : Construction environment expression annotation} → {enclosing : Enclosure annotation.channel} →
        Interpretation bindings construction enclosing → List Nat
  | _, _, _, _, .atom _ _ _ geometry => [geometry.position.val]
  | _, _, _, _, .rational _ _ _ => []
  | _, _, _, _, .root _ _ _ _ geometry => [geometry.position.val]
  | _, _, _, _, .neg _ _ _ _ cache => cache.positions
  | _, _, _, _, .add _ _ _ _ _ _ _ _ _ left right => left.positions ++ right.positions
  | _, _, _, _, .addNeg _ _ _ _ cache => cache.positions
  | _, _, _, _, .sub _ _ _ _ _ _ _ _ _ left right => left.positions ++ right.positions
  | _, _, _, _, .subSelf _ _ _ _ cache => cache.positions
  | _, _, _, _, .mul _ _ _ _ _ _ _ _ _ left right => left.positions ++ right.positions
  | _, _, _, _, .square _ _ _ _ _ cache => cache.positions

end Interpretation

set_option genInjectivity false in
/-- A cached output enclosure and its authenticated original construction traversal. -/
structure Enclosed {arity : Nat} {environment : Fin arity → Annotated}
    (bindings : List (Binding environment)) {expression : Expr arity} {annotation : Annotated}
    (construction : Construction environment expression annotation) where
  /-- The actual cached formal geometric realization of the original output channel. -/
  result : Enclosure annotation.channel
  /-- The retained original nodes, binding receipts and computed child enclosures. -/
  cache : construction.Interpretation bindings result

constructive_injectivity Enclosed

namespace Enclosed

/-- Every numerical observation of a cached interpretation stays in its actual computed output ball. -/
theorem contains {arity : Nat} {environment : Fin arity → Annotated}
    {bindings : List (Binding environment)} {expression : Expr arity} {annotation : Annotated}
    {construction : Construction environment expression annotation} (enclosed : construction.Enclosed bindings)
    (index : Nat) : enclosed.result.ball.Contains (enclosed.result.source.sample index) :=
  enclosed.result.contains index

/-- Retain an actual output and the same original cache through a complete output-record equality. -/
private def withResult {arity : Nat} {environment : Fin arity → Annotated}
    {bindings : List (Binding environment)} {expression : Expr arity} {annotation : Annotated}
    {construction : Construction environment expression annotation} {expected : Enclosure annotation.channel}
    (cache : construction.Interpretation bindings expected) (result : Enclosure annotation.channel)
    (same : result = expected) : construction.Enclosed bindings :=
  ⟨result, same.symm ▸ cache⟩

/-- A complete output equality authenticates the unchanged original interpreted cache. -/
private theorem withResult_eq {arity : Nat} {environment : Fin arity → Annotated}
    {bindings : List (Binding environment)} {expression : Expr arity} {annotation : Annotated}
    {construction : Construction environment expression annotation} {expected : Enclosure annotation.channel}
    (cache : construction.Interpretation bindings expected) (result : Enclosure annotation.channel)
    (same : result = expected) : withResult cache result same = ⟨expected, cache⟩ := by
  cases same
  rfl

end Enclosed

/-- Interpret each actual original construction child once, retaining its computed geometric result.

The procedure never reads optimized output residual samples or repeats the
original compilation. Shared branches reuse one child enclosure while keeping
the original operation and its exact annotation channel transport.
-/
@[expose] def enclose {arity : Nat} {environment : Fin arity → Annotated}
    (bindings : List (Binding environment)) : {expression : Expr arity} → {annotation : Annotated} →
      (construction : Construction environment expression annotation) → construction.Geometry bindings →
        construction.Enclosed bindings
  | _, _, .atom index annotation original, geometry =>
      ⟨geometry.enclose annotation original, .atom index annotation original geometry⟩
  | _, _, .rational value annotation original, _ =>
      ⟨(Enclosure.exact value).cast (congrArg Annotated.channel original).symm,
        .rational value annotation original⟩
  | _, _, .root parameter sheet annotation original, geometry =>
      ⟨geometry.enclose annotation original, .root parameter sheet annotation original geometry⟩
  | _, _, .neg child construction original, geometry =>
      let enclosed := construction.enclose bindings geometry
      ⟨enclosed.result.neg.cast (congrArg Annotated.channel original).symm,
        .neg child construction original enclosed.result enclosed.cache⟩
  | _, _, .add different first second firstConstruction secondConstruction inferAlgebraic original, geometry =>
      let left := firstConstruction.enclose bindings geometry.1
      let right := secondConstruction.enclose bindings geometry.2
      ⟨(left.result.add right.result).cast (congrArg Annotated.channel original).symm,
        .add different first second firstConstruction secondConstruction inferAlgebraic original
          left.result right.result left.cache right.cache⟩
  | _, _, .addNeg child construction original, geometry =>
      let enclosed := construction.enclose bindings geometry
      ⟨(enclosed.result.add enclosed.result.neg).cast (congrArg Annotated.channel original).symm,
        .addNeg child construction original enclosed.result enclosed.cache⟩
  | _, _, .sub different first second firstConstruction secondConstruction inferAlgebraic original, geometry =>
      let left := firstConstruction.enclose bindings geometry.1
      let right := secondConstruction.enclose bindings geometry.2
      ⟨(left.result.sub right.result).cast (congrArg Annotated.channel original).symm,
        .sub different first second firstConstruction secondConstruction inferAlgebraic original
          left.result right.result left.cache right.cache⟩
  | _, _, .subSelf child construction original, geometry =>
      let enclosed := construction.enclose bindings geometry
      ⟨(enclosed.result.sub enclosed.result).cast (congrArg Annotated.channel original).symm,
        .subSelf child construction original enclosed.result enclosed.cache⟩
  | _, _, .mul different first second firstConstruction secondConstruction inferAlgebraic original, geometry =>
      let left := firstConstruction.enclose bindings geometry.1
      let right := secondConstruction.enclose bindings geometry.2
      ⟨(left.result.mul right.result).cast (congrArg Annotated.channel original).symm,
        .mul different first second firstConstruction secondConstruction inferAlgebraic original
          left.result right.result left.cache right.cache⟩
  | _, _, .square child construction inferAlgebraic original, geometry =>
      let enclosed := construction.enclose bindings geometry
      ⟨(enclosed.result.mul enclosed.result).cast (congrArg Annotated.channel original).symm,
        .square child construction inferAlgebraic original enclosed.result enclosed.cache⟩

/-- The actual retained interpretation has the common ball computed from its original syntax.

The authenticated used-leaf contract suffices. Each shared node consumes one
child agreement, and every channel transport preserves the complete ball.
No optimized algebraic residual participates in this readback.
-/
theorem enclose_ball {arity : Nat} {environment : Fin arity → Annotated}
    (bindings : List (Binding environment)) :
    {expression : Expr arity} → {annotation : Annotated} →
    (construction : Construction environment expression annotation) →
    (geometry : construction.Geometry bindings) → (leafBalls : Leaf arity → Ball) →
    Geometry.Balls (construction := construction) geometry leafBalls →
      (construction.enclose bindings geometry).result.ball = expression.ball leafBalls
  | _, _, .atom index annotation original, geometry, _, agreement =>
      (geometry.enclose_ball annotation original).trans agreement
  | _, _, .rational value annotation original, _, _, _ =>
      ((Enclosure.exact value).cast_ball (congrArg Annotated.channel original).symm).trans
        (Enclosure.exact_ball value)
  | _, _, .root parameter sheet annotation original, geometry, _, agreement =>
      (geometry.enclose_ball annotation original).trans agreement
  | _, _, .neg _ construction original, geometry, leafBalls, agreement =>
      let result := (construction.enclose bindings geometry).result
      ((result.neg).cast_ball (congrArg Annotated.channel original).symm).trans
        (result.neg_ball.trans (congrArg Ball.neg (enclose_ball bindings construction geometry leafBalls agreement)))
  | _, _, .add _ _ _ left right _ original, geometry, leafBalls, agreement =>
      let firstResult := (left.enclose bindings geometry.1).result
      let secondResult := (right.enclose bindings geometry.2).result
      ((firstResult.add secondResult).cast_ball (congrArg Annotated.channel original).symm).trans
        ((firstResult.add_ball secondResult).trans (congrArg₂ Ball.add
          (enclose_ball bindings left geometry.1 leafBalls agreement.1)
          (enclose_ball bindings right geometry.2 leafBalls agreement.2)))
  | _, _, .addNeg _ construction original, geometry, leafBalls, agreement =>
      let result := (construction.enclose bindings geometry).result
      let same := enclose_ball bindings construction geometry leafBalls agreement
      ((result.add result.neg).cast_ball (congrArg Annotated.channel original).symm).trans
        ((result.add_ball result.neg).trans (congrArg₂ Ball.add same
          (result.neg_ball.trans (congrArg Ball.neg same))))
  | _, _, .sub _ _ _ left right _ original, geometry, leafBalls, agreement =>
      let firstResult := (left.enclose bindings geometry.1).result
      let secondResult := (right.enclose bindings geometry.2).result
      ((firstResult.sub secondResult).cast_ball (congrArg Annotated.channel original).symm).trans
        ((firstResult.sub_ball secondResult).trans (congrArg₂ Ball.sub
          (enclose_ball bindings left geometry.1 leafBalls agreement.1)
          (enclose_ball bindings right geometry.2 leafBalls agreement.2)))
  | _, _, .subSelf _ construction original, geometry, leafBalls, agreement =>
      let result := (construction.enclose bindings geometry).result
      let same := enclose_ball bindings construction geometry leafBalls agreement
      ((result.sub result).cast_ball (congrArg Annotated.channel original).symm).trans
        ((result.sub_ball result).trans (congrArg₂ Ball.sub same same))
  | _, _, .mul _ _ _ left right _ original, geometry, leafBalls, agreement =>
      let firstResult := (left.enclose bindings geometry.1).result
      let secondResult := (right.enclose bindings geometry.2).result
      ((firstResult.mul secondResult).cast_ball (congrArg Annotated.channel original).symm).trans
        ((firstResult.mul_ball secondResult).trans (congrArg₂ Ball.mul
          (enclose_ball bindings left geometry.1 leafBalls agreement.1)
          (enclose_ball bindings right geometry.2 leafBalls agreement.2)))
  | _, _, .square _ construction _ original, geometry, leafBalls, agreement =>
      let result := (construction.enclose bindings geometry).result
      let same := enclose_ball bindings construction geometry leafBalls agreement
      ((result.mul result).cast_ball (congrArg Annotated.channel original).symm).trans
        ((result.mul_ball result).trans (congrArg₂ Ball.mul same same))

/-- A certified view of the same original interpretation consuming one retained common bound tree. -/
abbrev Bounded {arity : Nat} {environment : Fin arity → Annotated} {bindings : List (Binding environment)}
    {expression : Expr arity} {annotation : Annotated} (construction : Construction environment expression annotation)
    (geometry : construction.Geometry bindings) {leafBalls : Leaf arity → Ball}
    (bounds : Expr.Bounds leafBalls expression) :=
  { value : construction.Enclosed bindings //
      value = construction.enclose bindings geometry ∧ value.result.ball = bounds.ball }

namespace Bounded

/-- The cached interpretation is the complete original result at its same actual input geometry. -/
theorem computed {arity : Nat} {environment : Fin arity → Annotated} {bindings : List (Binding environment)}
    {expression : Expr arity} {annotation : Annotated} {construction : Construction environment expression annotation}
    {geometry : construction.Geometry bindings} {leafBalls : Leaf arity → Ball}
    {bounds : Expr.Bounds leafBalls expression} (bounded : Bounded construction geometry bounds) :
    bounded.val = construction.enclose bindings geometry := bounded.property.1

/-- The actual cached output consumes the complete node ball retained by the same bound tree. -/
theorem ball_eq {arity : Nat} {environment : Fin arity → Annotated} {bindings : List (Binding environment)}
    {expression : Expr arity} {annotation : Annotated} {construction : Construction environment expression annotation}
    {geometry : construction.Geometry bindings} {leafBalls : Leaf arity → Ball}
    {bounds : Expr.Bounds leafBalls expression} (bounded : Bounded construction geometry bounds) :
    bounded.val.result.ball = bounds.ball := bounded.property.2

end Bounded

/-- Interpret actual original children using only retained node balls and the supplied-ball arithmetic constructors.

The returned value retains the original numerical programs, construction and
used bounded leaf receipts. Its whole-record equality authenticates the existing
interpretation; no original interpreter or common-ball computation is executed
inside this procedure. Shared nodes interpret their original child once.
-/
def encloseFromBounds {arity : Nat} {environment : Fin arity → Annotated}
    (bindings : List (Binding environment)) :
    {expression : Expr arity} → {annotation : Annotated} →
    (construction : Construction environment expression annotation) →
    (geometry : construction.Geometry bindings) → {leafBalls : Leaf arity → Ball} →
    (bounds : Expr.Bounds leafBalls expression) →
    Geometry.Balls (construction := construction) geometry leafBalls → Bounded construction geometry bounds
  | _, _, .atom index annotation original, geometry, _, .atom _ _ same, agreement =>
      let value := ⟨geometry.enclose annotation original, Interpretation.atom index annotation original geometry⟩
      ⟨value, rfl, (geometry.enclose_ball annotation original).trans (agreement.trans same.symm)⟩
  | _, _, .rational value annotation original, _, _, .rational _ ball same, _ =>
      let output := Enclosure.exactFromBall value ball same
      let result := output.cast (congrArg Annotated.channel original).symm
      let resultEq := congrArg (fun enclosing => enclosing.cast (congrArg Annotated.channel original).symm)
        (Enclosure.exactFromBall_eq value ball same)
      let cache := Interpretation.rational value annotation original
      let actual := Enclosed.withResult cache result resultEq
      ⟨actual, Enclosed.withResult_eq cache result resultEq,
        (output.cast_ball _).trans (Enclosure.exactFromBall_ball value ball same)⟩
  | _, _, .root parameter sheet annotation original, geometry, _, .root _ _ _ same, agreement =>
      let value := ⟨geometry.enclose annotation original,
        Interpretation.root parameter sheet annotation original geometry⟩
      ⟨value, rfl, (geometry.enclose_ball annotation original).trans (agreement.trans same.symm)⟩
  | _, _, .neg child construction original, geometry, _, .neg childBounds ball same, agreement =>
      let childValue := encloseFromBounds bindings construction geometry childBounds agreement
      let childResult := childValue.val.result
      have childBall := childValue.ball_eq.trans childBounds.ball_eq
      let formula := same.trans (congrArg Ball.neg childBall.symm)
      let output := childResult.negFromBall ball formula
      let result := output.cast (congrArg Annotated.channel original).symm
      let resultEq := congrArg (fun enclosing => enclosing.cast (congrArg Annotated.channel original).symm)
        (Enclosure.negFromBall_eq childResult ball formula)
      let cache := Interpretation.neg child construction original childResult childValue.val.cache
      let actual := Enclosed.withResult cache result resultEq
      have computed := (Enclosed.withResult_eq cache result resultEq).trans
        (congrArg (fun enclosed : construction.Enclosed bindings =>
          (⟨enclosed.result.neg.cast (congrArg Annotated.channel original).symm,
            Interpretation.neg child construction original enclosed.result enclosed.cache⟩ :
              (Construction.neg child construction original).Enclosed bindings)) childValue.computed)
      ⟨actual, computed, (output.cast_ball _).trans (Enclosure.negFromBall_ball childResult ball formula)⟩
  | _, _, .add different first second left right inferAlgebraic original, geometry, _,
      .add firstBounds secondBounds ball same, agreement =>
      let firstValue := encloseFromBounds bindings left geometry.1 firstBounds agreement.1
      let secondValue := encloseFromBounds bindings right geometry.2 secondBounds agreement.2
      let firstResult := firstValue.val.result
      let secondResult := secondValue.val.result
      have firstBall := firstValue.ball_eq.trans firstBounds.ball_eq
      have secondBall := secondValue.ball_eq.trans secondBounds.ball_eq
      let formula := same.trans (congrArg₂ Ball.add firstBall.symm secondBall.symm)
      let output := firstResult.addFromBall secondResult ball formula
      let result := output.cast (congrArg Annotated.channel original).symm
      let resultEq := congrArg (fun enclosing => enclosing.cast (congrArg Annotated.channel original).symm)
        (Enclosure.addFromBall_eq firstResult secondResult ball formula)
      let cache := Interpretation.add different first second left right inferAlgebraic original
        firstResult secondResult firstValue.val.cache secondValue.val.cache
      let actual := Enclosed.withResult cache result resultEq
      have computed := (Enclosed.withResult_eq cache result resultEq).trans
        (congrArg₂ (fun firstValue : left.Enclosed bindings => fun secondValue : right.Enclosed bindings =>
          (⟨(firstValue.result.add secondValue.result).cast (congrArg Annotated.channel original).symm,
            Interpretation.add different first second left right inferAlgebraic original
              firstValue.result secondValue.result firstValue.cache secondValue.cache⟩ :
                (Construction.add different first second left right inferAlgebraic original).Enclosed bindings))
          firstValue.computed secondValue.computed)
      ⟨actual, computed,
        (output.cast_ball _).trans (Enclosure.addFromBall_ball firstResult secondResult ball formula)⟩
  | _, _, .addNeg child construction original, geometry, _,
      .add childBounds (.neg _ negativeBall negativeSame) ball same, agreement =>
      let childValue := encloseFromBounds bindings construction geometry childBounds agreement
      let childResult := childValue.val.result
      have childBall := childValue.ball_eq.trans childBounds.ball_eq
      let negativeFormula := negativeSame.trans (congrArg Ball.neg childBall.symm)
      let negative := childResult.negFromBall negativeBall negativeFormula
      have negativeBallEq := (Enclosure.negFromBall_ball childResult negativeBall negativeFormula).trans negativeSame
      let formula := same.trans (congrArg₂ Ball.add childBall.symm negativeBallEq.symm)
      let output := childResult.addFromBall negative ball formula
      let result := output.cast (congrArg Annotated.channel original).symm
      let negativeEq := Enclosure.negFromBall_eq childResult negativeBall negativeFormula
      let outputEq := (Enclosure.addFromBall_eq childResult negative ball formula).trans
        (congrArg (fun negative => childResult.add negative) negativeEq)
      let resultEq := congrArg (fun enclosing => enclosing.cast (congrArg Annotated.channel original).symm) outputEq
      let cache := Interpretation.addNeg child construction original childResult childValue.val.cache
      let actual := Enclosed.withResult cache result resultEq
      have computed := (Enclosed.withResult_eq cache result resultEq).trans
        (congrArg (fun enclosed : construction.Enclosed bindings =>
          (⟨(enclosed.result.add enclosed.result.neg).cast (congrArg Annotated.channel original).symm,
            Interpretation.addNeg child construction original enclosed.result enclosed.cache⟩ :
              (Construction.addNeg child construction original).Enclosed bindings)) childValue.computed)
      ⟨actual, computed,
        (output.cast_ball _).trans (Enclosure.addFromBall_ball childResult negative ball formula)⟩
  | _, _, .sub different first second left right inferAlgebraic original, geometry, _,
      .sub firstBounds secondBounds ball same, agreement =>
      let firstValue := encloseFromBounds bindings left geometry.1 firstBounds agreement.1
      let secondValue := encloseFromBounds bindings right geometry.2 secondBounds agreement.2
      let firstResult := firstValue.val.result
      let secondResult := secondValue.val.result
      have firstBall := firstValue.ball_eq.trans firstBounds.ball_eq
      have secondBall := secondValue.ball_eq.trans secondBounds.ball_eq
      let formula := same.trans (congrArg₂ Ball.sub firstBall.symm secondBall.symm)
      let output := firstResult.subFromBall secondResult ball formula
      let result := output.cast (congrArg Annotated.channel original).symm
      let resultEq := congrArg (fun enclosing => enclosing.cast (congrArg Annotated.channel original).symm)
        (Enclosure.subFromBall_eq firstResult secondResult ball formula)
      let cache := Interpretation.sub different first second left right inferAlgebraic original
        firstResult secondResult firstValue.val.cache secondValue.val.cache
      let actual := Enclosed.withResult cache result resultEq
      have computed := (Enclosed.withResult_eq cache result resultEq).trans
        (congrArg₂ (fun firstValue : left.Enclosed bindings => fun secondValue : right.Enclosed bindings =>
          (⟨(firstValue.result.sub secondValue.result).cast (congrArg Annotated.channel original).symm,
            Interpretation.sub different first second left right inferAlgebraic original
              firstValue.result secondValue.result firstValue.cache secondValue.cache⟩ :
                (Construction.sub different first second left right inferAlgebraic original).Enclosed bindings))
          firstValue.computed secondValue.computed)
      ⟨actual, computed,
        (output.cast_ball _).trans (Enclosure.subFromBall_ball firstResult secondResult ball formula)⟩
  | _, _, .subSelf child construction original, geometry, _, .sub childBounds _ ball same, agreement =>
      let childValue := encloseFromBounds bindings construction geometry childBounds agreement
      let childResult := childValue.val.result
      have childBall := childValue.ball_eq.trans childBounds.ball_eq
      let formula := same.trans (congrArg₂ Ball.sub childBall.symm childBall.symm)
      let output := childResult.subFromBall childResult ball formula
      let result := output.cast (congrArg Annotated.channel original).symm
      let resultEq := congrArg (fun enclosing => enclosing.cast (congrArg Annotated.channel original).symm)
        (Enclosure.subFromBall_eq childResult childResult ball formula)
      let cache := Interpretation.subSelf child construction original childResult childValue.val.cache
      let actual := Enclosed.withResult cache result resultEq
      have computed := (Enclosed.withResult_eq cache result resultEq).trans
        (congrArg (fun enclosed : construction.Enclosed bindings =>
          (⟨(enclosed.result.sub enclosed.result).cast (congrArg Annotated.channel original).symm,
            Interpretation.subSelf child construction original enclosed.result enclosed.cache⟩ :
              (Construction.subSelf child construction original).Enclosed bindings)) childValue.computed)
      ⟨actual, computed,
        (output.cast_ball _).trans (Enclosure.subFromBall_ball childResult childResult ball formula)⟩
  | _, _, .mul different first second left right inferAlgebraic original, geometry, _,
      .mul firstBounds secondBounds ball same, agreement =>
      let firstValue := encloseFromBounds bindings left geometry.1 firstBounds agreement.1
      let secondValue := encloseFromBounds bindings right geometry.2 secondBounds agreement.2
      let firstResult := firstValue.val.result
      let secondResult := secondValue.val.result
      have firstBall := firstValue.ball_eq.trans firstBounds.ball_eq
      have secondBall := secondValue.ball_eq.trans secondBounds.ball_eq
      let formula := same.trans (congrArg₂ Ball.mul firstBall.symm secondBall.symm)
      let output := firstResult.mulFromBall secondResult ball formula
      let result := output.cast (congrArg Annotated.channel original).symm
      let resultEq := congrArg (fun enclosing => enclosing.cast (congrArg Annotated.channel original).symm)
        (Enclosure.mulFromBall_eq firstResult secondResult ball formula)
      let cache := Interpretation.mul different first second left right inferAlgebraic original
        firstResult secondResult firstValue.val.cache secondValue.val.cache
      let actual := Enclosed.withResult cache result resultEq
      have computed := (Enclosed.withResult_eq cache result resultEq).trans
        (congrArg₂ (fun firstValue : left.Enclosed bindings => fun secondValue : right.Enclosed bindings =>
          (⟨(firstValue.result.mul secondValue.result).cast (congrArg Annotated.channel original).symm,
            Interpretation.mul different first second left right inferAlgebraic original
              firstValue.result secondValue.result firstValue.cache secondValue.cache⟩ :
                (Construction.mul different first second left right inferAlgebraic original).Enclosed bindings))
          firstValue.computed secondValue.computed)
      ⟨actual, computed,
        (output.cast_ball _).trans (Enclosure.mulFromBall_ball firstResult secondResult ball formula)⟩
  | _, _, .square child construction inferAlgebraic original, geometry, _, .mul childBounds _ ball same, agreement =>
      let childValue := encloseFromBounds bindings construction geometry childBounds agreement
      let childResult := childValue.val.result
      have childBall := childValue.ball_eq.trans childBounds.ball_eq
      let formula := same.trans (congrArg₂ Ball.mul childBall.symm childBall.symm)
      let output := childResult.mulFromBall childResult ball formula
      let result := output.cast (congrArg Annotated.channel original).symm
      let resultEq := congrArg (fun enclosing => enclosing.cast (congrArg Annotated.channel original).symm)
        (Enclosure.mulFromBall_eq childResult childResult ball formula)
      let cache := Interpretation.square child construction inferAlgebraic original childResult childValue.val.cache
      let actual := Enclosed.withResult cache result resultEq
      have computed := (Enclosed.withResult_eq cache result resultEq).trans
        (congrArg (fun enclosed : construction.Enclosed bindings =>
          (⟨(enclosed.result.mul enclosed.result).cast (congrArg Annotated.channel original).symm,
            Interpretation.square child construction inferAlgebraic original enclosed.result enclosed.cache⟩ :
              (Construction.square child construction inferAlgebraic original).Enclosed bindings)) childValue.computed)
      ⟨actual, computed,
        (output.cast_ball _).trans (Enclosure.mulFromBall_ball childResult childResult ball formula)⟩

end Construction

namespace Compiled

/-- Geometric input receipts for exactly the used leaves in this compilation's original binding table. -/
abbrev Geometry {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (compiled : Compiled environment expression) : Type :=
  compiled.construction.Geometry compiled.bindings

set_option genInjectivity false in
/-- A spatial interpretation retaining the complete original compiled expression and its child caches. -/
structure Enclosed {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (bindings : List (Binding environment)) (compiled : Compiled environment expression) where
  /-- The complete actual original compiled value, with its annotations and construction. -/
  original : Compiled environment expression
  /-- The retained compiled value is exactly the input to this interpretation. -/
  original_eq : original = compiled
  /-- The complete actual input binding table retains its original occurrence annotations and bounds. -/
  table : List (Binding environment)
  /-- The retained table is exactly the original input of the bounded geometric receipts. -/
  table_eq : table = bindings
  /-- Cached geometry follows that same input's original construction and output channel. -/
  enclosed : compiled.construction.Enclosed bindings

constructive_injectivity Enclosed

namespace Enclosed

/-- Read the cached formal geometric output without reinterpreting any original child. -/
@[expose] def result {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    {bindings : List (Binding environment)} {compiled : Compiled environment expression}
    (enclosed : compiled.Enclosed bindings) : Enclosure compiled.annotation.channel := enclosed.enclosed.result

/-- The cached formal geometric output realizes the original expression's exact evaluator channel. -/
def denoteEquivalent {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    {bindings : List (Binding environment)} {compiled : Compiled environment expression}
    (enclosed : compiled.Enclosed bindings) :
    Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent (expression.denote environment).name
      enclosed.enclosed.result.source.toApproximation.toNamed := by
  rewrite [← compiled.channel_eq]
  exact enclosed.enclosed.result.equivalent

end Enclosed

/-- Enclose an actual retained compilation using geometry for exactly its used leaf occurrences. -/
@[expose] def enclose {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (compiled : Compiled environment expression) (bindings : List (Binding environment))
    (geometry : compiled.construction.Geometry bindings) : compiled.Enclosed bindings :=
  ⟨compiled, rfl, bindings, rfl, compiled.construction.enclose bindings geometry⟩

/-- Enclose a retained compilation with receipts indexed by its exact original binding spine. -/
@[expose] def encloseBindings {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (compiled : Compiled environment expression) (geometry : compiled.Geometry) :
    compiled.Enclosed compiled.bindings := compiled.enclose compiled.bindings geometry

/-- An actual retained compilation has the ball computed by its original syntax and authenticated used leaves. -/
theorem enclose_ball {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (compiled : Compiled environment expression) (bindings : List (Binding environment))
    (geometry : compiled.construction.Geometry bindings) (leafBalls : Leaf arity → Ball)
    (agreement : Construction.Geometry.Balls (construction := compiled.construction) geometry leafBalls) :
    (compiled.enclose bindings geometry).result.ball = expression.ball leafBalls :=
  compiled.construction.enclose_ball bindings geometry leafBalls agreement

/-- The original binding-spine interpretation has exactly the syntax-computed common ball. -/
theorem encloseBindings_ball {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (compiled : Compiled environment expression) (geometry : compiled.Geometry) (leafBalls : Leaf arity → Ball)
    (agreement : Construction.Geometry.Balls (construction := compiled.construction) geometry leafBalls) :
    (compiled.encloseBindings geometry).result.ball = expression.ball leafBalls :=
  compiled.enclose_ball compiled.bindings geometry leafBalls agreement

/-- A certified existing compiled interpretation consuming its retained original bound tree. -/
abbrev Bounded {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (compiled : Compiled environment expression) (bindings : List (Binding environment))
    (geometry : compiled.construction.Geometry bindings) {leafBalls : Leaf arity → Ball}
    (bounds : Expr.Bounds leafBalls expression) :=
  { value : compiled.Enclosed bindings //
      value = compiled.enclose bindings geometry ∧ value.result.ball = bounds.ball }

namespace Bounded

/-- The cached result is the complete original compiled interpretation and input binding spine. -/
theorem computed {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    {compiled : Compiled environment expression} {bindings : List (Binding environment)}
    {geometry : compiled.construction.Geometry bindings} {leafBalls : Leaf arity → Ball}
    {bounds : Expr.Bounds leafBalls expression} (bounded : Bounded compiled bindings geometry bounds) :
    bounded.val = compiled.enclose bindings geometry := bounded.property.1

/-- The retained compiled output has the same complete ball as its stored bound tree. -/
theorem ball_eq {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    {compiled : Compiled environment expression} {bindings : List (Binding environment)}
    {geometry : compiled.construction.Geometry bindings} {leafBalls : Leaf arity → Ball}
    {bounds : Expr.Bounds leafBalls expression} (bounded : Bounded compiled bindings geometry bounds) :
    bounded.val.result.ball = bounds.ball := bounded.property.2

end Bounded

/-- Interpret the same original compilation using its supplied per-node bound cache directly.

The original compiled value and actual binding spine remain in the existing
result record. Bounds are read from the supplied tree; its producer and the
original common-ball arithmetic do not run inside this procedure.
-/
def encloseFromBounds {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (compiled : Compiled environment expression) (bindings : List (Binding environment))
    (geometry : compiled.construction.Geometry bindings) {leafBalls : Leaf arity → Ball}
    (bounds : Expr.Bounds leafBalls expression)
    (agreement : Construction.Geometry.Balls (construction := compiled.construction) geometry leafBalls) :
    Bounded compiled bindings geometry bounds :=
  let enclosed := compiled.construction.encloseFromBounds bindings geometry bounds agreement
  let value := ⟨compiled, rfl, bindings, rfl, enclosed.val⟩
  have computed := congrArg (fun result : compiled.construction.Enclosed bindings =>
    (⟨compiled, rfl, bindings, rfl, result⟩ : compiled.Enclosed bindings)) enclosed.computed
  ⟨value, computed, by
    change enclosed.val.result.ball = bounds.ball
    exact enclosed.ball_eq⟩

/-- Consume precomputed node bounds at the same original compilation's own binding spine. -/
def encloseBindingsFromBounds {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (compiled : Compiled environment expression) (geometry : compiled.Geometry) {leafBalls : Leaf arity → Ball}
    (bounds : Expr.Bounds leafBalls expression)
    (agreement : Construction.Geometry.Balls (construction := compiled.construction) geometry leafBalls) :
    Bounded compiled compiled.bindings geometry bounds :=
  compiled.encloseFromBounds compiled.bindings geometry bounds agreement

/-- The supplied bounds retain the complete original interpretation on its own binding spine. -/
theorem encloseBindingsFromBounds_computed {arity : Nat} {environment : Fin arity → Annotated}
    {expression : Expr arity} (compiled : Compiled environment expression) (geometry : compiled.Geometry)
    {leafBalls : Leaf arity → Ball} (bounds : Expr.Bounds leafBalls expression)
    (agreement : Construction.Geometry.Balls (construction := compiled.construction) geometry leafBalls) :
    (compiled.encloseBindingsFromBounds geometry bounds agreement).val = compiled.encloseBindings geometry :=
  (compiled.encloseBindingsFromBounds geometry bounds agreement).computed

/-- A complete finite binding table supplies the exact used geometric inputs of a retained compilation. -/
@[expose] def encloseOfTable {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (compiled : Compiled environment expression)
    (entries : (index : Fin compiled.bindings.length) → Enclosure (Binding.channels compiled.bindings index)) :
    compiled.Enclosed compiled.bindings :=
  compiled.enclose compiled.bindings
    (Construction.Geometry.ofTable compiled.bindings entries compiled.construction
      compiled.construction.supported_bindings)

end Compiled

end Purelib.Approximation.Gaussian.Acquisition.Expression.Basic

end
