module

public import Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Denominator
public import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Geometric.Bounds.Evaluation
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Box
import Purelib.Riemann.RootContinuation.CoherentRoot.Polynomial
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Overlap
import Purelib.RootIsolation.Owner.Bridge.Basic
import Purelib.Approximation.Gaussian.Acquisition.Annotated.Basic
import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Basic
import Purelib.Approximation.Gaussian.Provenance.Algebraic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
meta import Purelib.Elab.ConstructiveInjectivity

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.InteriorStep.Expression

open Purelib.RootIsolation.Progressive.Chamber.Frame (ChamberFrame)
open Purelib.RootIsolation.Progressive.Chamber.Overlap (ChamberOverlap)
open Purelib.Approximation.Gaussian.Acquisition.Expression
open Purelib.Approximation.Gaussian.Geometric (Enclosure)
open Purelib.Approximation.Gaussian.Enclosure (Ball)
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Approximation.Gaussian
open Denominator (Point)
open Checked.Geometric

variable {start middle : ChamberFrame} {step : ChamberOverlap start middle} {index : start.Index}
    {source : Root start index} {target : Root middle (step.matching.forward index)}

/-- A common leaf table uses the actual retained bridge ball for its original nonlinear root atom.

Displayed square-root leaves keep their independently supplied common balls.
Their actual used-leaf geometry remains a separate authenticated obligation.
-/
@[expose] def leafBalls (rootBall : Ball) (displayed : Canonical → Fin 2 → Ball) : Basic.Leaf 1 → Ball
  | .atom _ => rootBall
  | .root parameter sheet => displayed parameter sheet

set_option genInjectivity false in
/-- The once computed expression programme on one exact original prepared path piece.

The original root corridor determines its cached root ball. Arithmetic bounds
and inverse tests are computed from that ball and retained displayed-leaf
balls before any actual parameter input is specialized.
-/
structure Program (piece : InteriorStep step index source target) (expression : Checked.Expr 1) where
  /-- The complete original piece retains its source, target, bridge and genuine handoffs. -/
  original : InteriorStep step index source target
  /-- The retained piece is the exact original supplied parent. -/
  original_eq : original = piece
  /-- The actual corridor ball is computed once from the same original bridge box. -/
  rootBall : { ball : Ball // ball = Ball.ofBox piece.bridge.val.box }
  /-- The retained common balls of separately displayed square-root leaves. -/
  displayed : Canonical → Fin 2 → Ball
  /-- The actual finite arithmetic and ordered domain inspection. -/
  result : Bounds.Outcome (leafBalls rootBall.val displayed) expression
  /-- This result is the original structural procedure on the same retained input balls. -/
  result_eq : result = Bounds.inspect (leafBalls rootBall.val displayed) expression

constructive_injectivity Program

/-- Compute the original corridor ball and structural programme once without evaluating a parameter root. -/
@[expose] def inspect (piece : InteriorStep step index source target) (expression : Checked.Expr 1)
    (displayed : Canonical → Fin 2 → Ball) : Program piece expression :=
  let rootBall := Ball.ofBox piece.bridge.val.box
  let result := Bounds.inspect (leafBalls rootBall displayed) expression
  ⟨piece, rfl, ⟨rootBall, rfl⟩, displayed, result, rfl⟩

namespace Program

variable {piece : InteriorStep step index source target} {expression : Checked.Expr 1}

/-- Retain an actual inspected corridor ball and its complete original bound result.

The supplied result includes its exact structural-procedure readback. No
inspection, root acquisition or parameter specialization is repeated.
-/
@[expose] def ofResult (piece : InteriorStep step index source target)
    (rootBall : { ball : Ball // ball = Ball.ofBox piece.bridge.val.box })
    (displayed : Canonical → Fin 2 → Ball)
    (result : Bounds.Outcome (leafBalls rootBall.val displayed) expression)
    (computed : result = Bounds.inspect (leafBalls rootBall.val displayed) expression) :
    Program piece expression :=
  ⟨piece, rfl, rootBall, displayed, result, computed⟩

/-- The retained result constructor is the complete original structural programme. -/
theorem ofResult_eq (piece : InteriorStep step index source target)
    (rootBall : { ball : Ball // ball = Ball.ofBox piece.bridge.val.box })
    (displayed : Canonical → Fin 2 → Ball)
    (result : Bounds.Outcome (leafBalls rootBall.val displayed) expression)
    (computed : result = Bounds.inspect (leafBalls rootBall.val displayed) expression) :
    ofResult piece rootBall displayed result computed = inspect piece expression displayed := by
  rcases rootBall with ⟨ball, sameBall⟩
  cases sameBall
  cases computed
  rfl

/-- Read the same retained common leaf table without repeating corridor-ball construction. -/
abbrev balls (program : Program piece expression) := leafBalls program.rootBall.val program.displayed

/-- Enclose the actual original point's root samples in the programme's retained corridor ball. -/
def encloseRoot (program : Program piece expression) {time : Rational} {inside : Inside time}
    (point : Point piece time inside) : Enclosure (point.environment Denominator.Point.atomIndex).channel :=
  let geometric := point.root.geometric
  { source := geometric
    equivalent := point.root.geometric_agreesWith geometric (fun _ => rfl)
    ball := program.rootBall.val
    contains := fun stage => program.rootBall.property.symm ▸ Ball.contains_ofBox (point.sample_inside stage) }

/-- The original root enclosure consumes the same retained common atom ball. -/
private theorem encloseRoot_ball_readback (program : Program piece expression)
    {time : Rational} {inside : Inside time} (point : Point piece time inside) :
    (program.encloseRoot point).ball = program.balls (.atom Denominator.Point.atomIndex) := rfl

/-- Read the exact stored common atom ball of the original point enclosure. -/
theorem encloseRoot_ball (program : Program piece expression) {time : Rational} {inside : Inside time}
    (point : Point piece time inside) :
    (program.encloseRoot point).ball = program.balls (.atom Denominator.Point.atomIndex) :=
  encloseRoot_ball_readback program point

/-- The retained root enclosure uses the exact original root's geometric sample programme. -/
private theorem encloseRoot_source_readback (program : Program piece expression)
    {time : Rational} {inside : Inside time} (point : Point piece time inside) :
    (program.encloseRoot point).source = point.root.geometric := rfl

/-- Read the complete unchanged original root sample programme from its retained common enclosure. -/
theorem encloseRoot_source (program : Program piece expression) {time : Rational} {inside : Inside time}
    (point : Point piece time inside) : (program.encloseRoot point).source = point.root.geometric :=
  encloseRoot_source_readback program point

set_option genInjectivity false in
/-- One genuine same-parameter original point, admission and optional used-leaf geometry.

Only actual used geometry is an obligation. No successful inverse attempt,
comparison result or desired final enclosure is supplied by this receipt.
-/
structure Input (program : Program piece expression) (time : Rational) (inside : Inside time) where
  /-- The complete original point/root/input/track cache at this same rational parameter. -/
  point : Point piece time inside
  /-- The actual original admission tree uses that point's unchanged original root annotation. -/
  admitted : Checked.Admitted point.environment expression
  /-- Genuine geometry is optional and concerns the original used bounded leaves only. -/
  offered : Option (Bounds.Inputs program.balls admitted)

constructive_injectivity Input

/-- Retain a genuine parameter input and its exact original optional geometry without evaluation. -/
@[expose] def input (program : Program piece expression) {time : Rational} {inside : Inside time}
    (point : Point piece time inside) (admitted : Checked.Admitted point.environment expression)
    (offered : Option (Bounds.Inputs program.balls admitted)) : program.Input time inside :=
  ⟨point, admitted, offered⟩

set_option genInjectivity false in
/-- A parameter specialization physically retaining both complete original parents.

The original programme contains every structural bound and unresolved domain
occurrence. Its actual original point/admission receipt remains alongside the
original numerical success, exact-zero or fillable missing-geometry outcome.
-/
structure Assessment (program : Program piece expression) (time : Rational) (inside : Inside time) where
  /-- The complete original once-computed programme is physically retained. -/
  bounds : Program piece expression
  /-- The retained programme is exactly this original parent. -/
  bounds_eq : bounds = program
  /-- The same original point and admission are physically retained. -/
  input : bounds.Input time inside
  /-- The actual original specialization or fillable geometry request. -/
  result : Bounds.Attempt bounds.result input.admitted
  /-- This is the exact original finite preparation on the same stored programme and offered geometry. -/
  computed : result = bounds.result.prepare input.admitted input.offered

constructive_injectivity Assessment

/-- Specialize the retained original programme without inspecting it or reconstructing any common ball. -/
def assess (program : Program piece expression) {time : Rational} {inside : Inside time}
    (input : program.Input time inside) : program.Assessment time inside :=
  let result := program.result.prepare input.admitted input.offered
  ⟨program, rfl, input, result, rfl⟩

/-- Read the same physically retained point receipt at its authenticated original programme index. -/
@[expose] def Assessment.originalInput {program : Program piece expression}
    {time : Rational} {inside : Inside time} (assessment : program.Assessment time inside) :
    program.Input time inside :=
  Eq.ndrec (motive := fun bounds => bounds.Input time inside) assessment.input assessment.bounds_eq

/-- Specialization retains the same complete programme and its exact original parameter input. -/
private theorem assess_input_readback (program : Program piece expression)
    {time : Rational} {inside : Inside time} (input : program.Input time inside) :
    (program.assess input).originalInput = input := rfl

/-- Read the complete actual original point/admission/geometry receipt from its parameter assessment. -/
theorem assess_input (program : Program piece expression) {time : Rational} {inside : Inside time}
    (input : program.Input time inside) : (program.assess input).originalInput = input :=
  assess_input_readback program input

/-- The assessment retains the exact same supplied whole programme parent. -/
theorem assess_bounds (program : Program piece expression) {time : Rational} {inside : Inside time}
    (input : program.Input time inside) : (program.assess input).bounds = program :=
  (program.assess input).bounds_eq

/-- Every actual positive realization lies in the retained ball at each rational path parameter and sample index. -/
theorem contains (program : Program piece expression) {common : Bounds.Common program.balls expression}
    (_positive : program.result = .prepared common) {time : Rational} {inside : Inside time}
    (input : program.Input time inside) (geometry : Bounds.Inputs program.balls input.admitted) (stage : Nat) :
    common.ball.Contains ((common.realize input.admitted geometry).value.enclosing.source.sample stage) :=
  common.contains input.admitted geometry stage

end Program

/-- Admit the actual original root atom of one retained parameter point without re-isolation. -/
@[expose] def rootAdmitted {piece : InteriorStep step index source target} {time : Rational} {inside : Inside time}
    (point : Point piece time inside) : Checked.Admitted point.environment (.atom Denominator.Point.atomIndex) :=
  Checked.Admitted.atom point.environment Denominator.Point.atomIndex (Algebraic.Sidecar.ofRoot point.sidecar)

/-- Supply genuine geometry for an actual original atom under any retained surrounding expression. -/
@[expose] def Program.rootGeometry {piece : InteriorStep step index source target}
    {expression : Checked.Expr 1} {time : Rational} {inside : Inside time}
    (program : Program piece expression) (point : Point piece time inside) :
    Bounds.Inputs program.balls (rootAdmitted point) :=
  Bounds.Inputs.atom program.balls point.environment Denominator.Point.atomIndex
    (Algebraic.Sidecar.ofRoot point.sidecar) (program.encloseRoot point) (program.encloseRoot_ball point)

/-- Supply genuine geometry for the original root atom from its retained original corridor box. -/
@[expose] def rootInput {piece : InteriorStep step index source target} {time : Rational} {inside : Inside time}
    (program : Program piece (.atom Denominator.Point.atomIndex)) (point : Point piece time inside) :
    program.Input time inside :=
  program.input point (rootAdmitted point) (some (program.rootGeometry point))

/-- Supply the ordered constant-one-plus-original-root admission and its actual common-box geometry. -/
@[expose] def oneAddRootInput {piece : InteriorStep step index source target} {time : Rational} {inside : Inside time}
    (program : Program piece (.add (Checked.Expr.rational 1) (Checked.Expr.atom Denominator.Point.atomIndex)))
    (point : Point piece time inside) : program.Input time inside :=
  let first := Checked.Admitted.rational point.environment 1
  let second := rootAdmitted point
  let geometry := (Bounds.Inputs.rational program.balls point.environment 1, program.rootGeometry point)
  program.input point (first.add second) (some geometry)

/-- Specialize the original root reciprocal using genuine geometry derived from the retained path box. -/
@[expose] def rootInverseInput {piece : InteriorStep step index source target}
    {time : Rational} {inside : Inside time}
    (program : Program piece (.inverse (Checked.Expr.atom Denominator.Point.atomIndex)))
    (point : Point piece time inside) :
    program.Input time inside :=
  program.input point (.inverse (rootAdmitted point)) (some (program.rootGeometry point))

/-- Supply the ordered one-plus-root reciprocal on the same original atom and common path box. -/
@[expose] def oneAddRootInverseInput {piece : InteriorStep step index source target}
    {time : Rational} {inside : Inside time}
    (program : Program piece
      (.inverse (.add (Checked.Expr.rational 1) (Checked.Expr.atom Denominator.Point.atomIndex))))
    (point : Point piece time inside) : program.Input time inside :=
  let first := Checked.Admitted.rational point.environment 1
  let second := rootAdmitted point
  let geometry := (Bounds.Inputs.rational program.balls point.environment 1, program.rootGeometry point)
  program.input point (.inverse (first.add second)) (some geometry)

namespace Program

set_option genInjectivity false in
/-- Genuine original parameter inputs for one retained common programme.

Every point is indexed by the same original prepared interior piece and its
same rational parameter. Its actual used geometry may remain honestly absent;
specialization retains that fillable request beside the original bound result.
-/
structure Family {piece : InteriorStep step index source target} {expression : Checked.Expr 1}
    (program : Program piece expression) where
  /-- The actual original programme is retained beside its same-parameter source inputs. -/
  original : Program piece expression
  /-- The retained programme is the exact supplied original parent. -/
  original_eq : original = program
  /-- Actual original point/admission/geometry receipts at every rational parameter of the piece. -/
  inputs : (time : Rational) → (inside : Inside time) → original.Input time inside

constructive_injectivity Family

/-- Retain genuine same-parameter source inputs without asserting successful arithmetic or clearance. -/
@[expose] def family {piece : InteriorStep step index source target} {expression : Checked.Expr 1}
    (program : Program piece expression)
    (inputs : (time : Rational) → (inside : Inside time) → program.Input time inside) : Family program :=
  ⟨program, rfl, inputs⟩

/-- Specialize one actual parameter while consuming the same stored programme and original point receipt. -/
def Family.at {piece : InteriorStep step index source target} {expression : Checked.Expr 1}
    {program : Program piece expression} (family : Family program) (time : Rational) (inside : Inside time) :
    family.original.Assessment time inside :=
  let input := family.inputs time inside
  family.original.assess input

/-- The family parameter factory consumes the exact same retained programme and original input receipt. -/
private theorem Family.at_readback {piece : InteriorStep step index source target} {expression : Checked.Expr 1}
    {program : Program piece expression} (family : Family program) (time : Rational) (inside : Inside time) :
    family.at time inside = family.original.assess (family.inputs time inside) := rfl

/-- Identify the complete actual parameter assessment with the original retained programme factory. -/
theorem Family.at_eq_assess {piece : InteriorStep step index source target} {expression : Checked.Expr 1}
    {program : Program piece expression} (family : Family program) (time : Rational) (inside : Inside time) :
    family.at time inside = family.original.assess (family.inputs time inside) :=
  family.at_readback time inside

/-- Every genuine parameter realization uses the same computed positive programme at each sample index. -/
theorem Family.contains {piece : InteriorStep step index source target} {expression : Checked.Expr 1}
    {program : Program piece expression} (family : Family program)
    {common : Bounds.Common family.original.balls expression}
    (positive : family.original.result = .prepared common) (time : Rational) (inside : Inside time)
    (geometry : Bounds.Inputs family.original.balls (family.inputs time inside).admitted) (stage : Nat) :
    common.ball.Contains ((common.realize (family.inputs time inside).admitted geometry).value.enclosing.source.sample
      stage) := family.original.contains positive (family.inputs time inside) geometry stage

end Program

/-- Build the genuine root-reciprocal parameter family from the exact original prepared root caches. -/
@[expose] def rootInverseFamily {piece : InteriorStep step index source target}
    (program : Program piece (.inverse (Checked.Expr.atom Denominator.Point.atomIndex))) : Program.Family program :=
  program.family (fun time inside => rootInverseInput program (Denominator.pointAt piece time inside))

/-- Build the ordered one-plus-root reciprocal family from those same original same-parameter caches. -/
@[expose] def oneAddRootInverseFamily {piece : InteriorStep step index source target}
    (program : Program piece
      (.inverse (.add (Checked.Expr.rational 1) (Checked.Expr.atom Denominator.Point.atomIndex)))) :
    Program.Family program :=
  program.family (fun time inside => oneAddRootInverseInput program (Denominator.pointAt piece time inside))

end Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.InteriorStep.Expression
end
