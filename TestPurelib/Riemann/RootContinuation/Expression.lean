module

import Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Expression.Trace
import Purelib.Riemann.RootContinuation.CoherentRoot.Polynomial
import Purelib.RootIsolation.Track.Basic
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Overlap
import Purelib.RootIsolation.Progressive.Chamber.Path.Basic
import Purelib.Data.Rat.Fraction

namespace TestPurelib.Riemann.RootContinuation.Expression

open Purelib.RootIsolation.Progressive.Chamber.Frame (ChamberFrame)
open Purelib.RootIsolation.Progressive.Chamber.Overlap (ChamberOverlap)
open Purelib.RootIsolation.Progressive.Chamber.Path.Basic (ChamberPath)
open Purelib.Riemann.RootContinuation.CoherentRoot.Chamber
open Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.InteriorStep
open Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.InteriorStep.Expression
open Purelib.Approximation.Gaussian.Acquisition.Expression
open Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Geometric
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.RootContinuation
open Purelib.RootIsolation.Track.Basic (WindingOneTrack)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Geometry.Rational (Box)
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

section

variable {polynomial : CoefficientPolynomial} {ambient : Box} {track : WindingOneTrack polynomial ambient}

/-- The supplied target needs only its actual original sample readback, irrespective of conservative bookkeeping. -/
example (certificate : CoherentRoot.CertifiedName track) (actualTarget : GeometricApproximation)
    (samples : ∀ stage, actualTarget.sample stage = certificate.approximation.sample stage) :
    NamedEquivalent certificate.value.name actualTarget.toApproximation.toNamed :=
  certificate.geometric_agreesWith actualTarget samples

/-- The old default contract retains exactly the original actual-target comparison construction. -/
example (certificate : CoherentRoot.CertifiedName track) :
    certificate.geometric_agrees = certificate.geometric_agreesWith certificate.geometric (fun _ => rfl) :=
  certificate.geometric_agrees_eq

end

variable {start middle : ChamberFrame} {step : ChamberOverlap start middle} {index : start.Index}
    {source : Root start index} {target : Root middle (step.matching.forward index)}
    {piece : InteriorStep step index source target} {expression : Checked.Expr 1}

/-- An actual parameter assessment retains its full original programme, not just a scalar ball equality. -/
example (program : Program piece expression) {time : Rational} {inside : Inside time}
    (input : program.Input time inside) : (program.assess input).bounds = program := program.assess_bounds input

/-- The actual same-parameter point, admission and geometry receipt is retained completely. -/
example (program : Program piece expression) {time : Rational} {inside : Inside time}
    (input : program.Input time inside) : (program.assess input).originalInput = input := program.assess_input input

/-- Both numeric outcomes and missing evidence have the exact original finite factory equation. -/
example (program : Program piece expression) {time : Rational} {inside : Inside time}
    (input : program.Input time inside) :
    (program.assess input).result = (program.assess input).bounds.result.prepare
      (program.assess input).input.admitted (program.assess input).input.offered :=
  (program.assess input).computed

/-- The public family factory identifies its actual assessment with the original retained source receipt. -/
example {program : Program piece expression} (family : program.Family) (time : Rational) (inside : Inside time) :
    family.at time inside = family.original.assess (family.inputs time inside) := family.at_eq_assess time inside

/-- Root reciprocal geometry uses the supplied original point without selecting another root or parameter. -/
example (program : Program piece (.inverse (Checked.Expr.atom Denominator.Point.atomIndex)))
    {time : Rational} {inside : Inside time} (point : Denominator.Point piece time inside) :
    (rootInverseInput program point).point = point := rfl

/-- The real root enclosure keeps the complete same original geometric target programme. -/
example (program : Program piece expression) {time : Rational} {inside : Inside time}
    (point : Denominator.Point piece time inside) :
    (program.encloseRoot point).source = point.root.geometric := program.encloseRoot_source point

/-- Ordered one-plus-root reciprocals retain that same complete original point. -/
example (program : Program piece
    (.inverse (.add (Checked.Expr.rational 1) (Checked.Expr.atom Denominator.Point.atomIndex))))
    {time : Rational} {inside : Inside time} (point : Denominator.Point piece time inside) :
    (oneAddRootInverseInput program point).point = point := rfl

/-- The original trace decision physically retains every cached piece and its actual source/target family. -/
example {finish : ChamberFrame} {path : ChamberPath start finish} {trace : Trace path index source}
    {family : trace.Interior} {displayed} (pieces : Trace.Expression.Pieces expression displayed family) :
    pieces.decide.original = pieces := pieces.decide.original_eq

/-- An absent interior family produces the original request with its exact unchanged trace and starting cache. -/
theorem missingInterior_retainsTrace {finish : ChamberFrame} {path : ChamberPath start finish}
    (trace : Trace path index source)
    (displayed) :
    (match Trace.Expression.prepare trace expression displayed none with
      | .prepared _ offered _ _ => nomatch offered
      | .requested request => request.original = trace ∧ request.initial = source) :=
  ⟨rfl, rfl⟩

end TestPurelib.Riemann.RootContinuation.Expression
