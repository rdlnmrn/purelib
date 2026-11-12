module

import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Acquisition
import Purelib.Approximation.Gaussian.Provenance.PolynomialRoot
import Purelib.Polynomial.Dense.GCD
import Purelib.Polynomial.Elimination.Axis.Separated
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Approximation.Gaussian.Division.Search.State
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.System.IO
import Purelib.Geometry.Rational.Box.Sample
import TestPurelib.RootIsolation.Power

/-!
# Proposed original-box admission and productive algebraic consumption

Finite untrusted cofactors are checked at the actual original polynomial and
box. The productive case consumes the returned state, original root and
sidecar through checked powers and cached acquisition. Negative cases keep
region failures, submitted-certificate failures and finite inconclusivity
distinct, including a repeated source with winding eight.
-/

namespace TestPurelib.RootIsolation.ProposedBoxAdmission

open Purelib
open Purelib.RootIsolation
open Purelib.RootIsolation.State.WindingOne
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Rational.Bezout.Basic (Proposal)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Acquisition.Expression.Checked
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Geometry.Rational (Box)
open TestPurelib.RootIsolation.Power

/-- Produce finite cofactor data without claiming that the resulting identity is valid. -/
private def proposedCofactors (p q : Dense.Basic.RationalPolynomial) : Proposal :=
  let result := Dense.GCD.extendedGCD p q
  let inverse := result.gcd.leadingCoeff⁻¹
  ⟨DensePolynomial.scale inverse result.left, DensePolynomial.scale inverse result.right⟩

/-- Submit the four original line proposals, with no isolation or identity hypotheses. -/
private def data (p : CoefficientPolynomial) (box : Box) : Admission.Data :=
  ⟨fun side => some (proposedCofactors (side.real p box) (side.imaginary p box)), []⟩

/-- A deliberately empty finite evidence request. -/
private def missing : Admission.Data := ⟨fun _ => none, []⟩

/-- A compact classification used only by these executable subject regressions. -/
private def tag {p ambient box data budget} : Admission.Outcome p ambient box data budget → String
  | .zero _ => "zero"
  | .constant _ _ => "constant"
  | .accepted _ => "accepted"
  | .pending _ => "pending"
  | .invalid _ failure => match failure with
    | .improper _ => "improper"
    | .outside _ => "outside"
    | .probe _ _ _ => "bad-probe"
    | .contact _ _ _ _ => "contact"
    | .certificate _ _ _ _ => "bad-certificate"
    | .winding _ _ _ => "wrong-winding"

/-- Every returned checked-state construction keeps its exact original proposed box. -/
example {p : CoefficientPolynomial} {ambient box : Box}
    (proper : box.Proper) (inside : box.Refines ambient)
    (certificates : Admission.Certificates p box Admission.Side.all)
    (four : Winding.Box.Basic.quadrupledBoxWinding p box = 4) :
    (Admission.fromCertificates proper inside certificates four).box = box :=
  Admission.fromCertificates_box proper inside certificates four

/-- Probe work remains below its actual finite budget for every original polynomial and probe list. -/
example {p box probes fuel} (scan : Admission.ProbeScan p box probes fuel) : scan.used ≤ fuel := scan.used_le

/-- Side work remains below its actual finite budget for every original request and side list. -/
example {p box data sides fuel} (scan : Admission.SideScan p box data sides fuel) : scan.used ≤ fuel := scan.used_le

/-- Execute proposed-box failures and retain the exact finite unfinished work. -/
private def checkFailures : IO Unit := do
  unless tag (Admission.check 0 ambient ambient missing 0) = "zero" do
    throw (IO.userError "zero polynomial classification was lost")
  unless tag (Admission.check (DensePolynomial.constant 1) ambient ambient missing 0) = "constant" do
    throw (IO.userError "constant polynomial classification was lost")
  let improper : Box := ⟨1, 1, -1 / 16, 1 / 16, by decide, by decide⟩
  unless tag (Admission.check squarePolynomial ambient improper missing 0) = "improper" do
    throw (IO.userError "the original improper box was not rejected")
  let outside : Box := ⟨2, 3, -1 / 16, 1 / 16, by decide, by decide⟩
  unless tag (Admission.check squarePolynomial ambient outside missing 0) = "outside" do
    throw (IO.userError "the original outside box was not rejected")
  let wide : Box := ⟨0, 4, -1 / 4, 1 / 4, by decide, by decide⟩
  unless tag (Admission.check squarePolynomial wide outside (data squarePolynomial outside) 5) = "wrong-winding" do
    throw (IO.userError "wrong original winding was admitted")
  let wrong := { data squarePolynomial ambient with
    cofactors := fun side => match side with
      | .left => some ⟨0, 0⟩
      | other => (data squarePolynomial ambient).cofactors other }
  unless tag (Admission.check squarePolynomial ambient ambient wrong 5) = "bad-certificate" do
    throw (IO.userError "a failed submitted cofactor identity was admitted")
  let badProbe : Admission.Data := ⟨fun _ => none, [0]⟩
  unless tag (Admission.check squarePolynomial ambient ambient badProbe 1) = "bad-probe" do
    throw (IO.userError "an out-of-boundary submitted probe was mislabeled")
  let withBoundaryRoot := Polynomial.Power.Gaussian.rootPolynomial 1 ⟨2, by decide⟩
  let contact : Admission.Data := ⟨fun _ => none, [1]⟩
  unless tag (Admission.check withBoundaryRoot ambient ambient contact 1) = "contact" do
    throw (IO.userError "an actual original boundary root was not retained")
  match Admission.check squarePolynomial ambient ambient missing 2 with
  | .pending pending =>
      unless pending.sides.used = 2 ∧ pending.sides.unresolved.length = 2 ∧
          pending.sides.unprocessed = [.bottom, .top] do
        throw (IO.userError "the finite side budget lost processed events or unprocessed original sides")
  | _ => throw (IO.userError "missing finite side evidence was not inconclusive")
  let probes : Admission.Data := ⟨fun _ => none, [⟨1, -1 / 16⟩, ⟨1, 1 / 16⟩]⟩
  match Admission.check squarePolynomial ambient ambient probes 1 with
  | .pending pending =>
      unless pending.probes.used = 1 ∧ pending.probes.unprocessed = [⟨1, 1 / 16⟩] ∧
          pending.sides.used = 0 ∧ pending.sides.unprocessed = Admission.Side.all do
        throw (IO.userError "the finite probe budget performed or discarded unbudgeted work")
  | _ => throw (IO.userError "the finite probe tail did not remain inconclusive")
  match Admission.check squarePolynomial ambient ambient (data squarePolynomial ambient) 4 with
  | .pending pending =>
      match pending.stopping with
      | .winding _ => pure ()
      | _ => throw (IO.userError "the completed side budget lost its outstanding winding obligation")
  | _ => throw (IO.userError "winding was executed without its own remaining budget")
  let repeated := squarePolynomial * squarePolynomial
  match Admission.check repeated ambient ambient (data repeated ambient) 5 with
  | .invalid _ (.winding actual _ _) =>
      unless actual = 8 do throw (IO.userError "the original repeated source lost its actual winding eight")
  | _ => throw (IO.userError "the repeated original source was silently replaced or winding-one admitted")

/-- Consume a returned original root admission through productive checked algebraic acquisition. -/
private def checkProduction : IO Unit := do
  let input := powerInput ⟨2, by decide⟩ (by decide)
  let elimination := Elimination.Axis.Separated.separatedAxisEliminationCertificate
    squarePolynomial input.nonzero input.degreePositive
  match PolynomialRoot.Sidecar.checkSquarefreeBox input elimination ambient ambient
      (data squarePolynomial ambient) 5 with
  | .ready admitted =>
      let box := admitted.checked.state.box
      unless box.xLower = ambient.xLower ∧ box.xUpper = ambient.xUpper ∧
          box.yLower = ambient.yLower ∧ box.yUpper = ambient.yUpper ∧
          admitted.root.approximation.sample 0 = ambient.anchor do
        throw (IO.userError "the productive admission replaced the original box or its actual initial sample")
      let intrinsic := Algebraic.Sidecar.ofRoot admitted.sidecar
      let environment : Fin 1 → Annotated := fun _ => Annotated.opaque admitted.root.value
      let atom := Admitted.atom environment ⟨0, by decide⟩ intrinsic
      match (atom.pow 2).check with
      | .finished finished =>
          let materialized := finished.materialize
          match materialized.sidecar.scalar? with
          | some scalar => unless scalar.value = 2 do
              throw (IO.userError "the returned original root lost its productive square equation")
          | none => throw (IO.userError "the returned intrinsic sidecar did not feed checked power acquisition")
          let state := Division.Search.State.initial finished.source.channel
          let acquired := finished.acquire state (CoherentNamed.Coherence.exact 1) (1 / 16) (by decide)
          unless acquired.1.route = Division.Acquisition.State.Route.cached ∧
              acquired.1.next.state.nextIndex = state.nextIndex do
            throw (IO.userError "productive acquisition discarded the returned checked decision or original state")
      | _ => throw (IO.userError "the returned intrinsic root did not complete its admitted expression")
  | _ => throw (IO.userError "a valid original proposed box did not construct its original intrinsic root")

/-- Run the exact proposed-box admission and productive-consumer regressions. -/
public def check : IO Unit := do
  checkFailures
  checkProduction
  System.IO.println "proposed original-box admission: checked finite failures, budgets and productive root acquisition"

end TestPurelib.RootIsolation.ProposedBoxAdmission

/-- Execute the finite proposed-box admission regressions without any checkpoint stores or numerical producers. -/
public def main : IO Unit := TestPurelib.RootIsolation.ProposedBoxAdmission.check
