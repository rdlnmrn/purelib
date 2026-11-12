module

public import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Compute
public import Purelib.Polynomial.Dense.Rational.Bezout.Basic
public import Purelib.RootIsolation.Curve.Event.Analysis
public import Purelib.RationalFunctions.Curve.Canonical.Line
public import Purelib.Polynomial.Dense.Gaussian.Path.Axis
import Purelib.Polynomial.Clearance.Box.Line.Bezout
import Purelib.Polynomial.Clearance.Box.Line.Restriction
import Purelib.Polynomial.Clearance.Box.Boundary.Lines
public import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Finite admission of a proposed original winding-one box

Coefficient preprocessing retains zero, constant and original multiplicity
outcomes. Untrusted finite cofactor data, boundary probes and the actual winding
are checked against the same original polynomial and proposed box. A budget
limits probe, side and winding inspections; missing certificates and unprocessed
work remain explicit. A failed certificate or finite attempt is not a global
root-existence or nonexistence claim.
-/

public section
namespace Purelib.RootIsolation.State.WindingOne.Admission

open Purelib
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Rational.Bezout.Basic (Proposal CoprimeCertificate)
open Purelib.Polynomial.Dense.Gaussian.Path
open Purelib.Geometry.Rational (Box)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.RationalFunctions
open Purelib.RootIsolation

set_option genInjectivity false in
/-- The four original box sides, in left, right, bottom and top checking order. -/
inductive Side where
  /-- The lower real coordinate. -/ | left
  /-- The upper real coordinate. -/ | right
  /-- The lower imaginary coordinate. -/ | bottom
  /-- The upper imaginary coordinate. -/ | top
  deriving @[expose] DecidableEq

constructive_injectivity Side

namespace Side

/-- The complete original side order. -/
@[expose] def all : List Side := [.left, .right, .bottom, .top]

/-- The original real-coordinate path polynomial on one proposed side. -/
@[expose] def real (p : CoefficientPolynomial) (box : Box) : Side → Dense.Basic.RationalPolynomial
  | .left => Axis.verticalPathReal p box.xLower
  | .right => Axis.verticalPathReal p box.xUpper
  | .bottom => Axis.horizontalPathReal p box.yLower
  | .top => Axis.horizontalPathReal p box.yUpper

/-- The original imaginary-coordinate path polynomial on one proposed side. -/
@[expose] def imaginary (p : CoefficientPolynomial) (box : Box) : Side → Dense.Basic.RationalPolynomial
  | .left => Axis.verticalPathImag p box.xLower
  | .right => Axis.verticalPathImag p box.xUpper
  | .bottom => Axis.horizontalPathImag p box.yLower
  | .top => Axis.horizontalPathImag p box.yUpper

/-- The exact original rational line whose finite event analysis is retained when evidence is missing. -/
@[expose] def curve (box : Box) : Side → Curve.RationalCurve
  | .left => Curve.Canonical.Line.realLine box.xLower
  | .right => Curve.Canonical.Line.realLine box.xUpper
  | .bottom => Curve.Canonical.Line.imaginaryLine box.yLower
  | .top => Curve.Canonical.Line.imaginaryLine box.yUpper

end Side

set_option genInjectivity false in
/-- Proposed finite line cofactors and original boundary probes, without validity assumptions. -/
structure Data where
  /-- Every proposed side may carry its own untrusted finite cofactor pair. -/
  cofactors : Side → Option Proposal
  /-- The exact ordered Gaussian points proposed for boundary-contact inspection. -/
  probes : List Canonical

constructive_injectivity Data

set_option genInjectivity false in
/-- A violated geometric, winding-one or submitted-certificate condition.

Certificate and probe failures concern the submitted data. Contact carries
an actual original-boundary root. Wrong winding excludes this winding-one
contract only; in particular winding eight does not assert that a repeated
root is absent.
-/
inductive Invalid (p : CoefficientPolynomial) (ambient proposed : Box) (data : Data) where
  /-- The proposed box has zero width or height. -/
  | improper (failed : ¬ proposed.Proper)
  /-- The proposed box is not contained in its original ambient. -/
  | outside (failed : ¬ proposed.Refines ambient)
  /-- A submitted probe is not on the original proposed boundary. -/
  | probe (point : Canonical) (member : point ∈ data.probes)
      (failed : ¬ Box.Boundary.OnBoxBoundary proposed point)
  /-- An inspected original boundary point is an exact root of the original polynomial. -/
  | contact (point : Canonical) (member : point ∈ data.probes)
      (boundary : Box.Boundary.OnBoxBoundary proposed point) (zero : p.eval point = 0)
  /-- One submitted pair fails its exact original line identity. -/
  | certificate (side : Side) (raw : Proposal) (submitted : data.cofactors side = some raw)
      (failure : raw.Invalid (side.real p proposed) (side.imaginary p proposed))
  /-- The computed original winding is not four. -/
  | winding (actual : Int) (actual_eq : actual = Winding.Box.Basic.quadrupledBoxWinding p proposed)
      (failed : actual ≠ 4)

constructive_injectivity Invalid

set_option genInjectivity false in
/-- The exact finite boundary-probe scan, retaining its first failure or unprocessed tail. -/
inductive ProbeScan (p : CoefficientPolynomial) (box : Box) : List Canonical → Nat → Type where
  /-- No probes remain; no further budget is consumed. -/
  | done (fuel : Nat) : ProbeScan p box [] fuel
  /-- The original nonempty probe tail remains unprocessed at zero fuel. -/
  | stopped (point : Canonical) (tail : List Canonical) : ProbeScan p box (point :: tail) 0
  /-- The inspected point is not a boundary probe. -/
  | outside (fuel : Nat) (point : Canonical) (tail : List Canonical)
      (failed : ¬ Box.Boundary.OnBoxBoundary box point) : ProbeScan p box (point :: tail) (fuel + 1)
  /-- The inspected point is a proved boundary contact. -/
  | contact (fuel : Nat) (point : Canonical) (tail : List Canonical)
      (boundary : Box.Boundary.OnBoxBoundary box point) (zero : p.eval point = 0) :
      ProbeScan p box (point :: tail) (fuel + 1)
  /-- This original boundary point is not a root, followed by the actual remaining scan. -/
  | checked {fuel : Nat} (point : Canonical) {tail : List Canonical}
      (boundary : Box.Boundary.OnBoxBoundary box point) (nonzero : p.eval point ≠ 0)
      (rest : ProbeScan p box tail fuel) : ProbeScan p box (point :: tail) (fuel + 1)

constructive_injectivity ProbeScan

namespace ProbeScan

/-- Inspect at most the supplied number of original probes, stopping at the first actual failed condition. -/
@[expose] def run (p : CoefficientPolynomial) (box : Box) :
    (probes : List Canonical) → (fuel : Nat) → ProbeScan p box probes fuel
  | [], fuel => .done fuel
  | point :: tail, 0 => .stopped point tail
  | point :: tail, fuel + 1 =>
      if boundary : Box.Boundary.OnBoxBoundary box point then
        if zero : p.eval point = 0 then .contact fuel point tail boundary zero
        else .checked point boundary zero (run p box tail fuel)
      else .outside fuel point tail boundary

/-- Count only the probes actually inspected by this scan. -/
@[expose] def used {p box probes fuel} : ProbeScan p box probes fuel → Nat
  | .done _ | .stopped _ _ => 0
  | .outside _ _ _ _ | .contact _ _ _ _ _ => 1
  | .checked _ _ _ rest => rest.used + 1

/-- Every actual probe scan respects its supplied finite budget. -/
theorem used_le {p box probes fuel} (scan : ProbeScan p box probes fuel) : scan.used ≤ fuel := by
  induction scan with
  | done => exact Nat.zero_le _
  | stopped => exact Nat.le_refl _
  | outside => exact Nat.succ_le_succ (Nat.zero_le _)
  | contact => exact Nat.succ_le_succ (Nat.zero_le _)
  | checked point boundary nonzero rest ih => exact Nat.succ_le_succ ih

/-- Read every original probe not inspected after exhaustion or first failure. -/
@[expose] def unprocessed {p box probes fuel} : ProbeScan p box probes fuel → List Canonical
  | .done _ => []
  | .stopped point tail => point :: tail
  | .outside _ _ tail _ | .contact _ _ tail _ _ => tail
  | .checked _ _ _ rest => rest.unprocessed

/-- Read a failed submitted probe or proved contact at its original source-list membership. -/
@[expose] def failure {p box probes fuel} (scan : ProbeScan p box probes fuel)
    (ambient : Box) (data : Data) (present : ∀ point, point ∈ probes → point ∈ data.probes) :
    Option (Invalid p ambient box data) :=
  match scan with
  | .done _ | .stopped _ _ => none
  | .outside _ point _ failed => some (.probe point (present point (.head _)) failed)
  | .contact _ point _ boundary zero => some (.contact point (present point (.head _)) boundary zero)
  | .checked _ _ _ rest => rest.failure ambient data (fun point member => present point (.tail _ member))

end ProbeScan

set_option genInjectivity false in
/-- Checked original line cofactors in the exact supplied side order. -/
inductive Certificates (p : CoefficientPolynomial) (box : Box) : List Side → Type where
  /-- The empty side list requires no certificates. -/
  | nil : Certificates p box []
  /-- The exact original first line identity followed by its retained tail. -/
  | cons {side : Side} {tail : List Side}
      (certificate : CoprimeCertificate (side.real p box) (side.imaginary p box))
      (rest : Certificates p box tail) : Certificates p box (side :: tail)

constructive_injectivity Certificates

set_option genInjectivity false in
/-- The actual budgeted side scan, including missing evidence, failed identities and every unprocessed tail. -/
inductive SideScan (p : CoefficientPolynomial) (box : Box) (data : Data) : List Side → Nat → Type where
  /-- No original sides remain. -/
  | done (fuel : Nat) : SideScan p box data [] fuel
  /-- The complete original side tail remains unprocessed at zero fuel. -/
  | stopped (side : Side) (tail : List Side) : SideScan p box data (side :: tail) 0
  /-- This side has no certificate; retain its actual finite curve-event analysis and continue. -/
  | missing {fuel : Nat} (side : Side) {tail : List Side} (absent : data.cofactors side = none)
      (analysis : Curve.Event.Analysis p (side.curve box))
      (analysis_eq : analysis = Curve.Event.analyze p (side.curve box))
      (rest : SideScan p box data tail fuel) : SideScan p box data (side :: tail) (fuel + 1)
  /-- The exact submitted pair failed its finite unit-identity comparison. -/
  | invalid (fuel : Nat) (side : Side) (tail : List Side) (raw : Proposal)
      (submitted : data.cofactors side = some raw)
      (failure : raw.Invalid (side.real p box) (side.imaginary p box)) :
      SideScan p box data (side :: tail) (fuel + 1)
  /-- This side's actual checker accepted the original cofactors, followed by its retained tail. -/
  | checked {fuel : Nat} (side : Side) {tail : List Side} (raw : Proposal)
      (submitted : data.cofactors side = some raw)
      (certificate : CoprimeCertificate (side.real p box) (side.imaginary p box))
      (checked : raw.check (side.real p box) (side.imaginary p box) = .ok certificate)
      (rest : SideScan p box data tail fuel) : SideScan p box data (side :: tail) (fuel + 1)

constructive_injectivity SideScan

namespace SideScan

/-- Check only the budgeted original side prefix, retaining actual missing-side event analyses. -/
@[expose] def run (p : CoefficientPolynomial) (box : Box) (data : Data) :
    (sides : List Side) → (fuel : Nat) → SideScan p box data sides fuel
  | [], fuel => .done fuel
  | side :: tail, 0 => .stopped side tail
  | side :: tail, fuel + 1 =>
      match submitted : data.cofactors side with
      | none => .missing side submitted (Curve.Event.analyze p (side.curve box)) rfl
          (run p box data tail fuel)
      | some raw => match checked : raw.check (side.real p box) (side.imaginary p box) with
        | .error failure => .invalid fuel side tail raw submitted failure
        | .ok certificate => .checked side raw submitted certificate checked (run p box data tail fuel)

/-- Count the exact original side inspections performed. -/
@[expose] def used {p box data sides fuel} : SideScan p box data sides fuel → Nat
  | .done _ | .stopped _ _ => 0
  | .invalid _ _ _ _ _ _ => 1
  | .missing _ _ _ _ rest | .checked _ _ _ _ _ rest => rest.used + 1

/-- Every actual side scan respects its finite budget. -/
theorem used_le {p box data sides fuel} (scan : SideScan p box data sides fuel) : scan.used ≤ fuel := by
  induction scan with
  | done => exact Nat.zero_le _
  | stopped => exact Nat.le_refl _
  | invalid => exact Nat.succ_le_succ (Nat.zero_le _)
  | missing side absent analysis analysis_eq rest ih => exact Nat.succ_le_succ ih
  | checked side raw submitted certificate checked rest ih => exact Nat.succ_le_succ ih

/-- Retain every original side still unprocessed after exhaustion or first certificate failure. -/
@[expose] def unprocessed {p box data sides fuel} : SideScan p box data sides fuel → List Side
  | .done _ => []
  | .stopped side tail => side :: tail
  | .invalid _ _ tail _ _ _ => tail
  | .missing _ _ _ _ rest | .checked _ _ _ _ _ rest => rest.unprocessed

/-- List every processed side whose finite event analysis remains unresolved by absent cofactor evidence. -/
@[expose] def unresolved {p box data sides fuel} : SideScan p box data sides fuel → List Side
  | .done _ | .stopped _ _ | .invalid _ _ _ _ _ _ => []
  | .missing side _ _ _ rest => side :: rest.unresolved
  | .checked _ _ _ _ _ rest => rest.unresolved

/-- Read the actual submitted-certificate failure without turning it into geometric invalidity. -/
@[expose] def failure {p box data sides fuel} : SideScan p box data sides fuel →
    (ambient : Box) → Option (Invalid p ambient box data)
  | .done _, _ | .stopped _ _, _ => none
  | .invalid _ side _ raw submitted failure, _ => some (.certificate side raw submitted failure)
  | .missing _ _ _ _ rest, ambient | .checked _ _ _ _ _ rest, ambient => rest.failure ambient

/-- Read the same checked cofactors only when every original side has actually completed successfully. -/
@[expose] def certificates {p box data sides fuel} : SideScan p box data sides fuel →
    Option (Certificates p box sides)
  | .done _ => some .nil
  | .stopped _ _ | .invalid _ _ _ _ _ _ | .missing _ _ _ _ _ => none
  | .checked _ _ _ certificate _ rest => rest.certificates.map (Certificates.cons certificate)

end SideScan

/-- Assemble a state from the same checked side caches and exact original geometry and winding.

No line producer is called. The four original cofactor identities supply the
full ambient-line clearances and their restrictions to the proposed box.
-/
def fromCertificates {p : CoefficientPolynomial} {ambient proposed : Box}
    (proper : proposed.Proper) (inside : proposed.Refines ambient)
    (certificates : Certificates p proposed Side.all)
    (four : Winding.Box.Basic.quadrupledBoxWinding p proposed = 4) :
    Basic.WindingOneState p ambient :=
  match certificates with
  | .cons left (.cons right (.cons bottom (.cons top .nil))) =>
      let l := Clearance.Box.Line.Bezout.verticalOfCoprime p ambient proposed.xLower left
      let r := Clearance.Box.Line.Bezout.verticalOfCoprime p ambient proposed.xUpper right
      let b := Clearance.Box.Line.Bezout.horizontalOfCoprime p ambient proposed.yLower bottom
      let t := Clearance.Box.Line.Bezout.horizontalOfCoprime p ambient proposed.yUpper top
      ⟨proposed, inside, proper,
        Clearance.Box.Boundary.Lines.boundaryOfLines
          (l.restrict inside) (r.restrict inside) (b.restrict inside) (t.restrict inside),
        four, l, r, b, t⟩

/-- The checked construction retains the complete original proposed box. -/
theorem fromCertificates_box {p : CoefficientPolynomial} {ambient proposed : Box}
    (proper : proposed.Proper) (inside : proposed.Refines ambient)
    (certificates : Certificates p proposed Side.all)
    (four : Winding.Box.Basic.quadrupledBoxWinding p proposed = 4) :
    (fromCertificates proper inside certificates four).box = proposed := by
  cases certificates with
  | cons left rest => cases rest with
    | cons right rest => cases rest with
      | cons bottom rest => cases rest with
        | cons top rest => cases rest; rfl

set_option genInjectivity false in
/-- The actual finite condition preventing completion of the original admission attempt. -/
inductive Stopping {p : CoefficientPolynomial} {proposed : Box} {data : Data} {budget : Nat}
    (probes : ProbeScan p proposed data.probes budget)
    (sides : SideScan p proposed data Side.all (budget - probes.used)) where
  /-- Original boundary probes remain after the consumed budget. -/
  | probes (remaining : probes.unprocessed ≠ [])
  /-- At least one side is missing, unprocessed or otherwise not completely certified. -/
  | sides (unfinished : sides.certificates = none)
  /-- All required data is checked, but no fuel remains for the actual winding computation. -/
  | winding (exhausted : ¬ probes.used + sides.used < budget)

constructive_injectivity Stopping

set_option genInjectivity false in
/-- An unfinished finite admission retains all original attempted and unprocessed work.

The probe and side scans are the actual procedures on their supplied budgets.
Their indexed tails retain every unprocessed probe or side. Missing sides keep
all finite event data; no event count is reinterpreted as root existence.
-/
structure Pending (p : CoefficientPolynomial) (ambient proposed : Box) (data : Data) (budget : Nat) where
  /-- The exact original positive preprocessing, including its unreduced source multiplicities. -/
  preprocessing : Dense.Gaussian.Squarefree.Decomposition.Compute.PositivePreprocessing p
  /-- The actual original probe scan on the whole budget. -/
  probes : ProbeScan p proposed data.probes budget
  /-- The probe scan is the same original finite procedure. -/
  probes_eq : probes = ProbeScan.run p proposed data.probes budget
  /-- The actual original side scan using only remaining probe fuel. -/
  sides : SideScan p proposed data Side.all (budget - probes.used)
  /-- The remaining sides execute only after all probes have finished without invalidity. -/
  sides_eq : sides = SideScan.run p proposed data Side.all (budget - probes.used)
  /-- The exact remaining-probe, side-evidence or winding-budget stopping condition. -/
  stopping : Stopping probes sides

constructive_injectivity Pending

set_option genInjectivity false in
/-- One exact checked state and the actual original finite work that admitted it. -/
structure Accepted (p : CoefficientPolynomial) (ambient proposed : Box) (data : Data) (budget : Nat) where
  /-- The same original positive preprocessing and multiplicity decomposition. -/
  preprocessing : Dense.Gaussian.Squarefree.Decomposition.Compute.PositivePreprocessing p
  /-- The actual original probe scan. -/ probes : ProbeScan p proposed data.probes budget
  /-- The same original finite probe procedure was used. -/
  probes_eq : probes = ProbeScan.run p proposed data.probes budget
  /-- The actual original side scan on the remaining budget. -/
  sides : SideScan p proposed data Side.all (budget - probes.used)
  /-- The same original finite side procedure was used. -/
  sides_eq : sides = SideScan.run p proposed data Side.all (budget - probes.used)
  /-- The actual probe, side and final winding work respects the original budget. -/
  work_le : probes.used + sides.used + 1 ≤ budget
  /-- The same actual completely checked original side cofactors. -/
  certificates : Certificates p proposed Side.all
  /-- The side cache is read from the same actual successful finite scan. -/
  certificates_eq : sides.certificates = some certificates
  /-- The checked original box is proper. -/ proper : proposed.Proper
  /-- The checked original box refines its ambient. -/ inside : proposed.Refines ambient
  /-- The actual computed original winding. -/ winding : Int
  /-- This integer is computed from the same original polynomial and box. -/
  winding_eq : winding = Winding.Box.Basic.quadrupledBoxWinding p proposed
  /-- That actual winding meets the winding-one contract. -/ four : winding = 4
  /-- The exact original state admitted by those checks. -/ state : Basic.WindingOneState p ambient
  /-- This state consumes precisely the same checked geometry, cofactor bank and winding. -/
  state_eq : state = fromCertificates proper inside certificates (winding_eq.symm.trans four)
  /-- No different proposed box is substituted. -/ box_eq : state.box = proposed

constructive_injectivity Accepted

set_option genInjectivity false in
/-- Exact coefficient classification, checked winding-one admission, witnessed failure or finite inconclusivity. -/
inductive Outcome (p : CoefficientPolynomial) (ambient proposed : Box) (data : Data) (budget : Nat) where
  /-- The original polynomial is identically zero. -/ | zero (certificate : p.isZero = true)
  /-- The original polynomial is nonzero constant. -/
  | constant (nonzero : p.isZero = false) (degreeZero : p.natDegree = 0)
  /-- The exact original winding-one proposal was admitted. -/
  | accepted (result : Accepted p ambient proposed data budget)
  /-- A proved original geometric/contact/winding failure or invalid submitted certificate. -/
  | invalid (preprocessing : Dense.Gaussian.Squarefree.Decomposition.Compute.PositivePreprocessing p)
      (failure : Invalid p ambient proposed data)
  /-- The actual finite attempt and every remaining obligation are retained. -/
  | pending (result : Pending p ambient proposed data budget)

constructive_injectivity Outcome

/-- Check a finite proposed original winding-one box without an isolation-validity premise.

The budget counts each inspected probe, side and final winding. Coefficient
preprocessing and the two fixed geometric guards precede that finite work.
Absent evidence remains inconclusive. In particular, a repeated-source
winding different from four rejects only this winding-one contract.
-/
@[expose] def check (p : CoefficientPolynomial) (ambient proposed : Box) (data : Data) (budget : Nat) :
    Outcome p ambient proposed data budget :=
  match Dense.Gaussian.Squarefree.Decomposition.Compute.preprocess p with
  | .zero certificate => .zero certificate
  | .constant nonzero degreeZero => .constant nonzero degreeZero
  | .positive preprocessing =>
    letI : Decidable proposed.Proper := inferInstanceAs
      (Decidable (proposed.xLower < proposed.xUpper ∧ proposed.yLower < proposed.yUpper))
    letI : Decidable (proposed.Refines ambient) := inferInstanceAs
      (Decidable (ambient.xLower ≤ proposed.xLower ∧ proposed.xUpper ≤ ambient.xUpper ∧
        ambient.yLower ≤ proposed.yLower ∧ proposed.yUpper ≤ ambient.yUpper))
    if proper : proposed.Proper then
      if inside : proposed.Refines ambient then
        let probes := ProbeScan.run p proposed data.probes budget
        match probes.failure ambient data (fun _ member => member) with
        | some failure => .invalid preprocessing failure
        | none =>
          let sides := SideScan.run p proposed data Side.all (budget - probes.used)
          match sides.failure ambient with
          | some failure => .invalid preprocessing failure
          | none =>
            if probesFinished : probes.unprocessed = [] then
              match certificatesEq : sides.certificates with
              | none => .pending ⟨preprocessing, probes, rfl, sides, rfl, .sides certificatesEq⟩
              | some certificates =>
                if windingFuel : probes.used + sides.used < budget then
                  let actual := Winding.Box.Basic.quadrupledBoxWinding p proposed
                  if four : actual = 4 then
                    let state := fromCertificates proper inside certificates four
                    .accepted ⟨preprocessing, probes, rfl, sides, rfl, Nat.succ_le_of_lt windingFuel,
                      certificates, certificatesEq, proper, inside,
                      actual, rfl, four, state, rfl, fromCertificates_box proper inside certificates four⟩
                  else .invalid preprocessing (.winding actual rfl four)
                else .pending ⟨preprocessing, probes, rfl, sides, rfl, .winding windingFuel⟩
            else .pending ⟨preprocessing, probes, rfl, sides, rfl, .probes probesFinished⟩
      else .invalid preprocessing (.outside inside)
    else .invalid preprocessing (.improper proper)

end Purelib.RootIsolation.State.WindingOne.Admission
end
