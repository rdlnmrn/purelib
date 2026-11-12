module

import Purelib.Approximation.Gaussian.Acquisition.Annotated.Arithmetic
public import Purelib.Approximation.Gaussian.Provenance.Algebraic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Provenance.Algebraic.Comparison
import Purelib.Approximation.Gaussian.Provenance.Algebraic.Imaginary
meta import Purelib.Approximation.Gaussian.Provenance.Algebraic.Imaginary
import Purelib.Approximation.Gaussian.Name.Coherent.Power
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Data.Gaussian.Norm.Basic
meta import Purelib.Approximation.Gaussian.Provenance.Algebraic.Comparison
meta import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Acquisition.Provenance.Inspection
import Purelib.Data.Gaussian.Field
meta import Purelib.Approximation.Gaussian.Acquisition.Annotated.Arithmetic
meta import Purelib.Approximation.Gaussian.Acquisition.Provenance.Inspection
meta import Purelib.Approximation.Gaussian.Provenance.Algebraic
meta import Purelib.Data.Gaussian.Field

/-! # Original finite algebraic constructions and automatic arithmetic acquisition -/

namespace TestPurelib.Approximation.Gaussian.AlgebraicConstruction

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Data.Gaussian.Basic (Canonical)

example {channel : CoherentNamed} (original : Algebraic.Sidecar channel) :
    (original.pow 0).origin = Algebraic.Origin.powZero original.origin := original.pow_zero_origin

example {channel : CoherentNamed} (original : Algebraic.Sidecar channel) :
    (original.pow 0).cached = Algebraic.Cached.powZero original.cached := original.pow_zero_cached

example {channel : CoherentNamed} (original : Algebraic.Sidecar channel) :
    (original.pow 0).residual = (Algebraic.Sidecar.ofRational (RationalSidecar.exact 1)).residual :=
  original.pow_zero_residual

example {channel : CoherentNamed} (original : Algebraic.Sidecar channel) :
    (original.pow 0).scalar? = some (RationalSidecar.exact 1) := original.pow_zero_scalar

example {channel : CoherentNamed} (original : Algebraic.Sidecar channel) :
    (original.pow 0).decide = (Algebraic.Sidecar.ofRational (RationalSidecar.exact 1)).decide :=
  original.pow_zero_decide

example {channel : CoherentNamed} (original : Algebraic.Sidecar channel) (exponent : Nat) :
    original.pow (exponent + 1) = (original.pow exponent).mul original := original.pow_succ exponent

example {first second : CoherentNamed} (left : Algebraic.Sidecar first) (right : Algebraic.Sidecar second) :
    Equivalence.NamedEquivalent
      (Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner.polynomialEval
        (left.add right).polynomial (CoherentNamed.add first second)).name
      (CoherentNamed.Coherence.exact 0).name := (left.add right).equation

example {channel : CoherentNamed} (sidecar : Algebraic.Sidecar channel) : Division.Prepared.Decision channel :=
  (Acquisition.Provenance.algebraic sidecar).exact

example {channel : CoherentNamed} (sidecar : Algebraic.Sidecar channel) :
    sidecar.neg.polynomial.natDegree = sidecar.polynomial.natDegree := sidecar.neg_degree

example {channel : CoherentNamed} (sidecar : Algebraic.Sidecar channel) (index : Nat) :
    sidecar.neg.residual.source.sample index = -sidecar.residual.source.sample index := sidecar.neg_sample index

example {channel : CoherentNamed} (sidecar : Algebraic.Sidecar channel) :
    sidecar.neg.cached = Algebraic.Cached.neg sidecar.cached := sidecar.neg_cached

example {channel : CoherentNamed} (sidecar : Algebraic.Sidecar channel) :
    Equivalence.NamedEquivalent
      (Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner.polynomialEval
        sidecar.neg.polynomial (CoherentNamed.neg channel)).name
      (CoherentNamed.Coherence.exact 0).name := sidecar.neg.equation

/-- Read actual arithmetic input samples through a generalized retained construction cache. -/
private meta def retainedInputs {channel : CoherentNamed} {origin : Algebraic.Origin channel}
    {polynomial : Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {residual : Purelib.Polynomial.Approximation.Gaussian.Residual polynomial channel}
    (cache : Algebraic.Cached origin polynomial residual) :
    Option (Canonical × Canonical) :=
  match cache with
  | .arithmetic _ _ _ result => some (result.first.source.sample 6, result.second.source.sample 7)
  | .quadraticSum _ _ _ _ _ _ result => some (result.first.source.sample 6, result.second.source.sample 7)
  | _ => none

/-- Read a retained rational child through its actual direct unary cache constructor. -/
private def retainedNegChild {channel : CoherentNamed} {origin : Algebraic.Origin channel}
    {polynomial : Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {residual : Purelib.Polynomial.Approximation.Gaussian.Residual polynomial channel}
    (cache : Algebraic.Cached origin polynomial residual) : Option (Canonical) :=
  match cache with
  | .neg child => match child with
      | .rational reading => some reading.value
      | _ => none
  | _ => none

/-- Read the actual original input polynomial from the retained zero-power child cache. -/
private def powerZeroParent? {channel : CoherentNamed} {origin : Algebraic.Origin channel}
    {polynomial : Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {residual : Purelib.Polynomial.Approximation.Gaussian.Residual polynomial channel}
    (cache : Algebraic.Cached origin polynomial residual) :
    Option Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial :=
  match cache with
  | .powZero (polynomial := parentPolynomial) _ => some parentPolynomial
  | _ => none

/-- Execute zero power with its retained original cache and unchanged constant-one scalar and sample program.

The original child may be a nonlinear root with no scalar reading. All
output samples, including a large finite index, remain constant one; the
reader and division decision consume that same constant without root refinement.
-/
public def checkZeroPower {channel : CoherentNamed} (original : Algebraic.Sidecar channel)
    (powered : Algebraic.Sidecar (Name.Coherent.Power.namedPower channel 0)) : IO Unit := do
  unless powerZeroParent? powered.cached = some original.polynomial do
    throw (IO.userError "zero power discarded its same original parent cache or polynomial")
  unless powered.polynomial = (Algebraic.Sidecar.ofRational (RationalSidecar.exact 1)).polynomial ∧
      powered.residual.scale = 0 ∧ powered.residual.source.errorScale = 0 do
    throw (IO.userError "zero power changed its original constant-one polynomial or quantitative residual")
  for index in [0, 1, 7, 100000] do
    unless powered.residual.source.sample index = 1 do
      throw (IO.userError "zero power changed the original constant sample program")
  match powered.scalar? with
  | some reading =>
      unless reading.value = 1 do throw (IO.userError "zero power lost its exact constant-one reading")
  | none => throw (IO.userError "zero power inspected an opaque child instead of reading its original exact one")
  match powered.resolve with
  | .scalar reading _ =>
      unless reading.value = 1 do throw (IO.userError "zero power resolved through an incorrect scalar")
  | _ => throw (IO.userError "zero power repeated geometric or root localization instead of its exact scalar decision")
  unless powered.decide.isPrepared do
    throw (IO.userError "zero power changed the original nonzero constant-one decision")
  let named := Name.Coherent.Power.namedPower channel 0
  unless (Name.Sampling.approximation named.name).sample 7 = 1 do
    throw (IO.userError "zero power changed the same original constant-one numerical channel")

/-- Execute direct unary cache retention and the original numerical negation channel natively. -/
public def checkNegation : IO Unit := do
  let original := Algebraic.Sidecar.ofRational (RationalSidecar.exact 2)
  let negative := original.neg
  unless retainedNegChild negative.cached = some 2 ∧
      negative.polynomial.natDegree = original.polynomial.natDegree ∧
      negative.residual.scale = original.residual.scale do
    throw (IO.userError "native negation replaced its original cache, degree or scale")
  for index in [0, 1, 4, 7] do
    unless negative.residual.source.sample index = -original.residual.source.sample index ∧
        negative.polynomial.eval (negative.residual.source.sample index) = 0 do
      throw (IO.userError "native negation changed its original indexed numerical sample or residual")
  match negative.scalar? with
  | some reading =>
      unless reading.value = -2 do
        throw (IO.userError "native negation changed its retained original scalar reading")
  | none => throw (IO.userError "native negation discarded its retained exact scalar child")

/-- Execute recursive annotation arithmetic while retaining actual stored numerical programs. -/
private meta def checkConstruction : IO Unit := do
  let first := Algebraic.Sidecar.ofRational (RationalSidecar.exact 2)
  let second := Algebraic.Sidecar.ofRational (RationalSidecar.exact 3)
  let sum := Acquisition.Annotated.add (Acquisition.Annotated.algebraic first)
    (Acquisition.Annotated.algebraic second)
  let product := Acquisition.Annotated.mul sum (Acquisition.Annotated.rational 3)
  match product.provenance with
  | some (.algebraic retained) =>
      unless retained.residual.source.sample 5 = 15 ∧ retained.polynomial.eval 15 = 0 do
        throw (IO.userError "automatic algebraic propagation lost the original recursive result")
      unless retained.decide.isPrepared do
        throw (IO.userError "recursive algebraic acquisition failed to prepare its original nonzero channel")
      unless retainedInputs retained.cached = some (5, 3) do
        throw (IO.userError "recursive construction replaced its retained input residual programs")
  | _ => throw (IO.userError "automatic recursive arithmetic discarded supported algebraic evidence")
  let cancellation := Acquisition.Annotated.add
    (Acquisition.Annotated.algebraic (Algebraic.Sidecar.ofRational (RationalSidecar.exact (-2))))
    (Acquisition.Annotated.algebraic first)
  match cancellation.provenance with
  | some (.algebraic retained) =>
      unless !retained.decide.isPrepared ∧ retained.residual.source.sample 4 = 0 do
        throw (IO.userError "automatic algebraic cancellation did not exclude its original channel")
  | _ => throw (IO.userError "automatic algebraic cancellation lost its evidence")

/-- Execute unary closure, independent equality and actual prepared inverse cache readback. -/
private def checkUnaryConstruction : IO Unit := do
  let first := Algebraic.Sidecar.ofRational (RationalSidecar.exact 2)
  let second := Algebraic.Sidecar.ofRational (RationalSidecar.exact 3)
  let negative := first.neg
  let power := first.pow 3
  checkZeroPower first (first.pow 0)
  let zeroInput := Algebraic.Sidecar.ofRational (RationalSidecar.exact 0)
  checkZeroPower zeroInput (zeroInput.pow 0)
  let difference := second.sub first
  let conjugated := first.conj
  unless negative.polynomial.natDegree = first.polynomial.natDegree ∧
      negative.residual.scale = first.residual.scale do
    throw (IO.userError "direct algebraic negation enlarged its original degree or residual scale")
  unless retainedNegChild negative.cached = some 2 do
    throw (IO.userError "direct algebraic negation replaced its retained unary constructor or original child cache")
  match difference.scalar? with
  | some reading =>
      unless reading.value = 1 do
        throw (IO.userError "retained linear difference lost its exact original-channel scalar evidence")
  | none => throw (IO.userError "checked monic linear algebraic result remained unclassified")
  unless negative.residual.source.sample 3 = -2 ∧ power.residual.source.sample 4 = 8 ∧
      difference.residual.source.sample 5 = 1 ∧ conjugated.residual.source.sample 6 = 2 do
    throw (IO.userError "unary algebraic closure lost its original numerical operation samples")
  match (first.compare (Algebraic.Sidecar.ofRational (RationalSidecar.exact 2))).comparison with
  | .equal _ => pure ()
  | .distinct _ _ => throw (IO.userError "independent exact algebraic inputs failed original-channel equality")
  match (first.compare second).comparison with
  | .distinct _ _ => pure ()
  | .equal _ => throw (IO.userError "distinct original algebraic inputs were identified")
  match first.inverse with
  | .obstructed _ => throw (IO.userError "nonzero algebraic inverse was obstructed")
  | .ready _ cache result _ =>
      unless cache.result.sample 3 = (2 : Canonical)⁻¹ ∧
          result.residual.source.sample 4 = cache.result.sample 4 ∧
          result.residual.scale = cache.residualScale do
        throw (IO.userError "checked algebraic inverse replaced its retained paid numerical cache")
      match result.scalar? with
      | some reading =>
          unless reading.value = (2 : Canonical)⁻¹ do
            throw (IO.userError "paid reciprocal lost its exact original-child scalar evidence")
      | none => throw (IO.userError "paid scalar inverse repeated general polynomial localization")
      match ((result.conj).add second).scalar? with
      | some reading =>
          unless reading.value = (2 : Canonical)⁻¹ + 3 do
            throw (IO.userError "arithmetic after a retained scalar inverse lost its original exact reading")
      | none => throw (IO.userError "scalar inverse evidence failed to propagate through conjugation and addition")
  let zero := Algebraic.Sidecar.ofRational (RationalSidecar.exact 0)
  match zero.inverse with
  | .obstructed _ => pure ()
  | .ready _ _ _ _ => throw (IO.userError "zero algebraic inverse lost its original obstruction")

/-- Check both original channels and the cached imaginary-difference decision on two exact algebraic inputs. -/
private def checkImaginaryConstruction : IO Unit := do
  let imaginary : Canonical := ⟨0, 1⟩
  let original := Algebraic.Sidecar.ofRational (RationalSidecar.exact imaginary)
  let inspection := Algebraic.Sidecar.inspectImaginary _ original
  match inspection.compared.left.scalar?, inspection.compared.right.scalar?,
      inspection.compared.materialize.difference.scalar? with
  | some left, some right, some difference =>
      unless left.value = ⟨0, -1⟩ ∧ right.value = imaginary ∧ difference.value = ⟨0, 2⟩ do
        throw (IO.userError "imaginary inspection changed its original owners or ordered difference")
  | _, _, _ => throw (IO.userError "imaginary inspection lost a retained original scalar cache")
  match inspection.compared.decision with
  | .excluded _ => throw (IO.userError "a nonreal algebraic input lost its prepared imaginary difference")
  | .prepared prepared =>
      unless 0 < prepared.apart.certificate.lowerSq do
        throw (IO.userError "imaginary inspection lost its prepared difference floor")
  let real := Algebraic.Sidecar.ofRational (RationalSidecar.exact 1)
  match (Algebraic.Sidecar.inspectImaginary _ real).compared.decision with
  | .excluded _ => pure ()
  | .prepared _ => throw (IO.userError "a real algebraic input lost its zero imaginary-difference decision")

#eval checkConstruction
#eval checkUnaryConstruction
#eval checkImaginaryConstruction

end TestPurelib.Approximation.Gaussian.AlgebraicConstruction
