module

public import Purelib.Riemann.RootContinuation.CoherentRoot.Chamber
public import Purelib.Riemann.RootContinuation.CoherentRoot.Arithmetic
public import Purelib.Riemann.RootContinuation.CoherentRoot.Arithmetic.Localization
import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Arithmetic retaining original continued input occurrences

Both input traces retain their original coefficient paths and endpoint owners.
Arithmetic is materialized on their actual initial and selected final caches.
Coincident arithmetic results retain both input occurrences; no squarefree
result family, constant degree or global branch selector is asserted.
-/

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot.Chamber

open Purelib.Polynomial.Dense.Companion (Operation)
open Purelib.RootIsolation.Progressive.Chamber.Frame (ChamberFrame)
open Purelib.RootIsolation.Progressive.Chamber.Path.Basic (ChamberPath)
open Purelib.Polynomial.Approximation.Gaussian renaming Arithmetic -> PolynomialArithmetic
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Polynomial.Approximation.Gaussian.Evaluation

namespace Root

/-- Compute original root arithmetic using both exact cached initial boxes and residuals.

Both original certified root records remain literal fields of the result.
The unchanged polynomial arithmetic consumes residuals authenticated against
those same original certificates, without recovering either chamber owner.
-/
@[expose] def arithmetic {firstFrame secondFrame : ChamberFrame}
    {firstIndex : firstFrame.Index} {secondIndex : secondFrame.Index} (operation : Operation)
    (first : Root firstFrame firstIndex) (second : Root secondFrame secondIndex) :
    CoherentRoot.Arithmetic operation first.certificate second.certificate :=
  let firstResidual := first.residualFromBox first.track.initial.box first.initial_box
  let secondResidual := second.residualFromBox second.track.initial.box second.initial_box
  let numeric := PolynomialArithmetic.ofResiduals operation firstResidual secondResidual
  let original : PolynomialArithmetic operation first.certificate.residualCertificate
      second.certificate.residualCertificate :=
    first.residualFromBox_eq first.track.initial.box first.initial_box ▸
      second.residualFromBox_eq second.track.initial.box second.initial_box ▸ numeric
  ⟨first.certificate, rfl, second.certificate, rfl, original⟩

/-- Transporting both authenticated residual indices preserves the complete original arithmetic record. -/
private theorem arithmetic_residuals_eq {firstFrame secondFrame : ChamberFrame}
    {firstIndex : firstFrame.Index} {secondIndex : secondFrame.Index} (operation : Operation)
    (first : Root firstFrame firstIndex) (second : Root secondFrame secondIndex)
    (firstResidual : Polynomial.Approximation.Gaussian.Residual firstFrame.polynomial first.certificate.value)
    (firstSame : firstResidual = first.certificate.residualCertificate)
    (secondResidual : Polynomial.Approximation.Gaussian.Residual secondFrame.polynomial second.certificate.value)
    (secondSame : secondResidual = second.certificate.residualCertificate) :
    (let numeric := PolynomialArithmetic.ofResiduals operation firstResidual secondResidual
     let original : PolynomialArithmetic operation first.certificate.residualCertificate
         second.certificate.residualCertificate := firstSame ▸ secondSame ▸ numeric
     (⟨first.certificate, rfl, second.certificate, rfl, original⟩ :
       CoherentRoot.Arithmetic operation first.certificate second.certificate)) =
      CoherentRoot.Arithmetic.ofRoots operation first.certificate second.certificate := by
  cases firstSame
  cases secondSame
  exact (CoherentRoot.Arithmetic.ofRoots_eq operation first.certificate second.certificate).symm

/-- Cached original-root arithmetic gives the complete original arithmetic record. -/
theorem arithmetic_eq {firstFrame secondFrame : ChamberFrame}
    {firstIndex : firstFrame.Index} {secondIndex : secondFrame.Index} (operation : Operation)
    (first : Root firstFrame firstIndex) (second : Root secondFrame secondIndex) :
    first.arithmetic operation second =
      CoherentRoot.Arithmetic.ofRoots operation first.certificate second.certificate :=
  arithmetic_residuals_eq operation first second
    (first.residualFromBox first.track.initial.box first.initial_box)
    (first.residualFromBox_eq first.track.initial.box first.initial_box)
    (second.residualFromBox second.track.initial.box second.initial_box)
    (second.residualFromBox_eq second.track.initial.box second.initial_box)

end Root

variable {firstStart firstFinish secondStart secondFinish : ChamberFrame}
variable {firstPath : ChamberPath firstStart firstFinish} {secondPath : ChamberPath secondStart secondFinish}
variable {firstIndex : firstStart.Index} {secondIndex : secondStart.Index}
variable {first : Root firstStart firstIndex} {second : Root secondStart secondIndex}

set_option genInjectivity false in
/-- Arithmetic on the actual initial and final caches of two original continued occurrences.

The traces remain indices of this certificate. Their original root owners,
path overlaps and branch matchings survive a coincidence of result values.
Each arithmetic cache retains its own computed polynomial and sample bounds.
-/
structure Arithmetic (operation : Operation) (firstTrace : Trace firstPath firstIndex first)
    (secondTrace : Trace secondPath secondIndex second) where
  /-- The actual arithmetic cache on the two original starting root certificates. -/
  initial : CoherentRoot.Arithmetic operation first.certificate second.certificate
  /-- The starting arithmetic consumes exactly the two original root caches. -/
  initial_eq : initial = CoherentRoot.Arithmetic.ofRoots operation first.certificate second.certificate
  /-- The actual arithmetic cache on the two selected original endpoint certificates. -/
  endpoint : CoherentRoot.Arithmetic operation firstTrace.endpoint.certificate secondTrace.endpoint.certificate
  /-- The endpoint arithmetic consumes exactly the two retained numerical endpoint caches. -/
  endpoint_eq : endpoint = CoherentRoot.Arithmetic.ofRoots operation
    firstTrace.endpoint.certificate secondTrace.endpoint.certificate

constructive_injectivity Arithmetic

namespace Arithmetic

/-- Compute arithmetic before and after two prepared original branch traces without a supplied result branch. -/
@[expose] def ofTraces (operation : Operation) (firstTrace : Trace firstPath firstIndex first)
    (secondTrace : Trace secondPath secondIndex second) : Arithmetic operation firstTrace secondTrace :=
  ⟨first.arithmetic operation second, Root.arithmetic_eq operation first second,
    firstTrace.endpoint.arithmetic operation secondTrace.endpoint,
    Root.arithmetic_eq operation firstTrace.endpoint secondTrace.endpoint⟩

variable {operation : Operation} {firstTrace : Trace firstPath firstIndex first}
variable {secondTrace : Trace secondPath secondIndex second}

/-- The unchanged coherent operation at the selected endpoints agrees with its actual stored sample program.

This compares two constructions at the same endpoint. The input values may
have changed along either original coefficient path.
-/
def endpointEquivalent (arithmetic : Arithmetic operation firstTrace secondTrace) :
    NamedEquivalent (PolynomialArithmetic.channel operation firstTrace.endpoint.certificate.value
      secondTrace.endpoint.certificate.value).name arithmetic.endpoint.result.toApproximation.toNamed :=
  arithmetic.endpoint.equivalent

/-- The endpoint operation satisfies its same computed polynomial equation, including repeated result roots. -/
def endpointEquation (arithmetic : Arithmetic operation firstTrace secondTrace) :
    NamedEquivalent (Horner.polynomialEval arithmetic.endpoint.polynomial
      (PolynomialArithmetic.channel operation firstTrace.endpoint.certificate.value
        secondTrace.endpoint.certificate.value)).name (Name.Coherent.CoherentNamed.Coherence.exact 0).name :=
  arithmetic.endpoint.equation

/-- Independent numerical arithmetic at the same two original endpoint occurrences agrees with the retained result.

The endpoint occurrence indices, rather than equal result polynomials or close
readings, identify both branches. Original winding certificates derive both
input comparisons, then coherent arithmetic computes the output budget.
-/
def compareEndpoint (arithmetic : Arithmetic operation firstTrace secondTrace)
    (firstEnd : Root firstFinish (firstPath.finalIndex firstIndex))
    (secondEnd : Root secondFinish (secondPath.finalIndex secondIndex))
    (other : CoherentRoot.Arithmetic operation firstEnd.certificate secondEnd.certificate) :
    NamedEquivalent arithmetic.endpoint.result.toApproximation.toNamed other.result.toApproximation.toNamed := by
  have left := firstTrace.endpoint.namedEquivalent firstEnd
  have right := secondTrace.endpoint.namedEquivalent secondEnd
  have operationEquivalent : NamedEquivalent
      (PolynomialArithmetic.channel operation firstTrace.endpoint.certificate.value
        secondTrace.endpoint.certificate.value).name
      (PolynomialArithmetic.channel operation firstEnd.certificate.value secondEnd.certificate.value).name := by
    cases operation with
    | add => exact Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects _ _ _ _ left right
    | mul => exact Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects _ _ _ _ left right
  exact NamedEquivalent.trans (NamedEquivalent.symm arithmetic.endpoint.equivalent)
    (NamedEquivalent.trans operationEquivalent other.equivalent)

/-- Oppositely ordered continued products coincide while retaining both original ordered input traces. -/
def productReverseEquivalent (forward : Arithmetic .mul firstTrace secondTrace)
    (backward : Arithmetic .mul secondTrace firstTrace) :
    NamedEquivalent forward.endpoint.result.toApproximation.toNamed backward.endpoint.result.toApproximation.toNamed :=
  NamedEquivalent.trans (NamedEquivalent.symm forward.endpoint.equivalent)
    (NamedEquivalent.trans (Name.Coherent.Arithmetic.Product.Laws.coherentMul_comm
      firstTrace.endpoint.certificate.value secondTrace.endpoint.certificate.value) backward.endpoint.equivalent)

set_option genInjectivity false in
/-- A retained endpoint arithmetic selection supplying exact zero or denominator preparation.

The selected root belongs to the actual endpoint arithmetic cache. Repeated
result roots are localized by the original multiplicity-aware procedure; neither
input path occurrence is replaced by the selected arithmetic result owner.
-/
structure EndpointPreparation (arithmetic : Arithmetic operation firstTrace secondTrace) where
  /-- The actual retained multiplicity localization and stable endpoint result selection. -/
  selection : CoherentRoot.Arithmetic.Selection arithmetic.endpoint

constructive_injectivity EndpointPreparation

/-- Compute the same endpoint arithmetic's exact selection once for repeated denominator decisions. -/
def prepareEndpoint (arithmetic : Arithmetic operation firstTrace secondTrace) : EndpointPreparation arithmetic :=
  ⟨arithmetic.endpoint.select⟩

/-- Return a certified original endpoint pole or a prepared denominator from the same retained selection.

An excluded result proves zero for this exact endpoint operation. It does not
assert a pole elsewhere on the path, or supply missing interior clearance.
-/
def EndpointPreparation.decide {arithmetic : Arithmetic operation firstTrace secondTrace}
    (prepared : EndpointPreparation arithmetic) : Division.Prepared.Decision
      (PolynomialArithmetic.channel operation firstTrace.endpoint.certificate.value
        secondTrace.endpoint.certificate.value) :=
  prepared.selection.decide

end Arithmetic

end Purelib.Riemann.RootContinuation.CoherentRoot.Chamber

end
