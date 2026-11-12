module
import Purelib.Data.Rat.Fraction.Basic
public import Purelib.RootIsolation.FTA.Squarefree.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
public import Purelib.RootIsolation.Exact.Ownership.Prepare
public import Purelib.RootIsolation.Exact.Ownership.Cardinality
import Purelib.RootIsolation.FTA.Squarefree.Input

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.RootIsolation.Exact.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Polynomial

open Purelib.RootIsolation

open Purelib.Data.Rat.Fraction (Rational)

section
@[expose] public section

/-!
# Choice-free box-only finite constructive FTA

This is the paper-facing numerical layer over the explicit constructive
fraction and Gaussian representations.  The squarefree certificate is finite
dense extended-Euclid data.  Both axis eliminants are computed internally by
the fraction-free separated Sylvester construction.
-/

namespace Purelib.RootIsolation.FTA.Squarefree.Build.BoxFTA

/-- Attach original ownership and maximality to one retained complete isolation.

The supplied family keeps its original ordered tracks and support. Both
the owner selector and finite maximality certificate refer to the same
polynomial and isolation, without running another isolation producer.
An optional exact elimination cache is retained inside the ownership callback
and consumed when that callback is demanded. The absent cache preserves the
original complete result and its lazy ownership construction.
-/
def fromIsolation {p : CoefficientPolynomial} (input : FTA.Squarefree.Input p)
    (isolation : Exact.Basic.Output p (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p) p.natDegree)
    (cached : Option {value : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p
      input.eliminationDegree // value = input.elimination} := none) :
    FTA.Squarefree.BoxResult p :=
  { eliminationDegree := input.eliminationDegree
    elimination := fun _ => match cached with
      | none => input.elimination
      | some retained => retained.val
    isolation := isolation
    ownership := fun track supported =>
      let elimination := match cached with
        | none => input.elimination
        | some retained => retained.val
      Exact.Ownership.Prepare.selectOutputOwner
        input.degreeAtLeastTwo input.squarefree elimination isolation track supported
    maximality := input.familyCardLe }

/-- Attach the same original numerical result to its checked elimination and requested isolation. -/
def ofPrepared {p : CoefficientPolynomial} {input : FTA.Squarefree.Input p} {request : Option Rational}
    (prepared : FTA.Squarefree.Input.Prepared input request) : FTA.Squarefree.BoxResult p :=
  fromIsolation input prepared.isolation (some ⟨prepared.elimination, prepared.elimination_eq⟩)

/-- Standalone choice-free box-only finite RFAP. -/
def prove {p : CoefficientPolynomial} (input : FTA.Squarefree.Input p)
    (request : Option Rational := none) : FTA.Squarefree.BoxResult p :=
  ofPrepared (input.prepare request)

/-- A retained isolation equal to the original constructor gives the complete original box result. -/
theorem fromIsolation_eq_prove {p : CoefficientPolynomial} (input : FTA.Squarefree.Input p)
    (isolation : Exact.Basic.Output p (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p) p.natDegree)
    {request : Option Rational} (same : isolation = input.isolation request) :
    fromIsolation input isolation = prove input request :=
  congrArg (fromIsolation input) same

/-- Degree-greater-than-one specialization with an explicit finite
squarefree certificate.  A later irreducibility wrapper may compute this
certificate, but the trusted numerical theorem needs no sparse or
infinite-root interface. -/
def proveDegreeGtOne
    {p : CoefficientPolynomial} (squarefree :
      Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (degree : 1 < p.natDegree) (request : Option Rational := none) : FTA.Squarefree.BoxResult p :=
  prove { squarefree := squarefree, degreeAtLeastTwo := degree } request
/-- The absent event request preserves the complete original coefficient-selected box result. -/
theorem prove_none {p : CoefficientPolynomial} (input : FTA.Squarefree.Input p) :
    prove input none = fromIsolation input input.isolation := rfl

/-- The original box constructor retains each complete Newton track at its actual degree index. -/
theorem prove_trackAt_origin
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (input : Input p)
    (request : Option Rational) (index : Fin p.natDegree) :
    Track.Newton.Build.Origin input.degreeAtLeastTwo input.squarefree input.elimination
      ((prove input request).isolation.trackAt index) :=
  input.isolation_trackAt_origin request index

/-- Retained preparation preserves the complete original isolation and owner-selection result. -/
theorem ofPrepared_eq_original {p : CoefficientPolynomial} {input : FTA.Squarefree.Input p} {request : Option Rational}
    (prepared : FTA.Squarefree.Input.Prepared input request) :
    ofPrepared prepared =
      ({ eliminationDegree := input.eliminationDegree
         elimination := fun _ => input.elimination
         isolation := input.isolation request
         ownership := fun track supported =>
           Exact.Ownership.Prepare.selectOutputOwner
             input.degreeAtLeastTwo input.squarefree input.elimination (input.isolation request) track supported
         maximality := input.familyCardLe } : FTA.Squarefree.BoxResult p) := by
  rcases prepared with ⟨elimination, eliminationEq, isolation, isolationEq⟩
  cases eliminationEq
  cases isolationEq
  rfl

/-- The cached builder agrees with the complete original numerical FTA result, including its owner procedure. -/
theorem prove_eq_original {p : CoefficientPolynomial} (input : FTA.Squarefree.Input p)
    (request : Option Rational := none) :
    prove input request =
      ({ eliminationDegree := input.eliminationDegree
         elimination := fun _ => input.elimination
         isolation := input.isolation request
         ownership := fun track supported =>
           Exact.Ownership.Prepare.selectOutputOwner
             input.degreeAtLeastTwo input.squarefree input.elimination (input.isolation request) track supported
         maximality := input.familyCardLe } : FTA.Squarefree.BoxResult p) := rfl

/-- A restored original preparation returns the same complete canonical numerical FTA result. -/
theorem ofPrepared_eq_prove {p : CoefficientPolynomial} {input : FTA.Squarefree.Input p} {request : Option Rational}
    (prepared : FTA.Squarefree.Input.Prepared input request) : ofPrepared prepared = prove input request :=
  (ofPrepared_eq_original prepared).trans (prove_eq_original input request).symm

/-- Equal original coefficient polynomials transport the complete same numerical FTA procedure and output. -/
theorem prove_transport {source target : CoefficientPolynomial} (equal : source = target)
    (input : FTA.Squarefree.Input source) (request : Option Rational := none) :
    (show FTA.Squarefree.BoxResult target from equal ▸ prove input request) =
      prove (show FTA.Squarefree.Input target from equal ▸ input) request := by
  cases equal
  rfl

end Purelib.RootIsolation.FTA.Squarefree.Build.BoxFTA

end

public section

namespace Purelib.RootIsolation.FTA.Squarefree.Build.BoxFTA

/-- A supplied exact elimination cache preserves the complete original box result.

Ownership consumes the selected actual certificate. The whole readback
retains every original track, support and maximality certificate.
-/
theorem fromIsolation_cached_eq_default {p : CoefficientPolynomial} (input : FTA.Squarefree.Input p)
    (isolation : Exact.Basic.Output p (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p) p.natDegree)
    (cached : Option {value : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p
      input.eliminationDegree // value = input.elimination}) :
    fromIsolation input isolation cached = fromIsolation input isolation := by
  cases cached with
  | none => rfl
  | some retained =>
      rcases retained with ⟨value, same⟩
      cases same
      rfl

end Purelib.RootIsolation.FTA.Squarefree.Build.BoxFTA

end
section
@[expose] public section

/-!
# Choice-free box/CCL finite FTA interface

The winding calculation supplies the exact degree-many family and the total
shrinking box tracks.  Each finite accuracy request computes a nonzero
rational sample of its refined box, converts that sample to a canonical
Gaussian-integer fraction, and runs the terminating CCL encoder.  Thus the box
and projective records are carried together without extracting a quotient
representative or naming a completed root.
-/

namespace Purelib.RootIsolation.FTA.Squarefree.Build.Box

/-- Choice-free degree-many box isolation equipped with finite CCL requests. -/
def prove {p :
  CoefficientPolynomial}
    (input : RootIsolation.FTA.Squarefree.Input p)
    (request : Option Rational := none) : FTA.Squarefree.AdapterResult p :=
  ⟨FTA.Squarefree.Build.BoxFTA.prove input request⟩

/-- Degree-greater-than-one specialization from explicit finite squarefree
Bézout data. -/
def proveDegreeGtOne {p :
  CoefficientPolynomial}
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (degree : 1 < p.natDegree) (request : Option Rational := none) : FTA.Squarefree.AdapterResult p :=
  prove ⟨squarefree, degree⟩ request
end Purelib.RootIsolation.FTA.Squarefree.Build.Box

end
