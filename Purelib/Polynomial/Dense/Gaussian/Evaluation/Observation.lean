module

public import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Computation.Query.Computation

/-! # Retained exact polynomial readings at displayed rational points -/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Evaluation

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Computation.Query

set_option genInjectivity false in
/-- A cached exact value at its original polynomial and displayed point.

The value is executable data. Its equality certificate permits consumers
to reuse the value in root tests and quantitative refinement budgets.
-/
structure Reading (polynomial : CoefficientPolynomial) where
  /-- The original evaluation point. -/ point : Canonical
  /-- The computed polynomial value, retained once. -/ value : Canonical
  /-- The cache reads the same original polynomial at the same point. -/ valueEq : polynomial.eval point = value

namespace Reading

/-- Retain an already computed exact polynomial value at its original point. -/
@[expose] def ofValue (polynomial : CoefficientPolynomial) (point value : Canonical)
    (valueEq : polynomial.eval point = value) : Reading polynomial := ⟨point, value, valueEq⟩

/-- A certified point identity transports the same retained value to that requested original point. -/
theorem value_eq_at {polynomial : CoefficientPolynomial} (reading : Reading polynomial) (point : Canonical)
    (pointEq : reading.point = point) : reading.value = polynomial.eval point :=
  reading.valueEq.symm.trans (congrArg polynomial.eval pointEq)

set_option genInjectivity false in
/-- A polynomial reply whose retained point differs from the displayed request. -/
structure Mismatch where
  /-- The point requested by the original operation. -/ expected : Canonical
  /-- The different point retained in the actual reply. -/ reported : Canonical
  /-- The reply violates equality with the requested point. -/ different : reported ≠ expected

/-- Evaluate the original polynomial once and retain its exact point and value. -/
@[expose] def ofPoint (polynomial : CoefficientPolynomial) (point : Canonical) : Reading polynomial :=
  ⟨point, polynomial.eval point, rfl⟩

/-- Request a certified polynomial reading, rejecting a reply for a different original point. -/
@[expose] def request (polynomial : CoefficientPolynomial) (point : Canonical) :
    Protocol Canonical (Reading polynomial) (Except Mismatch {reply : Reading polynomial //
      reply.point = point}) :=
  (Protocol.query point).map fun reply =>
    if same : reply.point = point then .ok ⟨reply, same⟩ else .error ⟨point, reply.point, same⟩

/-- The original evaluator supplies the exact retained reading at the requested point. -/
theorem request_value (polynomial : CoefficientPolynomial) (point : Canonical) :
    ((request polynomial point).run (ofPoint polynomial)).value = .ok ⟨ofPoint polynomial point, rfl⟩ := by
  change ((if same : (ofPoint polynomial point).point = point then
    Except.ok ⟨ofPoint polynomial point, same⟩ else
      Except.error (⟨point, (ofPoint polynomial point).point, same⟩ : Mismatch)) :
    Except Mismatch {reply : Reading polynomial // reply.point = point}) = _
  rewrite [dif_pos (show (ofPoint polynomial point).point = point from rfl)]
  rfl

/-- A polynomial request records precisely the original point and its complete certified reply. -/
theorem request_trace (polynomial : CoefficientPolynomial) (point : Canonical)
    (oracle : Canonical → Reading polynomial) :
    ((request polynomial point).run oracle).trace = [⟨point, oracle point⟩] :=
  Protocol.map_run_trace _ _ _

end Reading

end Purelib.Polynomial.Dense.Gaussian.Evaluation
