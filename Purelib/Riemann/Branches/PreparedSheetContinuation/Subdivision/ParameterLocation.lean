module

public import Purelib.Riemann.Branches.PreparedSheetContinuation
public import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # A half-open query position in the same retained prepared subdivision

Finite selection skips stationary accepted requests and reads the first
actual request whose upper parameter exceeds the query. The result is
only an original branch position and local fraction. It acquires no root,
preparation, center observation, trace or query during lookup.
-/

public section

namespace Purelib.Riemann.Branches.PreparedSheetContinuation.Subdivision

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Integration
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore
  (edgeOfStep edgeOfStep_point CenterStates CenteredEdge centeredEdges)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
variable {ambient : Box} {start finish : Canonical} {segment : ClearSegment curve.polynomial ambient start finish}
variable {within : segment.WithinAmbient}

/-- An exact branch position and bounded local fraction in the SAME retained subdivision.

The existing Sum/Subtype containers retain the literal selected request
through their subdivision index. No request, cache or Owner is copied into
an independent preparation, and an empty word has no half-open position.
-/
@[expose] def ParameterLocation (time : Rational) :
    {left : Endpoint} → {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))} →
      Subdivision segment within left owner → Type
  | _, _, .stop _ _ => Empty
  | left, _, .next _ _ request _ _ _ remaining =>
      Sum {fraction : Rational // (0 ≤ fraction ∧ fraction ≤ 1) ∧ parameterAt left request fraction = time}
        (ParameterLocation time remaining)

/-- Locate the first actual half-open request at the supplied global segment parameter.

The terminal upper bound rules out nil. Each rejected head passes the same
parameter into the literal stored tail. A chosen head has positive width,
so its exact normalized fraction is executable even when other requests
are stationary or repeated.
-/
def locateParameter (time : Rational) :
    {left : Endpoint} → {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))} →
    (subdivision : Subdivision segment within left owner) →
    left.parameter ≤ time → time < subdivision.endpoint.parameter → ParameterLocation time subdivision
  | _, _, .stop _ _, lower, upper => False.elim (upper.2 lower)
  | left, _, .next _ _ request _ _ _ remaining, lower, upper =>
      if before : time < request.endpoint.parameter then
        let proper : left.parameter < request.endpoint.parameter :=
          ⟨lower.trans before.1, fun reverse => before.2 (reverse.trans lower)⟩
        let fraction := (time - left.parameter) / (request.endpoint.parameter - left.parameter)
        let inside := Field.fraction_inside proper ⟨lower, before.1⟩
        let same : parameterAt left request fraction = time := by
          rewrite [parameterAt_eq_affine]
          have product := Data.Rat.Fraction.Field.div_mul_cancel_of_ne
            (time - left.parameter) (request.endpoint.parameter - left.parameter)
            (ne_of_gt (Arithmetic.sub_pos_direct proper))
          change left.parameter + fraction * (request.endpoint.parameter - left.parameter) = time
          rewrite [product]
          ring1
        Sum.inl ⟨fraction, inside, same⟩
      else Sum.inr (locateParameter time remaining (Arithmetic.le_of_not_gt_direct before) upper)

namespace ParameterLocation

variable {time : Rational} {left : Endpoint}
variable {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
variable {subdivision : Subdivision segment within left owner}

/-- Read the original accepted-step edge from the selected literal branch, using its SAME cached source and request. -/
@[expose] def edge (differential : Differential genus) (sheet : Fin 2) :
    {left : Endpoint} → {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))} →
    {subdivision : Subdivision segment within left owner} → ParameterLocation time subdivision →
      PreparedConstantModels.PreparedEdge curve differential
  | _, _, .stop _ _ => fun absent => Empty.elim absent
  | left, owner, .next _ _ request cached ordered small remaining => fun location =>
      match (show Sum
          {fraction : Rational // (0 ≤ fraction ∧ fraction ≤ 1) ∧ parameterAt left request fraction = time}
          (ParameterLocation time remaining) from location) with
      | Sum.inl _ =>
          edgeOfStep curve differential segment within left owner request cached ordered small sheet
      | Sum.inr rest => edge differential sheet rest

/-- Read the selected local query parameter, preserving its original normalized branch fraction. -/
@[expose] def fraction : {left : Endpoint} →
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))} →
    {subdivision : Subdivision segment within left owner} → ParameterLocation time subdivision → Rational
  | _, _, .stop _ _ => fun absent => Empty.elim absent
  | left, _, .next _ _ request _ _ _ remaining => fun location =>
      match (show Sum
          {fraction : Rational // (0 ≤ fraction ∧ fraction ≤ 1) ∧ parameterAt left request fraction = time}
          (ParameterLocation time remaining) from location) with
      | Sum.inl found => found.val
      | Sum.inr rest => fraction rest

/-- Every selected local fraction lies in its original accepted step's closed unit interval. -/
theorem inside : {left : Endpoint} →
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))} →
    {subdivision : Subdivision segment within left owner} → (location : ParameterLocation time subdivision) →
      0 ≤ location.fraction ∧ location.fraction ≤ 1
  | _, _, .stop _ _ => fun absent => Empty.elim absent
  | left, _, .next _ _ request _ _ _ remaining => fun location =>
      match (show Sum
          {fraction : Rational // (0 ≤ fraction ∧ fraction ≤ 1) ∧ parameterAt left request fraction = time}
          (ParameterLocation time remaining) from location) with
      | Sum.inl found => found.property.1
      | Sum.inr rest => inside rest

/-- The selected original edge point is the requested global parameter on the SAME original clear segment. -/
theorem point_eq (differential : Differential genus) (sheet : Fin 2) :
    {left : Endpoint} → {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))} →
    {subdivision : Subdivision segment within left owner} → (location : ParameterLocation time subdivision) →
      (location.edge differential sheet).point location.fraction = segment.pointAt time
  | _, _, .stop _ _ => fun absent => Empty.elim absent
  | left, owner, .next _ _ request cached ordered small remaining => fun location =>
      match (show Sum
          {fraction : Rational // (0 ≤ fraction ∧ fraction ≤ 1) ∧ parameterAt left request fraction = time}
          (ParameterLocation time remaining) from location) with
      | Sum.inl found =>
          (edgeOfStep_point curve differential segment within left owner request cached ordered small
            sheet found.val).trans
            (congrArg segment.pointAt found.property.2)
      | Sum.inr rest => point_eq differential sheet rest

/-- Read the exact original accepted-request occurrence index, including skipped stationary requests. -/
@[expose] def index : {left : Endpoint} → {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))} →
    {subdivision : Subdivision segment within left owner} → ParameterLocation time subdivision →
      Fin subdivision.requests.length
  | _, _, .stop _ _ => fun absent => Empty.elim absent
  | left, _, .next _ _ request _ _ _ remaining => fun location =>
      match (show Sum
          {fraction : Rational // (0 ≤ fraction ∧ fraction ≤ 1) ∧ parameterAt left request fraction = time}
          (ParameterLocation time remaining) from location) with
      | Sum.inl _ => ⟨0, Nat.zero_lt_succ _⟩
      | Sum.inr rest => (index rest).succ

/-- Read the same selected occurrence as a bounded index of the ORIGINAL prepared-edge list. -/
@[expose] def edgeIndex (differential : Differential genus) (sheet : Fin 2) :
    {left : Endpoint} → {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))} →
    {subdivision : Subdivision segment within left owner} → ParameterLocation time subdivision →
      Fin (PreparedSubdivisionModelCore.preparedEdges curve differential sheet subdivision).length
  | _, _, .stop _ _ => fun absent => Empty.elim absent
  | left, _, .next _ _ request _ _ _ remaining => fun location =>
      match (show Sum
          {fraction : Rational // (0 ≤ fraction ∧ fraction ≤ 1) ∧ parameterAt left request fraction = time}
          (ParameterLocation time remaining) from location) with
      | Sum.inl _ => ⟨0, Nat.zero_lt_succ _⟩
      | Sum.inr rest => (edgeIndex differential sheet rest).succ

/-- The selected prepared-edge position is the exact same raw request occurrence, including stationary prefixes. -/
theorem edgeIndex_val (differential : Differential genus) (sheet : Fin 2) :
    {left : Endpoint} → {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))} →
    {subdivision : Subdivision segment within left owner} → (location : ParameterLocation time subdivision) →
      (location.edgeIndex differential sheet).val = location.index.val
  | _, _, .stop _ _ => fun absent => Empty.elim absent
  | left, _, .next _ _ request _ _ _ remaining => fun location =>
      match (show Sum
          {fraction : Rational // (0 ≤ fraction ∧ fraction ≤ 1) ∧ parameterAt left request fraction = time}
          (ParameterLocation time remaining) from location) with
      | Sum.inl _ => rfl
      | Sum.inr rest => congrArg Nat.succ (edgeIndex_val differential sheet rest)

/-- The exact indexed original prepared edge is the SAME whole selected edge, including its cached source/request.

The explicit retained index bound is used by the original list reader.
This is equality of complete original data, not equality of coordinates,
sheet labels or an independently reconstructed Owner.
-/
theorem edge_at (differential : Differential genus) (sheet : Fin 2) :
    {left : Endpoint} → {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))} →
    {subdivision : Subdivision segment within left owner} → (location : ParameterLocation time subdivision) →
      (PreparedSubdivisionModelCore.preparedEdges curve differential sheet
        subdivision)[(location.edgeIndex differential sheet).val]'(location.edgeIndex differential sheet).isLt =
          location.edge differential sheet
  | _, _, .stop _ _ => fun absent => Empty.elim absent
  | left, _, .next _ _ request _ _ _ remaining => fun location =>
      match (show Sum
          {fraction : Rational // (0 ≤ fraction ∧ fraction ≤ 1) ∧ parameterAt left request fraction = time}
          (ParameterLocation time remaining) from location) with
      | Sum.inl _ => rfl
      | Sum.inr rest => edge_at differential sheet rest

/-- The selected edge is a literal member of the original centered family for ANY supplied complete center cache.

This theorem is erased. It does not execute canonical center observations
when the actual runtime consumer only needs its original root query.
-/
theorem centered_member (differential : Differential genus) (sheet : Fin 2) :
    {left : Endpoint} → {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))} →
    {subdivision : Subdivision segment within left owner} → (location : ParameterLocation time subdivision) →
    (centers : CenterStates curve differential sheet subdivision) →
      ∃ parent : CenteredEdge curve differential,
        parent ∈ centeredEdges curve differential sheet subdivision centers ∧
          parent.edge = location.edge differential sheet
  | _, _, .stop _ _ => fun absent _ => Empty.elim absent
  | left, owner, .next _ _ request cached ordered small remaining => fun location centers =>
      match (show Sum
          {fraction : Rational // (0 ≤ fraction ∧ fraction ≤ 1) ∧ parameterAt left request fraction = time}
          (ParameterLocation time remaining) from location) with
      | Sum.inl _ =>
          ⟨⟨edgeOfStep curve differential segment within left owner request cached ordered small sheet, centers.1⟩,
            List.mem_cons_self, rfl⟩
      | Sum.inr rest => by
          obtain ⟨parent, member, same⟩ := centered_member differential sheet rest centers.2
          exact ⟨parent, List.mem_cons_of_mem _ member, same⟩

end ParameterLocation
end Purelib.Riemann.Branches.PreparedSheetContinuation.Subdivision

end
