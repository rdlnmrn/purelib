module

public import Purelib.Riemann.Branches.PreparedSheetContinuation.Subdivision.ParameterLocation
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore

/-! # The literal centered occurrence selected by a retained parameter location

The executable index follows the same raw accepted-request branches and the
supplied original center family. It constructs no center observation, root,
query or subdivision, and keeps skipped stationary requests in its index.
-/

public section

namespace Purelib.Riemann.Branches.PreparedSheetContinuation.Subdivision.ParameterLocation

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenterStates centeredEdges)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {genus : Nat} {curve : HyperellipticCurve genus}
variable {ambient : Box} {start finish : Canonical} {segment : ClearSegment curve.polynomial ambient start finish}
variable {within : segment.WithinAmbient} {time : Rational}

/-- Read the same raw occurrence as a bounded index of the supplied original centered-edge family. -/
@[expose] def centeredIndex (differential : Differential genus) (sheet : Fin 2) :
    {left : Endpoint} → {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))} →
    {subdivision : Subdivision segment within left owner} → (location : ParameterLocation time subdivision) →
    (centers : CenterStates curve differential sheet subdivision) →
      Fin (centeredEdges curve differential sheet subdivision centers).length
  | _, _, .stop _ _ => fun absent _ => Empty.elim absent
  | left, _, .next _ _ request _ _ _ remaining => fun location centers =>
      match (show Sum
          {fraction : Rational // (0 ≤ fraction ∧ fraction ≤ 1) ∧ parameterAt left request fraction = time}
          (ParameterLocation time remaining) from location) with
      | Sum.inl _ => ⟨0, Nat.zero_lt_succ _⟩
      | Sum.inr rest => (centeredIndex differential sheet rest centers.2).succ

/-- The selected centered position has the original raw request index, including skipped zero-width prefixes. -/
theorem centeredIndex_val (differential : Differential genus) (sheet : Fin 2) :
    {left : Endpoint} → {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))} →
    {subdivision : Subdivision segment within left owner} → (location : ParameterLocation time subdivision) →
    (centers : CenterStates curve differential sheet subdivision) →
      (location.centeredIndex differential sheet centers).val = location.index.val
  | _, _, .stop _ _ => fun absent _ => Empty.elim absent
  | left, _, .next _ _ request _ _ _ remaining => fun location centers =>
      match (show Sum
          {fraction : Rational // (0 ≤ fraction ∧ fraction ≤ 1) ∧ parameterAt left request fraction = time}
          (ParameterLocation time remaining) from location) with
      | Sum.inl _ => rfl
      | Sum.inr rest => congrArg Nat.succ (centeredIndex_val differential sheet rest centers.2)

/-- The complete selected centered parent owns the identical accepted-step edge and source cache used by the query. -/
theorem centeredEdge_at (differential : Differential genus) (sheet : Fin 2) :
    {left : Endpoint} → {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))} →
    {subdivision : Subdivision segment within left owner} → (location : ParameterLocation time subdivision) →
    (centers : CenterStates curve differential sheet subdivision) →
      ((centeredEdges curve differential sheet subdivision centers)[
        (location.centeredIndex differential sheet centers).val]'
          (location.centeredIndex differential sheet centers).isLt).edge = location.edge differential sheet
  | _, _, .stop _ _ => fun absent _ => Empty.elim absent
  | left, _, .next _ _ request _ _ _ remaining => fun location centers =>
      match (show Sum
          {fraction : Rational // (0 ≤ fraction ∧ fraction ≤ 1) ∧ parameterAt left request fraction = time}
          (ParameterLocation time remaining) from location) with
      | Sum.inl _ => rfl
      | Sum.inr rest => centeredEdge_at differential sheet rest centers.2

end Purelib.Riemann.Branches.PreparedSheetContinuation.Subdivision.ParameterLocation

end
