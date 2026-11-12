module

public import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
public import Purelib.Integration.Partition.Interval.Chain.Indexed
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # Exact interval chains of the original centered subdivision

The retained subdivision and same center family determine its ordered
parameter intervals. Their endpoint chain and nonnegative widths follow
from the original constructors, including zero-width accepted steps.
-/

public section

namespace Purelib.Riemann.Integration.PreparedSubdivisionModelCore

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.List
open Purelib.Integration.Partition (Interval)
open Purelib.Polynomial
open Purelib.Riemann.Branches

namespace CenteredEdge

/-- Read the two original parameter endpoints without replacing the centered edge or its source/request owners. -/
@[expose] def parameterInterval {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus} (centered : CenteredEdge curve differential) : Interval :=
  ⟨centered.edge.left.parameter, centered.edge.request.endpoint.parameter⟩

end CenteredEdge

/-- The SAME ordered centered subdivision intervals chain its original left endpoint to its actual terminal endpoint. -/
theorem centeredEdges_chain {genus : Nat}
    (curve : HyperellipticCurve genus) (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : ClearSheetContinuation.Subdivision.Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))} (sheet : Fin 2) :
    (subdivision : PreparedSubdivision segment within left owner) →
    (centers : CenterStates curve differential sheet subdivision) →
    Interval.Chain left.parameter subdivision.endpoint.parameter
      ((centeredEdges curve differential sheet subdivision centers).map CenteredEdge.parameterInterval)
  | .stop current owner, _ => .nil current.parameter
  | .next current owner _request _cached _ordered _small remaining, centers =>
      .cons (centeredEdges_chain curve differential sheet remaining centers.2)

/-- Every original centered child has nonnegative parameter width, including a retained zero-width step. -/
theorem centeredEdges_ordered {genus : Nat}
    (curve : HyperellipticCurve genus) (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : ClearSheetContinuation.Subdivision.Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))} (sheet : Fin 2)
    (subdivision : PreparedSubdivision segment within left owner)
    (centers : CenterStates curve differential sheet subdivision) :
    ∀ centered ∈ centeredEdges curve differential sheet subdivision centers,
      0 ≤ centered.parameterInterval.finish - centered.parameterInterval.start := by
  induction subdivision with
  | stop endpoint owner =>
      intro centered membership
      change centered ∈ [] at membership
      cases membership
  | @next left owner request cached ordered small remaining induction =>
      intro centered membership
      change centered ∈ _ :: _ at membership
      rcases Membership.mem_cons.mp membership with equal | membership
      · subst centered
        exact Data.Rat.Fraction.Order.Arithmetic.sub_nonneg_direct ordered
      · exact induction centers.2 centered membership

end Purelib.Riemann.Integration.PreparedSubdivisionModelCore

end
