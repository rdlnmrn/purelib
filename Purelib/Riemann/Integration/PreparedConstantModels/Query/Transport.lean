module

public import Purelib.Riemann.Integration.PreparedConstantModels.Query

/-! # Whole direct-query transport along equality of the original prepared edge

Equality elimination preserves the complete original queried Owner and its
whole factory certificate. The query, its direct Owner and physical-index
Owner remain the same heterogeneous values; no query or source is rebuilt.
-/

public section

namespace Purelib.Riemann.Integration.PreparedConstantModels.PreparedEdge.Query

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
    {first last : PreparedEdge curve differential} {time : Rational} {inside : 0 ≤ time ∧ time ≤ 1}

/-- Reindex the complete original query and factory certificate along equality of the SAME prepared edge. -/
@[expose] def castEdge (equal : first = last) (query : Query first time inside) : Query last time inside := by
  cases equal
  exact query

/-- Exact edge transport retains the entire original Query, including its direct Owner and whole factory equation. -/
theorem castEdge_heq (equal : first = last) (query : Query first time inside) :
    HEq (castEdge equal query) query := by
  cases equal
  unfold castEdge
  rfl

/-- Exact edge transport retains the SAME complete original direct Owner heterogeneously. -/
theorem castEdge_direct_heq (equal : first = last) (query : Query first time inside) :
    HEq (castEdge equal query).direct query.direct := by
  cases equal
  unfold castEdge
  rfl

/-- Exact edge transport retains the SAME complete physical-index query Owner heterogeneously. -/
theorem castEdge_owner_heq (equal : first = last) (query : Query first time inside) :
    HEq (castEdge equal query).owner query.owner := by
  cases equal
  unfold castEdge
  rfl

end Purelib.Riemann.Integration.PreparedConstantModels.PreparedEdge.Query

end
