module

public import Purelib.Riemann.Integration.PreparedSubdivisionModelCore

/-! # Exact subdivision transport of the original retained center family

Equality transport preserves the complete already selected center states.
The original ordered centered-edge list is unchanged; no center, root query,
continuation, source model or observation is selected again.
-/

public section

namespace Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenterStates

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Owner Subdivision)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
variable {ambient : Box} {start finish : Canonical}
variable {segment : ClearSegment curve.polynomial ambient start finish} {within : segment.WithinAmbient}
variable {current : Endpoint} {owner : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
variable {sheet : Fin 2} {first last : Subdivision segment within current owner}

/-- Transport the SAME complete retained center family across exact equality of its original subdivision index. -/
@[expose] def castSubdivision (equal : first = last) (centers : CenterStates curve differential sheet first) :
    CenterStates curve differential sheet last := by
  cases equal
  exact centers

/-- The transported original center family retains its entire stored value heterogeneously. -/
theorem castSubdivision_heq (equal : first = last) (centers : CenterStates curve differential sheet first) :
    HEq (castSubdivision equal centers) centers := by
  cases equal
  rfl

/-- Exact subdivision transport preserves every original ordered centered edge and its actual selected state. -/
theorem castSubdivision_edges (equal : first = last) (centers : CenterStates curve differential sheet first) :
    centeredEdges curve differential sheet last (castSubdivision equal centers) =
      centeredEdges curve differential sheet first centers := by
  cases equal
  rfl

end Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenterStates

end
