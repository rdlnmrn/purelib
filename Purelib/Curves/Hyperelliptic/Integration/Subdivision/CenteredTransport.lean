module
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuation
public import Purelib.Riemann.Integration.PreparedSubdivisionAutomaticModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.RootIsolation.SquareRoot.Subdivision.OwnerTransport
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation

open Purelib

open Purelib.Curves

open Purelib.Curves.Hyperelliptic

open Purelib.Geometry

open Purelib.Polynomial.Geometry

open Purelib.Riemann.Branches

open Purelib.Riemann.Branches.ClearSheetContinuation

open Purelib.Riemann.Integration

open Purelib.Riemann.Topology

open Purelib.RootIsolation.SquareRoot.Subdivision

section
@[expose] public section

/-!
# Aggregate A-backward quartic sample certificates

This module identifies the explicit 64-edge A-backward sample table with the
canonical centres stored by the completed prepared path.
-/

namespace Purelib.Curves.Hyperelliptic.Integration.Subdivision.CenteredTransport

/-- Transporting the retained initial root owner by equality preserves the canonical centered-edge list. -/
private theorem
  aBackwardCanonicalCenteredEdges_cast
    {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical}
    {segment : ClearPath.ClearSegment curve.polynomial ambient
      start finish}
    {within : segment.WithinAmbient}
    {left : Subdivision.Endpoint}
    {source target : SquareRootContinuationChain.Owner
      (curve.polynomial.eval (segment.pointAt left.parameter))}
    (differential : Differentials.Basic.Differential genus)
    (sheet : Fin 2) (equal : source = target)
    (data : PreparedSheetContinuation.Subdivision segment within
      left source) :
    PreparedSubdivisionModelCore.centeredEdges curve differential sheet
        (OwnerTransport.castSubdivisionOwner equal data)
        (PreparedSubdivisionAutomaticModels.canonicalCenterStates curve
          differential sheet (OwnerTransport.castSubdivisionOwner equal data)) =
      PreparedSubdivisionModelCore.centeredEdges curve differential sheet
        data
        (PreparedSubdivisionAutomaticModels.canonicalCenterStates curve
          differential sheet data) := by
  cases equal
  rfl

/-- Canonical centered edges agree across equal retained subdivisions.

The equality transports the original root owner and dependent subdivision data. -/
theorem
  aBackwardCanonicalCenteredEdges_heq
    {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical}
    {segment : ClearPath.ClearSegment curve.polynomial ambient
      start finish}
    {within : segment.WithinAmbient}
    {left : Subdivision.Endpoint}
    {firstOwner : SquareRootContinuationChain.Owner
      (curve.polynomial.eval (segment.pointAt left.parameter))}
    {secondOwner : SquareRootContinuationChain.Owner
      (curve.polynomial.eval (segment.pointAt left.parameter))}
    (differential : Differentials.Basic.Differential genus)
    (sheet : Fin 2)
    (first : PreparedSheetContinuation.Subdivision segment within
      left firstOwner)
    (second : PreparedSheetContinuation.Subdivision segment within
      left secondOwner)
    (ownerEqual : firstOwner = secondOwner)
    (equal : HEq first second) :
    PreparedSubdivisionModelCore.centeredEdges curve differential sheet
        first
        (PreparedSubdivisionAutomaticModels.canonicalCenterStates curve
          differential sheet first) =
      PreparedSubdivisionModelCore.centeredEdges curve differential sheet
        second
        (PreparedSubdivisionAutomaticModels.canonicalCenterStates curve
          differential sheet second) := by
  cases ownerEqual
  have dataEqual : first = second := eq_of_heq equal
  cases dataEqual
  rfl
end Purelib.Curves.Hyperelliptic.Integration.Subdivision.CenteredTransport

end

section
@[expose] public section

/-!
# Aggregate horizontal quartic sample certificates

This module connects the exact rational samples emitted by the standalone
Python generator to the 64 canonical centered edges of the prepared
A-forward horizontal connector, then aggregates the local error bounds by
finite Cauchy--Schwarz.
-/

namespace Purelib.Curves.Hyperelliptic.Integration.Subdivision.CenteredTransport

/-- Canonical centres are unchanged by a proof-only transport of the initial root owner. -/
theorem canonicalCenteredEdges_cast
    {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical}
    {segment : ClearPath.ClearSegment curve.polynomial ambient
      start finish}
    {within : segment.WithinAmbient}
    {left : Subdivision.Endpoint}
    {source target : SquareRootContinuationChain.Owner
      (curve.polynomial.eval (segment.pointAt left.parameter))}
    (differential : Differentials.Basic.Differential genus)
    (sheet : Fin 2) (equal : source = target)
    (data : PreparedSheetContinuation.Subdivision segment within
      left source) :
    PreparedSubdivisionModelCore.centeredEdges curve differential sheet
        (OwnerTransport.castSubdivisionOwner equal data)
        (PreparedSubdivisionAutomaticModels.canonicalCenterStates curve
          differential sheet (OwnerTransport.castSubdivisionOwner equal data)) =
      PreparedSubdivisionModelCore.centeredEdges curve differential sheet
        data
        (PreparedSubdivisionAutomaticModels.canonicalCenterStates curve
          differential sheet data) := by
  cases equal
  rfl

/-- Heterogeneously equal dependent subdivisions expose the same ordinary list of centred edges. -/
theorem canonicalCenteredEdges_heq
    {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical}
    {segment : ClearPath.ClearSegment curve.polynomial ambient
      start finish}
    {within : segment.WithinAmbient}
    {left : Subdivision.Endpoint}
    {firstOwner : SquareRootContinuationChain.Owner
      (curve.polynomial.eval (segment.pointAt left.parameter))}
    {secondOwner : SquareRootContinuationChain.Owner
      (curve.polynomial.eval (segment.pointAt left.parameter))}
    (differential : Differentials.Basic.Differential genus)
    (sheet : Fin 2)
    (first : PreparedSheetContinuation.Subdivision segment within
      left firstOwner)
    (second : PreparedSheetContinuation.Subdivision segment within
      left secondOwner)
    (ownerEqual : firstOwner = secondOwner)
    (equal : HEq first second) :
    PreparedSubdivisionModelCore.centeredEdges curve differential sheet
        first
        (PreparedSubdivisionAutomaticModels.canonicalCenterStates curve
          differential sheet first) =
      PreparedSubdivisionModelCore.centeredEdges curve differential sheet
        second
        (PreparedSubdivisionAutomaticModels.canonicalCenterStates curve
          differential sheet second) := by
  cases ownerEqual
  have dataEqual : first = second := eq_of_heq equal
  cases dataEqual
  rfl
end Purelib.Curves.Hyperelliptic.Integration.Subdivision.CenteredTransport

end
