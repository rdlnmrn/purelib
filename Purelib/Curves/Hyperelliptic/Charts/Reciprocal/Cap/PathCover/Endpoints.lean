module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
public import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial.Endpoints
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Approximation.Gaussian.Equivalence

/-! # Endpoint Point owners on original cap comparison parents

Each supplied Point remains its original continued value. Patch ownership
and exact affine endpoint identities compare its generator with the retained
parent endpoint generator without preparing a substitute Point.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.ParentData

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (Point)
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {genus count : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {differential : Differential genus} {parent : Parent curve differential}

/-- An original requested starting Point has the same generator as the parent's retained first Point. -/
def firstPoint_owner (data : ParentData cap differential count parent)
    (coordinate : Spatial.Coordinate data.segment.comparison.first data.segment.comparison.last)
    (sample : Point data.terminal.neighborhood.patch (coordinate.point 0)) :
    NamedEquivalent data.data.first.point.certificate.value.name sample.certificate.value.name :=
  data.first_owner.symm.trans
    (pointEquivalent data.patch data.terminal.neighborhood.patch data.patch_eq 0 (by decide +kernel)
      (data.first_eq.symm.trans coordinate.point_zero.symm)
      (coordinate.point_inside data.segment.firstInside data.segment.lastInside
        (by decide +kernel) (by decide +kernel)) sample)

/-- An original requested finishing Point has the same generator as the parent's retained last Point. -/
def lastPoint_owner (data : ParentData cap differential count parent)
    (coordinate : Spatial.Coordinate data.segment.comparison.first data.segment.comparison.last)
    (sample : Point data.terminal.neighborhood.patch (coordinate.point 1)) :
    NamedEquivalent data.data.last.point.certificate.value.name sample.certificate.value.name :=
  data.last_owner.symm.trans
    (pointEquivalent data.patch data.terminal.neighborhood.patch data.patch_eq 1 (by decide +kernel)
      (data.last_eq.symm.trans coordinate.point_one.symm)
      (coordinate.point_inside data.segment.firstInside data.segment.lastInside
        (by decide +kernel) (by decide +kernel)) sample)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.ParentData

end
