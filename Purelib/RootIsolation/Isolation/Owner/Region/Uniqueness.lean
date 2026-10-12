module

import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Count
import Purelib.RootIsolation.Track.Newton.Build
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Tactic.QuotientFreeOmega

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Isolation.Owner.Region.Uniqueness

open Purelib.Data.Gaussian

/-- Two winding-one states carried by the same winding-one region cannot be
positively separated.  A further strict refinement of each state would split
the region into two contributions of raw winding at least four, contradicting
the region's displayed raw winding four. -/
private theorem windingOneStates_not_separated_in_region
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
      Purelib.Geometry.Rational.Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p
      degreeBound)
    (region left right : Purelib.RootIsolation.State.WindingOne.Basic.WindingOneState p ambient)
    (leftRefines : left.box.Refines region.box)
    (rightRefines : right.box.Refines region.box) :
    ¬left.box.Separated right.box := open Purelib.Geometry.Rational in open Purelib.Polynomial in open
      Purelib.RootIsolation in by
  intro separated
  let leftTrack := Track.Newton.Build.ofInitial degreeAtLeastTwo squarefree
    elimination left
  let rightTrack := Track.Newton.Build.ofInitial degreeAtLeastTwo squarefree
    elimination right
  let leftSmall := leftTrack.refine left 1 (by decide)
  let rightSmall := rightTrack.refine right 1 (by decide)
  have leftNested : leftSmall.box.Refines left.box :=
    leftTrack.nested left 1 (by decide)
  have rightNested : rightSmall.box.Refines right.box :=
    rightTrack.nested right 1 (by decide)
  have smallSeparated : leftSmall.box.Separated rightSmall.box :=
    separated.of_refines leftNested rightNested
  have leftInside : leftSmall.box.StrictInterior region.box :=
    (Geometry.Rational.Box.Refinement.StrictInterior.Boxes.trans_refines (leftTrack.strict left 1 (by decide)))
        leftRefines
  have rightInside : rightSmall.box.StrictInterior region.box :=
    (Geometry.Rational.Box.Refinement.StrictInterior.Boxes.trans_refines (rightTrack.strict right 1 (by decide)))
        rightRefines
  let clearRegion : Clearance.Box.Region.ClearRegion p ambient :=
    { box := region.box
      refinesAmbient := region.refinesAmbient
      proper := region.proper
      clearance := region.clearance }
  have atLeastEight := State.WindingOne.Count.region_rawWinding_ge_eight_of_separated
    degreeAtLeastTwo squarefree elimination clearRegion leftSmall rightSmall
      leftInside rightInside smallSeparated
  have exactlyFour := region.rawWindingFour
  dsimp only [clearRegion] at atLeastEight
  rw [exactlyFour] at atLeastEight
  omega
end Purelib.RootIsolation.Isolation.Owner.Region.Uniqueness

end
