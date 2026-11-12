module

import Purelib.Riemann.RootContinuation.CoordinateRootReference
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Paths.PreparedPathClosure
import Purelib.Tactic.QuotientFreeOmega

/-! # Complete coordinate-reference construction agreement

The private historical builder is retained only for a quantified kernel
comparison of the complete path, ambient and all original certificates.
No native result or independent root/period identification is asserted.
-/

namespace TestPurelib.Riemann.RootContinuation.CoordinateRootReference

open Purelib
open Purelib.Riemann
open Purelib.Curves
open Purelib.Data
open Purelib.Polynomial
open Purelib.Riemann.RootContinuation.CoordinateRootReference
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate (coordinatePolynomial)

/-- The complete former coordinate-reference builder retained for kernel agreement. -/
private def formerBuild (base : Gaussian.Basic.Canonical) (nonzero : base ≠ 0) : WindingOneLoop
  coordinatePolynomial base :=
  let stem := connector base nonzero
  { ambient := ambient base
    path := (stem.val.append (square base)).append (Hyperelliptic.Branches.BranchCutLifts.ClearPath.reverse
      stem.val)
    within := (stem.property.append (square_within base)).append
      (Hyperelliptic.Branches.BranchCutLifts.ClearPath.reverse_withinAmbient stem.val stem.property)
    winding := by
      rw [Paths.PreparedPathClosure.ClearPath.rawWinding_append, Paths.PreparedPathClosure.ClearPath.rawWinding_append,
        Paths.PreparedPathClosure.ClearPath.rawWinding_reverse, square_winding]
      omega }

/-- Factoring the actual connector-loop-reverse preserves the complete former reference result. -/
private theorem whole_former_build (base : Gaussian.Basic.Canonical) (nonzero : base ≠ 0) :
    Purelib.Riemann.RootContinuation.CoordinateRootReference.build base nonzero = formerBuild base nonzero := by
  unfold Purelib.Riemann.RootContinuation.CoordinateRootReference.build formerBuild WindingOneLoop.rebase
  rfl

end TestPurelib.Riemann.RootContinuation.CoordinateRootReference
