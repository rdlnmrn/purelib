module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
public import Purelib.Riemann.RootContinuation.NewtonRequestedBoundary

public section

/-! The retained geometric inputs needed to compare original periods with
resplit words. No annular or determinant request is required. -/
section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.RootContinuation.NewtonRequestedBoundary (BoundaryPreparation)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}

namespace Purelib.Riemann.Periods.NewtonPeriodGeometry

open Purelib.Curves in
open Purelib.Data in
set_option genInjectivity false in
/-- The retained grid geometry of an original period preparation.

The record keeps the Newton preparation, its requested target and radius, and the exact lifted grid, domain bank and
point list. -/
structure PeriodGeometry (original : Hyperelliptic.Branches.BranchCellBank curve branches higher) where
  /-- The Newton preparation tied to the original period owner. -/ preparation : NewtonPreparation original
  /-- The retained Newton-grid target. -/ target : Rat.Fraction.Rational
  /-- The retained Newton-grid radius. -/ radius : Rat.Fraction.Rational
  /-- The Newton grid for this preparation, target and radius. -/ grid : NewtonGrid preparation target radius
  /-- The lifted structure on the retained Newton grid. -/ lifted : LiftedPuncturedGrid grid.punctured
  /-- The face-domain bank on the same retained grid and lifted structure. -/ domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames grid.faces.regulars
  /-- The retained finite list of geometric points. -/ points : List Gaussian.Basic.Canonical

constructive_injectivity PeriodGeometry

end Purelib.Riemann.Periods.NewtonPeriodGeometry

namespace Purelib.Riemann.RootContinuation.NewtonRequestedBoundary.BoundaryPreparation

open Purelib.Data in
/-- Read the period geometry already stored in a boundary preparation.

Reuse its exact Newton grid, lifted structure, domain bank and paid cut points without rebuilding them. -/
@[expose] def periodGeometry
    {preparation : NewtonPreparation original} {first second : Fin genus}
    {target radius : Rat.Fraction.Rational} {floor : Nat}
    (boundary : BoundaryPreparation preparation first second target radius floor) :
    Purelib.Riemann.Periods.NewtonPeriodGeometry.PeriodGeometry original :=
  ⟨preparation, _, _, boundary.fine.family.single.grid, boundary.lifted,
    boundary.domains, boundary.paid.cut.cuts.points⟩

end Purelib.Riemann.RootContinuation.NewtonRequestedBoundary.BoundaryPreparation

end
