module
import Purelib.Data.Nat.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyTriangles
import Init.Data.Nat.MinMax
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces

/-! Reuse a prepared family's scalar requests at a later shared numerical
index. Only the floor changes; the component preparations and their cached
maximum are retained. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyLateRequests

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies

public section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms (CutCycleProgram)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies (PrimitiveFamily)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily (Budget)
open Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds (Coordinate)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {source :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {count : Nat}
  {programs : Data.Vector
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgram lifted source) count}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
    base.faces.regulars} {differential : Fin genus}
  {family : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily programs domains
    differential}
  {targets : Data.Vector Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds.Coordinate count}
  {floor : Nat}

/-- Raise the retained period-family budget to a supplied sufficient index while reusing its original component requests
and cached maximum.

The retained requests and maximum remain fixed while the supplied later index replaces the original floor. -/
@[expose] def atIndex (budget : PrimitiveFamily.Budget family targets floor) (index : Nat) (later : budget.index ≤
  index) :
    PrimitiveFamily.Budget family targets index where
  requests := budget.requests
  maximum := budget.maximum
  maximum_eq := budget.maximum_eq
  index := index
  index_eq := by
    have retained : max floor budget.maximum ≤ index := budget.index_eq ▸ later
    have maximumLater : budget.maximum ≤ index :=
      (Data.Nat.Order.le_max_right floor budget.maximum).trans retained
    exact (Nat.le_antisymm
      (Data.Nat.Order.max_le (Nat.le_refl index) maximumLater)
      (Data.Nat.Order.le_max_left index budget.maximum)).symm

/-- Raising the common index preserves the exact original component request bank. -/
theorem atIndex_requests (budget : PrimitiveFamily.Budget family targets floor) (index : Nat) (later : budget.index ≤
  index) :
    (FamilyLateRequests.atIndex budget index later).requests = budget.requests := rfl

/-- The raised budget has exactly the supplied retained common index. -/
theorem atIndex_index (budget : PrimitiveFamily.Budget family targets floor) (index : Nat) (later : budget.index ≤
  index) :
    (FamilyLateRequests.atIndex budget index later).index = index := rfl

end

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyLateRequests
