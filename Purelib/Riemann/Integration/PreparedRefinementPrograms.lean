module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Riemann.Integration.PreparedOwnerClosedSchedules
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Topology.PreparedCycleModels

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
public import Purelib.Riemann.Periods.PreparedRootClosedPeriodBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodNonempty
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.GeometricBasis
import Purelib.Data.Vector.Basic
import Purelib.Riemann.Integration.PreparedOwnerClosedBridges
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Refinement
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Riemann.Readings.PreparedBoundaryClosure

public section

/-!
# Standard finite period programs

The generic finite refinement constructors live in
`PreparedRefinementProgramCore`, below the retained root-closed A/B banks.
This facade owns the standard-period acquisition and realization interfaces.
-/

namespace Purelib.Riemann.Integration.PreparedRefinementPrograms

open Purelib.Riemann.Curves.AlgebraicDifferentials
open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts

/-! ## Root-closed finite cycle realization -/

open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Branches in
set_option genInjectivity false in
/-- A raw symplectic basis or a retained ordered geometric period bank.

The ordered case keeps its original bank and geometric-basis certificate; its cycle readback is tied to that same
retained bank. -/
inductive PeriodCycleBasis {genus : Nat} (curve : Basic.HyperellipticCurve genus) : Type 4 where
  /-- The supplied original raw symplectic cycle basis. -/ | raw (basis : BranchCutLifts.SymplecticBasis curve)
  /-- The retained ordered paired period bank with its own geometric-basis certificate. -/ | ordered (bank :
    Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank curve) (geometry : bank.GeometricBasis)

constructive_injectivity PeriodCycleBasis

namespace PeriodCycleBasis

open Purelib.Curves.Hyperelliptic in
/-- Retain the supplied ordered period bank with its own geometric-basis certificate. -/
@[expose] def ofOrdered {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    (bank : Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank curve) : PeriodCycleBasis curve :=
  .ordered bank bank.geometricBasis

open Purelib.Curves.Hyperelliptic in
open Purelib.Geometry.Path.Gaussian in
/-- Read the exact paired cycles belonging to the selected raw or ordered basis. -/
@[expose] def cycles {genus : Nat} {curve : Basic.HyperellipticCurve genus} :
    PeriodCycleBasis curve → Lifted.Family.PairedCycleRefinements 2 genus
  | .raw basis => basis.cycles
  | .ordered bank _ => bank.periodData.cycles

open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Branches in
/-- Read the underlying raw symplectic model, using the curve's canonical model for an ordered bank. -/
@[expose] def model {genus : Nat} {curve : Basic.HyperellipticCurve genus} :
    PeriodCycleBasis curve → BranchCutLifts.SymplecticBasis curve
  | .raw basis => basis
  | .ordered _ _ => BranchCutLifts.symplecticBasis curve

end PeriodCycleBasis

open Purelib.Curves.Hyperelliptic in
open Purelib.Geometry.Path.Gaussian in
open Purelib.Riemann.Periods in
open Purelib.Riemann.Topology in
/-- An explicit relation between computed paired cycles and their retained geometric basis.

The alternatives retain root-closed A and B seed witnesses, the genus-zero case, or one exact ordered bank with its
geometric certificate. -/
inductive SymplecticCycleRealization {genus : Nat} (curve : Basic.HyperellipticCurve genus) :
    Lifted.Family.PairedCycleRefinements 2 genus → Lifted.Family.PairedCycleRefinements 2 genus → Prop
  /-- The exact root-closed period bank with explicit A and B raw seed realization witnesses. -/ | rootClosed (bank :
    PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodBank curve)
      {raw : Lifted.Family.PairedCycleRefinements 2 genus}
      (aSeed : ∀ index, PreparedCycleModels.PreparedCycleData.RealizesRaw
        (.finiteCut (bank.rows index).tours.aTour.joined.data) ((raw.aCycle index).liftedPath 0))
      (bSeed : ∀ index, PreparedCycleModels.PreparedCycleData.RealizesRaw
        (.finiteCut (bank.rows index).tours.bTour.joined.data) ((raw.bCycle index).liftedPath 0)) :
      SymplecticCycleRealization curve bank.cycles raw
  /-- The paired families in the certified genus-zero case. -/ | empty (zero : genus = 0) (computed raw :
    Lifted.Family.PairedCycleRefinements 2 genus) :
      SymplecticCycleRealization curve computed raw
  /-- The retained ordered paired period bank with its own geometric-basis certificate. -/ | ordered (bank :
    Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank curve) (geometry : bank.GeometricBasis) :
      SymplecticCycleRealization curve bank.periodData.cycles
        (PeriodCycleBasis.ordered bank geometry).cycles

namespace SymplecticCycleRealization

open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Periods in
/-- The root-closed bank from the supplied branch data realizes the corresponding raw symplectic basis. -/
theorem ofData {genus : Nat} (curve : Basic.HyperellipticCurve genus) (branches : BranchIsolation.Data curve) :
    SymplecticCycleRealization curve (PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodBank.ofData curve
      branches).cycles
      (BranchCutLifts.symplecticBasisOfData curve branches).cycles := by
  apply rootClosed (PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodBank.ofData curve branches)
  · intro index
    rw [PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodBank.ofData_aTour]
    exact PreparedOwnerClosedSchedules.PreparedRefinementPrograms.ownerClosedAScheduleOfData_realizesRaw_zero curve
      branches index
  · intro index
    exact PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodBank.ofData_bTour_realizesRaw curve branches
      index

open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Riemann.Periods in
/-- The canonical root-closed bank realizes the curve's original raw symplectic basis. -/
theorem standard {genus : Nat} (curve : Basic.HyperellipticCurve genus) :
    SymplecticCycleRealization curve (PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodBank.ofCurve
      curve).cycles
      (BranchCutLifts.symplecticBasis curve).cycles := by
  cases genus with
  | zero => exact .empty rfl _ _
  | succ genus => exact ofData curve (BranchIsolation.data curve)

end SymplecticCycleRealization

section
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Riemann.Periods in
/-- Read raw cycle period data from the retained root-closed bank for the supplied branch isolation. -/
@[expose] def rawPeriodDataOfData {genus : Nat} (curve : Basic.HyperellipticCurve genus)
    (branches : BranchIsolation.Data curve) : PeriodMatrix.PeriodData curve :=
  (PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodBank.ofData curve branches).periodData

open Purelib.Curves.Hyperelliptic.Branches in
/-- The raw period data realizes the same original branch-data symplectic basis. -/
theorem rawPeriodDataOfData_realization {genus : Nat} (curve : Basic.HyperellipticCurve genus)
    (branches : BranchIsolation.Data curve) :
    SymplecticCycleRealization curve (rawPeriodDataOfData curve branches).cycles
      (BranchCutLifts.symplecticBasisOfData curve branches).cycles :=
  SymplecticCycleRealization.ofData curve branches

section
open Purelib.Riemann.Periods
/-- Read raw period data from the curve's canonical root-closed bank. -/
@[expose] def automaticRawPeriodData {genus : Nat} (curve : Basic.HyperellipticCurve genus) : PeriodMatrix.PeriodData
  curve :=
  (PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodBank.ofCurve curve).periodData

/-- Every canonical raw A-period model has a nonempty cell list. -/
theorem automaticRawPeriodData_aProgram_model_cells_positive {genus : Nat}
    (curve : Basic.HyperellipticCurve genus) (differential cycle : Fin genus) (index : Nat) :
    0 < (((automaticRawPeriodData curve).aProgram differential cycle).integral.model index).cells.length :=
  ((PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodBank.ofCurve curve).rows
    cycle).aProgram_cells_positive differential index

/-- Every canonical raw B-period model has a nonempty cell list. -/
theorem automaticRawPeriodData_bProgram_model_cells_positive {genus : Nat}
    (curve : Basic.HyperellipticCurve genus) (differential cycle : Fin genus) (index : Nat) :
    0 < (((automaticRawPeriodData curve).bProgram differential cycle).integral.model index).cells.length :=
  ((PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodBank.ofCurve curve).rows
    cycle).bProgram_cells_positive differential index

end

open Purelib.Curves.Hyperelliptic.Branches in
/-- The canonical raw period data realizes the original curve's symplectic basis. -/
theorem automaticRawPeriodData_realization {genus : Nat} (curve : Basic.HyperellipticCurve genus) :
    SymplecticCycleRealization curve (automaticRawPeriodData curve).cycles
      (BranchCutLifts.symplecticBasis curve).cycles :=
  SymplecticCycleRealization.standard curve

open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Riemann.Periods in
/-- Read standard period data from the ordered paired bank for the supplied branch isolation. -/
@[expose] def standardPeriodDataOfData {genus : Nat} (curve : Basic.HyperellipticCurve genus)
    (branches : BranchIsolation.Data curve) : PeriodMatrix.PeriodData curve :=
  (Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank.ofData curve branches).periodData

open Purelib.Curves.Hyperelliptic.Branches in
/-- The standard period data realizes the geometric basis of that same retained ordered bank. -/
theorem standardPeriodDataOfData_realization {genus : Nat} (curve : Basic.HyperellipticCurve genus)
    (branches : BranchIsolation.Data curve) :
    SymplecticCycleRealization curve (standardPeriodDataOfData curve branches).cycles
      (PeriodCycleBasis.ofOrdered (Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank.ofData curve
        branches)).cycles :=
  .ordered _ (Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank.ofData curve branches).geometricBasis

open Purelib.Riemann.Periods in
/-- Read standard period data from the curve's canonical ordered paired bank. -/
@[expose] def automaticStandardPeriodData {genus : Nat} (curve : Basic.HyperellipticCurve genus) :
  PeriodMatrix.PeriodData curve :=
  (Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank.ofCurve curve).periodData

/-- Every canonical ordered A-period model has a nonempty cell list. -/
theorem automaticStandardPeriodData_aProgram_model_cells_positive {genus : Nat}
    (curve : Basic.HyperellipticCurve genus) (differential cycle : Fin genus) (index : Nat) :
    0 < (((automaticStandardPeriodData curve).aProgram differential cycle).integral.model index).cells.length :=
  Meshes.PuncturedGrid.Paired.PeriodNonempty.PairedPeriodBank.aProgram_cells_positive
    (Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank.ofCurve curve) differential cycle index

/-- Every canonical ordered B-period model has a nonempty cell list. -/
theorem automaticStandardPeriodData_bProgram_model_cells_positive {genus : Nat}
    (curve : Basic.HyperellipticCurve genus) (differential cycle : Fin genus) (index : Nat) :
    0 < (((automaticStandardPeriodData curve).bProgram differential cycle).integral.model index).cells.length :=
  Meshes.PuncturedGrid.Paired.PeriodNonempty.PairedPeriodBank.bProgram_cells_positive
    (Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank.ofCurve curve) differential cycle index

/-- A retained ordered bank's period cycles realize its own exact geometric basis. -/
theorem retainedBank_realization {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    (bank : Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank curve) :
    SymplecticCycleRealization curve bank.periodData.cycles (PeriodCycleBasis.ofOrdered bank).cycles :=
  .ordered bank bank.geometricBasis

/-- The canonical standard period data realizes the same original ordered bank's geometric basis. -/
theorem automaticStandardPeriodData_realization {genus : Nat} (curve : Basic.HyperellipticCurve genus) :
    SymplecticCycleRealization curve (automaticStandardPeriodData curve).cycles
      (PeriodCycleBasis.ofOrdered (Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank.ofCurve curve)).cycles :=
  retainedBank_realization (Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank.ofCurve curve)

end

end Purelib.Riemann.Integration.PreparedRefinementPrograms
