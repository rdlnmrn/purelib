module
import Purelib.Data.List.Append
import Purelib.Data.List.Flatten
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodRequests
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Geometry.Path.Gaussian.Lifted.Refinement
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices

open Purelib.Approximation

open Purelib.Curves

open Purelib.Riemann

public section

/-!
# Curve-only acquisition of the corrected ordered period bank

The retained constructor exposes all the actual grid, branch-order, pairing,
preparation and face-assignment data. Genus zero acquires none of it.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank

set_option genInjectivity false in
/-- The existential geometry is retained as executable constructor data,
with the dependent preparation certifying the exact ordered branch words. -/
inductive PairedPeriodBank {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) : Type 4 where
  /-- The empty original program family with its retained proof of genus zero. -/ | empty (zero : genus = 0)
  /-- The actual original grid, ordered pairing and dependent corrected-period preparation. -/ | retained {branches :
    Hyperelliptic.Branches.BranchIsolation.Data curve} {higher : 1 < curve.polynomial.natDegree}
      {base : Meshes.FramedPuncturedGrid curve branches higher} {lifted : Meshes.LiftedPuncturedGrid base}
      {bank : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet :
        Fin 2} {ordered :
        Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
        {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered}
      (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)

constructive_injectivity PairedPeriodBank

namespace PairedPeriodBank

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}

/-- Read the actual corrected period programs, with the empty family in genus zero. -/
@[expose] def periodData : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank curve →
  Periods.PeriodMatrix.PeriodData curve
  | .empty zero =>
      { cycles :=
          { aCycle := fun index => Fin.elim0 (Fin.cast zero index)
            bCycle := fun index => Fin.elim0 (Fin.cast zero index) }
        aProgram := fun _ index => Fin.elim0 (Fin.cast zero index)
        bProgram := fun _ index => Fin.elim0 (Fin.cast zero index) }
  | .retained prepared => prepared.periodData

set_option genInjectivity false in
/-- Initial states read from this very corrected bank. The two programs
share the retained root, and every differential is the recast program of
these states. This is the ownership boundary for checkpoint acquisition;
it does not identify corrected walks with the former raw reference tours. -/
structure InitialRow (bank : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank curve) (index : Fin
  genus) where
  /-- The original root name shared by the retained A and corrected B initial states. -/ root :
    Gaussian.Name.Basic.Named
  /-- The actual original root-closed A initial state. -/ a :
    Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints.RootClosedState curve
    (Periods.PeriodMatrix.standardDifferential index) root
  /-- The actual original root-closed corrected B initial state. -/ b :
    Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints.RootClosedState curve
    (Periods.PeriodMatrix.standardDifferential index) root
  /-- The retained A state yields exactly the original bank's A cycle. -/ a_cycle :
    Periods.PreparedRootSafePeriodPrograms.RootClosedState.cycle a
    (Integration.PreparedRefinementProgramCore.standardDifferentials genus) = bank.periodData.cycles.aCycle index
  /-- The retained B state yields exactly the original bank's corrected B cycle. -/ b_cycle :
    Periods.PreparedRootSafePeriodPrograms.RootClosedState.cycle b
    (Integration.PreparedRefinementProgramCore.standardDifferentials genus) = bank.periodData.cycles.bCycle index
  /-- Every recast A-state program is exactly the corresponding original bank program. -/ a_program : ∀ differential,
    Periods.PreparedRootSafePeriodPrograms.RootClosedState.period a
    (Integration.PreparedRefinementProgramCore.standardDifferentials genus)
      (Periods.PeriodMatrix.standardDifferential differential)
      (Integration.PreparedRefinementProgramCore.standardDifferential_mem_standardDifferentials differential) =
    (bank.periodData.aProgram differential index).integral
  /-- Every recast B-state program is exactly the corresponding original corrected B program. -/ b_program : ∀
    differential, Periods.PreparedRootSafePeriodPrograms.RootClosedState.period b
    (Integration.PreparedRefinementProgramCore.standardDifferentials genus)
      (Periods.PeriodMatrix.standardDifferential differential)
      (Integration.PreparedRefinementProgramCore.standardDifferential_mem_standardDifferentials differential) =
    (bank.periodData.bProgram differential index).integral

constructive_injectivity InitialRow

/-- Read the already materialized states, without isolating roots,
preparing walks, or extracting centered parents again. -/
@[expose] def initialRow (bank : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank curve) (index :
  Fin genus) : bank.InitialRow index :=
  match bank with
  | .empty zero => Fin.elim0 (Fin.cast zero index)
  | .retained prepared =>
      ⟨_, (prepared.aWalk index).initial, (prepared.bWalk index).initial,
        rfl, rfl, fun _ => rfl, fun _ => rfl⟩

/-- Retain the supplied branch isolation and construct every subsequent
finite stage once. No caller root owner, order, B correction or integration
certificate is required. -/
@[expose] def ofData : {genus : Nat} → (curve : Hyperelliptic.Basic.HyperellipticCurve genus) →
  Hyperelliptic.Branches.BranchIsolation.Data curve →
  Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank curve
  | 0, _, _ => .empty rfl
  | genus + 1, curve, branches =>
      let higher := Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts.degreeGtOne_of_cycleIndex curve (⟨0,
        Nat.zero_lt_succ genus⟩ : Fin (genus + 1))
      let base := Meshes.FramedPuncturedGrid.ofData curve branches higher
      let lifted := Meshes.LiftedPuncturedGrid.build base
      let bank := Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.build lifted
      let ordered := bank.ordered 0
      let paired := Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.paired ordered
      .retained (Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.prepare paired)

/-- Intrinsic curve data suffices for acquisition of the full corrected
program family. The analytic boundary and energy estimates are separate. -/
@[expose] def ofCurve : {genus : Nat} → (curve : Hyperelliptic.Basic.HyperellipticCurve genus) →
  Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank curve
  | 0, _ => .empty rfl
  | _ + 1, curve => Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank.ofData curve
    (Hyperelliptic.Branches.BranchIsolation.data curve)

/-- With an actual period index, intrinsic curve acquisition agrees with acquisition from its original branch-isolation
data. -/
theorem ofCurve_positive (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (index : Fin genus) :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank.ofCurve curve =
      Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank.ofData curve
      (Hyperelliptic.Branches.BranchIsolation.data curve) := by
  cases genus with
  | zero => exact Fin.elim0 index
  | succ => rfl

/-- Genus-zero acquisition returns the exact empty bank. -/
theorem ofCurve_zero (curve : Hyperelliptic.Basic.HyperellipticCurve 0) :
  Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank.ofCurve curve = .empty rfl := rfl

end PairedPeriodBank
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank

end
