module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerRequests
import Mathlib.Data.Nat.Basic
import Purelib.Approximation.Budget.PreparedPrimitiveBatchBudget
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Periods.PreparedPeriodPrimitiveRequests
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Riemann

public section

/-!
# One shared corner bank for the complete corrected A/B family

The finite maximum is taken before primitive acquisition. All retained rows
therefore use the same numerical face data, including repeated faces and the
A prefixes inside corrected B walks. The second maximum selects one period
stage, and the estimates hold at every later stage of the original programs.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered}

namespace CornerFamily

set_option genInjectivity false in
/-- The original A and corrected B corner banks with their separately paid scalar requests. -/
structure CornerRowBudget (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
      (differential : Fin genus)
    (target : Fraction.Rational) (index : Fin genus) where
  /-- The actual original A-word corner bank. -/ a : Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerRequests.CornerBank
    prepared domains differential index false
  /-- The actual original corrected B-word corner bank, including its preceding A prefix. -/ b :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerRequests.CornerBank prepared domains differential index true
  /-- The paid scalar request for the retained original A bank. -/ aScalar : a.ScalarRequest target
  /-- The paid scalar request for the retained original corrected B bank. -/ bScalar : b.ScalarRequest target

constructive_injectivity CornerRowBudget

end CornerFamily

namespace CornerFamily.CornerRowBudget

/-- Prepare the original A and corrected B corner banks and allocate their scalar targets before acquiring numerical
values. -/
@[expose] def build (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (domains :
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
    (differential : Fin genus) (target : Fraction.Rational) (positive : 0 < target) (index : Fin genus) :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerFamily.CornerRowBudget prepared domains differential target index :=
  let a := Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerRequests.CornerBank.build prepared domains differential index
    false
  let b := Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerRequests.CornerBank.build prepared domains differential index
    true
  ⟨a, b, Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerRequests.CornerBank.ScalarRequest.build a target positive,
    Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerRequests.CornerBank.ScalarRequest.build b target positive⟩

/-- Take the maximum of the two original row-budget stages. -/
@[expose] def minimum {prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired} {domains :
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
    {differential : Fin genus} {target : Fraction.Rational} {index : Fin genus}
    (row : Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerFamily.CornerRowBudget prepared domains differential target
      index) : Nat :=
  max row.aScalar.minimum row.bScalar.minimum

end CornerFamily.CornerRowBudget

namespace CornerFamily

set_option genInjectivity false in
/-- All original paired-row scalar budgets with their exact common minimum numerical stage. -/
structure CornerScalars (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
      (differential : Fin genus) (target : Fraction.Rational) where
  /-- The actual dependent scalar budgets of all original paired rows. -/ rows : Data.Vector.DependentVector (fun index
    : Fin genus => Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerFamily.CornerRowBudget prepared domains differential
    target index)
  /-- The cached minimum sufficient numerical stage. -/ minimum : Nat
  /-- The cached stage equals the exact maximum of the original row minima. -/ minimum_eq : minimum = rows.maximum (fun
    _ row => row.minimum)

constructive_injectivity CornerScalars

end CornerFamily

namespace CornerFamily.CornerScalars

variable {prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired} {domains :
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {differential : Fin genus} {target : Fraction.Rational}

/-- Prepare every original paired row and cache the exact maximum of their scalar-budget stages. -/
@[expose] def build (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (domains :
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
    (differential : Fin genus) (target : Fraction.Rational) (positive : 0 < target) :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerFamily.CornerScalars prepared domains differential target :=
  let rows := Data.Vector.DependentVector.ofFn
    (Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerFamily.CornerRowBudget.build prepared domains differential target
    positive)
  ⟨rows, rows.maximum (fun _ row => row.minimum), rfl⟩

/-- Each original A budget is ready by the retained common numerical stage. -/
theorem a_minimum_le (scalars : Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerFamily.CornerScalars prepared domains
  differential target) (index : Fin genus) :
    (scalars.rows.get index).aScalar.minimum ≤ scalars.minimum := by
  rw [scalars.minimum_eq]
  exact (Nat.Order.le_max_left _ _).trans (scalars.rows.get_le_maximum (fun _ row => row.minimum) index)

/-- Each original corrected B budget is ready by the retained common numerical stage. -/
theorem b_minimum_le (scalars : Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerFamily.CornerScalars prepared domains
  differential target) (index : Fin genus) :
    (scalars.rows.get index).bScalar.minimum ≤ scalars.minimum := by
  rw [scalars.minimum_eq]
  exact (Nat.Order.le_max_right _ _).trans (scalars.rows.get_le_maximum (fun _ row => row.minimum) index)

set_option genInjectivity false in
/-- The actual original A/B requests acquired from one retained shared face bank. -/
structure Row (scalars : Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerFamily.CornerScalars prepared domains
  differential target) {numericalIndex : Nat}
    (numerics : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) numericalIndex domains)
    (minimumStage : Nat) (index : Fin genus) where
  /-- The original A request using the exact shared numerical bank. -/ a : (scalars.rows.get index).aScalar.Requested
    numerics minimumStage
  /-- The original corrected B request using the exact shared numerical bank. -/ b : (scalars.rows.get
    index).bScalar.Requested numerics minimumStage

constructive_injectivity Row

namespace Row

/-- Acquire both original row requests from the same supplied numerical bank at a sufficient stage. -/
@[expose] def build (scalars : Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerFamily.CornerScalars prepared domains
  differential target) {numericalIndex : Nat}
    (later : scalars.minimum ≤ numericalIndex)
    (numerics : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) numericalIndex domains)
    (minimumStage : Nat) (index : Fin genus) : Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerFamily.CornerScalars.Row
      scalars numerics minimumStage index :=
  ⟨(scalars.rows.get index).aScalar.requestWith ((scalars.a_minimum_le index).trans later) numerics minimumStage,
    (scalars.rows.get index).bScalar.requestWith ((scalars.b_minimum_le index).trans later) numerics minimumStage⟩

/-- Take the maximum of the original A and corrected B certified-tail stages. -/
@[expose] def threshold {scalars : Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerFamily.CornerScalars prepared
  domains differential target} {numericalIndex : Nat}
    {numerics : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) numericalIndex domains}
    {minimumStage : Nat} {index : Fin genus} (row :
      Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerFamily.CornerScalars.Row scalars numerics minimumStage index) :
      Nat :=
  max row.a.tail.stage row.b.tail.stage

end Row

set_option genInjectivity false in
/-- Supplying a surface bank at a sufficient index reuses it literally.
Neither A nor B constructs an independent primitive bank. -/
structure Requested (scalars : Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerFamily.CornerScalars prepared domains
  differential target) {numericalIndex : Nat}
    (numerics : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) numericalIndex domains)
    (minimumStage : Nat) where
  /-- All actual original A/B requests using the same retained numerical bank. -/ rows : Data.Vector.DependentVector
    (fun index : Fin genus => Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerFamily.CornerScalars.Row scalars numerics
    minimumStage index)
  /-- The cached common period-sampling stage. -/ stage : Nat
  /-- The period stage is exactly the maximum of the original floor and all retained row-tail thresholds. -/ stage_eq :
    stage = max minimumStage (rows.maximum (fun _ row => row.threshold))

constructive_injectivity Requested

/-- Acquire all original A/B rows from the supplied shared face bank and retain their common period stage. -/
@[expose] def requestWith (scalars : Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerFamily.CornerScalars prepared
  domains differential target) {numericalIndex : Nat}
    (later : scalars.minimum ≤ numericalIndex)
    (numerics : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) numericalIndex domains)
    (minimumStage : Nat) : Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerFamily.CornerScalars.Requested scalars
      numerics minimumStage :=
  let rows := Data.Vector.DependentVector.ofFn
    (Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerFamily.CornerScalars.Row.build scalars later numerics minimumStage)
  ⟨rows, max minimumStage (rows.maximum (fun _ row => row.threshold)), rfl⟩

namespace Requested

variable {scalars : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerFamily.CornerScalars prepared domains
  differential target} {numericalIndex minimumStage : Nat}
  {numerics : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
    (Periods.PeriodMatrix.standardDifferential differential) numericalIndex domains}

/-- The common retained period stage meets the independently supplied floor. -/
theorem stage_ge (requested : Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerFamily.CornerScalars.Requested scalars
  numerics minimumStage) : minimumStage ≤ requested.stage := by
  rw [requested.stage_eq]
  exact Nat.Order.le_max_left _ _

/-- Every later original A-program reading is within the target of its retained shared-bank corner value. -/
theorem a_accurate (requested : Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerFamily.CornerScalars.Requested scalars
  numerics minimumStage) (index : Fin genus)
    (stage : Nat) (later : requested.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq ((requested.rows.get index).a.value -
      ((prepared.periodData.aProgram differential index).integral.model stage).integralSample) < target := by
  apply (requested.rows.get index).a.accurate
  apply (Nat.Order.le_max_left _ _).trans
  apply (requested.rows.get_le_maximum (fun _ row => row.threshold) index).trans
  apply (Nat.Order.le_max_right minimumStage _).trans
  rw [← Nat.Order.max_eq_natMax, ← requested.stage_eq]
  exact later

/-- Every later original corrected B-program reading is within the target of its retained shared-bank corner value. -/
theorem b_accurate (requested : Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerFamily.CornerScalars.Requested scalars
  numerics minimumStage) (index : Fin genus)
    (stage : Nat) (later : requested.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq ((requested.rows.get index).b.value -
      ((prepared.periodData.bProgram differential index).integral.model stage).integralSample) < target := by
  apply (requested.rows.get index).b.accurate
  apply (Nat.Order.le_max_right _ _).trans
  apply (requested.rows.get_le_maximum (fun _ row => row.threshold) index).trans
  apply (Nat.Order.le_max_right minimumStage _).trans
  rw [← Nat.Order.max_eq_natMax, ← requested.stage_eq]
  exact later

end Requested
end CornerFamily.CornerScalars

set_option genInjectivity false in
/-- Automatic acquisition given the retained surface domains and positive
error request. The numerical and period floors may be raised independently. -/
structure CornerFamily (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (domains :
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
    (differential : Fin genus) (target : Fraction.Rational) (numericalFloor minimumStage : Nat) where
  /-- The original paired-row scalar budgets selected before numerical acquisition. -/ scalars :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerFamily.CornerScalars prepared domains differential target
  /-- The common numerical stage for the original shared face bank. -/ numericalIndex : Nat
  /-- The numerical stage is exactly the maximum of its original floor and retained scalar minimum. -/ numericalIndex_eq
    : numericalIndex = max numericalFloor scalars.minimum
  /-- The one actual shared numerical face bank for the selected original differential. -/ numerics :
    Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank (Periods.PeriodMatrix.standardDifferential
    differential) numericalIndex domains
  /-- Every original A/B request acquired from this exact retained numerical bank. -/ requested : scalars.Requested
    numerics minimumStage

constructive_injectivity CornerFamily

namespace CornerFamily

/-- Prepare the original scalar budgets first, acquire one common face bank, then request every original A/B row from
that exact cache. -/
@[expose] def build (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
  (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
    (differential : Fin genus) (target : Fraction.Rational) (positive : 0 < target)
    (numericalFloor minimumStage : Nat) : CornerFamily prepared
      domains differential target numericalFloor minimumStage :=
  let scalars := Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerFamily.CornerScalars.build prepared domains
    differential target positive
  let numericalIndex := max numericalFloor scalars.minimum
  let numerics := Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank.build
    (Periods.PeriodMatrix.standardDifferential differential) numericalIndex domains
  ⟨scalars, numericalIndex, rfl, numerics, scalars.requestWith (Nat.Order.le_max_right _ _) numerics minimumStage⟩

end CornerFamily

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired
