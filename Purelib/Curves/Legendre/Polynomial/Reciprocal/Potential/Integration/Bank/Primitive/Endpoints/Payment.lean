module

public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Bank.Primitive.Endpoints.Joins
public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Bank.Primitive.Endpoints.ClosingComparison
public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Bank.Primitive.Endpoints.Values
public import Purelib.Riemann.Paths.SegmentGapArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Fold
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Polynomial
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Endpoints
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Riemann.Normalization.ContinuedInverseRoot

/-! # Retained finite comparisons on the original sampled endpoint bank

Each adjacent link stores the actual returned comparison, and one closing
comparison uses the same original first endpoint. These data are built from
the real root/coordinate evidence and existing Samples, not from assumed
jump or total-integral bounds.
-/

public section

namespace Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Plan.Primitive.EndpointRequests

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives (PolynomialSample)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.PhysicalPrimitive (regularNumerator)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial Box)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (Point)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point (PrimitiveEndpoint)
open Purelib.Riemann.Paths
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

variable {parameter : Gaussian} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar}
    {sourceDifferential : Differential 1} {count : Nat}
    {error : Coordinate} {errorPositive : 0 < error} {floor : Nat}

/-- The original returned adjacent comparison at every literal neighboring occurrence, in order. -/
@[expose] def AdjacentComparisons
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) (target : Coordinate) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) → (values : Potentials bank) →
        (planned : Plan error errorPositive floor bank) →
          (requests : Requests regular coefficient accuracy positive bank planned) →
            (paths : LiftedCells bank planned) →
              (heads : Heads regular coefficient accuracy positive common bank values planned requests paths) →
                EndpointRequests coefficient.val target bank planned paths → Type 1 := by
  intro parents bank
  induction bank with
  | nil => exact fun _ _ _ _ _ _ => PUnit
  | cons data rest ih =>
      cases rest with
      | nil => exact fun _ _ _ _ _ _ => PUnit
      | cons next remaining =>
          intro values planned requests paths heads endpoints
          exact AdjacentComparison (parameter := parameter) (frame := frame) (cap := cap)
            (sourceDifferential := sourceDifferential) (count := count)
            (error := error) (errorPositive := errorPositive) (floor := floor)
            data next remaining values planned regular coefficient accuracy positive common target
            requests paths heads endpoints ×
            ih values.2.2 planned.2.2.2 requests.2.2.2 paths.2.2.2.2 heads.2 endpoints.2.2.2.2

/-- The original final comparison is indexed by this same bank's first request and actual physical starting value. -/
@[expose] def ClosingComparison
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) (target : Coordinate) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) → (values : Potentials bank) →
        (planned : Plan error errorPositive floor bank) →
          (requests : Requests regular coefficient accuracy positive bank planned) →
            (paths : LiftedCells bank planned) →
              (heads : Heads regular coefficient accuracy positive common bank values planned requests paths) →
                EndpointRequests coefficient.val target bank planned paths → Type 1 := by
  intro parents bank
  induction bank with
  | nil => exact fun _ _ _ _ _ _ => PUnit
  | cons data rest _ =>
      intro values planned requests paths heads endpoints
      exact LastComparison (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := count)
        (error := error) (errorPositive := errorPositive) (floor := floor)
        (targetPoint := planned.2.1.point 0) (targetPatch := data.terminal.neighborhood.patch)
        (targetPointOwner := endpoints.1.val)
        regular coefficient accuracy positive common target endpoints.2.2.1
          (heads.1.attached.physical.cell.value.eval data.segment.comparison.first)
          (.cons data rest) values planned requests paths heads endpoints

namespace AdjacentComparisons

/-- The exact function result retains each actual adjacent comparison on the supplied sampled cache. -/
private def BuildFamily
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) (target : Coordinate) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      Bank cap sourceDifferential count parents → Type 3 := fun {_parents} bank =>
    (values : Potentials bank) → (planned : Plan error errorPositive floor bank) →
      (requests : Requests regular coefficient accuracy positive bank planned) →
        (paths : LiftedCells bank planned) →
          (heads : Heads regular coefficient accuracy positive common bank values planned requests paths) →
            (endpoints : EndpointRequests coefficient.val target bank planned paths) →
              Samples regular coefficient accuracy positive common target
                bank values planned requests paths heads endpoints →
                  {first last : Named} → RootLinks bank first last → Junctions bank →
                    AdjacentComparisons (parameter := parameter) (frame := frame) (cap := cap)
                      (sourceDifferential := sourceDifferential) (count := count)
                      (error := error) (errorPositive := errorPositive) (floor := floor)
                      regular coefficient accuracy positive common target
                        bank values planned requests paths heads endpoints

/-- Build one real adjacent comparison before forcing its literal remaining comparison bank. -/
private def buildStep
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) (target : Coordinate)
    (targetPositive : 0 < target)
    {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (finishTail : Unit → BuildFamily (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      regular coefficient accuracy positive common target rest) :
    BuildFamily (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      regular coefficient accuracy positive common target (.cons data rest) := by
  cases rest with
  | nil => exact fun _ _ _ _ _ _ _ {_} {_} _ _ => ⟨⟩
  | cons next remaining =>
      intro values planned requests paths heads endpoints observed first last roots junctions
      let actual := compareAdjacent (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := count)
        (error := error) (errorPositive := errorPositive) (floor := floor)
        data next remaining values planned regular coefficient accuracy positive common target
        requests paths heads endpoints observed roots junctions targetPositive
      let tail := finishTail ()
      exact ⟨actual, tail values.2.2 planned.2.2.2 requests.2.2.2 paths.2.2.2.2 heads.2
        endpoints.2.2.2.2 observed.2 roots.tail junctions.2⟩

/-- Retain every actual adjacent observation comparison on the same supplied Sample and root-link spines. -/
def build
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) (target : Coordinate)
    (targetPositive : 0 < target) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) →
        (values : Potentials bank) → (planned : Plan error errorPositive floor bank) →
          (requests : Requests regular coefficient accuracy positive bank planned) →
            (paths : LiftedCells bank planned) →
              (heads : Heads regular coefficient accuracy positive common bank values planned requests paths) →
                (endpoints : EndpointRequests coefficient.val target bank planned paths) →
                  Samples regular coefficient accuracy positive common target
                    bank values planned requests paths heads endpoints →
                      {first last : Named} → RootLinks bank first last → Junctions bank →
                        AdjacentComparisons (parameter := parameter) (frame := frame) (cap := cap)
                          (sourceDifferential := sourceDifferential) (count := count)
                          (error := error) (errorPositive := errorPositive) (floor := floor)
                          regular coefficient accuracy positive common target
                            bank values planned requests paths heads endpoints :=
  fun {_parents} bank =>
    Bank.fold (motive := BuildFamily (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      regular coefficient accuracy positive common target)
      (fun _ _ _ _ _ _ _ {_} {_} _ _ => ⟨⟩)
      (buildStep (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := count)
        (error := error) (errorPositive := errorPositive) (floor := floor)
        regular coefficient accuracy positive common target targetPositive) bank

end AdjacentComparisons

namespace ClosingComparison

/-- The exact final-comparison constructor consumes the existing closing evidence and unchanged Samples. -/
private def BuildFamily
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) (target : Coordinate) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      Bank cap sourceDifferential count parents → Type 3 := fun {_parents} bank =>
    (values : Potentials bank) → (planned : Plan error errorPositive floor bank) →
      (requests : Requests regular coefficient accuracy positive bank planned) →
        (paths : LiftedCells bank planned) →
          (heads : Heads regular coefficient accuracy positive common bank values planned requests paths) →
            (endpoints : EndpointRequests coefficient.val target bank planned paths) →
              Samples regular coefficient accuracy positive common target
                bank values planned requests paths heads endpoints →
                  Closing coefficient.val target bank planned paths endpoints →
                    ClosingComparison (parameter := parameter) (frame := frame) (cap := cap)
                      (sourceDifferential := sourceDifferential) (count := count)
                      (error := error) (errorPositive := errorPositive) (floor := floor)
                      regular coefficient accuracy positive common target
                        bank values planned requests paths heads endpoints

/-- Invoke the original closing constructor once on the whole nonempty bank, without evaluating another tail. -/
private def buildStep
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) (target : Coordinate)
    (targetPositive : 0 < target)
    {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (_finishTail : Unit → BuildFamily (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      regular coefficient accuracy positive common target rest) :
    BuildFamily (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      regular coefficient accuracy positive common target (.cons data rest) :=
  fun values planned requests paths heads endpoints observed closing =>
    compareClosing (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      data rest values planned regular coefficient accuracy positive common target
      requests paths heads endpoints observed closing targetPositive

/-- Retain the actual final-versus-first comparison, or the original empty value when no occurrence exists. -/
def build
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) (target : Coordinate)
    (targetPositive : 0 < target) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) →
        (values : Potentials bank) → (planned : Plan error errorPositive floor bank) →
          (requests : Requests regular coefficient accuracy positive bank planned) →
            (paths : LiftedCells bank planned) →
              (heads : Heads regular coefficient accuracy positive common bank values planned requests paths) →
                (endpoints : EndpointRequests coefficient.val target bank planned paths) →
                  Samples regular coefficient accuracy positive common target
                    bank values planned requests paths heads endpoints →
                      Closing coefficient.val target bank planned paths endpoints →
                        ClosingComparison (parameter := parameter) (frame := frame) (cap := cap)
                          (sourceDifferential := sourceDifferential) (count := count)
                          (error := error) (errorPositive := errorPositive) (floor := floor)
                          regular coefficient accuracy positive common target
                            bank values planned requests paths heads endpoints :=
  fun {_parents} bank =>
    Bank.fold (motive := BuildFamily (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      regular coefficient accuracy positive common target)
      (fun _ _ _ _ _ _ _ _ => ⟨⟩)
      (buildStep (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := count)
        (error := error) (errorPositive := errorPositive) (floor := floor)
        regular coefficient accuracy positive common target targetPositive) bank

end ClosingComparison

/-- The actual ordered adjacent comparisons and original final comparison on the same checked endpoint bank. -/
abbrev Payment
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) (target : Coordinate)
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (bank : Bank cap sourceDifferential count parents) (values : Potentials bank)
    (planned : Plan error errorPositive floor bank)
    (requests : Requests regular coefficient accuracy positive bank planned) (paths : LiftedCells bank planned)
    (heads : Heads regular coefficient accuracy positive common bank values planned requests paths)
    (endpoints : EndpointRequests coefficient.val target bank planned paths) :=
  AdjacentComparisons (parameter := parameter) (frame := frame) (cap := cap)
    (sourceDifferential := sourceDifferential) (count := count)
    (error := error) (errorPositive := errorPositive) (floor := floor)
    regular coefficient accuracy positive common target bank values planned requests paths heads endpoints ×
  ClosingComparison (parameter := parameter) (frame := frame) (cap := cap)
    (sourceDifferential := sourceDifferential) (count := count)
    (error := error) (errorPositive := errorPositive) (floor := floor)
    regular coefficient accuracy positive common target bank values planned requests paths heads endpoints

namespace Payment

/-- Construct both actual comparison caches from the existing Samples and original geometric evidence. -/
def build
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) (target : Coordinate)
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (bank : Bank cap sourceDifferential count parents) (values : Potentials bank)
    (planned : Plan error errorPositive floor bank)
    (requests : Requests regular coefficient accuracy positive bank planned) (paths : LiftedCells bank planned)
    (heads : Heads regular coefficient accuracy positive common bank values planned requests paths)
    (endpoints : EndpointRequests coefficient.val target bank planned paths)
    (observed : Samples regular coefficient accuracy positive common target
      bank values planned requests paths heads endpoints)
    {first last : Named} (roots : RootLinks bank first last) (junctions : Junctions bank)
    (closing : Closing coefficient.val target bank planned paths endpoints) (targetPositive : 0 < target) :
    Payment (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      regular coefficient accuracy positive common target bank values planned requests paths heads endpoints :=
  let adjacent := AdjacentComparisons.build (parameter := parameter) (frame := frame) (cap := cap)
    (sourceDifferential := sourceDifferential) (count := count)
    (error := error) (errorPositive := errorPositive) (floor := floor)
    regular coefficient accuracy positive common target targetPositive
    bank values planned requests paths heads endpoints observed roots junctions
  let returned := ClosingComparison.build (parameter := parameter) (frame := frame) (cap := cap)
    (sourceDifferential := sourceDifferential) (count := count)
    (error := error) (errorPositive := errorPositive) (floor := floor)
    regular coefficient accuracy positive common target targetPositive
    bank values planned requests paths heads endpoints observed closing
  ⟨adjacent, returned⟩

/-- Exact scalar readbacks transport a paid reversed physical jump to the retained endpoint scalars. -/
private theorem scalar_gap_le
    (first last physicalFirst physicalLast : Gaussian) (bound : Coordinate)
    (firstEq : first = physicalFirst) (lastEq : last = physicalLast)
    (paid : Norm.Basic.normSq (physicalLast - physicalFirst) < bound) :
    Norm.Basic.normSq (first - last) ≤ bound :=
  (congrArg Norm.Basic.normSq (congrArg₂ (fun a b : Gaussian => a - b) firstEq lastEq)).trans_le
    ((Norm.Bounds.normSq_sub_symm physicalFirst physicalLast).trans_lt paid).le

/-- The original adjacent and final witnesses pay every retained scalar gap to one fixed original target.

The target request and target value stay fixed through all literal tails.
Each inequality consumes its retained original observation comparison and
the supplied Samples' scalar readbacks; it executes no comparison again.
-/
private theorem gaps_to
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) (target : Coordinate)
    {targetPoint : Gaussian}
    {targetPatch : ContinuedNeighborhood (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) count}
    {targetPointOwner : Point targetPatch targetPoint}
    (targetRequest : PrimitiveEndpoint targetPointOwner 0 coefficient.val floor target)
    (finish : Gaussian) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) →
        (values : Potentials bank) → (planned : Plan error errorPositive floor bank) →
          (requests : Requests regular coefficient accuracy positive bank planned) →
            (paths : LiftedCells bank planned) →
              (heads : Heads regular coefficient accuracy positive common bank values planned requests paths) →
                (endpoints : EndpointRequests coefficient.val target bank planned paths) →
                  (observed : Samples regular coefficient accuracy positive common target
                    bank values planned requests paths heads endpoints) →
                    AdjacentComparisons (parameter := parameter) (frame := frame) (cap := cap)
                      (sourceDifferential := sourceDifferential) (count := count)
                      (error := error) (errorPositive := errorPositive) (floor := floor)
                      regular coefficient accuracy positive common target
                        bank values planned requests paths heads endpoints →
                      LastComparison (parameter := parameter) (frame := frame) (cap := cap)
                        (sourceDifferential := sourceDifferential) (count := count)
                        (error := error) (errorPositive := errorPositive) (floor := floor)
                        (targetPoint := targetPoint) (targetPatch := targetPatch)
                        (targetPointOwner := targetPointOwner)
                        regular coefficient accuracy positive common target targetRequest finish
                          bank values planned requests paths heads endpoints →
                        SegmentGapArea.GapsSmall
                          (Samples.values regular coefficient accuracy positive common target
                            bank values planned requests paths heads endpoints observed) finish (8 * target) := by
  intro parents bank
  induction bank with
  | nil =>
      intro values planned requests paths heads endpoints observed _ _
      have empty := Samples.values_nil regular coefficient accuracy positive common target
        values planned requests paths heads endpoints observed
      exact Eq.mp (congrArg (fun rows : List (Gaussian × Gaussian) =>
        SegmentGapArea.GapsSmall rows finish (8 * target)) empty.symm) True.intro
  | cons data rest ih =>
      cases rest with
      | nil =>
          intro values planned requests paths heads endpoints observed adjacent returned
          have layout := Samples.values_cons data .nil values planned regular coefficient
            accuracy positive common target requests paths heads endpoints observed
          apply Eq.mp (congrArg (fun rows : List (Gaussian × Gaussian) =>
            SegmentGapArea.GapsSmall rows finish (8 * target)) layout.symm)
          have lastValue := PrimitiveEndpoint.Sample.value_eq (paid := endpoints.2.2.2.1) observed.1.2
          have last := lastValue.trans
            (congrArg (fun point : Gaussian => heads.1.attached.physical.cell.value.eval point) planned.2.1.point_one)
          have tailLayout := Samples.values_nil regular coefficient accuracy positive common target
            values.2.2 planned.2.2.2 requests.2.2.2 paths.2.2.2.2 heads.2 endpoints.2.2.2.2 observed.2
          have tailFirst := congrArg
            (fun rows : List (Gaussian × Gaussian) => SegmentGapArea.first rows finish) tailLayout
          have gap := scalar_gap_le _ _ _ _ (8 * target) tailFirst last returned.property
          have remaining := Eq.mp (congrArg (fun rows : List (Gaussian × Gaussian) =>
            SegmentGapArea.GapsSmall rows finish (8 * target)) tailLayout.symm) True.intro
          exact ⟨gap, remaining⟩
      | cons next remaining =>
          intro values planned requests paths heads endpoints observed adjacent returned
          have layout := Samples.values_cons data (.cons next remaining) values planned regular coefficient
            accuracy positive common target requests paths heads endpoints observed
          apply Eq.mp (congrArg (fun rows : List (Gaussian × Gaussian) =>
            SegmentGapArea.GapsSmall rows finish (8 * target)) layout.symm)
          have lastValue := PrimitiveEndpoint.Sample.value_eq (paid := endpoints.2.2.2.1) observed.1.2
          have last := lastValue.trans
            (congrArg (fun point : Gaussian => heads.1.attached.physical.cell.value.eval point) planned.2.1.point_one)
          have tailLayout := Samples.values_cons next remaining values.2.2 planned.2.2.2
            regular coefficient accuracy positive common target requests.2.2.2 paths.2.2.2.2
            heads.2 endpoints.2.2.2.2 observed.2
          have tailFirst := congrArg
            (fun rows : List (Gaussian × Gaussian) => SegmentGapArea.first rows finish) tailLayout
          have firstValue := PrimitiveEndpoint.Sample.value_eq
            (paid := endpoints.2.2.2.2.2.2.1) observed.2.1.1
          have first := tailFirst.trans (firstValue.trans
            (congrArg (fun point : Gaussian => heads.2.1.attached.physical.cell.value.eval point)
              planned.2.2.2.2.1.point_zero))
          have gap := scalar_gap_le _ _ _ _ (8 * target) first last adjacent.1.property
          have tail := ih values.2.2 planned.2.2.2 requests.2.2.2 paths.2.2.2.2 heads.2
            endpoints.2.2.2.2 observed.2 adjacent.2 returned
          exact ⟨gap, tail⟩

set_option linter.unusedVariables false in
/-- Every actual endpoint gap, including the returned final endpoint, is paid by the same retained comparison cache.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition. The named `paid` premises remain
required by callers and the proof, although absent from the conclusion.
-/
@[expose] def GapsSmallLaw : Prop :=
  ∀
    {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar}
    {sourceDifferential : Differential 1}
    {count : Nat}
    {error : Coordinate}
    {errorPositive : 0 < error}
    {floor : Nat}
    {index : Nat}
    {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate)
    (positive : 0 < accuracy)
    (common : Nat)
    (target : Coordinate)
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (bank : Bank cap sourceDifferential count parents)
    (values : Potentials bank)
    (planned : Plan error errorPositive floor bank)
    (requests : Requests regular coefficient accuracy positive bank planned)
    (paths : LiftedCells bank planned)
    (heads : Heads regular coefficient accuracy positive common bank values planned requests paths)
    (endpoints : EndpointRequests coefficient.val target bank planned paths)
    (observed : Samples regular coefficient accuracy positive common target
      bank values planned requests paths heads endpoints)
    (paid : Payment (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      regular coefficient accuracy positive common target bank values planned requests paths heads endpoints),
    SegmentGapArea.GapsSmall
      (Samples.values regular coefficient accuracy positive common target
        bank values planned requests paths heads endpoints observed)
      (SegmentGapArea.first (Samples.values regular coefficient accuracy positive common target
        bank values planned requests paths heads endpoints observed) 0) (8 * target)

/-- Every actual endpoint gap, including the returned final endpoint, is paid by the same retained comparison cache. -/
theorem gaps_small : GapsSmallLaw := by
  unfold GapsSmallLaw
  intro parameter frame collar cap sourceDifferential count error errorPositive floor index box regular
    coefficient accuracy positive common target parents bank values planned requests paths heads endpoints
    observed paid
  cases bank with
  | nil =>
      have empty := Samples.values_nil regular coefficient accuracy positive common target
        values planned requests paths heads endpoints observed
      exact Eq.mp (congrArg (fun rows : List (Gaussian × Gaussian) =>
        SegmentGapArea.GapsSmall rows (SegmentGapArea.first rows 0) (8 * target)) empty.symm) True.intro
  | cons data rest =>
      have all := gaps_to (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := count)
        (error := error) (errorPositive := errorPositive) (floor := floor)
        (targetPoint := planned.2.1.point 0) (targetPatch := data.terminal.neighborhood.patch)
        (targetPointOwner := endpoints.1.val)
        regular coefficient accuracy positive common target endpoints.2.2.1
        (heads.1.attached.physical.cell.value.eval data.segment.comparison.first)
        (.cons data rest) values planned requests paths heads endpoints observed paid.1 paid.2
      have layout := Samples.values_cons data rest values planned regular coefficient accuracy positive common target
        requests paths heads endpoints observed
      have firstLayout := congrArg
        (fun rows : List (Gaussian × Gaussian) => SegmentGapArea.first rows 0) layout
      have firstValue := PrimitiveEndpoint.Sample.value_eq (paid := endpoints.2.2.1) observed.1.1
      have first := firstLayout.trans (firstValue.trans
        (congrArg (fun point : Gaussian => heads.1.attached.physical.cell.value.eval point) planned.2.1.point_zero))
      exact Eq.mp (congrArg (fun finish : Gaussian => SegmentGapArea.GapsSmall
        (Samples.values regular coefficient accuracy positive common target
          (.cons data rest) values planned requests paths heads endpoints observed) finish (8 * target)) first.symm) all

set_option linter.unusedVariables false in
/-- The same retained adjacent and closing comparisons bound the actual sum of cached primitive increments.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition. The named `paid` premises remain
required by callers and the proof, although absent from the conclusion.
-/
@[expose] def IncrementsNormSqLeLaw : Prop :=
  ∀
    {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar}
    {sourceDifferential : Differential 1}
    {count : Nat}
    {error : Coordinate}
    {errorPositive : 0 < error}
    {floor : Nat}
    {index : Nat}
    {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate)
    (positive : 0 < accuracy)
    (common : Nat)
    (target : Coordinate)
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (bank : Bank cap sourceDifferential count parents)
    (values : Potentials bank)
    (planned : Plan error errorPositive floor bank)
    (requests : Requests regular coefficient accuracy positive bank planned)
    (paths : LiftedCells bank planned)
    (heads : Heads regular coefficient accuracy positive common bank values planned requests paths)
    (endpoints : EndpointRequests coefficient.val target bank planned paths)
    (observed : Samples regular coefficient accuracy positive common target
      bank values planned requests paths heads endpoints)
    (paid : Payment (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      regular coefficient accuracy positive common target bank values planned requests paths heads endpoints),
    Norm.Basic.normSq (gaussianSum
      ((Samples.values regular coefficient accuracy positive common target
        bank values planned requests paths heads endpoints observed).map (fun pair => pair.2 - pair.1))) ≤
      (parents.length : Coordinate) * ((parents.length : Coordinate) * (8 * target))

/-- The same retained adjacent and closing comparisons bound the actual sum of cached primitive increments. -/
theorem increments_normSq_le : IncrementsNormSqLeLaw := by
  unfold IncrementsNormSqLeLaw
  intro parameter frame collar cap sourceDifferential count error errorPositive floor index box regular
    coefficient accuracy positive common target parents bank values planned requests paths heads endpoints
    observed paid
  have gaps := gaps_small (parameter := parameter) (frame := frame) (cap := cap)
    (sourceDifferential := sourceDifferential) (count := count)
    (error := error) (errorPositive := errorPositive) (floor := floor)
    regular coefficient accuracy positive common target bank values planned requests paths heads endpoints observed paid
  have bound := SegmentGapArea.increments_normSq_le gaps
  have length := Samples.values_length regular coefficient accuracy positive common target
    bank values planned requests paths heads endpoints observed
  exact bound.trans_eq (congrArg
    (fun size : Nat => (size : Coordinate) * ((size : Coordinate) * (8 * target))) length)

end Payment

end Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Plan.Primitive.EndpointRequests

end
