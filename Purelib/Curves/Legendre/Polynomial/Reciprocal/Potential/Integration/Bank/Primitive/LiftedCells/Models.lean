module

public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Bank.Primitive.LiftedCells.Path
public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Endpoints
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path
import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Bank.Primitive.Cells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Fold
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Polynomial
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Path.Lifted.Model
import Purelib.Data.Nat.Order
import Purelib.Data.List.Map
public import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Uniform model banks on the same retained lifted path

Each actual Head contributes its existing weighted and cleared-remainder
models and their paid original uniform certificates. One delayed traversal
retains both ordered model lists and both path-certificate spines. Exact
endpoint transports align the indices with the already cached lifted path;
no Point, inverse, cube, model or path factory is replayed.
-/

public section

namespace Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Plan.Primitive

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives (PolynomialSample)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve (reciprocalCurve)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic
open Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.PhysicalPrimitive (regularNumerator)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial Box)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell LiftedPath)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Integration.PreparedRefinementMovement (movementSum movementMass movementMass_eq)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction

variable {parameter : Gaussian} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar}
    {sourceDifferential : Differential 1} {count : Nat}
    {error : Coordinate} {errorPositive : 0 < error} {floor : Nat}

namespace LiftedCells

/-- Two retained original model lists are uniformly certified cell-for-cell on one actual lifted path.

The exact Sigma stores only the two ordered finite caches and their
original uniform path certificates. It adds no source, model or geometry
owner and requires no final accuracy or programme relation.
-/
@[expose] def CertifiedModels {start finish : LiftedPoint 2} (keptPath : LiftedPath 2 start finish) : Type 2 :=
  (models : List CellModel × List CellModel) ×
  Path.Jets.UniformPathCertificates (reciprocalCurve (Fibre.frameCurve frame))
    (Integration.differential (-cap.polynomial)) models.1 keptPath ×
  Path.Jets.UniformPathCertificates (reciprocalCurve (Fibre.frameCurve frame))
    (Integration.differential ((wRemainder (parameter := parameter)) *
      HyperellipticReciprocal.polynomial (Fibre.frameCurve frame))) models.2 keptPath

namespace CertifiedModels

/-- Both original ordered model lists retain the exact cached path's occurrence count. -/
theorem lengths {start finish : LiftedPoint 2} {keptPath : LiftedPath 2 start finish}
    (retained : CertifiedModels (parameter := parameter) (frame := frame) (collar := collar) (cap := cap) keptPath) :
    retained.1.1.length = keptPath.cellCount ∧ retained.1.2.length = keptPath.cellCount :=
  ⟨LiftedPath.followedBy_length (Path.Jets.UniformPathCertificates.toFollowedBy retained.2.1),
    LiftedPath.followedBy_length (Path.Jets.UniformPathCertificates.toFollowedBy retained.2.2)⟩

end CertifiedModels

/-- The exact constructor function on literal Head, path and planning tails at one fixed shared sample. -/
private def CertifyFamily
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      Bank cap sourceDifferential count parents → Type 3 := fun {parents} bank =>
    (values : Potentials bank) → (planned : Plan error errorPositive floor bank) →
      (requests : Requests regular coefficient accuracy positive bank planned) →
        (paths : LiftedCells bank planned) →
          (heads : Heads regular coefficient accuracy positive common bank values planned requests paths) →
            Plan.commonFloor bank planned ≤ common →
              (factory : paths = build bank planned) → {start finish : LiftedPoint 2} →
                (chain : Nonempty (CenteredPathChain parents (start := start) (finish := finish))) →
                  (keptPath : LiftedPath 2 start finish) →
                    keptPath = path bank planned paths factory chain →
                      CertifiedModels (parameter := parameter) (frame := frame) (collar := collar) (cap := cap) keptPath

/-- An empty bank certifies the supplied actual empty path, excluding a nonempty mismatch by its factory equation. -/
private def emptyCertificates
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) :
    CertifyFamily (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      regular coefficient accuracy positive common .nil := by
  intro values planned requests paths heads originalPaid factory start finish chain keptPath pathFactory
  cases keptPath with
  | nil => exact ⟨([], []), .nil start, .nil start⟩
  | cons _keptHead keptTail =>
      have zero := path_cellCount (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := count)
        (error := error) (errorPositive := errorPositive) (floor := floor) .nil planned paths factory chain
      have counted := (congrArg LiftedPath.cellCount pathFactory).trans zero
      change Nat.succ keptTail.cellCount = 0 at counted
      exact False.elim (Nat.succ_ne_zero _ counted)

/-- Inspect the actual cached path head, certify its unchanged models and pass its literal path tail to the worker.

The original constructor injectivity is used only for erased index and
whole-cell identities. Every computational path value comes from the
supplied keptPath; no inferred constructor tail invokes the path factory.
-/
private def certifyStep
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat)
    {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (finishTail : Unit → CertifyFamily (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      regular coefficient accuracy positive common rest) :
    CertifyFamily (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      regular coefficient accuracy positive common (.cons data rest) := by
  intro values planned requests paths heads originalPaid factory start finish chain keptPath pathFactory
  have layout := path_cons (parameter := parameter) (frame := frame) (cap := cap)
    (sourceDifferential := sourceDifferential) (count := count)
    (error := error) (errorPositive := errorPositive) (floor := floor) data rest planned paths factory chain
  cases keptPath with
  | nil =>
      have counted := congrArg LiftedPath.cellCount (pathFactory.trans layout)
      change 0 = Nat.succ _ at counted
      exact False.elim (Nat.succ_ne_zero _ counted.symm)
  | @cons _ middle _ keptHead keptTail =>
      have whole := pathFactory.trans layout
      have components := LiftedPath.cons.inj whole
      have middleEq := components.1
      subst middle
      have firstEq := firstPoint_eq data rest planned paths factory chain
      have lastEq := lastPoint_eq data rest planned paths factory
      have headEq : keptHead = paths.2.2.1.castEndpoints firstEq lastEq := eq_of_heq components.2.1
      have tailEq : keptTail = path rest planned.2.2.2 paths.2.2.2.2
          (tail_eq data rest planned paths factory) (remaining_chain chain) := eq_of_heq components.2.2
      let uniforms := Head.certificates (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := count)
        (error := error) (errorPositive := errorPositive) (floor := floor)
        (index := index) (box := box) (firstSheet := paths.1) (lastSheet := paths.2.1)
        data rest values planned regular requests.1.val accuracy requests.2.1.val common
        paths.2.2.1 paths.2.2.2.1 heads.1 originalPaid
      let weightedHead := Eq.mp (congrArg
        (fun cell : LiftedCell start _ => Uniform.Jets.UniformCellCertificate
          (reciprocalCurve (Fibre.frameCurve frame)) (Integration.differential (-cap.polynomial))
          cell heads.1.pullbacks.1.val.model) headEq.symm) (uniforms.1.castEndpoints firstEq lastEq)
      let remainderHead := Eq.mp (congrArg
        (fun cell : LiftedCell start _ => Uniform.Jets.UniformCellCertificate
          (reciprocalCurve (Fibre.frameCurve frame))
          (Integration.differential ((wRemainder (parameter := parameter)) *
            HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)))
          cell heads.1.pullbacks.2.val.model) headEq.symm) (uniforms.2.castEndpoints firstEq lastEq)
      have originalMax : Nat.max planned.2.2.1.2.2.val (Plan.commonFloor rest planned.2.2.2) ≤ common :=
        Eq.mp (congrArg (fun value : Nat => value ≤ common) (Plan.commonFloor_cons data rest planned)) originalPaid
      have tailPaid := (Data.Nat.Order.le_max_right _ _).trans originalMax
      let remaining := finishTail ()
      let tail := remaining values.2.2 planned.2.2.2 requests.2.2.2 paths.2.2.2.2 heads.2 tailPaid
        (tail_eq data rest planned paths factory) (remaining_chain chain) keptTail tailEq
      let models := (heads.1.pullbacks.1.val.model :: tail.1.1, heads.1.pullbacks.2.val.model :: tail.1.2)
      let weighted : Path.Jets.UniformPathCertificates (reciprocalCurve (Fibre.frameCurve frame))
          (Integration.differential (-cap.polynomial)) models.1 (.cons keptHead keptTail) :=
        .cons (liftedCell := keptHead) (remaining := keptTail)
          (heads.1.pullbacks.1.val.start_eq.trans (congrArg LiftedPoint.coordinate firstEq))
          (heads.1.pullbacks.1.val.finish_eq.trans (congrArg LiftedPoint.coordinate lastEq))
          (.uniform weightedHead) tail.2.1
      let remainder : Path.Jets.UniformPathCertificates (reciprocalCurve (Fibre.frameCurve frame))
          (Integration.differential ((wRemainder (parameter := parameter)) *
            HyperellipticReciprocal.polynomial (Fibre.frameCurve frame))) models.2 (.cons keptHead keptTail) :=
        .cons (liftedCell := keptHead) (remaining := keptTail)
          (heads.1.pullbacks.2.val.start_eq.trans (congrArg LiftedPoint.coordinate firstEq))
          (heads.1.pullbacks.2.val.finish_eq.trans (congrArg LiftedPoint.coordinate lastEq))
          (.uniform remainderHead) tail.2.2
      exact ⟨models, weighted, remainder⟩

/-- Construct both ordered original model lists and genuine uniform certificate banks on the same cached path.

The shared regular sample and actual q stages stay fixed. Every head uses
its original models and paid uniform requests, then passes the literal
cache and GIVEN path tails to the delayed worker. Endpoint equations
affect only indices, and factory expressions occur only in erased proofs.
-/
def certify
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) → (values : Potentials bank) →
        (planned : Plan error errorPositive floor bank) →
          (requests : Requests regular coefficient accuracy positive bank planned) →
            (paths : LiftedCells bank planned) →
              (heads : Heads regular coefficient accuracy positive common bank values planned requests paths) →
                Plan.commonFloor bank planned ≤ common →
                  (factory : paths = build bank planned) → {start finish : LiftedPoint 2} →
                    (chain : Nonempty (CenteredPathChain parents (start := start) (finish := finish))) →
                      (keptPath : LiftedPath 2 start finish) →
                        keptPath = path bank planned paths factory chain →
                          CertifiedModels (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
                            keptPath :=
  fun {_parents} bank =>
    Bank.fold (motive := CertifyFamily (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := count)
        (error := error) (errorPositive := errorPositive) (floor := floor)
        regular coefficient accuracy positive common)
      (emptyCertificates (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := count)
        (error := error) (errorPositive := errorPositive) (floor := floor)
        regular coefficient accuracy positive common)
      (certifyStep (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := count)
        (error := error) (errorPositive := errorPositive) (floor := floor)
        regular coefficient accuracy positive common) bank

/-- Observe the two integral lists of the given retained model cache. -/
private def modelSamples {start finish : LiftedPoint 2} {keptPath : LiftedPath 2 start finish}
    (retained : CertifiedModels (parameter := parameter) (frame := frame)
      (collar := collar) (cap := cap) keptPath) :
    List Gaussian × List Gaussian :=
  (retained.1.1.map CellModel.integralSample, retained.1.2.map CellModel.integralSample)

/-- Observe the two original scalar readers on a supplied existing work/extra cache. -/
private def originalSamples (common : Nat)
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (bank : Bank cap sourceDifferential count parents) {values : Potentials bank}
    (packed : Plan.Materialized (error := error) (positive := errorPositive) (floor := floor)
      bank values common) : List Gaussian × List Gaussian :=
  (ExtraCells.weighted bank packed.1 packed.2, ExtraCells.regular bank packed.1 packed.2)

/-- The original owned fold equation identifies both model-integral lists on its literal cached path. -/
private theorem certify_samples
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) → (values : Potentials bank) →
        (planned : Plan error errorPositive floor bank) →
          (requests : Requests regular coefficient accuracy positive bank planned) →
            (paths : LiftedCells bank planned) →
              (heads : Heads regular coefficient accuracy positive common bank values planned requests paths) →
                (originalPaid : Plan.commonFloor bank planned ≤ common) →
                  (factory : paths = build bank planned) → {start finish : LiftedPoint 2} →
                    (chain : Nonempty (CenteredPathChain parents (start := start) (finish := finish))) →
                      (keptPath : LiftedPath 2 start finish) →
                        (pathFactory : keptPath = path bank planned paths factory chain) →
                          modelSamples (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
                            (certify (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
                              (sourceDifferential := sourceDifferential) (count := count)
                              (error := error) (errorPositive := errorPositive) (floor := floor)
                              regular coefficient accuracy positive common
                              bank values planned requests paths heads
                              originalPaid factory chain keptPath pathFactory) =
                            originalSamples (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
                              (sourceDifferential := sourceDifferential) (count := count)
                              (error := error) (errorPositive := errorPositive) (floor := floor)
                              common bank (values := values)
                              (Heads.original regular coefficient accuracy positive common
                                bank values planned requests paths heads originalPaid) := by
  intro parents bank
  induction bank with
  | nil =>
      intro values planned requests paths heads originalPaid factory start finish chain keptPath pathFactory
      have folded := Bank.fold_nil (motive := CertifyFamily (parameter := parameter) (frame := frame)
        (collar := collar) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := count)
        (error := error) (errorPositive := errorPositive) (floor := floor)
          regular coefficient accuracy positive common)
        (emptyCertificates (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
          (sourceDifferential := sourceDifferential) (count := count)
          (error := error) (errorPositive := errorPositive) (floor := floor)
          regular coefficient accuracy positive common)
        (certifyStep (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
          (sourceDifferential := sourceDifferential) (count := count)
          (error := error) (errorPositive := errorPositive) (floor := floor)
          regular coefficient accuracy positive common)
      have observed := congrArg
        (fun next : CertifyFamily (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
          (sourceDifferential := sourceDifferential) (count := count)
          (error := error) (errorPositive := errorPositive) (floor := floor)
            regular coefficient accuracy positive common .nil =>
          modelSamples (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
            (next values planned requests paths heads originalPaid factory chain keptPath pathFactory)) folded
      cases keptPath with
      | nil =>
          let original := Heads.original regular coefficient accuracy positive common
            .nil values planned requests paths heads originalPaid
          have right := congrArg₂ (fun left right : List Gaussian => (left, right))
            (ExtraCells.weighted_nil original.1 original.2) (ExtraCells.regular_nil original.1 original.2)
          exact observed.trans right.symm
      | cons _head tail =>
          have zero := path_cellCount (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
            (sourceDifferential := sourceDifferential) (count := count)
            (error := error) (errorPositive := errorPositive) (floor := floor) .nil planned paths factory chain
          have counted := (congrArg LiftedPath.cellCount pathFactory).trans zero
          change Nat.succ tail.cellCount = 0 at counted
          exact False.elim (Nat.succ_ne_zero _ counted)
  | cons data rest ih =>
      intro values planned requests paths heads originalPaid factory start finish chain keptPath pathFactory
      have layout := path_cons (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := count)
        (error := error) (errorPositive := errorPositive) (floor := floor) data rest planned paths factory chain
      cases keptPath with
      | nil =>
          have counted := congrArg LiftedPath.cellCount (pathFactory.trans layout)
          change 0 = Nat.succ _ at counted
          exact False.elim (Nat.succ_ne_zero _ counted.symm)
      | @cons _ middle _ keptHead keptTail =>
          have whole := pathFactory.trans layout
          have components := LiftedPath.cons.inj whole
          have middleEq := components.1
          subst middle
          have tailEq : keptTail = path rest planned.2.2.2 paths.2.2.2.2
              (tail_eq data rest planned paths factory) (remaining_chain chain) := eq_of_heq components.2.2
          have originalMax : Nat.max planned.2.2.1.2.2.val (Plan.commonFloor rest planned.2.2.2) ≤ common :=
            Eq.mp (congrArg (fun value : Nat => value ≤ common) (Plan.commonFloor_cons data rest planned)) originalPaid
          have tailPaid := (Data.Nat.Order.le_max_right _ _).trans originalMax
          have folded := Bank.fold_cons (motive := CertifyFamily (parameter := parameter) (frame := frame)
            (collar := collar) (cap := cap)
            (sourceDifferential := sourceDifferential) (count := count)
            (error := error) (errorPositive := errorPositive) (floor := floor)
              regular coefficient accuracy positive common)
            (emptyCertificates (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
              (sourceDifferential := sourceDifferential) (count := count)
              (error := error) (errorPositive := errorPositive) (floor := floor)
              regular coefficient accuracy positive common)
            (certifyStep (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
              (sourceDifferential := sourceDifferential) (count := count)
              (error := error) (errorPositive := errorPositive) (floor := floor)
              regular coefficient accuracy positive common) data rest
          have observed := congrArg
            (fun next : CertifyFamily (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
              (sourceDifferential := sourceDifferential) (count := count)
              (error := error) (errorPositive := errorPositive) (floor := floor)
                regular coefficient accuracy positive common (.cons data rest) =>
              modelSamples (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
                (next values planned requests paths heads originalPaid factory chain
                  (.cons keptHead keptTail) pathFactory)) folded
          have remaining := ih values.2.2 planned.2.2.2 requests.2.2.2 paths.2.2.2.2 heads.2 tailPaid
            (tail_eq data rest planned paths factory) (remaining_chain chain) keptTail tailEq
          have headModels := Heads.original_head_models (parameter := parameter) (frame := frame)
            (collar := collar) (cap := cap)
            (sourceDifferential := sourceDifferential) (count := count)
            (error := error) (errorPositive := errorPositive) (floor := floor)
            data rest values planned regular coefficient accuracy positive common requests paths heads originalPaid
          have headSamples := congrArg (fun models : CellModel × CellModel =>
            (models.1.integralSample, models.2.integralSample)) headModels
          have viewTail := Heads.original_tail (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
            (sourceDifferential := sourceDifferential) (count := count)
            (error := error) (errorPositive := errorPositive) (floor := floor)
            data rest values planned regular coefficient accuracy positive common
            requests paths heads originalPaid tailPaid
          have tailSamples := (congrArg (originalSamples (parameter := parameter) (frame := frame)
            (collar := collar) (cap := cap)
            (sourceDifferential := sourceDifferential) (count := count)
            (error := error) (errorPositive := errorPositive) (floor := floor)
            common rest (values := values.2.2)) viewTail).trans remaining.symm
          let original := Heads.original regular coefficient accuracy positive common
            (.cons data rest) values planned requests paths heads originalPaid
          have right := congrArg₂ (fun left right : List Gaussian => (left, right))
            (ExtraCells.weighted_cons data rest original.1 original.2)
            (ExtraCells.regular_cons data rest original.1 original.2)
          have aligned := congrArg₂
            (fun head : Gaussian × Gaussian => fun tail : List Gaussian × List Gaussian =>
              (head.1 :: tail.1, head.2 :: tail.2)) headSamples tailSamples
          exact observed.trans (right.trans aligned).symm

/-- Read both total weighted allowances from the supplied actual retained model lists. -/
private def modelAllowances {start finish : LiftedPoint 2} {keptPath : LiftedPath 2 start finish}
    (retained : CertifiedModels (parameter := parameter) (frame := frame)
      (collar := collar) (cap := cap) keptPath) : Coordinate × Coordinate :=
  ((PathModel.mk retained.1.1).totalWeightedAllowance, (PathModel.mk retained.1.2).totalWeightedAllowance)

/-- The same retained pullbacks have the original parent movement sum times their unchanged local allowance. -/
private theorem certify_allowances
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) → (values : Potentials bank) →
        (planned : Plan error errorPositive floor bank) →
          (requests : Requests regular coefficient accuracy positive bank planned) →
            (paths : LiftedCells bank planned) →
              (heads : Heads regular coefficient accuracy positive common bank values planned requests paths) →
                (originalPaid : Plan.commonFloor bank planned ≤ common) →
                  (factory : paths = build bank planned) → {start finish : LiftedPoint 2} →
                    (chain : Nonempty (CenteredPathChain parents (start := start) (finish := finish))) →
                      (keptPath : LiftedPath 2 start finish) →
                        (pathFactory : keptPath = path bank planned paths factory chain) →
                          modelAllowances (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
                            (certify (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
                              (sourceDifferential := sourceDifferential) (count := count)
                              (error := error) (errorPositive := errorPositive) (floor := floor)
                              regular coefficient accuracy positive common
                              bank values planned requests paths heads
                              originalPaid factory chain keptPath pathFactory) =
                            (movementSum parents * error, movementSum parents * error) := by
  intro parents bank
  induction bank with
  | nil =>
      intro values planned requests paths heads originalPaid factory start finish chain keptPath pathFactory
      have folded := Bank.fold_nil (motive := CertifyFamily (parameter := parameter) (frame := frame)
        (collar := collar) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := count)
        (error := error) (errorPositive := errorPositive) (floor := floor)
          regular coefficient accuracy positive common)
        (emptyCertificates (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
          (sourceDifferential := sourceDifferential) (count := count)
          (error := error) (errorPositive := errorPositive) (floor := floor)
          regular coefficient accuracy positive common)
        (certifyStep (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
          (sourceDifferential := sourceDifferential) (count := count)
          (error := error) (errorPositive := errorPositive) (floor := floor)
          regular coefficient accuracy positive common)
      have observed := congrArg
        (fun next : CertifyFamily (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
          (sourceDifferential := sourceDifferential) (count := count)
          (error := error) (errorPositive := errorPositive) (floor := floor)
            regular coefficient accuracy positive common .nil =>
          modelAllowances (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
            (next values planned requests paths heads originalPaid factory chain keptPath pathFactory)) folded
      cases keptPath with
      | nil =>
          have zero := Field.zero_mul_direct error
          exact observed.trans (congrArg (fun value : Coordinate => (value, value)) zero).symm
      | cons _head tail =>
          have zero := path_cellCount (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
            (sourceDifferential := sourceDifferential) (count := count)
            (error := error) (errorPositive := errorPositive) (floor := floor) .nil planned paths factory chain
          have counted := (congrArg LiftedPath.cellCount pathFactory).trans zero
          change Nat.succ tail.cellCount = 0 at counted
          exact False.elim (Nat.succ_ne_zero _ counted)
  | @cons parent parents data rest ih =>
      intro values planned requests paths heads originalPaid factory start finish chain keptPath pathFactory
      have layout := path_cons (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := count)
        (error := error) (errorPositive := errorPositive) (floor := floor) data rest planned paths factory chain
      cases keptPath with
      | nil =>
          have counted := congrArg LiftedPath.cellCount (pathFactory.trans layout)
          change 0 = Nat.succ _ at counted
          exact False.elim (Nat.succ_ne_zero _ counted.symm)
      | @cons _ middle _ keptHead keptTail =>
          have whole := pathFactory.trans layout
          have components := LiftedPath.cons.inj whole
          have middleEq := components.1
          subst middle
          have tailEq : keptTail = path rest planned.2.2.2 paths.2.2.2.2
              (tail_eq data rest planned paths factory) (remaining_chain chain) := eq_of_heq components.2.2
          have originalMax : Nat.max planned.2.2.1.2.2.val (Plan.commonFloor rest planned.2.2.2) ≤ common :=
            Eq.mp (congrArg (fun value : Nat => value ≤ common) (Plan.commonFloor_cons data rest planned)) originalPaid
          have tailPaid := (Data.Nat.Order.le_max_right _ _).trans originalMax
          have folded := Bank.fold_cons (motive := CertifyFamily (parameter := parameter) (frame := frame)
            (collar := collar) (cap := cap)
            (sourceDifferential := sourceDifferential) (count := count)
            (error := error) (errorPositive := errorPositive) (floor := floor)
              regular coefficient accuracy positive common)
            (emptyCertificates (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
              (sourceDifferential := sourceDifferential) (count := count)
              (error := error) (errorPositive := errorPositive) (floor := floor)
              regular coefficient accuracy positive common)
            (certifyStep (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
              (sourceDifferential := sourceDifferential) (count := count)
              (error := error) (errorPositive := errorPositive) (floor := floor)
              regular coefficient accuracy positive common) data rest
          have observed := congrArg
            (fun next : CertifyFamily (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
              (sourceDifferential := sourceDifferential) (count := count)
              (error := error) (errorPositive := errorPositive) (floor := floor)
                regular coefficient accuracy positive common (.cons data rest) =>
              modelAllowances (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
                (next values planned requests paths heads originalPaid factory chain
                  (.cons keptHead keptTail) pathFactory)) folded
          have remaining := ih values.2.2 planned.2.2.2 requests.2.2.2 paths.2.2.2.2 heads.2 tailPaid
            (tail_eq data rest planned paths factory) (remaining_chain chain) keptTail tailEq
          have displacement := congrArg₂ (fun last first : Gaussian => last - first) data.last_eq data.first_eq
          have movement : Basic.Canonical.normSq
              (data.segment.comparison.last - data.segment.comparison.first) = parent.edge.pointMovement :=
            (Norm.Basic.normSq_eq_canonical _).symm.trans (congrArg Norm.Basic.normSq displacement)
          have weighted := heads.1.pullbacks.1.val.weightedAllowance_eq
          have regularHead := heads.1.pullbacks.2.val.weightedAllowance_eq
          have head := congrArg₂ (fun first second : Coordinate => (first, second))
            (weighted.trans (congrArg (fun value : Coordinate => value * error) movement))
            (regularHead.trans (congrArg (fun value : Coordinate => value * error) movement))
          have aligned := congrArg₂
            (fun first second : Coordinate × Coordinate => (first.1 + second.1, first.2 + second.2))
            head remaining
          have scalar : parent.edge.pointMovement * error + movementSum parents * error =
              movementSum (parent :: parents) * error := by
            change parent.edge.pointMovement * error + movementSum parents * error =
              (parent.edge.pointMovement + movementSum parents) * error
            ring1
          exact observed.trans (aligned.trans (congrArg (fun value : Coordinate => (value, value)) scalar))

end LiftedCells

namespace Materialized

/-- Attach both model-certificate banks to a supplied actual path using its original cached-path identity.

Only uniform certificate/model-list assembly executes. The supplied
Materialized and path remain intact; no request, model, Head, original
view or lifted path is rebuilt. The same source callback owners remain
available through the original Head certificate readbacks.
-/
def certifyOnPath
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat)
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (bank : Bank cap sourceDifferential count parents) (values : Potentials bank)
    (planned : Plan error errorPositive floor bank)
    (requests : Requests regular coefficient accuracy positive bank planned) (paths : LiftedCells bank planned)
    (originalPaid : Plan.commonFloor bank planned ≤ common)
    (actual : Materialized regular coefficient accuracy positive common
      bank values planned requests paths originalPaid)
    (factory : paths = LiftedCells.build bank planned) {start finish : LiftedPoint 2}
    (chain : Nonempty (CenteredPathChain parents (start := start) (finish := finish)))
    (keptPath : LiftedPath 2 start finish)
    (pathFactory : keptPath = LiftedCells.path bank planned paths factory chain) :
    LiftedCells.CertifiedModels (parameter := parameter) (frame := frame) (collar := collar) (cap := cap) keptPath :=
  LiftedCells.certify (parameter := parameter) (frame := frame) (cap := cap)
    (sourceDifferential := sourceDifferential) (count := count)
    (error := error) (errorPositive := errorPositive) (floor := floor)
    regular coefficient accuracy positive common bank values planned requests paths actual.heads
    originalPaid factory chain keptPath pathFactory

/-- The GIVEN retained certificate/model cache reads the same two integral lists as this actual original bank.

The supplied equality names the one already constructed cache. Both
complete original head models and whole tail identities are consumed
pointwise, so this law neither reruns certifyOnPath nor materializes a
second work bank. It preserves order, repeats and stationary occurrences.
-/
theorem integral_lists_eq
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat)
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (bank : Bank cap sourceDifferential count parents) (values : Potentials bank)
    (planned : Plan error errorPositive floor bank)
    (requests : Requests regular coefficient accuracy positive bank planned) (paths : LiftedCells bank planned)
    (originalPaid : Plan.commonFloor bank planned ≤ common)
    (actual : Materialized regular coefficient accuracy positive common
      bank values planned requests paths originalPaid)
    (factory : paths = LiftedCells.build bank planned) {start finish : LiftedPoint 2}
    (chain : Nonempty (CenteredPathChain parents (start := start) (finish := finish)))
    (keptPath : LiftedPath 2 start finish)
    (pathFactory : keptPath = LiftedCells.path bank planned paths factory chain)
    (retained : LiftedCells.CertifiedModels (parameter := parameter) (frame := frame)
      (collar := collar) (cap := cap) keptPath)
    (retainedFactory : retained = certifyOnPath regular coefficient accuracy positive common
      bank values planned requests paths originalPaid actual factory chain keptPath pathFactory) :
    (retained.1.1.map CellModel.integralSample, retained.1.2.map CellModel.integralSample) =
      (ExtraCells.weighted bank actual.original.1 actual.original.2,
        ExtraCells.regular bank actual.original.1 actual.original.2) := by
  have same := LiftedCells.certify_samples (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
    (sourceDifferential := sourceDifferential) (count := count)
    (error := error) (errorPositive := errorPositive) (floor := floor)
    regular coefficient accuracy positive common bank values planned requests paths actual.heads
    originalPaid factory chain keptPath pathFactory
  have actualView := Materialized.original_eq actual
  have viewSamples := congrArg (LiftedCells.originalSamples (parameter := parameter) (frame := frame)
    (collar := collar) (cap := cap)
    (sourceDifferential := sourceDifferential) (count := count)
    (error := error) (errorPositive := errorPositive) (floor := floor)
    common bank (values := values)) actualView
  have cacheSamples := congrArg
    (LiftedCells.modelSamples (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)) retainedFactory
  exact cacheSamples.trans (same.trans viewSamples.symm)

/-- Both GIVEN retained model lists have exactly the original parent movement mass times their local allowance.

The original cached pullbacks retain that same allowance and their actual
segment endpoints. The whole retained factory equality identifies the
supplied lists; neither models nor geometry are reconstructed for this law.
-/
theorem allowances_eq
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat)
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (bank : Bank cap sourceDifferential count parents) (values : Potentials bank)
    (planned : Plan error errorPositive floor bank)
    (requests : Requests regular coefficient accuracy positive bank planned) (paths : LiftedCells bank planned)
    (originalPaid : Plan.commonFloor bank planned ≤ common)
    (actual : Materialized regular coefficient accuracy positive common
      bank values planned requests paths originalPaid)
    (factory : paths = LiftedCells.build bank planned) {start finish : LiftedPoint 2}
    (chain : Nonempty (CenteredPathChain parents (start := start) (finish := finish)))
    (keptPath : LiftedPath 2 start finish)
    (pathFactory : keptPath = LiftedCells.path bank planned paths factory chain)
    (retained : LiftedCells.CertifiedModels (parameter := parameter) (frame := frame)
      (collar := collar) (cap := cap) keptPath)
    (retainedFactory : retained = certifyOnPath regular coefficient accuracy positive common
      bank values planned requests paths originalPaid actual factory chain keptPath pathFactory) :
    ((PathModel.mk retained.1.1).aggregateAllowance, (PathModel.mk retained.1.2).aggregateAllowance) =
      (movementMass parents * error, movementMass parents * error) := by
  have same := LiftedCells.certify_allowances (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
    (sourceDifferential := sourceDifferential) (count := count)
    (error := error) (errorPositive := errorPositive) (floor := floor)
    regular coefficient accuracy positive common bank values planned requests paths actual.heads
    originalPaid factory chain keptPath pathFactory
  have cache := congrArg
    (LiftedCells.modelAllowances (parameter := parameter) (frame := frame) (collar := collar) (cap := cap))
    retainedFactory
  have totals := cache.trans same
  have counts := LiftedCells.CertifiedModels.lengths (parameter := parameter) (frame := frame)
    (collar := collar) (cap := cap) retained
  have countEq := (congrArg LiftedPath.cellCount pathFactory).trans
    (LiftedCells.path_cellCount (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor) bank planned paths factory chain)
  have firstCount := counts.1.trans countEq
  have secondCount := counts.2.trans countEq
  have first := congrArg₂ (fun size : Nat => fun total : Coordinate => (size : Coordinate) * total)
    firstCount (congrArg (fun pair : Coordinate × Coordinate => pair.1) totals)
  have second := congrArg₂ (fun size : Nat => fun total : Coordinate => (size : Coordinate) * total)
    secondCount (congrArg (fun pair : Coordinate × Coordinate => pair.2) totals)
  have scalar : (parents.length : Coordinate) * (movementSum parents * error) = movementMass parents * error := by
    rewrite [movementMass_eq]
    ring1
  exact congrArg₂ (fun first second : Coordinate => (first, second)) (first.trans scalar) (second.trans scalar)

end Materialized

end Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Plan.Primitive

end
