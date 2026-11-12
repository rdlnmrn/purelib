module
import Purelib.Data.Fin
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator
import Purelib.Approximation.Gaussian.Arithmetic.Add
import Purelib.Approximation.Gaussian.Arithmetic.Mul
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Run
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.State
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Vector.Operational.Basic
import Purelib.Approximation.Matrix.Operational.Integral.Action
public import Purelib.Curves.Legendre.GaussManin.Endpoint
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Dual
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Basic
import Purelib.Approximation.Matrix.Operational.Integral.Word
public import Purelib.Curves.Legendre.FractionalWords.Periods

import Purelib.Curves.Legendre.Monodromy
import Purelib.Curves.Legendre.Paths
import Purelib.Riemann.Integration.LegendreModularMonodromy
import Purelib.Riemann.Periods.PeriodMatrix
import Init.Data.Fin.Basic
import Init.Data.Fin.Lemmas
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Matrix.Integral.Two

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Arithmetic

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Words

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Approximation.Gaussian.Vector

open Purelib.Approximation.Gaussian.Vector.Operational.Basic

open Purelib.Approximation.Matrix.Operational.Integral

open Purelib.Curves.Legendre

open Purelib.Curves.Legendre.FractionalWords

open Purelib.Curves.Legendre.GaussManin

open Purelib.Curves.Legendre.GaussManin.Endpoint

open Purelib.Curves.Legendre.Periods

open Purelib.LinearAlgebra.Matrix

open Purelib.Riemann.Integration

open Purelib.Riemann.Periods

open Purelib.Topology.Knot.Braid.ThreeStrand.Integral

public section

/-!
# Dual finite period monodromy for the Legendre family

`wordMatrix` acts on homology-coordinate columns.  Periods evaluated on the
transported basis therefore carry `periodMatrix = transpose wordMatrix`.
This module gives that dual action its own normalized public interface.  It
does not identify periods on distinct endpoint curves.

The unconditional layer retains homogeneous period columns.  Productive
division is added only for the two standard dual actions whose first row is
not the constant unit.
-/

namespace Purelib.Curves.Legendre.PeriodMonodromy

open Purelib.Riemann.Integration.LegendreGaussManin
open Purelib.Riemann.Integration.LegendreModularMonodromy
open Purelib.Riemann.Integration.LegendreFractionalAction
open Purelib.Riemann.Integration.LegendreFractionalWords

/-- Exact Gaussian rational parameters and matrix coefficients. -/
abbrev Gaussian := Data.Gaussian.Basic.Canonical
/-- A finite two-dimensional integral matrix acting on the retained homology coordinates. -/
abbrev IntegralMatrix :=
  Basic.IntegralMatrix
/-- A Gaussian name with its retained coherent sample realization. -/
abbrev CoherentNamed := Coherent.CoherentNamed
/-- Operational equivalence of two retained named Gaussian quantities. -/
abbrev NamedEquivalent := Gaussian.Equivalence.NamedEquivalent
/-- The ordered pair of retained coherent A-period and B-period names. -/
abbrev RawPeriodVector := Operational.Basic.RawPeriodVector
/-- Coordinatewise operational equivalence of the two retained period columns. -/
abbrev VectorEquivalent := Operational.Basic.VectorEquivalent
/-- Typed apartness and productive division data for the original coherent denominator. -/
abbrev DenominatorPreparation :=
  Prepared.DenominatorPreparation

/-! ## One normalized fibre and its transported period columns -/

set_option genInjectivity false in
/-- Normalized period data needed by dual closed-loop transport. Unlike the legacy cancellation interface, this
structure does not demand a uniform lower bound for every coarse A-period sampler. A tail-separated scaled inverse
already contains exactly the apartness needed to define `tau`. -/
structure NormalizedData {parameter : Gaussian}
    (frame : Paths.Frame parameter) where
  /-- The retained normalized period data for this exact original framed curve. -/ normalized :
    PeriodMatrix.NormalizedPeriodData
    (Fibre.frameCurve frame)

constructive_injectivity NormalizedData

namespace NormalizedData

/-- Forget normalized inverse data while retaining the exact underlying period programs. -/
@[expose] def toFibreData {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    (data : NormalizedData frame) :
    Fibre.FibreData frame where
  periods := data.normalized.toPeriodData

/-- Read the original A-period name from the normalized base fibre. -/
@[expose] def aPeriod {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    (data : NormalizedData frame) : CoherentNamed :=
  data.normalized.toPeriodData.aMatrix 0 0

/-- Read the original B-period name from the normalized base fibre. -/
@[expose] def bPeriod {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    (data : NormalizedData frame) : CoherentNamed :=
  data.normalized.toPeriodData.bMatrix 0 0

/-- Read the normalized period ratio from the retained scaled inverse. -/
@[expose] def ratio {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    (data : NormalizedData frame) : CoherentNamed :=
  data.normalized.omega 0 0

/-- The normalized raw column identity requires only the scaled inverse already stored by `NormalizedPeriodData`. -/
@[expose] def raw_normalized {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    (data : NormalizedData frame) :
    VectorEquivalent data.toFibreData.rawPeriods
      (scaleVector data.aPeriod (fractionalVector data.ratio)) := by
  intro coordinate
  let comparison : Fin 2 → Type := fun index =>
    NamedEquivalent
      (data.toFibreData.rawPeriods index).name
      (scaleVector data.aPeriod
        (fractionalVector data.ratio) index).name
  refine Data.Fin.casesDependent (size := 1) (motive := comparison) ?_
    (fun tail => Data.Fin.casesDependent (size := 0)
      (motive := fun index => comparison index.succ) ?_
      (fun impossible => False.elim (Nat.not_lt_zero impossible.val impossible.isLt)) tail) coordinate
  · exact NamedEquivalent.symm
      (Mul.coherentMul_one_right data.aPeriod)
  · exact NamedEquivalent.symm
      (NormalizedFibreData.normalized_a_mul_ratio
        data.normalized)

/-- The finite endpoint-continuation object for any certified closed path on this normalized fibre. -/
@[expose] def continuation {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    (data : NormalizedData frame)
    (path : Paths.Path frame frame) :
    EndpointContinuation path where
  source := data.toFibreData
  target := data.toFibreData

/-- Actual periods on the base fibre evaluated on the homology basis transported around an arbitrary certified finite
loop. -/
@[expose] def periods {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    (data : NormalizedData frame)
    (path : Paths.Path frame frame) : RawPeriodVector :=
  (data.continuation path).periods

/-- The arbitrary-loop period column is the original `A` scale times the exact dual matrix acting on `(1,tau)`. -/
@[expose] def periods_normalized {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    (data : NormalizedData frame)
    (path : Paths.Path frame frame) :
    VectorEquivalent (data.periods path)
      (scaleVector data.aPeriod
        (Action.matrixAction
          (Dual.periodMatrix path.word)
          (fractionalVector data.ratio))) :=
  VectorEquivalent.trans
    (Action.matrixAction_respects _ data.raw_normalized)
    (matrixAction_scale _ data.aPeriod (fractionalVector data.ratio))

/-- Every legacy normalized fibre forgets to the smaller dual-transport interface without changing its period programs
or ratio. -/
@[expose] def ofLegacy {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    (data : NormalizedFibreData frame) :
    NormalizedData frame where
  normalized := data.normalized

end NormalizedData

set_option genInjectivity false in
/-- The normalized base fibre used by all standard closed-loop transports. -/
structure Data {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    (loops : Monodromy.StandardLoops frame) where
  /-- The original normalized base fibre shared by the retained standard loops. -/ base :
    NormalizedData frame

constructive_injectivity Data

namespace Data

/-- The generic finite endpoint-continuation object for a closed path on the normalized base fibre. -/
@[expose] def continuation {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Data loops) (path : Paths.Path frame frame) :
    EndpointContinuation path :=
  data.base.continuation path

/-- Actual base-fibre periods evaluated on the basis transported around a certified closed path. -/
@[expose] def periods {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Data loops) (path : Paths.Path frame frame) :
    RawPeriodVector :=
  data.base.periods path

/-- Transporting a normalized raw column is homogeneous matrix action on `(1,tau)`, with the original `A` period
retained as common scale. -/
@[expose] def periods_normalized {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Data loops) (path : Paths.Path frame frame) :
    VectorEquivalent (data.periods path)
      (scaleVector data.base.aPeriod
        (Action.matrixAction
          (Dual.periodMatrix path.word)
          (fractionalVector data.base.ratio))) :=
  data.base.periods_normalized path

/-- Evaluate base-fibre periods on the basis transported around the retained zero loop. -/
@[expose] def zeroPeriods {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Data loops) : RawPeriodVector := data.periods loops.zeroPath

/-- Evaluate base-fibre periods on the basis transported around the retained one loop. -/
@[expose] def onePeriods {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Data loops) : RawPeriodVector := data.periods loops.onePath

/-- Evaluate base-fibre periods on the basis transported around the retained infinity loop. -/
@[expose] def infinityPeriods {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Data loops) : RawPeriodVector := data.periods loops.infinityPath

/-- Evaluate base-fibre periods on the basis transported around the retained product loop. -/
@[expose] def productPeriods {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Data loops) : RawPeriodVector := data.periods loops.productPath

/-- The zero-loop period column is the original A-period times its exact dual homogeneous action. -/
@[expose] def zero_homogeneous {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Data loops) :
    VectorEquivalent data.zeroPeriods
      (scaleVector data.base.aPeriod
        (Action.matrixAction Monodromy.zeroPeriodMatrix
          (fractionalVector data.base.ratio))) := by
  simpa only [zeroPeriods] using data.periods_normalized loops.zeroPath
    |>.trans (fun coordinate => by
      rw [loops.zeroPath_periodMatrix]
      exact NamedEquivalent.refl _)

/-- The one-loop period column is the original A-period times its exact dual homogeneous action. -/
@[expose] def one_homogeneous {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Data loops) :
    VectorEquivalent data.onePeriods
      (scaleVector data.base.aPeriod
        (Action.matrixAction Monodromy.onePeriodMatrix
          (fractionalVector data.base.ratio))) := by
  simpa only [onePeriods] using data.periods_normalized loops.onePath
    |>.trans (fun coordinate => by
      rw [loops.onePath_periodMatrix]
      exact NamedEquivalent.refl _)

/-- The infinity-loop period column is the original A-period times its exact dual homogeneous action. -/
@[expose] def infinity_homogeneous {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Data loops) :
    VectorEquivalent data.infinityPeriods
      (scaleVector data.base.aPeriod
        (Action.matrixAction Monodromy.infinityPeriodMatrix
          (fractionalVector data.base.ratio))) := by
  simpa only [infinityPeriods] using data.periods_normalized loops.infinityPath
    |>.trans (fun coordinate => by
      rw [loops.infinityPath_periodMatrix]
      exact NamedEquivalent.refl _)

/-- The retained product loop acts as the identity on the original period column. -/
@[expose] def product_identity {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Data loops) :
    VectorEquivalent data.productPeriods data.base.toFibreData.rawPeriods := by
  unfold productPeriods
    Data.periods NormalizedData.periods
    NormalizedData.continuation EndpointContinuation.periods
  rw [loops.productPath_periodMatrix]
  exact Action.matrixAction_identity data.base.toFibreData.rawPeriods

end Data

/-! ## Exact standard dual rows -/

/-- The coherent affine transform tau minus two for the zero-loop dual action. -/
@[expose] def zeroAffineTransform (tau : CoherentNamed) : CoherentNamed :=
  add
    (Coherence.exact (-2)) tau

/-- The coherent denominator one plus twice tau for the one-loop dual action. -/
@[expose] def oneDenominator (tau : CoherentNamed) : CoherentNamed :=
  add
    (Coherence.exact 1)
    (mul
      (Coherence.exact 2) tau)

/-- The coherent denominator minus three minus twice tau for the infinity-loop dual action. -/
@[expose] def infinityDenominator (tau : CoherentNamed) : CoherentNamed :=
  add
    (Coherence.exact (-3))
    (mul
      (Coherence.exact (-2)) tau)

/-- The coherent numerator two plus tau for the infinity-loop dual action. -/
@[expose] def infinityNumerator (tau : CoherentNamed) : CoherentNamed :=
  add
    (Coherence.exact 2) tau

/-- Around zero the transformed `A` coordinate is exactly the original `A`: the dual denominator is the constant unit.
-/
@[expose] def zero_denominator_one (tau : CoherentNamed) :
    NamedEquivalent
      (fractionalDenominator
        Monodromy.zeroPeriodMatrix tau).name
      (Coherence.exact 1).name := by
  let one := Coherence.exact 1
  let zero := Coherence.exact 0
  have expanded := matrixAction_row_two
    Monodromy.zeroPeriodMatrix
    (fractionalVector tau) 0
  rw [Monodromy.zeroPeriodMatrix_explicit] at expanded
  change NamedEquivalent
    (fractionalDenominator
      Monodromy.zeroPeriodMatrix tau).name
    (add
      (mul one one)
      (mul zero tau)).name at expanded
  have simplifyTerms : NamedEquivalent
      (add
        (mul one one)
        (mul zero tau)).name
      (add one zero).name :=
    Congruence.coherentAdd_respects
      (mul one one) one
      (mul zero tau) zero
      (Mul.coherentMul_one_right one)
      (Mul.coherentMul_zero_left tau)
  exact NamedEquivalent.trans expanded
    (NamedEquivalent.trans
      simplifyTerms
      (Add.coherentAdd_zero_right one))

/-- The zero-loop homogeneous numerator is operationally the affine transform tau minus two. -/
@[expose] def zero_numerator_affine (tau : CoherentNamed) :
    NamedEquivalent
      (fractionalNumerator
        Monodromy.zeroPeriodMatrix tau).name
      (zeroAffineTransform tau).name := by
  let one := Coherence.exact 1
  let minusTwo := Coherence.exact (-2)
  have expanded := matrixAction_row_two
    Monodromy.zeroPeriodMatrix
    (fractionalVector tau) 1
  rw [Monodromy.zeroPeriodMatrix_explicit] at expanded
  change NamedEquivalent
    (fractionalNumerator
      Monodromy.zeroPeriodMatrix tau).name
    (add
      (mul minusTwo one)
      (mul one tau)).name at expanded
  exact NamedEquivalent.trans expanded
    (by
      simpa only [zeroAffineTransform,
        CoherentNamed.add] using
        Congruence.coherentAdd_respects _ _ _ _
          (Mul.coherentMul_one_right minusTwo)
          (Mul.coherentMul_one_left tau))

/-- The one-loop homogeneous denominator is operationally one plus twice tau. -/
@[expose] def one_denominator_explicit (tau : CoherentNamed) :
    NamedEquivalent
      (fractionalDenominator
        Monodromy.onePeriodMatrix tau).name
      (oneDenominator tau).name := by
  let one := Coherence.exact 1
  let two := Coherence.exact 2
  have expanded := matrixAction_row_two
    Monodromy.onePeriodMatrix
    (fractionalVector tau) 0
  rw [Monodromy.onePeriodMatrix_explicit] at expanded
  change NamedEquivalent
    (fractionalDenominator
      Monodromy.onePeriodMatrix tau).name
    (add
      (mul one one)
      (mul two tau)).name at expanded
  exact NamedEquivalent.trans expanded
    (by
      simpa only [oneDenominator,
        CoherentNamed.add] using
        Congruence.coherentAdd_respects _ _ _ _
          (Mul.coherentMul_one_right one)
          (NamedEquivalent.refl _))

/-- The one-loop homogeneous numerator is operationally the original tau name. -/
@[expose] def one_numerator_tau (tau : CoherentNamed) :
    NamedEquivalent
      (fractionalNumerator
        Monodromy.onePeriodMatrix tau).name tau.name := by
  let one := Coherence.exact 1
  let zero := Coherence.exact 0
  have expanded := matrixAction_row_two
    Monodromy.onePeriodMatrix
    (fractionalVector tau) 1
  rw [Monodromy.onePeriodMatrix_explicit] at expanded
  change NamedEquivalent
    (fractionalNumerator
      Monodromy.onePeriodMatrix tau).name
    (add
      (mul zero one)
      (mul one tau)).name at expanded
  have simplifyTerms : NamedEquivalent
      (add
        (mul zero one)
        (mul one tau)).name
      (add zero tau).name :=
    Congruence.coherentAdd_respects
      (mul zero one) zero
      (mul one tau) tau
      (Mul.coherentMul_zero_left one)
      (Mul.coherentMul_one_left tau)
  exact NamedEquivalent.trans expanded
    (NamedEquivalent.trans
      simplifyTerms
      (Add.coherentAdd_zero_left tau))

/-- The infinity-loop homogeneous denominator is operationally minus three minus twice tau. -/
@[expose] def infinity_denominator_explicit (tau : CoherentNamed) :
    NamedEquivalent
      (fractionalDenominator
        Monodromy.infinityPeriodMatrix tau).name
      (infinityDenominator tau).name := by
  let one := Coherence.exact 1
  let minusThree := Coherence.exact (-3)
  let minusTwo := Coherence.exact (-2)
  have expanded := matrixAction_row_two
    Monodromy.infinityPeriodMatrix
    (fractionalVector tau) 0
  rw [Monodromy.infinityPeriodMatrix_explicit] at expanded
  change NamedEquivalent
    (fractionalDenominator
      Monodromy.infinityPeriodMatrix tau).name
    (add
      (mul minusThree one)
      (mul minusTwo tau)).name at expanded
  exact NamedEquivalent.trans expanded
    (by
      simpa only [infinityDenominator,
        CoherentNamed.add] using
        Congruence.coherentAdd_respects _ _ _ _
          (Mul.coherentMul_one_right minusThree)
          (NamedEquivalent.refl _))

/-- The infinity-loop homogeneous numerator is operationally two plus tau. -/
@[expose] def infinity_numerator_explicit (tau : CoherentNamed) :
    NamedEquivalent
      (fractionalNumerator
        Monodromy.infinityPeriodMatrix tau).name
      (infinityNumerator tau).name := by
  let one := Coherence.exact 1
  let two := Coherence.exact 2
  have expanded := matrixAction_row_two
    Monodromy.infinityPeriodMatrix
    (fractionalVector tau) 1
  rw [Monodromy.infinityPeriodMatrix_explicit] at expanded
  change NamedEquivalent
    (fractionalNumerator
      Monodromy.infinityPeriodMatrix tau).name
    (add
      (mul two one)
      (mul one tau)).name at expanded
  exact NamedEquivalent.trans expanded
    (by
      simpa only [infinityNumerator,
        CoherentNamed.add] using
        Congruence.coherentAdd_respects _ _ _ _
          (Mul.coherentMul_one_right two)
          (Mul.coherentMul_one_left tau))

/-! ## Unconditional and productive headline packages -/

/-- Multiplication by the same coherent scale preserves coordinatewise period equivalence. -/
@[expose] def scaleVector_respects (scalar : CoherentNamed)
    {left right : RawPeriodVector} (equivalent :
      VectorEquivalent left right) :
    VectorEquivalent (scaleVector scalar left)
      (scaleVector scalar right) :=
  fun coordinate => Congruence.coherentMul_respects
    scalar scalar (left coordinate) (right coordinate)
    (NamedEquivalent.refl scalar.name)
    (equivalent coordinate)

/-- Arbitrary finite-word dual period transport. The actual periods from `EndpointContinuation` are the original `A`
scale times the stepwise action of the reversed transposed generator matrices on `(1,tau)`. -/
@[expose] def NormalizedData.periodWord_homogeneous {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    (data : NormalizedData frame)
    (path : Paths.Path frame frame) :
    VectorEquivalent (data.periods path)
      (scaleVector data.aPeriod
        (Word.blockAction (Periods.periodBraidMatrices path.word)
          (fractionalVector data.ratio))) :=
  VectorEquivalent.trans (data.periods_normalized path)
    (scaleVector_respects data.aPeriod
      (Periods.periodBraidRows_word path.word data.ratio))

/-- Standard-loop data inherits the arbitrary-word homogeneous theorem without adding any premise. -/
@[expose] def Data.periodWord_homogeneous {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Data loops) (path : Paths.Path frame frame) :
    VectorEquivalent (data.periods path)
      (scaleVector data.base.aPeriod
        (Word.blockAction (Periods.periodBraidMatrices path.word)
          (fractionalVector data.base.ratio))) :=
  data.base.periodWord_homogeneous path

/-- The zero-loop homogeneous matrix action gives the unit row and affine tau-minus-two row. -/
@[expose] def zero_rows_affine (tau : CoherentNamed) :
    VectorEquivalent
      (Action.matrixAction Monodromy.zeroPeriodMatrix
        (fractionalVector tau))
      (fractionalVector (zeroAffineTransform tau)) := by
  intro coordinate
  let comparison : Fin 2 → Type := fun index =>
    NamedEquivalent
      (Action.matrixAction Monodromy.zeroPeriodMatrix
        (fractionalVector tau) index).name
      (fractionalVector
        (zeroAffineTransform tau) index).name
  refine Data.Fin.casesDependent (size := 1) (motive := comparison) ?_
    (fun tail => Data.Fin.casesDependent (size := 0)
      (motive := fun index => comparison index.succ) ?_
      (fun impossible => False.elim (Nat.not_lt_zero impossible.val impossible.isLt)) tail) coordinate
  · exact zero_denominator_one tau
  · exact zero_numerator_affine tau

/-- The actual zero-loop period column equals the original A-period scale times the affine normalized column. -/
@[expose] def Data.zero_affine {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Data loops) :
    VectorEquivalent data.zeroPeriods
      (scaleVector data.base.aPeriod
        (fractionalVector (zeroAffineTransform
          data.base.ratio))) :=
  VectorEquivalent.trans data.zero_homogeneous
    (scaleVector_respects data.base.aPeriod
      (zero_rows_affine data.base.ratio))

set_option genInjectivity false in
/-- Small carrier whose generated recursor never unfolds the large period programs appearing in the public statement
types. -/
structure FractionFreeCertificatePayload
    (zeroType oneType infinityType productType : Type)
    (inverseType : Prop) where
  /-- The retained unconditional affine zero-loop period identity. -/ zero : zeroType
  /-- The retained homogeneous one-loop period identity. -/ one : oneType
  /-- The retained homogeneous infinity-loop period identity. -/ infinity : infinityType
  /-- The retained identity action of the standard product loop. -/ product : productType
  /-- The retained standard dual matrices satisfy the two explicit inverse product identities. -/ inverseMatrices :
    inverseType

constructive_injectivity FractionFreeCertificatePayload

/-- Unconditional certificate for the correct dual period action. Its zero-loop formula is already productive because
that dual denominator is exactly one. -/
@[expose] def FractionFreeCertificate {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Data loops) : Type :=
  FractionFreeCertificatePayload
    (VectorEquivalent data.zeroPeriods
      (scaleVector data.base.aPeriod
        (fractionalVector (zeroAffineTransform
          data.base.ratio))))
    (VectorEquivalent data.onePeriods
      (scaleVector data.base.aPeriod
        (Action.matrixAction Monodromy.onePeriodMatrix
          (fractionalVector data.base.ratio))))
    (VectorEquivalent data.infinityPeriods
      (scaleVector data.base.aPeriod
        (Action.matrixAction Monodromy.infinityPeriodMatrix
          (fractionalVector data.base.ratio))))
    (VectorEquivalent data.productPeriods data.base.toFibreData.rawPeriods)
    (Multiplication.mul
          (Multiplication.mul
            Monodromy.zeroPeriodMatrix
            Monodromy.onePeriodMatrix)
          Monodromy.infinityPeriodMatrix =
        Multiplication.identity ∧
      Multiplication.mul
          Monodromy.infinityPeriodMatrix
          (Multiplication.mul
            Monodromy.zeroPeriodMatrix
            Monodromy.onePeriodMatrix) =
        Multiplication.identity)

/-- Construct the fraction-free standard-loop certificate from the retained normalized fibre and exact dual matrix
identities. -/
@[expose] def certificate {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Data loops) :
      FractionFreeCertificate data := by
  unfold FractionFreeCertificate
  exact
    { zero := data.zero_affine
      one := data.one_homogeneous
      infinity := data.infinity_homogeneous
      product := data.product_identity
      inverseMatrices :=
        ⟨Monodromy.explicit_period_product_left,
          Monodromy.explicit_period_product_right⟩ }

/-- Productive denominator data for the exact one-loop dual denominator at the original tau. -/
abbrev OnePreparation (tau : CoherentNamed) :=
  DenominatorPreparation
    (fractionalDenominator Monodromy.onePeriodMatrix tau)

/-- Productive denominator data for the exact infinity-loop dual denominator at the original tau. -/
abbrev InfinityPreparation (tau : CoherentNamed) :=
  DenominatorPreparation
    (fractionalDenominator
      Monodromy.infinityPeriodMatrix tau)

/-- Form the one-loop fractional-linear value using its original retained denominator preparation. -/
@[expose] def oneTransform {tau : CoherentNamed}
    (preparation : OnePreparation tau) : CoherentNamed :=
  fractionalLinear Monodromy.onePeriodMatrix tau
    preparation

/-- Form the infinity-loop fractional-linear value using its original retained denominator preparation. -/
@[expose] def infinityTransform {tau : CoherentNamed}
    (preparation : InfinityPreparation tau) : CoherentNamed :=
  fractionalLinear Monodromy.infinityPeriodMatrix tau
    preparation

/-- Convert a homogeneous transported period column and a fraction-free quotient equation into the directly useful
statement that the productive quotient is the ratio of the two actual transported coordinates. -/
@[expose] def productiveRatio_ofHomogeneous
    (periods : RawPeriodVector)
    (scale denominator numerator transform : CoherentNamed)
    (denominatorTransport : NamedEquivalent (periods 0).name
      (mul scale denominator).name)
    (numeratorTransport : NamedEquivalent (periods 1).name
      (mul scale numerator).name)
    (quotientEquation : NamedEquivalent
      (mul denominator transform).name
      numerator.name) :
    NamedEquivalent
      (mul
        (periods 0) transform).name
      (periods 1).name :=
  NamedEquivalent.trans
    (Congruence.coherentMul_respects
      (periods 0)
      (mul scale denominator)
      transform transform denominatorTransport
      (NamedEquivalent.refl transform.name))
    (NamedEquivalent.trans
      (Laws.coherentMul_assoc
        scale denominator transform)
      (NamedEquivalent.trans
        (Congruence.coherentMul_respects
          scale scale
          (mul denominator transform)
          numerator
          (NamedEquivalent.refl scale.name)
          quotientEquation)
        (NamedEquivalent.symm
          numeratorTransport)))

/-- Arbitrary finite-word productive dual period theorem. Given exactly the per-generator and combined denominator
preparations for the reversed transposed generator list, the resulting stepwise value is operationally the ratio of the
two actual period coordinates returned by endpoint continuation. -/
@[expose] def NormalizedData.periodWord_productive_transport {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    (data : NormalizedData frame)
    (path : Paths.Path frame frame)
    (preparations : Periods.PeriodFoldPreparations path.word data.ratio) :
    NamedEquivalent
      (mul
        (data.periods path 0)
        (Fold.Basic.foldAction data.ratio (Periods.periodBraidMatrices path.word)
          preparations)).name
      (data.periods path 1).name := by
  let matrix := Dual.periodMatrix path.word
  let denominator := fractionalDenominator matrix data.ratio
  let numerator := fractionalNumerator matrix data.ratio
  let transform := Fold.Basic.foldAction data.ratio
    (Periods.periodBraidMatrices path.word) preparations
  have homogeneous := data.periods_normalized path
  have denominatorTransport := homogeneous 0
  change NamedEquivalent (data.periods path 0).name
    (mul data.aPeriod
      denominator).name at denominatorTransport
  have numeratorTransport := homogeneous 1
  change NamedEquivalent (data.periods path 1).name
    (mul data.aPeriod
      numerator).name at numeratorTransport
  exact productiveRatio_ofHomogeneous (data.periods path) data.aPeriod
    denominator numerator transform denominatorTransport numeratorTransport
    (by
      simpa only [matrix, denominator, numerator, transform] using
        Periods.periodFold_denominator_mul path.word data.ratio preparations)

/-- Standard-loop data inherits the arbitrary finite-word productive theorem for every additional certified closed path
on its base frame. -/
@[expose] def Data.periodWord_productive_transport {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Data loops) (path : Paths.Path frame frame)
    (preparations : Periods.PeriodFoldPreparations path.word data.base.ratio) :
    NamedEquivalent
      (mul
        (data.periods path 0)
        (Fold.Basic.foldAction data.base.ratio (Periods.periodBraidMatrices path.word)
          preparations)).name
      (data.periods path 1).name :=
  data.base.periodWord_productive_transport path preparations

/-- The unconditional affine zero output is the ratio of the two period coordinates transported around the actual zero
loop. -/
@[expose] def Data.zero_productive_transport {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Data loops) :
    NamedEquivalent
      (mul
        (data.zeroPeriods 0) (zeroAffineTransform data.base.ratio)).name
      (data.zeroPeriods 1).name := by
  have denominatorTransport := data.zero_affine 0
  change NamedEquivalent (data.zeroPeriods 0).name
    (mul data.base.aPeriod
      (Coherence.exact 1)).name
      at denominatorTransport
  have numeratorTransport := data.zero_affine 1
  change NamedEquivalent (data.zeroPeriods 1).name
    (mul data.base.aPeriod
      (zeroAffineTransform data.base.ratio)).name at numeratorTransport
  exact productiveRatio_ofHomogeneous data.zeroPeriods data.base.aPeriod
    (Coherence.exact 1)
    (zeroAffineTransform data.base.ratio)
    (zeroAffineTransform data.base.ratio) denominatorTransport
    numeratorTransport
    (Mul.coherentMul_one_left
      (zeroAffineTransform data.base.ratio))

/-- The prepared one-loop output is the ratio of the two period coordinates transported around the actual one loop. -/
@[expose] def Data.one_productive_transport {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Data loops) (preparation : OnePreparation
      data.base.ratio) :
    NamedEquivalent
      (mul
        (data.onePeriods 0) (oneTransform preparation)).name
      (data.onePeriods 1).name := by
  have denominatorTransport := data.one_homogeneous 0
  change NamedEquivalent (data.onePeriods 0).name
    (mul data.base.aPeriod
      (fractionalDenominator Monodromy.onePeriodMatrix
        data.base.ratio)).name at denominatorTransport
  have numeratorTransport := data.one_homogeneous 1
  change NamedEquivalent (data.onePeriods 1).name
    (mul data.base.aPeriod
      (fractionalNumerator Monodromy.onePeriodMatrix
        data.base.ratio)).name at numeratorTransport
  exact productiveRatio_ofHomogeneous data.onePeriods data.base.aPeriod
    (fractionalDenominator Monodromy.onePeriodMatrix
      data.base.ratio)
    (fractionalNumerator Monodromy.onePeriodMatrix
      data.base.ratio)
    (oneTransform preparation) denominatorTransport numeratorTransport
    (by
      simpa only [oneTransform] using
        (denominator_mul_fractionalLinear
          Monodromy.onePeriodMatrix data.base.ratio
          preparation))

/-- The prepared infinity-loop output is the ratio of the two period coordinates transported around the actual infinity
loop. -/
@[expose] def Data.infinity_productive_transport {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Data loops)
    (preparation : InfinityPreparation data.base.ratio) :
    NamedEquivalent
      (mul
        (data.infinityPeriods 0) (infinityTransform preparation)).name
      (data.infinityPeriods 1).name := by
  have denominatorTransport := data.infinity_homogeneous 0
  change NamedEquivalent (data.infinityPeriods 0).name
    (mul data.base.aPeriod
      (fractionalDenominator
        Monodromy.infinityPeriodMatrix
        data.base.ratio)).name at denominatorTransport
  have numeratorTransport := data.infinity_homogeneous 1
  change NamedEquivalent (data.infinityPeriods 1).name
    (mul data.base.aPeriod
      (fractionalNumerator
        Monodromy.infinityPeriodMatrix
        data.base.ratio)).name at numeratorTransport
  exact productiveRatio_ofHomogeneous data.infinityPeriods data.base.aPeriod
    (fractionalDenominator
      Monodromy.infinityPeriodMatrix data.base.ratio)
    (fractionalNumerator
      Monodromy.infinityPeriodMatrix data.base.ratio)
    (infinityTransform preparation) denominatorTransport numeratorTransport
    (by
      simpa only [infinityTransform] using
        (denominator_mul_fractionalLinear
          Monodromy.infinityPeriodMatrix data.base.ratio
          preparation))

set_option genInjectivity false in
/-- Small productive carrier, again separated from expanded process indices. The transport fields close the final
algebraic step for the supplied data; clients need not reconstruct it from the homogeneous and quotient fields. -/
structure ProductiveCertificatePayload
    (fractionFreeType oneType infinityType zeroTransportType
      oneTransportType infinityTransportType : Type) where
  /-- The retained unconditional standard-loop homogeneous and matrix identities. -/ fractionFree : fractionFreeType
  /-- The prepared one-loop denominator times its productive quotient equals the retained numerator operationally. -/
    oneEquation : oneType
  /-- The prepared infinity-loop denominator times its productive quotient equals the retained numerator operationally.
  -/
  infinityEquation : infinityType
  /-- The actual zero-loop A-period times the affine transform equals its actual B-period operationally. -/
    zeroTransport : zeroTransportType
  /-- The actual one-loop A-period times the prepared transform equals its actual B-period operationally. -/
    oneTransport : oneTransportType
  /-- The actual infinity-loop A-period times the prepared transform equals its actual B-period operationally. -/
    infinityTransport : infinityTransportType

constructive_injectivity ProductiveCertificatePayload

/-- Productive standard dual outputs. Only the one and infinity denominators require typed apartness; zero remains the
direct affine name. -/
@[expose] def ProductiveCertificate {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Data loops)
    (onePreparation : OnePreparation data.base.ratio)
    (infinityPreparation : InfinityPreparation data.base.ratio) : Type :=
  ProductiveCertificatePayload
    (FractionFreeCertificate data)
    (NamedEquivalent
      (mul
        (fractionalDenominator
          Monodromy.onePeriodMatrix data.base.ratio)
        (oneTransform onePreparation)).name
      (fractionalNumerator
        Monodromy.onePeriodMatrix data.base.ratio).name)
    (NamedEquivalent
      (mul
        (fractionalDenominator
          Monodromy.infinityPeriodMatrix data.base.ratio)
        (infinityTransform infinityPreparation)).name
      (fractionalNumerator
        Monodromy.infinityPeriodMatrix data.base.ratio).name)
    (NamedEquivalent
      (mul
        (data.zeroPeriods 0) (zeroAffineTransform data.base.ratio)).name
      (data.zeroPeriods 1).name)
    (NamedEquivalent
      (mul
        (data.onePeriods 0) (oneTransform onePreparation)).name
      (data.onePeriods 1).name)
    (NamedEquivalent
      (mul
        (data.infinityPeriods 0)
        (infinityTransform infinityPreparation)).name
      (data.infinityPeriods 1).name)

/-- Combine the homogeneous standard-loop identities with the two retained denominator preparations.

The result retains the original fraction-free certificate, quotient equations and transport identities for the actual
zero, one and infinity period columns. -/
@[expose] def productiveCertificate {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Data loops)
    (onePreparation : OnePreparation data.base.ratio)
    (infinityPreparation : InfinityPreparation data.base.ratio) :
    ProductiveCertificate data onePreparation infinityPreparation := by
  unfold ProductiveCertificate
  exact
    { fractionFree := certificate data
      oneEquation := denominator_mul_fractionalLinear _ _ onePreparation
      infinityEquation :=
        denominator_mul_fractionalLinear _ _ infinityPreparation
      zeroTransport := data.zero_productive_transport
      oneTransport := data.one_productive_transport onePreparation
      infinityTransport :=
        data.infinity_productive_transport infinityPreparation }

set_option genInjectivity false in
/-- Precisely indexed readiness for both nonconstant dual standard-loop denominators. -/
structure StandardReadyPayload (oneType infinityType : Type 1) where
  /-- The retained productive preparation for the exact one-loop denominator. -/ one : oneType
  /-- The retained productive preparation for the exact infinity-loop denominator. -/ infinity : infinityType

constructive_injectivity StandardReadyPayload

/-- The pair of denominator preparations indexed by the exact one and infinity dual actions at the original tau. -/
@[expose] def StandardReady (tau : CoherentNamed) : Type 1 :=
  StandardReadyPayload (OnePreparation tau)
    (InfinityPreparation tau)

/-- A ready pair feeds the productive dual headline certificate directly. -/
@[expose] def productiveCertificateOfReady {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Data loops) (ready : StandardReady
      data.base.ratio) :
    ProductiveCertificate data ready.one ready.infinity :=
  productiveCertificate data ready.one ready.infinity

/-! ## Retryable standard denominator acquisition -/

/-- Attempt finite acquisition of one-loop denominator readiness from its initial state.

The result retains the original tau, matrix, fuel and any unfinished acquisition state; exhaustion does not establish
that the denominator vanishes. -/
@[expose] def attemptStandardOne (tau : CoherentNamed) (fuel : Nat) :
    Run.RunResult
      Monodromy.onePeriodMatrix tau
      (State.initial
        Monodromy.onePeriodMatrix tau) fuel :=
  Run.attempt
    Monodromy.onePeriodMatrix tau
    (State.initial
      Monodromy.onePeriodMatrix tau) fuel

/-- Attempt finite acquisition of infinity-loop denominator readiness from its initial state.

The result retains the original tau, matrix, fuel and any unfinished acquisition state; exhaustion does not establish
that the denominator vanishes. -/
@[expose] def attemptStandardInfinity (tau : CoherentNamed) (fuel : Nat) :
    Run.RunResult
      Monodromy.infinityPeriodMatrix tau
      (State.initial
        Monodromy.infinityPeriodMatrix tau) fuel :=
  Run.attempt
    Monodromy.infinityPeriodMatrix tau
    (State.initial
      Monodromy.infinityPeriodMatrix tau) fuel

end Purelib.Curves.Legendre.PeriodMonodromy
