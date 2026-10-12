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
  LinearAlgebra.Matrix.Basic.IntegralMatrix
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
structure NormalizedData {parameter : Curves.Legendre.PeriodMonodromy.Gaussian}
    (frame : Paths.Frame parameter) where
  /-- The retained normalized period data for this exact original framed curve. -/ normalized :
    PeriodMatrix.NormalizedPeriodData
    (Fibre.frameCurve frame)

constructive_injectivity NormalizedData

namespace NormalizedData

/-- Forget normalized inverse data while retaining the exact underlying period programs. -/
@[expose] def toFibreData {parameter : Curves.Legendre.PeriodMonodromy.Gaussian}
    {frame : Paths.Frame parameter}
    (data : Curves.Legendre.PeriodMonodromy.NormalizedData frame) :
    Fibre.FibreData frame where
  periods := data.normalized.toPeriodData

/-- Read the original A-period name from the normalized base fibre. -/
@[expose] def aPeriod {parameter : Curves.Legendre.PeriodMonodromy.Gaussian}
    {frame : Paths.Frame parameter}
    (data : Curves.Legendre.PeriodMonodromy.NormalizedData frame) : CoherentNamed :=
  data.normalized.toPeriodData.aMatrix 0 0

/-- Read the original B-period name from the normalized base fibre. -/
@[expose] def bPeriod {parameter : Curves.Legendre.PeriodMonodromy.Gaussian}
    {frame : Paths.Frame parameter}
    (data : Curves.Legendre.PeriodMonodromy.NormalizedData frame) : CoherentNamed :=
  data.normalized.toPeriodData.bMatrix 0 0

/-- Read the normalized period ratio from the retained scaled inverse. -/
@[expose] def ratio {parameter : Curves.Legendre.PeriodMonodromy.Gaussian}
    {frame : Paths.Frame parameter}
    (data : Curves.Legendre.PeriodMonodromy.NormalizedData frame) : CoherentNamed :=
  data.normalized.omega 0 0

/-- The normalized raw column identity requires only the scaled inverse already stored by `NormalizedPeriodData`. -/
@[expose] def raw_normalized {parameter : Curves.Legendre.PeriodMonodromy.Gaussian}
    {frame : Paths.Frame parameter}
    (data : Curves.Legendre.PeriodMonodromy.NormalizedData frame) :
    Curves.Legendre.PeriodMonodromy.VectorEquivalent data.toFibreData.rawPeriods
      (LegendreModularMonodromy.scaleVector data.aPeriod (LegendreModularMonodromy.fractionalVector data.ratio)) := by
  intro coordinate
  let comparison : Fin 2 → Type := fun index =>
    Curves.Legendre.PeriodMonodromy.NamedEquivalent
      (data.toFibreData.rawPeriods index).name
      (LegendreModularMonodromy.scaleVector data.aPeriod
        (LegendreModularMonodromy.fractionalVector data.ratio) index).name
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
@[expose] def continuation {parameter : Curves.Legendre.PeriodMonodromy.Gaussian}
    {frame : Paths.Frame parameter}
    (data : Curves.Legendre.PeriodMonodromy.NormalizedData frame)
    (path : Paths.Path frame frame) :
    Endpoint.EndpointContinuation path where
  source := data.toFibreData
  target := data.toFibreData

/-- Actual periods on the base fibre evaluated on the homology basis transported around an arbitrary certified finite
loop. -/
@[expose] def periods {parameter : Curves.Legendre.PeriodMonodromy.Gaussian}
    {frame : Paths.Frame parameter}
    (data : Curves.Legendre.PeriodMonodromy.NormalizedData frame)
    (path : Paths.Path frame frame) : RawPeriodVector :=
  (data.continuation path).periods

/-- The arbitrary-loop period column is the original `A` scale times the exact dual matrix acting on `(1,tau)`. -/
@[expose] def periods_normalized {parameter : Curves.Legendre.PeriodMonodromy.Gaussian}
    {frame : Paths.Frame parameter}
    (data : Curves.Legendre.PeriodMonodromy.NormalizedData frame)
    (path : Paths.Path frame frame) :
    Curves.Legendre.PeriodMonodromy.VectorEquivalent (data.periods path)
      (LegendreModularMonodromy.scaleVector data.aPeriod
        (Action.matrixAction
          (Dual.periodMatrix path.word)
          (LegendreModularMonodromy.fractionalVector data.ratio))) :=
  VectorEquivalent.trans
    (Action.matrixAction_respects _ data.raw_normalized)
    (LegendreModularMonodromy.matrixAction_scale _ data.aPeriod (LegendreModularMonodromy.fractionalVector data.ratio))

/-- Every legacy normalized fibre forgets to the smaller dual-transport interface without changing its period programs
or ratio. -/
@[expose] def ofLegacy {parameter : Curves.Legendre.PeriodMonodromy.Gaussian}
    {frame : Paths.Frame parameter}
    (data : LegendreModularMonodromy.NormalizedFibreData frame) :
    Curves.Legendre.PeriodMonodromy.NormalizedData frame where
  normalized := data.normalized

end NormalizedData

set_option genInjectivity false in
/-- The normalized base fibre used by all standard closed-loop transports. -/
structure Data {parameter : Curves.Legendre.PeriodMonodromy.Gaussian}
    {frame : Paths.Frame parameter}
    (loops : Monodromy.StandardLoops frame) where
  /-- The original normalized base fibre shared by the retained standard loops. -/ base :
    Curves.Legendre.PeriodMonodromy.NormalizedData frame

constructive_injectivity Data

namespace Data

/-- The generic finite endpoint-continuation object for a closed path on the normalized base fibre. -/
@[expose] def continuation {parameter : Curves.Legendre.PeriodMonodromy.Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Curves.Legendre.PeriodMonodromy.Data loops) (path : Paths.Path frame frame) :
    Endpoint.EndpointContinuation path :=
  data.base.continuation path

/-- Actual base-fibre periods evaluated on the basis transported around a certified closed path. -/
@[expose] def periods {parameter : Curves.Legendre.PeriodMonodromy.Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Curves.Legendre.PeriodMonodromy.Data loops) (path : Paths.Path frame frame) :
    RawPeriodVector :=
  data.base.periods path

/-- Transporting a normalized raw column is homogeneous matrix action on `(1,tau)`, with the original `A` period
retained as common scale. -/
@[expose] def periods_normalized {parameter : Curves.Legendre.PeriodMonodromy.Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Curves.Legendre.PeriodMonodromy.Data loops) (path : Paths.Path frame frame) :
    Curves.Legendre.PeriodMonodromy.VectorEquivalent (data.periods path)
      (LegendreModularMonodromy.scaleVector data.base.aPeriod
        (Action.matrixAction
          (Dual.periodMatrix path.word)
          (LegendreModularMonodromy.fractionalVector data.base.ratio))) :=
  data.base.periods_normalized path

/-- Evaluate base-fibre periods on the basis transported around the retained zero loop. -/
@[expose] def zeroPeriods {parameter : Curves.Legendre.PeriodMonodromy.Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Curves.Legendre.PeriodMonodromy.Data loops) : RawPeriodVector := data.periods loops.zeroPath

/-- Evaluate base-fibre periods on the basis transported around the retained one loop. -/
@[expose] def onePeriods {parameter : Curves.Legendre.PeriodMonodromy.Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Curves.Legendre.PeriodMonodromy.Data loops) : RawPeriodVector := data.periods loops.onePath

/-- Evaluate base-fibre periods on the basis transported around the retained infinity loop. -/
@[expose] def infinityPeriods {parameter : Curves.Legendre.PeriodMonodromy.Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Curves.Legendre.PeriodMonodromy.Data loops) : RawPeriodVector := data.periods loops.infinityPath

/-- Evaluate base-fibre periods on the basis transported around the retained product loop. -/
@[expose] def productPeriods {parameter : Curves.Legendre.PeriodMonodromy.Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Curves.Legendre.PeriodMonodromy.Data loops) : RawPeriodVector := data.periods loops.productPath

/-- The zero-loop period column is the original A-period times its exact dual homogeneous action. -/
@[expose] def zero_homogeneous {parameter : Curves.Legendre.PeriodMonodromy.Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Curves.Legendre.PeriodMonodromy.Data loops) :
    Curves.Legendre.PeriodMonodromy.VectorEquivalent data.zeroPeriods
      (LegendreModularMonodromy.scaleVector data.base.aPeriod
        (Action.matrixAction Monodromy.zeroPeriodMatrix
          (LegendreModularMonodromy.fractionalVector data.base.ratio))) := by
  simpa only [Curves.Legendre.PeriodMonodromy.Data.zeroPeriods] using data.periods_normalized loops.zeroPath
    |>.trans (fun coordinate => by
      rw [loops.zeroPath_periodMatrix]
      exact NamedEquivalent.refl _)

/-- The one-loop period column is the original A-period times its exact dual homogeneous action. -/
@[expose] def one_homogeneous {parameter : Curves.Legendre.PeriodMonodromy.Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Curves.Legendre.PeriodMonodromy.Data loops) :
    Curves.Legendre.PeriodMonodromy.VectorEquivalent data.onePeriods
      (LegendreModularMonodromy.scaleVector data.base.aPeriod
        (Action.matrixAction Monodromy.onePeriodMatrix
          (LegendreModularMonodromy.fractionalVector data.base.ratio))) := by
  simpa only [Curves.Legendre.PeriodMonodromy.Data.onePeriods] using data.periods_normalized loops.onePath
    |>.trans (fun coordinate => by
      rw [loops.onePath_periodMatrix]
      exact NamedEquivalent.refl _)

/-- The infinity-loop period column is the original A-period times its exact dual homogeneous action. -/
@[expose] def infinity_homogeneous {parameter : Curves.Legendre.PeriodMonodromy.Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Curves.Legendre.PeriodMonodromy.Data loops) :
    Curves.Legendre.PeriodMonodromy.VectorEquivalent data.infinityPeriods
      (LegendreModularMonodromy.scaleVector data.base.aPeriod
        (Action.matrixAction Monodromy.infinityPeriodMatrix
          (LegendreModularMonodromy.fractionalVector data.base.ratio))) := by
  simpa only [Curves.Legendre.PeriodMonodromy.Data.infinityPeriods] using data.periods_normalized loops.infinityPath
    |>.trans (fun coordinate => by
      rw [loops.infinityPath_periodMatrix]
      exact NamedEquivalent.refl _)

/-- The retained product loop acts as the identity on the original period column. -/
@[expose] def product_identity {parameter : Curves.Legendre.PeriodMonodromy.Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Curves.Legendre.PeriodMonodromy.Data loops) :
    Curves.Legendre.PeriodMonodromy.VectorEquivalent data.productPeriods data.base.toFibreData.rawPeriods := by
  unfold Purelib.Curves.Legendre.PeriodMonodromy.Data.productPeriods
    Purelib.Curves.Legendre.PeriodMonodromy.Data.periods Purelib.Curves.Legendre.PeriodMonodromy.NormalizedData.periods
    Curves.Legendre.PeriodMonodromy.NormalizedData.continuation EndpointContinuation.periods
  rw [loops.productPath_periodMatrix]
  exact Action.matrixAction_identity data.base.toFibreData.rawPeriods

end Data

/-! ## Exact standard dual rows -/

/-- The coherent affine transform tau minus two for the zero-loop dual action. -/
@[expose] def zeroAffineTransform (tau : Curves.Legendre.PeriodMonodromy.CoherentNamed) : CoherentNamed :=
  CoherentNamed.add
    (Coherence.exact (-2)) tau

/-- The coherent denominator one plus twice tau for the one-loop dual action. -/
@[expose] def oneDenominator (tau : Curves.Legendre.PeriodMonodromy.CoherentNamed) : CoherentNamed :=
  CoherentNamed.add
    (Coherence.exact 1)
    (CoherentNamed.mul
      (Coherence.exact 2) tau)

/-- The coherent denominator minus three minus twice tau for the infinity-loop dual action. -/
@[expose] def infinityDenominator (tau : Curves.Legendre.PeriodMonodromy.CoherentNamed) : CoherentNamed :=
  CoherentNamed.add
    (Coherence.exact (-3))
    (CoherentNamed.mul
      (Coherence.exact (-2)) tau)

/-- The coherent numerator two plus tau for the infinity-loop dual action. -/
@[expose] def infinityNumerator (tau : Curves.Legendre.PeriodMonodromy.CoherentNamed) : CoherentNamed :=
  CoherentNamed.add
    (Coherence.exact 2) tau

/-- Around zero the transformed `A` coordinate is exactly the original `A`: the dual denominator is the constant unit.
-/
@[expose] def zero_denominator_one (tau : Curves.Legendre.PeriodMonodromy.CoherentNamed) :
    Curves.Legendre.PeriodMonodromy.NamedEquivalent
      (LegendreModularMonodromy.fractionalDenominator
        Monodromy.zeroPeriodMatrix tau).name
      (Coherence.exact 1).name := by
  let one := Coherence.exact 1
  let zero := Coherence.exact 0
  have expanded := LegendreModularMonodromy.matrixAction_row_two
    Monodromy.zeroPeriodMatrix
    (LegendreModularMonodromy.fractionalVector tau) 0
  rw [Monodromy.zeroPeriodMatrix_explicit] at expanded
  change Curves.Legendre.PeriodMonodromy.NamedEquivalent
    (LegendreModularMonodromy.fractionalDenominator
      Monodromy.zeroPeriodMatrix tau).name
    (CoherentNamed.add
      (CoherentNamed.mul one one)
      (CoherentNamed.mul zero tau)).name at expanded
  have simplifyTerms : Curves.Legendre.PeriodMonodromy.NamedEquivalent
      (CoherentNamed.add
        (CoherentNamed.mul one one)
        (CoherentNamed.mul zero tau)).name
      (CoherentNamed.add one zero).name :=
    Congruence.coherentAdd_respects
      (CoherentNamed.mul one one) one
      (CoherentNamed.mul zero tau) zero
      (Mul.coherentMul_one_right one)
      (Mul.coherentMul_zero_left tau)
  exact NamedEquivalent.trans expanded
    (NamedEquivalent.trans
      simplifyTerms
      (Add.coherentAdd_zero_right one))

/-- The zero-loop homogeneous numerator is operationally the affine transform tau minus two. -/
@[expose] def zero_numerator_affine (tau : Curves.Legendre.PeriodMonodromy.CoherentNamed) :
    Curves.Legendre.PeriodMonodromy.NamedEquivalent
      (LegendreModularMonodromy.fractionalNumerator
        Monodromy.zeroPeriodMatrix tau).name
      (Curves.Legendre.PeriodMonodromy.zeroAffineTransform tau).name := by
  let one := Coherence.exact 1
  let minusTwo := Coherence.exact (-2)
  have expanded := LegendreModularMonodromy.matrixAction_row_two
    Monodromy.zeroPeriodMatrix
    (LegendreModularMonodromy.fractionalVector tau) 1
  rw [Monodromy.zeroPeriodMatrix_explicit] at expanded
  change Curves.Legendre.PeriodMonodromy.NamedEquivalent
    (LegendreModularMonodromy.fractionalNumerator
      Monodromy.zeroPeriodMatrix tau).name
    (CoherentNamed.add
      (CoherentNamed.mul minusTwo one)
      (CoherentNamed.mul one tau)).name at expanded
  exact NamedEquivalent.trans expanded
    (by
      simpa only [Curves.Legendre.PeriodMonodromy.zeroAffineTransform,
        CoherentNamed.add] using
        Congruence.coherentAdd_respects _ _ _ _
          (Mul.coherentMul_one_right minusTwo)
          (Mul.coherentMul_one_left tau))

/-- The one-loop homogeneous denominator is operationally one plus twice tau. -/
@[expose] def one_denominator_explicit (tau : Curves.Legendre.PeriodMonodromy.CoherentNamed) :
    Curves.Legendre.PeriodMonodromy.NamedEquivalent
      (LegendreModularMonodromy.fractionalDenominator
        Monodromy.onePeriodMatrix tau).name
      (Curves.Legendre.PeriodMonodromy.oneDenominator tau).name := by
  let one := Coherence.exact 1
  let two := Coherence.exact 2
  have expanded := LegendreModularMonodromy.matrixAction_row_two
    Monodromy.onePeriodMatrix
    (LegendreModularMonodromy.fractionalVector tau) 0
  rw [Monodromy.onePeriodMatrix_explicit] at expanded
  change Curves.Legendre.PeriodMonodromy.NamedEquivalent
    (LegendreModularMonodromy.fractionalDenominator
      Monodromy.onePeriodMatrix tau).name
    (CoherentNamed.add
      (CoherentNamed.mul one one)
      (CoherentNamed.mul two tau)).name at expanded
  exact NamedEquivalent.trans expanded
    (by
      simpa only [Curves.Legendre.PeriodMonodromy.oneDenominator,
        CoherentNamed.add] using
        Congruence.coherentAdd_respects _ _ _ _
          (Mul.coherentMul_one_right one)
          (NamedEquivalent.refl _))

/-- The one-loop homogeneous numerator is operationally the original tau name. -/
@[expose] def one_numerator_tau (tau : Curves.Legendre.PeriodMonodromy.CoherentNamed) :
    Curves.Legendre.PeriodMonodromy.NamedEquivalent
      (LegendreModularMonodromy.fractionalNumerator
        Monodromy.onePeriodMatrix tau).name tau.name := by
  let one := Coherence.exact 1
  let zero := Coherence.exact 0
  have expanded := LegendreModularMonodromy.matrixAction_row_two
    Monodromy.onePeriodMatrix
    (LegendreModularMonodromy.fractionalVector tau) 1
  rw [Monodromy.onePeriodMatrix_explicit] at expanded
  change Curves.Legendre.PeriodMonodromy.NamedEquivalent
    (LegendreModularMonodromy.fractionalNumerator
      Monodromy.onePeriodMatrix tau).name
    (CoherentNamed.add
      (CoherentNamed.mul zero one)
      (CoherentNamed.mul one tau)).name at expanded
  have simplifyTerms : Curves.Legendre.PeriodMonodromy.NamedEquivalent
      (CoherentNamed.add
        (CoherentNamed.mul zero one)
        (CoherentNamed.mul one tau)).name
      (CoherentNamed.add zero tau).name :=
    Congruence.coherentAdd_respects
      (CoherentNamed.mul zero one) zero
      (CoherentNamed.mul one tau) tau
      (Mul.coherentMul_zero_left one)
      (Mul.coherentMul_one_left tau)
  exact NamedEquivalent.trans expanded
    (NamedEquivalent.trans
      simplifyTerms
      (Add.coherentAdd_zero_left tau))

/-- The infinity-loop homogeneous denominator is operationally minus three minus twice tau. -/
@[expose] def infinity_denominator_explicit (tau : Curves.Legendre.PeriodMonodromy.CoherentNamed) :
    Curves.Legendre.PeriodMonodromy.NamedEquivalent
      (LegendreModularMonodromy.fractionalDenominator
        Monodromy.infinityPeriodMatrix tau).name
      (Curves.Legendre.PeriodMonodromy.infinityDenominator tau).name := by
  let one := Coherence.exact 1
  let minusThree := Coherence.exact (-3)
  let minusTwo := Coherence.exact (-2)
  have expanded := LegendreModularMonodromy.matrixAction_row_two
    Monodromy.infinityPeriodMatrix
    (LegendreModularMonodromy.fractionalVector tau) 0
  rw [Monodromy.infinityPeriodMatrix_explicit] at expanded
  change Curves.Legendre.PeriodMonodromy.NamedEquivalent
    (LegendreModularMonodromy.fractionalDenominator
      Monodromy.infinityPeriodMatrix tau).name
    (CoherentNamed.add
      (CoherentNamed.mul minusThree one)
      (CoherentNamed.mul minusTwo tau)).name at expanded
  exact NamedEquivalent.trans expanded
    (by
      simpa only [Curves.Legendre.PeriodMonodromy.infinityDenominator,
        CoherentNamed.add] using
        Congruence.coherentAdd_respects _ _ _ _
          (Mul.coherentMul_one_right minusThree)
          (NamedEquivalent.refl _))

/-- The infinity-loop homogeneous numerator is operationally two plus tau. -/
@[expose] def infinity_numerator_explicit (tau : Curves.Legendre.PeriodMonodromy.CoherentNamed) :
    Curves.Legendre.PeriodMonodromy.NamedEquivalent
      (LegendreModularMonodromy.fractionalNumerator
        Monodromy.infinityPeriodMatrix tau).name
      (Curves.Legendre.PeriodMonodromy.infinityNumerator tau).name := by
  let one := Coherence.exact 1
  let two := Coherence.exact 2
  have expanded := LegendreModularMonodromy.matrixAction_row_two
    Monodromy.infinityPeriodMatrix
    (LegendreModularMonodromy.fractionalVector tau) 1
  rw [Monodromy.infinityPeriodMatrix_explicit] at expanded
  change Curves.Legendre.PeriodMonodromy.NamedEquivalent
    (LegendreModularMonodromy.fractionalNumerator
      Monodromy.infinityPeriodMatrix tau).name
    (CoherentNamed.add
      (CoherentNamed.mul two one)
      (CoherentNamed.mul one tau)).name at expanded
  exact NamedEquivalent.trans expanded
    (by
      simpa only [Curves.Legendre.PeriodMonodromy.infinityNumerator,
        CoherentNamed.add] using
        Congruence.coherentAdd_respects _ _ _ _
          (Mul.coherentMul_one_right two)
          (Mul.coherentMul_one_left tau))

/-! ## Unconditional and productive headline packages -/

/-- Multiplication by the same coherent scale preserves coordinatewise period equivalence. -/
@[expose] def scaleVector_respects (scalar : Curves.Legendre.PeriodMonodromy.CoherentNamed)
    {left right : Curves.Legendre.PeriodMonodromy.RawPeriodVector} (equivalent :
      Curves.Legendre.PeriodMonodromy.VectorEquivalent left right) :
    Curves.Legendre.PeriodMonodromy.VectorEquivalent (LegendreModularMonodromy.scaleVector scalar left)
      (LegendreModularMonodromy.scaleVector scalar right) :=
  fun coordinate => Congruence.coherentMul_respects
    scalar scalar (left coordinate) (right coordinate)
    (NamedEquivalent.refl scalar.name)
    (equivalent coordinate)

/-- Arbitrary finite-word dual period transport. The actual periods from `EndpointContinuation` are the original `A`
scale times the stepwise action of the reversed transposed generator matrices on `(1,tau)`. -/
@[expose] def NormalizedData.periodWord_homogeneous {parameter : Curves.Legendre.PeriodMonodromy.Gaussian}
    {frame : Paths.Frame parameter}
    (data : Curves.Legendre.PeriodMonodromy.NormalizedData frame)
    (path : Paths.Path frame frame) :
    Curves.Legendre.PeriodMonodromy.VectorEquivalent (data.periods path)
      (LegendreModularMonodromy.scaleVector data.aPeriod
        (Word.blockAction (Periods.periodBraidMatrices path.word)
          (LegendreModularMonodromy.fractionalVector data.ratio))) :=
  VectorEquivalent.trans (data.periods_normalized path)
    (Curves.Legendre.PeriodMonodromy.scaleVector_respects data.aPeriod
      (Periods.periodBraidRows_word path.word data.ratio))

/-- Standard-loop data inherits the arbitrary-word homogeneous theorem without adding any premise. -/
@[expose] def Data.periodWord_homogeneous {parameter : Curves.Legendre.PeriodMonodromy.Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Curves.Legendre.PeriodMonodromy.Data loops) (path : Paths.Path frame frame) :
    Curves.Legendre.PeriodMonodromy.VectorEquivalent (data.periods path)
      (LegendreModularMonodromy.scaleVector data.base.aPeriod
        (Word.blockAction (Periods.periodBraidMatrices path.word)
          (LegendreModularMonodromy.fractionalVector data.base.ratio))) :=
  data.base.periodWord_homogeneous path

/-- The zero-loop homogeneous matrix action gives the unit row and affine tau-minus-two row. -/
@[expose] def zero_rows_affine (tau : Curves.Legendre.PeriodMonodromy.CoherentNamed) :
    Curves.Legendre.PeriodMonodromy.VectorEquivalent
      (Action.matrixAction Monodromy.zeroPeriodMatrix
        (LegendreModularMonodromy.fractionalVector tau))
      (LegendreModularMonodromy.fractionalVector (Curves.Legendre.PeriodMonodromy.zeroAffineTransform tau)) := by
  intro coordinate
  let comparison : Fin 2 → Type := fun index =>
    Curves.Legendre.PeriodMonodromy.NamedEquivalent
      (Action.matrixAction Monodromy.zeroPeriodMatrix
        (LegendreModularMonodromy.fractionalVector tau) index).name
      (LegendreModularMonodromy.fractionalVector
        (Curves.Legendre.PeriodMonodromy.zeroAffineTransform tau) index).name
  refine Data.Fin.casesDependent (size := 1) (motive := comparison) ?_
    (fun tail => Data.Fin.casesDependent (size := 0)
      (motive := fun index => comparison index.succ) ?_
      (fun impossible => False.elim (Nat.not_lt_zero impossible.val impossible.isLt)) tail) coordinate
  · exact Curves.Legendre.PeriodMonodromy.zero_denominator_one tau
  · exact Curves.Legendre.PeriodMonodromy.zero_numerator_affine tau

/-- The actual zero-loop period column equals the original A-period scale times the affine normalized column. -/
@[expose] def Data.zero_affine {parameter : Curves.Legendre.PeriodMonodromy.Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Curves.Legendre.PeriodMonodromy.Data loops) :
    Curves.Legendre.PeriodMonodromy.VectorEquivalent data.zeroPeriods
      (LegendreModularMonodromy.scaleVector data.base.aPeriod
        (LegendreModularMonodromy.fractionalVector (Curves.Legendre.PeriodMonodromy.zeroAffineTransform
          data.base.ratio))) :=
  VectorEquivalent.trans data.zero_homogeneous
    (Curves.Legendre.PeriodMonodromy.scaleVector_respects data.base.aPeriod
      (Curves.Legendre.PeriodMonodromy.zero_rows_affine data.base.ratio))

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
@[expose] def FractionFreeCertificate {parameter : Curves.Legendre.PeriodMonodromy.Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Curves.Legendre.PeriodMonodromy.Data loops) : Type :=
  Curves.Legendre.PeriodMonodromy.FractionFreeCertificatePayload
    (Curves.Legendre.PeriodMonodromy.VectorEquivalent data.zeroPeriods
      (LegendreModularMonodromy.scaleVector data.base.aPeriod
        (LegendreModularMonodromy.fractionalVector (Curves.Legendre.PeriodMonodromy.zeroAffineTransform
          data.base.ratio))))
    (Curves.Legendre.PeriodMonodromy.VectorEquivalent data.onePeriods
      (LegendreModularMonodromy.scaleVector data.base.aPeriod
        (Action.matrixAction Monodromy.onePeriodMatrix
          (LegendreModularMonodromy.fractionalVector data.base.ratio))))
    (Curves.Legendre.PeriodMonodromy.VectorEquivalent data.infinityPeriods
      (LegendreModularMonodromy.scaleVector data.base.aPeriod
        (Action.matrixAction Monodromy.infinityPeriodMatrix
          (LegendreModularMonodromy.fractionalVector data.base.ratio))))
    (Curves.Legendre.PeriodMonodromy.VectorEquivalent data.productPeriods data.base.toFibreData.rawPeriods)
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
@[expose] def certificate {parameter : Curves.Legendre.PeriodMonodromy.Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Curves.Legendre.PeriodMonodromy.Data loops) :
      Purelib.Curves.Legendre.PeriodMonodromy.FractionFreeCertificate data := by
  unfold Purelib.Curves.Legendre.PeriodMonodromy.FractionFreeCertificate
  exact
    { zero := data.zero_affine
      one := data.one_homogeneous
      infinity := data.infinity_homogeneous
      product := data.product_identity
      inverseMatrices :=
        ⟨Monodromy.explicit_period_product_left,
          Monodromy.explicit_period_product_right⟩ }

/-- Productive denominator data for the exact one-loop dual denominator at the original tau. -/
abbrev OnePreparation (tau : Curves.Legendre.PeriodMonodromy.CoherentNamed) :=
  Curves.Legendre.PeriodMonodromy.DenominatorPreparation
    (LegendreModularMonodromy.fractionalDenominator Monodromy.onePeriodMatrix tau)

/-- Productive denominator data for the exact infinity-loop dual denominator at the original tau. -/
abbrev InfinityPreparation (tau : Curves.Legendre.PeriodMonodromy.CoherentNamed) :=
  Curves.Legendre.PeriodMonodromy.DenominatorPreparation
    (LegendreModularMonodromy.fractionalDenominator
      Monodromy.infinityPeriodMatrix tau)

/-- Form the one-loop fractional-linear value using its original retained denominator preparation. -/
@[expose] def oneTransform {tau : Curves.Legendre.PeriodMonodromy.CoherentNamed}
    (preparation : Curves.Legendre.PeriodMonodromy.OnePreparation tau) : CoherentNamed :=
  LegendreModularMonodromy.fractionalLinear Monodromy.onePeriodMatrix tau
    preparation

/-- Form the infinity-loop fractional-linear value using its original retained denominator preparation. -/
@[expose] def infinityTransform {tau : Curves.Legendre.PeriodMonodromy.CoherentNamed}
    (preparation : Curves.Legendre.PeriodMonodromy.InfinityPreparation tau) : CoherentNamed :=
  LegendreModularMonodromy.fractionalLinear Monodromy.infinityPeriodMatrix tau
    preparation

/-- Convert a homogeneous transported period column and a fraction-free quotient equation into the directly useful
statement that the productive quotient is the ratio of the two actual transported coordinates. -/
@[expose] def productiveRatio_ofHomogeneous
    (periods : Curves.Legendre.PeriodMonodromy.RawPeriodVector)
    (scale denominator numerator transform : Curves.Legendre.PeriodMonodromy.CoherentNamed)
    (denominatorTransport : Curves.Legendre.PeriodMonodromy.NamedEquivalent (periods 0).name
      (CoherentNamed.mul scale denominator).name)
    (numeratorTransport : Curves.Legendre.PeriodMonodromy.NamedEquivalent (periods 1).name
      (CoherentNamed.mul scale numerator).name)
    (quotientEquation : Curves.Legendre.PeriodMonodromy.NamedEquivalent
      (CoherentNamed.mul denominator transform).name
      numerator.name) :
    Curves.Legendre.PeriodMonodromy.NamedEquivalent
      (CoherentNamed.mul
        (periods 0) transform).name
      (periods 1).name :=
  NamedEquivalent.trans
    (Congruence.coherentMul_respects
      (periods 0)
      (CoherentNamed.mul scale denominator)
      transform transform denominatorTransport
      (NamedEquivalent.refl transform.name))
    (NamedEquivalent.trans
      (Laws.coherentMul_assoc
        scale denominator transform)
      (NamedEquivalent.trans
        (Congruence.coherentMul_respects
          scale scale
          (CoherentNamed.mul denominator transform)
          numerator
          (NamedEquivalent.refl scale.name)
          quotientEquation)
        (NamedEquivalent.symm
          numeratorTransport)))

/-- Arbitrary finite-word productive dual period theorem. Given exactly the per-generator and combined denominator
preparations for the reversed transposed generator list, the resulting stepwise value is operationally the ratio of the
two actual period coordinates returned by endpoint continuation. -/
@[expose] def NormalizedData.periodWord_productive_transport {parameter : Curves.Legendre.PeriodMonodromy.Gaussian}
    {frame : Paths.Frame parameter}
    (data : Curves.Legendre.PeriodMonodromy.NormalizedData frame)
    (path : Paths.Path frame frame)
    (preparations : Periods.PeriodFoldPreparations path.word data.ratio) :
    Curves.Legendre.PeriodMonodromy.NamedEquivalent
      (CoherentNamed.mul
        (data.periods path 0)
        (Fold.Basic.foldAction data.ratio (Periods.periodBraidMatrices path.word)
          preparations)).name
      (data.periods path 1).name := by
  let matrix := Dual.periodMatrix path.word
  let denominator := LegendreModularMonodromy.fractionalDenominator matrix data.ratio
  let numerator := LegendreModularMonodromy.fractionalNumerator matrix data.ratio
  let transform := Fold.Basic.foldAction data.ratio
    (Periods.periodBraidMatrices path.word) preparations
  have homogeneous := data.periods_normalized path
  have denominatorTransport := homogeneous 0
  change Curves.Legendre.PeriodMonodromy.NamedEquivalent (data.periods path 0).name
    (CoherentNamed.mul data.aPeriod
      denominator).name at denominatorTransport
  have numeratorTransport := homogeneous 1
  change Curves.Legendre.PeriodMonodromy.NamedEquivalent (data.periods path 1).name
    (CoherentNamed.mul data.aPeriod
      numerator).name at numeratorTransport
  exact Curves.Legendre.PeriodMonodromy.productiveRatio_ofHomogeneous (data.periods path) data.aPeriod
    denominator numerator transform denominatorTransport numeratorTransport
    (by
      simpa only [matrix, denominator, numerator, transform] using
        Periods.periodFold_denominator_mul path.word data.ratio preparations)

/-- Standard-loop data inherits the arbitrary finite-word productive theorem for every additional certified closed path
on its base frame. -/
@[expose] def Data.periodWord_productive_transport {parameter : Curves.Legendre.PeriodMonodromy.Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Curves.Legendre.PeriodMonodromy.Data loops) (path : Paths.Path frame frame)
    (preparations : Periods.PeriodFoldPreparations path.word data.base.ratio) :
    Curves.Legendre.PeriodMonodromy.NamedEquivalent
      (CoherentNamed.mul
        (data.periods path 0)
        (Fold.Basic.foldAction data.base.ratio (Periods.periodBraidMatrices path.word)
          preparations)).name
      (data.periods path 1).name :=
  data.base.periodWord_productive_transport path preparations

/-- The unconditional affine zero output is the ratio of the two period coordinates transported around the actual zero
loop. -/
@[expose] def Data.zero_productive_transport {parameter : Curves.Legendre.PeriodMonodromy.Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Curves.Legendre.PeriodMonodromy.Data loops) :
    Curves.Legendre.PeriodMonodromy.NamedEquivalent
      (CoherentNamed.mul
        (data.zeroPeriods 0) (Curves.Legendre.PeriodMonodromy.zeroAffineTransform data.base.ratio)).name
      (data.zeroPeriods 1).name := by
  have denominatorTransport := data.zero_affine 0
  change Curves.Legendre.PeriodMonodromy.NamedEquivalent (data.zeroPeriods 0).name
    (CoherentNamed.mul data.base.aPeriod
      (Coherence.exact 1)).name
      at denominatorTransport
  have numeratorTransport := data.zero_affine 1
  change Curves.Legendre.PeriodMonodromy.NamedEquivalent (data.zeroPeriods 1).name
    (CoherentNamed.mul data.base.aPeriod
      (Curves.Legendre.PeriodMonodromy.zeroAffineTransform data.base.ratio)).name at numeratorTransport
  exact Curves.Legendre.PeriodMonodromy.productiveRatio_ofHomogeneous data.zeroPeriods data.base.aPeriod
    (Coherence.exact 1)
    (Curves.Legendre.PeriodMonodromy.zeroAffineTransform data.base.ratio)
    (Curves.Legendre.PeriodMonodromy.zeroAffineTransform data.base.ratio) denominatorTransport
    numeratorTransport
    (Mul.coherentMul_one_left
      (Curves.Legendre.PeriodMonodromy.zeroAffineTransform data.base.ratio))

/-- The prepared one-loop output is the ratio of the two period coordinates transported around the actual one loop. -/
@[expose] def Data.one_productive_transport {parameter : Curves.Legendre.PeriodMonodromy.Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Curves.Legendre.PeriodMonodromy.Data loops) (preparation : Curves.Legendre.PeriodMonodromy.OnePreparation
      data.base.ratio) :
    Curves.Legendre.PeriodMonodromy.NamedEquivalent
      (CoherentNamed.mul
        (data.onePeriods 0) (Curves.Legendre.PeriodMonodromy.oneTransform preparation)).name
      (data.onePeriods 1).name := by
  have denominatorTransport := data.one_homogeneous 0
  change Curves.Legendre.PeriodMonodromy.NamedEquivalent (data.onePeriods 0).name
    (CoherentNamed.mul data.base.aPeriod
      (LegendreModularMonodromy.fractionalDenominator Monodromy.onePeriodMatrix
        data.base.ratio)).name at denominatorTransport
  have numeratorTransport := data.one_homogeneous 1
  change Curves.Legendre.PeriodMonodromy.NamedEquivalent (data.onePeriods 1).name
    (CoherentNamed.mul data.base.aPeriod
      (LegendreModularMonodromy.fractionalNumerator Monodromy.onePeriodMatrix
        data.base.ratio)).name at numeratorTransport
  exact Curves.Legendre.PeriodMonodromy.productiveRatio_ofHomogeneous data.onePeriods data.base.aPeriod
    (LegendreModularMonodromy.fractionalDenominator Monodromy.onePeriodMatrix
      data.base.ratio)
    (LegendreModularMonodromy.fractionalNumerator Monodromy.onePeriodMatrix
      data.base.ratio)
    (Curves.Legendre.PeriodMonodromy.oneTransform preparation) denominatorTransport numeratorTransport
    (by
      simpa only [Curves.Legendre.PeriodMonodromy.oneTransform] using
        (LegendreModularMonodromy.denominator_mul_fractionalLinear
          Monodromy.onePeriodMatrix data.base.ratio
          preparation))

/-- The prepared infinity-loop output is the ratio of the two period coordinates transported around the actual infinity
loop. -/
@[expose] def Data.infinity_productive_transport {parameter : Curves.Legendre.PeriodMonodromy.Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Curves.Legendre.PeriodMonodromy.Data loops)
    (preparation : Curves.Legendre.PeriodMonodromy.InfinityPreparation data.base.ratio) :
    Curves.Legendre.PeriodMonodromy.NamedEquivalent
      (CoherentNamed.mul
        (data.infinityPeriods 0) (Curves.Legendre.PeriodMonodromy.infinityTransform preparation)).name
      (data.infinityPeriods 1).name := by
  have denominatorTransport := data.infinity_homogeneous 0
  change Curves.Legendre.PeriodMonodromy.NamedEquivalent (data.infinityPeriods 0).name
    (CoherentNamed.mul data.base.aPeriod
      (LegendreModularMonodromy.fractionalDenominator
        Monodromy.infinityPeriodMatrix
        data.base.ratio)).name at denominatorTransport
  have numeratorTransport := data.infinity_homogeneous 1
  change Curves.Legendre.PeriodMonodromy.NamedEquivalent (data.infinityPeriods 1).name
    (CoherentNamed.mul data.base.aPeriod
      (LegendreModularMonodromy.fractionalNumerator
        Monodromy.infinityPeriodMatrix
        data.base.ratio)).name at numeratorTransport
  exact Curves.Legendre.PeriodMonodromy.productiveRatio_ofHomogeneous data.infinityPeriods data.base.aPeriod
    (LegendreModularMonodromy.fractionalDenominator
      Monodromy.infinityPeriodMatrix data.base.ratio)
    (LegendreModularMonodromy.fractionalNumerator
      Monodromy.infinityPeriodMatrix data.base.ratio)
    (Curves.Legendre.PeriodMonodromy.infinityTransform preparation) denominatorTransport numeratorTransport
    (by
      simpa only [Curves.Legendre.PeriodMonodromy.infinityTransform] using
        (LegendreModularMonodromy.denominator_mul_fractionalLinear
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
@[expose] def ProductiveCertificate {parameter : Curves.Legendre.PeriodMonodromy.Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Curves.Legendre.PeriodMonodromy.Data loops)
    (onePreparation : Curves.Legendre.PeriodMonodromy.OnePreparation data.base.ratio)
    (infinityPreparation : Curves.Legendre.PeriodMonodromy.InfinityPreparation data.base.ratio) : Type :=
  Curves.Legendre.PeriodMonodromy.ProductiveCertificatePayload
    (Curves.Legendre.PeriodMonodromy.FractionFreeCertificate data)
    (Curves.Legendre.PeriodMonodromy.NamedEquivalent
      (CoherentNamed.mul
        (LegendreModularMonodromy.fractionalDenominator
          Monodromy.onePeriodMatrix data.base.ratio)
        (Curves.Legendre.PeriodMonodromy.oneTransform onePreparation)).name
      (LegendreModularMonodromy.fractionalNumerator
        Monodromy.onePeriodMatrix data.base.ratio).name)
    (Curves.Legendre.PeriodMonodromy.NamedEquivalent
      (CoherentNamed.mul
        (LegendreModularMonodromy.fractionalDenominator
          Monodromy.infinityPeriodMatrix data.base.ratio)
        (Curves.Legendre.PeriodMonodromy.infinityTransform infinityPreparation)).name
      (LegendreModularMonodromy.fractionalNumerator
        Monodromy.infinityPeriodMatrix data.base.ratio).name)
    (Curves.Legendre.PeriodMonodromy.NamedEquivalent
      (CoherentNamed.mul
        (data.zeroPeriods 0) (Curves.Legendre.PeriodMonodromy.zeroAffineTransform data.base.ratio)).name
      (data.zeroPeriods 1).name)
    (Curves.Legendre.PeriodMonodromy.NamedEquivalent
      (CoherentNamed.mul
        (data.onePeriods 0) (Curves.Legendre.PeriodMonodromy.oneTransform onePreparation)).name
      (data.onePeriods 1).name)
    (Curves.Legendre.PeriodMonodromy.NamedEquivalent
      (CoherentNamed.mul
        (data.infinityPeriods 0)
        (Curves.Legendre.PeriodMonodromy.infinityTransform infinityPreparation)).name
      (data.infinityPeriods 1).name)

/-- Combine the homogeneous standard-loop identities with the two retained denominator preparations.

The result retains the original fraction-free certificate, quotient equations and transport identities for the actual
zero, one and infinity period columns. -/
@[expose] def productiveCertificate {parameter : Curves.Legendre.PeriodMonodromy.Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Curves.Legendre.PeriodMonodromy.Data loops)
    (onePreparation : Curves.Legendre.PeriodMonodromy.OnePreparation data.base.ratio)
    (infinityPreparation : Curves.Legendre.PeriodMonodromy.InfinityPreparation data.base.ratio) :
    Purelib.Curves.Legendre.PeriodMonodromy.ProductiveCertificate data onePreparation infinityPreparation := by
  unfold Purelib.Curves.Legendre.PeriodMonodromy.ProductiveCertificate
  exact
    { fractionFree := Curves.Legendre.PeriodMonodromy.certificate data
      oneEquation := LegendreModularMonodromy.denominator_mul_fractionalLinear _ _ onePreparation
      infinityEquation :=
        LegendreModularMonodromy.denominator_mul_fractionalLinear _ _ infinityPreparation
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
@[expose] def StandardReady (tau : Curves.Legendre.PeriodMonodromy.CoherentNamed) : Type 1 :=
  Curves.Legendre.PeriodMonodromy.StandardReadyPayload (Curves.Legendre.PeriodMonodromy.OnePreparation tau)
    (Curves.Legendre.PeriodMonodromy.InfinityPreparation tau)

/-- A ready pair feeds the productive dual headline certificate directly. -/
@[expose] def productiveCertificateOfReady {parameter : Curves.Legendre.PeriodMonodromy.Gaussian}
    {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (data : Curves.Legendre.PeriodMonodromy.Data loops) (ready : Curves.Legendre.PeriodMonodromy.StandardReady
      data.base.ratio) :
    Curves.Legendre.PeriodMonodromy.ProductiveCertificate data ready.one ready.infinity :=
  Curves.Legendre.PeriodMonodromy.productiveCertificate data ready.one ready.infinity

/-! ## Retryable standard denominator acquisition -/

/-- Attempt finite acquisition of one-loop denominator readiness from its initial state.

The result retains the original tau, matrix, fuel and any unfinished acquisition state; exhaustion does not establish
that the denominator vanishes. -/
@[expose] def attemptStandardOne (tau : Curves.Legendre.PeriodMonodromy.CoherentNamed) (fuel : Nat) :
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
@[expose] def attemptStandardInfinity (tau : Curves.Legendre.PeriodMonodromy.CoherentNamed) (fuel : Nat) :
    Run.RunResult
      Monodromy.infinityPeriodMatrix tau
      (State.initial
        Monodromy.infinityPeriodMatrix tau) fuel :=
  Run.attempt
    Monodromy.infinityPeriodMatrix tau
    (State.initial
      Monodromy.infinityPeriodMatrix tau) fuel

end Purelib.Curves.Legendre.PeriodMonodromy
