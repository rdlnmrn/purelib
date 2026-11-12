module
import Purelib.Data.Fin
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator
import Purelib.Approximation.Gaussian.Arithmetic.Add
import Purelib.Approximation.Gaussian.Arithmetic.Distributive
import Purelib.Approximation.Gaussian.Arithmetic.Mul
import Purelib.Approximation.Gaussian.Division.Cancellation
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Geometric.Coherent.Comparison
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Apart
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Apart.Preparation
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Approximation.Gaussian.Vector.Operational.Basic
public import Purelib.Approximation.Matrix.Operational.Integral.Action
import Purelib.Approximation.Matrix.Operational.Integral.Basic
import Purelib.Curves.Hyperelliptic.Basic
public import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Words

public import Purelib.Curves.Legendre.Monodromy
import Purelib.Curves.Legendre.Paths
public import Purelib.Riemann.Periods.PeriodTheorem
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Vector.Basic
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Approximation.Matrix.Operational.Vector
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum

open Purelib.LinearAlgebra.Matrix

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Matrix.Operational.Integral

open Purelib.Curves.Legendre

open Purelib.Approximation.Gaussian.Name.Coherent

@[expose] public section

/-!
# Finite normalized modular operations for the Legendre family

In genus one the finite Riemann-period package supplies the normalized
productive name `tau = A⁻¹B`.  This module develops the finite homogeneous
matrix algebra and apartness-certified fractional-linear operations used by
the dual period-monodromy interface.  It does not assert equality between
periods on different fibres.

No completed period, analytic quotient, or global upper-half-plane point is
introduced.
-/

namespace Purelib.Riemann.Integration.LegendreModularMonodromy

open Purelib.Riemann.Integration.LegendreGaussManin
open Purelib.Riemann.Periods.PeriodMatrix
open Purelib.LinearAlgebra.Gaussian.QuadraticForm
open Purelib.Riemann.Periods.PeriodMatrix.ScaledInverseCertificate

open Purelib.Data.Rat in
/-- The rational coordinate carrier for the retained Legendre period data. -/
abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier of the Legendre parameter. -/
abbrev Gaussian := Basic.Canonical
/-- The original two-dimensional integral monodromy matrix carrier. -/
abbrev IntegralMatrix := Basic.IntegralMatrix
/-- The original two-entry coherent Gaussian period vector. -/
abbrev RawPeriodVector := Approximation.Gaussian.Vector.Operational.Basic.RawPeriodVector
/-- Pointwise named equivalence of the original period vectors. -/
abbrev VectorEquivalent := Approximation.Gaussian.Vector.Operational.Basic.VectorEquivalent
/-- The original executable apartness certificate for a Gaussian name. -/
abbrev Apart := Basic.Named.Apart
open Purelib.Riemann.Periods in
/-- The retained positive lower certificate for a one-by-one A-period entry. -/
abbrev OneByOneLower :=
  OneByOneEntryCandidateLowerCertificate

/-- A two-element finite index is zero or one. -/
private theorem finTwo_cases (coordinate : Fin 2) :
    coordinate = 0 ∨ coordinate = 1 := by
  rcases coordinate with ⟨value, bound⟩
  cases value with
  | zero => exact Or.inl rfl
  | succ value =>
      cases value with
      | zero => exact Or.inr rfl
      | succ value =>
          have impossible : False := by omega0
          exact False.elim impossible

/-! ## Small finite operational algebra -/

section
open Purelib.Approximation.Gaussian
open Purelib.Riemann.Periods
/-- A singleton coherent named sum is equivalent to its sole entry. -/
public def sumNamed_one (values : Fin 1 -> Coherent.CoherentNamed) :
    Equivalence.NamedEquivalent (sumNamed values).name
      (values 0).name := by
  let zero := CoherentNamed.Coherence.exact 0
  let geometricZero := geometricNamed
    (Geometric.GeometricApproximation.exact 0)
  have removeTail : Equivalence.NamedEquivalent
      (CoherentNamed.add (values 0)
        geometricZero).name
      (CoherentNamed.add (values 0) zero).name :=
    Congruence.coherentAdd_respects
      (values 0) (values 0) geometricZero zero
      (Equivalence.NamedEquivalent.refl (values 0).name)
      Geometric.Coherent.Comparison.geometricZero_equivalent_exact
  change Equivalence.NamedEquivalent
    (CoherentNamed.add (values 0)
      geometricZero).name (values 0).name
  exact Equivalence.NamedEquivalent.trans removeTail
    (Arithmetic.Add.coherentAdd_zero_right (values 0))

/-- A two-entry coherent named sum is equivalent to their ordered addition. -/
public def sumNamed_two (values : Fin 2 -> Coherent.CoherentNamed) :
    Equivalence.NamedEquivalent (sumNamed values).name
      (CoherentNamed.add
        (values 0) (values 1)).name := by
  let tail := fun coordinate : Fin 1 => values coordinate.succ
  have tailEquivalent := sumNamed_one tail
  change Equivalence.NamedEquivalent
    (CoherentNamed.add (values 0)
      (sumNamed tail)).name
    (CoherentNamed.add (values 0) (values 1)).name
  exact Congruence.coherentAdd_respects
    (values 0) (values 0)
    (sumNamed tail) (values 1)
    (Equivalence.NamedEquivalent.refl (values 0).name)
    tailEquivalent

end

open Purelib.Approximation.Gaussian in
/-- One-by-one named matrix multiplication is equivalent to the single entry product. -/
public def matrixMul_one (left right : NamedMatrix 1) :
    Equivalence.NamedEquivalent (matrixMul left right 0 0).name
      (CoherentNamed.mul
        (left 0 0) (right 0 0)).name := by
  rw [matrixMul_apply]
  simpa only using sumNamed_one (fun middle : Fin 1 =>
    CoherentNamed.mul
      (left 0 middle) (right middle 0))

set_option genInjectivity false in
open Purelib in
/-- Normalized genus-one fibre data with an explicit A-period lower certificate.

The retained frame fixes the original curve; its normalized period data and one-by-one A-entry lower bound retain the
same matrix owner. -/
structure NormalizedFibreData {parameter : Gaussian}
    (frame : Paths.Frame parameter) where
  /-- The normalized period data of the curve fixed by the original Legendre frame. -/ normalized : NormalizedPeriodData
    (Periods.Fibre.frameCurve frame)
  /-- The retained strictly positive lower bound for that normalized data's original A-entry. -/ aPeriodLower :
    OneByOneLower normalized.toPeriodData.aMatrix

constructive_injectivity NormalizedFibreData

namespace NormalizedFibreData

section
open Purelib
/-- Read the original unnormalized period data of the retained Legendre fibre. -/
def toFibreData {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    (data : NormalizedFibreData frame) : Periods.Fibre.FibreData frame where
  periods := data.normalized.toPeriodData

/-- Read the unique original A-period entry of the normalized fibre. -/
def aPeriod {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    (data : NormalizedFibreData frame) : Coherent.CoherentNamed :=
  data.normalized.toPeriodData.aMatrix 0 0

/-- Read the unique original B-period entry of the normalized fibre. -/
def bPeriod {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    (data : NormalizedFibreData frame) : Coherent.CoherentNamed :=
  data.normalized.toPeriodData.bMatrix 0 0

/-- Read the unique normalized period ratio from the retained fibre data. -/
def ratio {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    (data : NormalizedFibreData frame) : Coherent.CoherentNamed :=
  data.normalized.omega 0 0

/-- The first raw fibre period is exactly its retained A-period. -/
@[simp] theorem rawPeriods_zero {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    (data : NormalizedFibreData frame) :
    data.toFibreData.rawPeriods 0 = data.aPeriod := rfl

/-- The second raw fibre period is exactly its retained B-period. -/
@[simp] theorem rawPeriods_one {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    (data : NormalizedFibreData frame) :
    data.toFibreData.rawPeriods 1 = data.bPeriod := by
  unfold toFibreData Periods.Fibre.FibreData.rawPeriods
    Periods.Fibre.FibreData.rawRefinement bPeriod
  rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]
  rfl

end

open Purelib.Approximation.Gaussian in
open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Periods in
/-- Multiplying the original genus-one A-period by the normalized ratio recovers the B-period up to named equivalence.

The proof retains the scaled inverse's adjugate and apart scalar, reduces the one-by-one matrix products, and cancels
that exact reciprocal witness. -/
def normalized_a_mul_ratio {curve :
    Basic.HyperellipticCurve 1}
    (normalized : NormalizedPeriodData curve) :
    Equivalence.NamedEquivalent
      (CoherentNamed.mul
        (normalized.toPeriodData.aMatrix 0 0)
        (normalized.omega 0 0)).name
      (normalized.toPeriodData.bMatrix 0 0).name := by
  let periods := normalized.toPeriodData
  let inverse := normalized.aInverse
  let a := periods.aMatrix 0 0
  let b := periods.bMatrix 0 0
  let adjugate := inverse.adjugate 0 0
  let scalar := inverse.scalar
  let reciprocal := inverseScalar inverse
  let numerator := matrixMul inverse.adjugate periods.bMatrix 0 0
  have numeratorProduct : Equivalence.NamedEquivalent numerator.name
      (CoherentNamed.mul adjugate b).name := by
    change Equivalence.NamedEquivalent
      (matrixMul inverse.adjugate periods.bMatrix 0 0).name
      (CoherentNamed.mul
        (inverse.adjugate 0 0) (periods.bMatrix 0 0)).name
    exact matrixMul_one inverse.adjugate periods.bMatrix
  have aAdjugate : Equivalence.NamedEquivalent
      (CoherentNamed.mul a adjugate).name scalar.name := by
    have direct := matrixMul_one periods.aMatrix inverse.adjugate
    have identity := inverse.right_identity 0 0
    have matrixToScalar : Equivalence.NamedEquivalent
        (matrixMul periods.aMatrix inverse.adjugate 0 0).name scalar.name := by
      rw [scaleIdentity_apply, if_pos rfl] at identity
      exact identity
    exact Equivalence.NamedEquivalent.trans
      (Equivalence.NamedEquivalent.symm (by
        change Equivalence.NamedEquivalent
          (matrixMul periods.aMatrix inverse.adjugate 0 0).name
          (CoherentNamed.mul
            (periods.aMatrix 0 0) (inverse.adjugate 0 0)).name at direct
        exact direct)) matrixToScalar
  have exposeNumerator : Equivalence.NamedEquivalent
      (CoherentNamed.mul a
        (CoherentNamed.mul numerator reciprocal)).name
      (CoherentNamed.mul a
        (CoherentNamed.mul
          (CoherentNamed.mul adjugate b)
          reciprocal)).name :=
    Congruence.coherentMul_respects a a
      (CoherentNamed.mul numerator reciprocal)
      (CoherentNamed.mul
        (CoherentNamed.mul adjugate b) reciprocal)
      (Equivalence.NamedEquivalent.refl a.name)
      (Congruence.coherentMul_respects numerator
        (CoherentNamed.mul adjugate b)
        reciprocal reciprocal numeratorProduct
        (Equivalence.NamedEquivalent.refl reciprocal.name))
  have rearrange : Equivalence.NamedEquivalent
      (CoherentNamed.mul a
        (CoherentNamed.mul
          (CoherentNamed.mul adjugate b)
          reciprocal)).name
      (CoherentNamed.mul
        (CoherentNamed.mul a adjugate)
        (CoherentNamed.mul reciprocal b)).name := by
    let adjugateB := CoherentNamed.mul adjugate b
    let bReciprocal := CoherentNamed.mul b reciprocal
    let reciprocalB := CoherentNamed.mul reciprocal b
    have innerAssociate : Equivalence.NamedEquivalent
        (CoherentNamed.mul adjugateB reciprocal).name
        (CoherentNamed.mul adjugate
          bReciprocal).name := by
      simpa only [adjugateB, bReciprocal,
        CoherentNamed.mul] using
        Laws.coherentMul_assoc adjugate b reciprocal
    have exposeInner : Equivalence.NamedEquivalent
        (CoherentNamed.mul a
          (CoherentNamed.mul adjugateB
            reciprocal)).name
        (CoherentNamed.mul a
          (CoherentNamed.mul adjugate
            bReciprocal)).name :=
      Congruence.coherentMul_respects a a
        (CoherentNamed.mul adjugateB reciprocal)
        (CoherentNamed.mul adjugate bReciprocal)
        (Equivalence.NamedEquivalent.refl a.name)
        innerAssociate
    have exposeAAdjugate : Equivalence.NamedEquivalent
        (CoherentNamed.mul a
          (CoherentNamed.mul adjugate
            bReciprocal)).name
        (CoherentNamed.mul
          (CoherentNamed.mul a adjugate)
          bReciprocal).name := by
      exact Equivalence.NamedEquivalent.symm (by
        simpa only [bReciprocal,
          CoherentNamed.mul] using
          Laws.coherentMul_assoc
            a adjugate bReciprocal)
    have swapTail : Equivalence.NamedEquivalent bReciprocal.name reciprocalB.name := by
      simpa only [bReciprocal, reciprocalB,
        CoherentNamed.mul] using
        Laws.coherentMul_comm b reciprocal
    have replaceTail : Equivalence.NamedEquivalent
        (CoherentNamed.mul
          (CoherentNamed.mul a adjugate)
          bReciprocal).name
        (CoherentNamed.mul
          (CoherentNamed.mul a adjugate)
          reciprocalB).name :=
      Congruence.coherentMul_respects
        (CoherentNamed.mul a adjugate)
        (CoherentNamed.mul a adjugate)
        bReciprocal reciprocalB
        (Equivalence.NamedEquivalent.refl _) swapTail
    exact Equivalence.NamedEquivalent.trans exposeInner
      (Equivalence.NamedEquivalent.trans exposeAAdjugate
        replaceTail)
  have replaceAdjugate : Equivalence.NamedEquivalent
      (CoherentNamed.mul
        (CoherentNamed.mul a adjugate)
        (CoherentNamed.mul reciprocal b)).name
      (CoherentNamed.mul scalar
        (CoherentNamed.mul reciprocal b)).name :=
    Congruence.coherentMul_respects
      (CoherentNamed.mul a adjugate) scalar
      (CoherentNamed.mul reciprocal b)
      (CoherentNamed.mul reciprocal b)
      aAdjugate (Equivalence.NamedEquivalent.refl _)
  have cancelScalar : Equivalence.NamedEquivalent
      (CoherentNamed.mul scalar
        (CoherentNamed.mul reciprocal b)).name
      b.name := by
    apply Equivalence.NamedEquivalent.trans
    · exact Equivalence.NamedEquivalent.symm
        (Laws.coherentMul_assoc scalar reciprocal b)
    · let scalarReciprocal :=
        CoherentNamed.mul scalar reciprocal
      have scalarReciprocalOne : Equivalence.NamedEquivalent scalarReciprocal.name
          (CoherentNamed.Coherence.exact 1).name :=
        Equivalence.NamedEquivalent.trans
          (show Equivalence.NamedEquivalent scalarReciprocal.name
              (CoherentNamed.mul reciprocal scalar).name from
            by
                simpa only [scalarReciprocal, CoherentNamed.mul]
                  using Laws.coherentMul_comm scalar reciprocal)
          (by
            have cancel :=
              Division.Cancellation.reciprocal_mul_cancel
                scalar inverse.scalarApart
            simpa only [reciprocal, scalar,
              inverseScalar,
              CoherentNamed.mul] using cancel)
      change Equivalence.NamedEquivalent
        (CoherentNamed.mul scalarReciprocal b).name
        b.name
      exact Equivalence.NamedEquivalent.trans
        (Congruence.coherentMul_respects scalarReciprocal
          (CoherentNamed.Coherence.exact 1) b b
          scalarReciprocalOne
          (Equivalence.NamedEquivalent.refl b.name))
        (Arithmetic.Mul.coherentMul_one_left b)
  change Equivalence.NamedEquivalent
    (CoherentNamed.mul a
      (CoherentNamed.mul numerator reciprocal)).name
    b.name
  exact Equivalence.NamedEquivalent.trans exposeNumerator
    (Equivalence.NamedEquivalent.trans rearrange
      (Equivalence.NamedEquivalent.trans replaceAdjugate
        cancelScalar))

section
open Purelib
open Purelib.Approximation.Gaussian
/-- The retained fibre's A-period times its normalized ratio is equivalent to its B-period. -/
def a_mul_ratio {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    (data : NormalizedFibreData frame) :
    Equivalence.NamedEquivalent
      (CoherentNamed.mul data.aPeriod data.ratio).name
      data.bPeriod.name :=
  normalized_a_mul_ratio data.normalized

/-! The direct finite lower certificate prepares a cancellable synchronized
view of the raw `A` period. -/

/-- The coherent approximation obtained by sampling the original A-period name. -/
def sampledAPeriod {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    (data : NormalizedFibreData frame) : Coherent.CoherentNamed :=
  CoherentNamed.ofApproximation
    (Sampling.approximation data.aPeriod.name)

/-- The retained A-period lower bound controls every possible value of its sampled process. -/
def sampledAPossibleApart {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    (data : NormalizedFibreData frame) :
    Process.Apart.Possible.PossibleApart data.sampledAPeriod.name.process where
  lowerSq := data.aPeriodLower.lowerSq
  positive := data.aPeriodLower.positive
  lower := by
    intro state value possible
    change (Sampling.approximation data.aPeriod.name).Possible
      state value at possible
    rcases possible with ⟨later, _order, rfl⟩
    exact data.aPeriodLower.sample_lower later

/-- Prepare the sampled A-period with its retained possible-value apartness certificate. -/
def preparedAPeriod {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    (data : NormalizedFibreData frame) : Coherent.CoherentNamed :=
  CoherentNamed.apartify data.sampledAPeriod
    data.sampledAPossibleApart

/-- Read the executable apartness certificate of the prepared A-period. -/
def preparedAPeriodApart {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    (data : NormalizedFibreData frame) : Apart data.preparedAPeriod.name where
  certificate := Process.Apart.Preparation.apartifyApart data.sampledAPossibleApart

/-- The original A-period is equivalent to its sampled and apartness-prepared name. -/
def aPeriod_equivalent_prepared {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    (data : NormalizedFibreData frame) :
    Equivalence.NamedEquivalent data.aPeriod.name data.preparedAPeriod.name :=
  Equivalence.NamedEquivalent.trans
    (Sequence.Name.Equivalence.named_toSamplingNamed data.aPeriod.name)
    (CoherentNamed.apartifyEquivalent
      data.sampledAPeriod data.sampledAPossibleApart)

end

open Purelib in
open Purelib.Riemann.Periods in
/-- Read normalized Legendre fibre data from a period result with a supplied A-entry lower bound.

The bound is transported along the result's exact cached-normalization readback, preserving its original matrix and
period owners. -/
def ofPeriodResult {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    (result : PeriodTheorem.Result
      (Periods.Fibre.frameCurve frame))
    (aPeriodLower : OneByOneLower result.periodData.aMatrix) :
    NormalizedFibreData frame where
  normalized := result.normalized
  aPeriodLower := by
    rw [result.normalized_readback]
    exact aPeriodLower

end NormalizedFibreData

/-! ## Matrix action on a normalized column -/

open Purelib.Approximation.Gaussian in
/-- Multiply each original period-vector entry by the same coherent Gaussian scalar. -/
def scaleVector (scalar : Coherent.CoherentNamed) (values : RawPeriodVector) :
    RawPeriodVector := fun coordinate =>
  CoherentNamed.mul scalar (values coordinate)

open Purelib.Approximation.Gaussian in
open Purelib.Riemann.Periods in
/-- A finite named sum of scaled entries is equivalent to scaling the original sum.

The constructive recursion keeps the original ordered entries and compares the geometric empty sum with exact zero
before distributing each scalar term. -/
def sumNamed_scale_left : {count : Nat} ->
    (scalar : Coherent.CoherentNamed) -> (values : Fin count ->
      Coherent.CoherentNamed) ->
      Equivalence.NamedEquivalent
        (sumNamed fun coordinate =>
          CoherentNamed.mul scalar
            (values coordinate)).name
        (CoherentNamed.mul scalar
          (sumNamed values)).name
  | 0, scalar, values => by
      let geometricZero := geometricNamed
        (Geometric.GeometricApproximation.exact 0)
      let exactZero := CoherentNamed.Coherence.exact 0
      have rightZero : Equivalence.NamedEquivalent
          (CoherentNamed.mul scalar geometricZero).name
          exactZero.name :=
        Equivalence.NamedEquivalent.trans
          (Congruence.coherentMul_respects scalar scalar
            geometricZero exactZero
            (Equivalence.NamedEquivalent.refl scalar.name)
            Geometric.Coherent.Comparison.geometricZero_equivalent_exact)
          (Arithmetic.Mul.coherentMul_zero_right scalar)
      change Equivalence.NamedEquivalent geometricZero.name
        (CoherentNamed.mul scalar geometricZero).name
      exact Equivalence.NamedEquivalent.trans
        Geometric.Coherent.Comparison.geometricZero_equivalent_exact
        (Equivalence.NamedEquivalent.symm rightZero)
  | count + 1, scalar, values => by
      let tail := fun coordinate : Fin count => values coordinate.succ
      let tailSum := sumNamed tail
      let scaledTail := fun coordinate : Fin count =>
        CoherentNamed.mul scalar (tail coordinate)
      have tailEquivalent := sumNamed_scale_left scalar tail
      have replaceTail : Equivalence.NamedEquivalent
          (CoherentNamed.add
            (CoherentNamed.mul scalar (values 0))
            (sumNamed scaledTail)).name
          (CoherentNamed.add
            (CoherentNamed.mul scalar (values 0))
            (CoherentNamed.mul scalar tailSum)).name :=
        Congruence.coherentAdd_respects
          (CoherentNamed.mul scalar (values 0))
          (CoherentNamed.mul scalar (values 0))
          (sumNamed scaledTail)
          (CoherentNamed.mul scalar tailSum)
          (Equivalence.NamedEquivalent.refl _) tailEquivalent
      change Equivalence.NamedEquivalent
        (CoherentNamed.add
          (CoherentNamed.mul scalar (values 0))
          (sumNamed scaledTail)).name
        (CoherentNamed.mul scalar
          (CoherentNamed.add
            (values 0) tailSum)).name
      exact Equivalence.NamedEquivalent.trans replaceTail
        (Equivalence.NamedEquivalent.symm
          (Arithmetic.Distributive.coherentMul_add_left
            scalar (values 0) tailSum))

open Purelib in
open Purelib.Approximation.Gaussian in
open Purelib.Riemann.Periods in
/-- Integral matrix action commutes with coherent scalar multiplication up to vector equivalence.

Each original row keeps its two coefficient terms; pointwise product and finite-sum equivalences move the same retained
scalar outside the row sum. -/
def matrixAction_scale (matrix : IntegralMatrix) (scalar : Coherent.CoherentNamed)
    (values : RawPeriodVector) :
    VectorEquivalent (Action.matrixAction matrix (scaleVector scalar values))
      (scaleVector scalar (Action.matrixAction matrix values)) := by
  intro row
  let terms := fun column : Fin 2 =>
    CoherentNamed.mul
      (Basic.integralNamedMatrix matrix row column) (values column)
  have moveScalar : Equivalence.NamedEquivalent
      (sumNamed fun column : Fin 2 =>
        CoherentNamed.mul
          (Basic.integralNamedMatrix matrix row column)
          (CoherentNamed.mul scalar
            (values column))).name
      (sumNamed fun column : Fin 2 =>
        CoherentNamed.mul scalar
          (terms column)).name :=
    sumNamed_respects _ _ fun column =>
      Laws.coherentMul_left_comm
        (Basic.integralNamedMatrix matrix row
        column)
        scalar (values column)
  change Equivalence.NamedEquivalent
    (Action.matrixAction matrix (scaleVector scalar values) row).name
    (CoherentNamed.mul scalar
      (Action.matrixAction matrix values row)).name
  rw [Action.matrixAction, matrixMul_apply]
  change Equivalence.NamedEquivalent
    (sumNamed fun column : Fin 2 =>
      CoherentNamed.mul
        (Basic.integralNamedMatrix matrix row column)
        (CoherentNamed.mul scalar
          (values column))).name
    (CoherentNamed.mul scalar
      (Action.matrixAction matrix values row)).name
  rw [Action.matrixAction, matrixMul_apply]
  exact Equivalence.NamedEquivalent.trans moveScalar
    (sumNamed_scale_left scalar terms)

open Purelib.Approximation.Gaussian in
/-- The coherent two-entry vector consisting of exact one followed by the retained ratio. -/
def fractionalVector (tau : Coherent.CoherentNamed) : RawPeriodVector :=
  fun coordinate => if coordinate = 0 then
    CoherentNamed.Coherence.exact 1
  else tau

open Purelib in
open Purelib.Approximation.Gaussian in
open Purelib.Data in
/-- The original fibre period vector equals A-period times its normalized ratio vector up to named equivalence. -/
def NormalizedFibreData.raw_normalized {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    (data : NormalizedFibreData frame) :
    VectorEquivalent data.toFibreData.rawPeriods
      (scaleVector data.aPeriod (fractionalVector data.ratio)) := by
  intro coordinate
  refine Fin.casesByRecursion ?_ (fun tail => Fin.casesByRecursion ?_
    (fun impossible => _root_.Fin.elim0 impossible) tail) coordinate
  · exact (Equivalence.NamedEquivalent.symm
      (Arithmetic.Mul.coherentMul_one_right data.aPeriod) :
      Equivalence.NamedEquivalent
        (data.toFibreData.rawPeriods (0 : Fin (1 + 1))).name
        ((scaleVector data.aPeriod (fractionalVector data.ratio)) (0 : Fin (1 + 1))).name)
  · exact (Equivalence.NamedEquivalent.symm data.a_mul_ratio :
      Equivalence.NamedEquivalent
        (data.toFibreData.rawPeriods (Fin.succ (0 : Fin (0 + 1)))).name
        ((scaleVector data.aPeriod (fractionalVector data.ratio))
          (Fin.succ (0 : Fin (0 + 1)))).name)

open Purelib.Approximation.Gaussian in
/-- The first fractional-vector entry is exact one. -/
@[simp] theorem fractionalVector_zero (tau : Coherent.CoherentNamed) :
    fractionalVector tau 0 =
      CoherentNamed.Coherence.exact 1 := rfl

/-- The second fractional-vector entry is the original ratio. -/
@[simp] theorem fractionalVector_one (tau : Coherent.CoherentNamed) :
    fractionalVector tau 1 = tau := by
  unfold fractionalVector
  rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]

open Purelib in
/-- Read one row of the integral matrix action on the retained fractional vector. -/
def fractionalRow (matrix : IntegralMatrix) (tau : Coherent.CoherentNamed)
    (row : Fin 2) : Coherent.CoherentNamed :=
  Action.matrixAction matrix (fractionalVector tau) row

/-- Read the first transformed fractional-vector row as the denominator. -/
def fractionalDenominator (matrix : IntegralMatrix) (tau : Coherent.CoherentNamed) :
    Coherent.CoherentNamed := fractionalRow matrix tau 0

/-- Read the second transformed fractional-vector row as the numerator. -/
def fractionalNumerator (matrix : IntegralMatrix) (tau : Coherent.CoherentNamed) :
    Coherent.CoherentNamed := fractionalRow matrix tau 1

open Purelib in
open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
open Purelib.Riemann.Periods in
/-- Expand an integral matrix row into its two exact-cast coefficient products up to named equivalence.

The original ordered sum and coefficient entries are preserved, with geometric coefficient names compared to the exact
integer casts. -/
def matrixAction_row_two (matrix : IntegralMatrix) (values : RawPeriodVector)
    (row : Fin 2) :
    Equivalence.NamedEquivalent
      (Action.matrixAction matrix values row).name
      (CoherentNamed.add
        (CoherentNamed.mul
          (CoherentNamed.Coherence.exact
            (Cast.integralGaussian (matrix row 0))) (values 0))
        (CoherentNamed.mul
          (CoherentNamed.Coherence.exact
            (Cast.integralGaussian (matrix row 1))) (values 1))).name := by
  let terms := fun column : Fin 2 =>
    CoherentNamed.mul
      (Basic.integralNamedMatrix matrix row column) (values column)
  have exposeSum : Equivalence.NamedEquivalent
      (sumNamed terms).name
      (CoherentNamed.add
        (terms 0) (terms 1)).name := sumNamed_two terms
  have coefficientEquivalent : forall column : Fin 2,
      Equivalence.NamedEquivalent
        (Basic.integralNamedMatrix matrix row column).name
        (CoherentNamed.Coherence.exact
          (Cast.integralGaussian (matrix row column))).name := by
    intro column
    rw [Basic.integralNamedMatrix_apply]
    exact Geometric.Coherent.Comparison.geometricExact_equivalent_exact _
  have replaceTerms : Equivalence.NamedEquivalent
      (CoherentNamed.add
        (terms 0) (terms 1)).name
      (CoherentNamed.add
        (CoherentNamed.mul
          (CoherentNamed.Coherence.exact
            (Cast.integralGaussian (matrix row 0))) (values 0))
        (CoherentNamed.mul
          (CoherentNamed.Coherence.exact
            (Cast.integralGaussian (matrix row 1))) (values 1))).name :=
    Congruence.coherentAdd_respects
      (terms 0)
      (CoherentNamed.mul
        (CoherentNamed.Coherence.exact
          (Cast.integralGaussian (matrix row 0))) (values 0))
      (terms 1)
      (CoherentNamed.mul
        (CoherentNamed.Coherence.exact
          (Cast.integralGaussian (matrix row 1))) (values 1))
      (Congruence.coherentMul_respects
        (Basic.integralNamedMatrix matrix row 0)
        (CoherentNamed.Coherence.exact
          (Cast.integralGaussian (matrix row 0)))
        (values 0) (values 0) (coefficientEquivalent 0)
        (Equivalence.NamedEquivalent.refl (values 0).name))
      (Congruence.coherentMul_respects
        (Basic.integralNamedMatrix matrix row 1)
        (CoherentNamed.Coherence.exact
          (Cast.integralGaussian (matrix row 1)))
        (values 1) (values 1) (coefficientEquivalent 1)
        (Equivalence.NamedEquivalent.refl (values 1).name))
  rw [Action.matrixAction, matrixMul_apply]
  change Equivalence.NamedEquivalent
    (sumNamed terms).name _
  exact Equivalence.NamedEquivalent.trans exposeSum replaceTerms

section
open Purelib
open Purelib.Approximation.Gaussian
/-- The standard loop around one has fractional denominator equivalent to exact one. -/
def one_denominator_one (tau : Coherent.CoherentNamed) :
    Equivalence.NamedEquivalent
      (fractionalDenominator Monodromy.oneMatrix tau).name
      (CoherentNamed.Coherence.exact 1).name := by
  let one := CoherentNamed.Coherence.exact 1
  let zero := CoherentNamed.Coherence.exact 0
  have expanded := matrixAction_row_two
    Monodromy.oneMatrix (fractionalVector tau) 0
  change Equivalence.NamedEquivalent
    (fractionalDenominator Monodromy.oneMatrix tau).name
    (CoherentNamed.add
      (CoherentNamed.mul one one)
      (CoherentNamed.mul zero tau)).name at expanded
  have simplifyTerms : Equivalence.NamedEquivalent
      (CoherentNamed.add
        (CoherentNamed.mul one one)
        (CoherentNamed.mul zero tau)).name
      (CoherentNamed.add one zero).name :=
    Congruence.coherentAdd_respects
      (CoherentNamed.mul one one) one
      (CoherentNamed.mul zero tau) zero
      (Arithmetic.Mul.coherentMul_one_right one)
      (Arithmetic.Mul.coherentMul_zero_left tau)
  exact Equivalence.NamedEquivalent.trans expanded
    (Equivalence.NamedEquivalent.trans simplifyTerms
      (Arithmetic.Add.coherentAdd_zero_right one))

/-- The standard loop around one has numerator equivalent to two plus the retained ratio. -/
def one_numerator_two_add (tau : Coherent.CoherentNamed) :
    Equivalence.NamedEquivalent
      (fractionalNumerator Monodromy.oneMatrix tau).name
      (CoherentNamed.add
        (CoherentNamed.Coherence.exact 2) tau).name := by
  let one := CoherentNamed.Coherence.exact 1
  let two := CoherentNamed.Coherence.exact 2
  have expanded := matrixAction_row_two
    Monodromy.oneMatrix (fractionalVector tau) 1
  change Equivalence.NamedEquivalent
    (fractionalNumerator Monodromy.oneMatrix tau).name
    (CoherentNamed.add
      (CoherentNamed.mul two one)
      (CoherentNamed.mul one tau)).name at expanded
  exact Equivalence.NamedEquivalent.trans expanded
    (Congruence.coherentAdd_respects
      (CoherentNamed.mul two one) two
      (CoherentNamed.mul one tau) tau
      (Arithmetic.Mul.coherentMul_one_right two)
      (Arithmetic.Mul.coherentMul_one_left tau))

end

open Purelib.Approximation.Gaussian in
/-- Add exact two to the retained coherent period ratio. -/
def oneAffineTransform (tau : Coherent.CoherentNamed) :
  Coherent.CoherentNamed :=
  CoherentNamed.add
    (CoherentNamed.Coherence.exact 2) tau

section
open Purelib.Approximation.Gaussian
/-- Apply an integral fractional transformation using the supplied prepared denominator.

The numerator is multiplied by the reciprocal of that exact prepared name and its retained apartness witness;
denominator preparation remains explicit input. -/
def fractionalLinear (matrix : IntegralMatrix) (tau : Coherent.CoherentNamed)
    (preparation : Division.Prepared.DenominatorPreparation
      (fractionalDenominator matrix tau)) : Coherent.CoherentNamed :=
  CoherentNamed.mul
    (fractionalNumerator matrix tau)
    (CoherentNamed.div
      (CoherentNamed.Coherence.exact 1)
      preparation.prepared preparation.apart)

/-- The prepared denominator times its fractional transformation is equivalent to the original numerator.

Cancellation uses the same denominator preparation and apartness witness that constructed the reciprocal, preserving its
actual executable name. -/
def prepared_denominator_mul_fractionalLinear
    (matrix : IntegralMatrix) (tau : Coherent.CoherentNamed)
    (preparation : Division.Prepared.DenominatorPreparation
      (fractionalDenominator matrix tau)) :
    Equivalence.NamedEquivalent
      (CoherentNamed.mul
        preparation.prepared
        (fractionalLinear matrix tau preparation)).name
      (fractionalNumerator matrix tau).name := by
  let denominator := preparation.prepared
  let numerator := fractionalNumerator matrix tau
  let reciprocal := CoherentNamed.div
    (CoherentNamed.Coherence.exact 1) denominator
      preparation.apart
  let reciprocalDenominator :=
    CoherentNamed.mul reciprocal denominator
  let one := CoherentNamed.Coherence.exact 1
  have rearrange : Equivalence.NamedEquivalent
      (CoherentNamed.mul denominator
        (CoherentNamed.mul numerator reciprocal)).name
      (CoherentNamed.mul numerator
        reciprocalDenominator).name := by
    let numeratorReciprocal :=
      CoherentNamed.mul numerator reciprocal
    apply Equivalence.NamedEquivalent.trans
    · simpa only [numeratorReciprocal,
        CoherentNamed.mul] using
        Laws.coherentMul_comm
          denominator numeratorReciprocal
    · simpa only [numeratorReciprocal, reciprocalDenominator,
        CoherentNamed.mul] using
        Laws.coherentMul_assoc
          numerator reciprocal denominator
  have cancel : Equivalence.NamedEquivalent reciprocalDenominator.name
      one.name := by
    simpa only [reciprocalDenominator, reciprocal, one,
      CoherentNamed.mul] using
      Division.Cancellation.reciprocal_mul_cancel denominator
        preparation.apart
  change Equivalence.NamedEquivalent
    (CoherentNamed.mul denominator
      (CoherentNamed.mul numerator reciprocal)).name
    numerator.name
  exact Equivalence.NamedEquivalent.trans rearrange
    (Equivalence.NamedEquivalent.trans
      (Congruence.coherentMul_respects numerator numerator
        reciprocalDenominator one
        (Equivalence.NamedEquivalent.refl numerator.name) cancel)
      (Arithmetic.Mul.coherentMul_one_right numerator))

/-- The original denominator times the prepared fractional transformation is equivalent to the numerator. -/
def denominator_mul_fractionalLinear
    (matrix : IntegralMatrix) (tau : Coherent.CoherentNamed)
    (preparation : Division.Prepared.DenominatorPreparation
      (fractionalDenominator matrix tau)) :
    Equivalence.NamedEquivalent
      (CoherentNamed.mul
        (fractionalDenominator matrix tau)
        (fractionalLinear matrix tau preparation)).name
      (fractionalNumerator matrix tau).name :=
  Equivalence.NamedEquivalent.trans
    (Congruence.coherentMul_respects
      (fractionalDenominator matrix tau) preparation.prepared
      (fractionalLinear matrix tau preparation)
      (fractionalLinear matrix tau preparation) preparation.equivalent
      (Equivalence.NamedEquivalent.refl _))
    (prepared_denominator_mul_fractionalLinear matrix tau preparation)

/-! ## Standard productive transformations -/

end

section
open Purelib
/-- The fractional denominator for the standard loop around zero. -/
def standardZeroDenominator (tau : Coherent.CoherentNamed) :
  Coherent.CoherentNamed :=
  fractionalDenominator Monodromy.zeroMatrix
    tau

/-- The fractional denominator for the standard loop around one. -/
def standardOneDenominator (tau : Coherent.CoherentNamed) :
  Coherent.CoherentNamed :=
  fractionalDenominator Monodromy.oneMatrix
    tau

/-- The fractional denominator for the standard loop around infinity. -/
def standardInfinityDenominator (tau : Coherent.CoherentNamed) :
  Coherent.CoherentNamed :=
  fractionalDenominator Monodromy.infinityMatrix
    tau

end

section
open Purelib.Approximation.Gaussian
/-- A retained executable denominator preparation for the standard loop around zero. -/
def StandardZeroPreparation (tau : Coherent.CoherentNamed) : Type 1 :=
  Division.Prepared.DenominatorPreparation (standardZeroDenominator tau)

/-- A retained executable denominator preparation for the standard loop around one. -/
def StandardOnePreparation (tau : Coherent.CoherentNamed) : Type 1 :=
  Division.Prepared.DenominatorPreparation (standardOneDenominator tau)

/-- A retained executable denominator preparation for the standard loop around infinity. -/
def StandardInfinityPreparation (tau : Coherent.CoherentNamed) : Type 1 :=
  Division.Prepared.DenominatorPreparation (standardInfinityDenominator tau)

end

section
open Purelib
open Purelib.Approximation.Gaussian
/-- Apply the standard zero-loop fractional transformation using its retained denominator preparation. -/
def zeroTransform {tau : Coherent.CoherentNamed}
    (preparation : StandardZeroPreparation tau) : Coherent.CoherentNamed := by
  change Division.Prepared.DenominatorPreparation
    (fractionalDenominator Monodromy.zeroMatrix tau)
      at preparation
  exact fractionalLinear Monodromy.zeroMatrix
    tau preparation

/-- Apply the standard one-loop fractional transformation using its retained denominator preparation. -/
def oneTransform {tau : Coherent.CoherentNamed}
    (preparation : StandardOnePreparation tau) : Coherent.CoherentNamed := by
  change Division.Prepared.DenominatorPreparation
    (fractionalDenominator Monodromy.oneMatrix tau)
      at preparation
  exact fractionalLinear Monodromy.oneMatrix
    tau preparation

/-- The prepared one-loop transformation is equivalent to adding two to the original ratio.

The result transports the retained denominator to exact one, cancels its prepared reciprocal, and retains the original
numerator equivalence. -/
def oneTransform_equivalent_affine {tau : Coherent.CoherentNamed}
    (preparation : StandardOnePreparation tau) :
    Equivalence.NamedEquivalent (oneTransform preparation).name
      (oneAffineTransform tau).name := by
  change Division.Prepared.DenominatorPreparation
    (fractionalDenominator Monodromy.oneMatrix tau)
      at preparation
  let one := CoherentNamed.Coherence.exact 1
  let transformed := fractionalLinear
    Monodromy.oneMatrix tau preparation
  let numerator := fractionalNumerator
    Monodromy.oneMatrix tau
  have onePrepared : Equivalence.NamedEquivalent one.name preparation.prepared.name :=
    Equivalence.NamedEquivalent.trans
      (Equivalence.NamedEquivalent.symm
        (one_denominator_one tau)) preparation.equivalent
  have scaled : Equivalence.NamedEquivalent
      (CoherentNamed.mul one transformed).name
      numerator.name :=
    Equivalence.NamedEquivalent.trans
      (Congruence.coherentMul_respects
        one preparation.prepared transformed transformed onePrepared
        (Equivalence.NamedEquivalent.refl transformed.name))
      (by
          simpa only [transformed, numerator, CoherentNamed.mul]
            using (prepared_denominator_mul_fractionalLinear Monodromy.oneMatrix tau preparation))
  change Equivalence.NamedEquivalent transformed.name (oneAffineTransform tau).name
  exact Equivalence.NamedEquivalent.trans
    (Equivalence.NamedEquivalent.symm
      (Arithmetic.Mul.coherentMul_one_left transformed))
    (Equivalence.NamedEquivalent.trans scaled
      (by
          simpa only [numerator, oneAffineTransform]
            using one_numerator_two_add tau))

/-- Apply the standard infinity-loop fractional transformation using its retained denominator preparation. -/
def infinityTransform {tau : Coherent.CoherentNamed}
    (preparation : StandardInfinityPreparation tau) : Coherent.CoherentNamed := by
  change Division.Prepared.DenominatorPreparation
    (fractionalDenominator Monodromy.infinityMatrix tau)
      at preparation
  exact fractionalLinear Monodromy.infinityMatrix
    tau preparation

end

open Purelib
/-- The infinity monodromy matrix is a two-sided inverse of the ordered one-times-zero product. -/
theorem infinity_inverse_combined :
    Multiplication.mul
        Monodromy.infinityMatrix
        (Multiplication.mul
          Monodromy.oneMatrix
          Monodromy.zeroMatrix) =
      Multiplication.identity ∧
    Multiplication.mul
        (Multiplication.mul
          Monodromy.oneMatrix
          Monodromy.zeroMatrix)
        Monodromy.infinityMatrix =
      Multiplication.identity :=
  ⟨Monodromy.explicit_loop_product_left,
    Monodromy.explicit_loop_product_right⟩

/-- The retained infinity and combined paths have mutually inverse integral word matrices. -/
theorem reversal_path_matrices {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    (loops : Monodromy.StandardLoops frame) :
    Multiplication.mul
        (Topology.Knot.Braid.ThreeStrand.Integral.Words.wordMatrix
          loops.infinityPath.word)
        (Topology.Knot.Braid.ThreeStrand.Integral.Words.wordMatrix
          loops.combinedPath.word) = Multiplication.identity ∧
    Multiplication.mul
        (Topology.Knot.Braid.ThreeStrand.Integral.Words.wordMatrix
          loops.combinedPath.word)
        (Topology.Knot.Braid.ThreeStrand.Integral.Words.wordMatrix
          loops.infinityPath.word) = Multiplication.identity :=
  Monodromy.StandardLoops.reversePath_matrix_identities
    loops.combinedPath

end Purelib.Riemann.Integration.LegendreModularMonodromy
