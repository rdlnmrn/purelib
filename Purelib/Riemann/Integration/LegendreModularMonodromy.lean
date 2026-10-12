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
abbrev IntegralMatrix := LinearAlgebra.Matrix.Basic.IntegralMatrix
/-- The original two-entry coherent Gaussian period vector. -/
abbrev RawPeriodVector := Purelib.Approximation.Gaussian.Vector.Operational.Basic.RawPeriodVector
/-- Pointwise named equivalence of the original period vectors. -/
abbrev VectorEquivalent := Purelib.Approximation.Gaussian.Vector.Operational.Basic.VectorEquivalent
/-- The original executable apartness certificate for a Gaussian name. -/
abbrev Apart := Purelib.Approximation.Gaussian.Name.Basic.Named.Apart
open Purelib.Riemann.Periods in
/-- The retained positive lower certificate for a one-by-one A-period entry. -/
abbrev OneByOneLower :=
  PeriodMatrix.OneByOneEntryCandidateLowerCertificate

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
public def sumNamed_one (values : Fin 1 -> Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed) :
    Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent (PeriodMatrix.sumNamed values).name
      (values 0).name := by
  let zero := Name.Coherent.CoherentNamed.Coherence.exact 0
  let geometricZero := PeriodMatrix.geometricNamed
    (Geometric.GeometricApproximation.exact 0)
  have removeTail : Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
      (Name.Coherent.CoherentNamed.add (values 0)
        geometricZero).name
      (Name.Coherent.CoherentNamed.add (values 0) zero).name :=
    Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects
      (values 0) (values 0) geometricZero zero
      (Equivalence.NamedEquivalent.refl (values 0).name)
      Geometric.Coherent.Comparison.geometricZero_equivalent_exact
  change Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
    (Name.Coherent.CoherentNamed.add (values 0)
      geometricZero).name (values 0).name
  exact Equivalence.NamedEquivalent.trans removeTail
    (Arithmetic.Add.coherentAdd_zero_right (values 0))

/-- A two-entry coherent named sum is equivalent to their ordered addition. -/
public def sumNamed_two (values : Fin 2 -> Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed) :
    Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent (PeriodMatrix.sumNamed values).name
      (Name.Coherent.CoherentNamed.add
        (values 0) (values 1)).name := by
  let tail := fun coordinate : Fin 1 => values coordinate.succ
  have tailEquivalent := sumNamed_one tail
  change Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
    (Name.Coherent.CoherentNamed.add (values 0)
      (PeriodMatrix.sumNamed tail)).name
    (Name.Coherent.CoherentNamed.add (values 0) (values 1)).name
  exact Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects
    (values 0) (values 0)
    (PeriodMatrix.sumNamed tail) (values 1)
    (Equivalence.NamedEquivalent.refl (values 0).name)
    tailEquivalent

end

open Purelib.Approximation.Gaussian in
/-- One-by-one named matrix multiplication is equivalent to the single entry product. -/
public def matrixMul_one (left right : NamedMatrix 1) :
    Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent (matrixMul left right 0 0).name
      (Name.Coherent.CoherentNamed.mul
        (left 0 0) (right 0 0)).name := by
  rw [matrixMul_apply]
  simpa only using sumNamed_one (fun middle : Fin 1 =>
    Name.Coherent.CoherentNamed.mul
      (left 0 middle) (right middle 0))

set_option genInjectivity false in
open Purelib in
/-- Normalized genus-one fibre data with an explicit A-period lower certificate.

The retained frame fixes the original curve; its normalized period data and one-by-one A-entry lower bound retain the
same matrix owner. -/
structure NormalizedFibreData {parameter : Gaussian}
    (frame : Curves.Legendre.Paths.Frame parameter) where
  /-- The normalized period data of the curve fixed by the original Legendre frame. -/ normalized : NormalizedPeriodData
    (Curves.Legendre.Periods.Fibre.frameCurve frame)
  /-- The retained strictly positive lower bound for that normalized data's original A-entry. -/ aPeriodLower :
    OneByOneLower normalized.toPeriodData.aMatrix

constructive_injectivity NormalizedFibreData

namespace NormalizedFibreData

section
open Purelib
/-- Read the original unnormalized period data of the retained Legendre fibre. -/
def toFibreData {parameter : Gaussian}
    {frame : Curves.Legendre.Paths.Frame parameter}
    (data : NormalizedFibreData frame) : Curves.Legendre.Periods.Fibre.FibreData frame where
  periods := data.normalized.toPeriodData

/-- Read the unique original A-period entry of the normalized fibre. -/
def aPeriod {parameter : Gaussian}
    {frame : Curves.Legendre.Paths.Frame parameter}
    (data : NormalizedFibreData frame) : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed :=
  data.normalized.toPeriodData.aMatrix 0 0

/-- Read the unique original B-period entry of the normalized fibre. -/
def bPeriod {parameter : Gaussian}
    {frame : Curves.Legendre.Paths.Frame parameter}
    (data : NormalizedFibreData frame) : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed :=
  data.normalized.toPeriodData.bMatrix 0 0

/-- Read the unique normalized period ratio from the retained fibre data. -/
def ratio {parameter : Gaussian}
    {frame : Curves.Legendre.Paths.Frame parameter}
    (data : NormalizedFibreData frame) : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed :=
  data.normalized.omega 0 0

/-- The first raw fibre period is exactly its retained A-period. -/
@[simp] theorem rawPeriods_zero {parameter : Gaussian}
    {frame : Curves.Legendre.Paths.Frame parameter}
    (data : NormalizedFibreData frame) :
    data.toFibreData.rawPeriods 0 = data.aPeriod := rfl

/-- The second raw fibre period is exactly its retained B-period. -/
@[simp] theorem rawPeriods_one {parameter : Gaussian}
    {frame : Curves.Legendre.Paths.Frame parameter}
    (data : NormalizedFibreData frame) :
    data.toFibreData.rawPeriods 1 = data.bPeriod := by
  unfold toFibreData Curves.Legendre.Periods.Fibre.FibreData.rawPeriods
    Curves.Legendre.Periods.Fibre.FibreData.rawRefinement bPeriod
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
    Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
      (Name.Coherent.CoherentNamed.mul
        (normalized.toPeriodData.aMatrix 0 0)
        (normalized.omega 0 0)).name
      (normalized.toPeriodData.bMatrix 0 0).name := by
  let periods := normalized.toPeriodData
  let inverse := normalized.aInverse
  let a := periods.aMatrix 0 0
  let b := periods.bMatrix 0 0
  let adjugate := inverse.adjugate 0 0
  let scalar := inverse.scalar
  let reciprocal := PeriodMatrix.inverseScalar inverse
  let numerator := matrixMul inverse.adjugate periods.bMatrix 0 0
  have numeratorProduct : Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent numerator.name
      (Name.Coherent.CoherentNamed.mul adjugate b).name := by
    change Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
      (matrixMul inverse.adjugate periods.bMatrix 0 0).name
      (Name.Coherent.CoherentNamed.mul
        (inverse.adjugate 0 0) (periods.bMatrix 0 0)).name
    exact matrixMul_one inverse.adjugate periods.bMatrix
  have aAdjugate : Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
      (Name.Coherent.CoherentNamed.mul a adjugate).name scalar.name := by
    have direct := matrixMul_one periods.aMatrix inverse.adjugate
    have identity := inverse.right_identity 0 0
    have matrixToScalar : Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
        (matrixMul periods.aMatrix inverse.adjugate 0 0).name scalar.name := by
      rw [scaleIdentity_apply, if_pos rfl] at identity
      exact identity
    exact Equivalence.NamedEquivalent.trans
      (Equivalence.NamedEquivalent.symm (by
        change Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
          (matrixMul periods.aMatrix inverse.adjugate 0 0).name
          (Name.Coherent.CoherentNamed.mul
            (periods.aMatrix 0 0) (inverse.adjugate 0 0)).name at direct
        exact direct)) matrixToScalar
  have exposeNumerator : Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
      (Name.Coherent.CoherentNamed.mul a
        (Name.Coherent.CoherentNamed.mul numerator reciprocal)).name
      (Name.Coherent.CoherentNamed.mul a
        (Name.Coherent.CoherentNamed.mul
          (Name.Coherent.CoherentNamed.mul adjugate b)
          reciprocal)).name :=
    Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects a a
      (Name.Coherent.CoherentNamed.mul numerator reciprocal)
      (Name.Coherent.CoherentNamed.mul
        (Name.Coherent.CoherentNamed.mul adjugate b) reciprocal)
      (Equivalence.NamedEquivalent.refl a.name)
      (Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects numerator
        (Name.Coherent.CoherentNamed.mul adjugate b)
        reciprocal reciprocal numeratorProduct
        (Equivalence.NamedEquivalent.refl reciprocal.name))
  have rearrange : Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
      (Name.Coherent.CoherentNamed.mul a
        (Name.Coherent.CoherentNamed.mul
          (Name.Coherent.CoherentNamed.mul adjugate b)
          reciprocal)).name
      (Name.Coherent.CoherentNamed.mul
        (Name.Coherent.CoherentNamed.mul a adjugate)
        (Name.Coherent.CoherentNamed.mul reciprocal b)).name := by
    let adjugateB := Name.Coherent.CoherentNamed.mul adjugate b
    let bReciprocal := Name.Coherent.CoherentNamed.mul b reciprocal
    let reciprocalB := Name.Coherent.CoherentNamed.mul reciprocal b
    have innerAssociate : Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
        (Name.Coherent.CoherentNamed.mul adjugateB reciprocal).name
        (Name.Coherent.CoherentNamed.mul adjugate
          bReciprocal).name := by
      simpa only [adjugateB, bReciprocal,
        Name.Coherent.CoherentNamed.mul] using
        Name.Coherent.Arithmetic.Product.Laws.coherentMul_assoc adjugate b reciprocal
    have exposeInner : Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
        (Name.Coherent.CoherentNamed.mul a
          (Name.Coherent.CoherentNamed.mul adjugateB
            reciprocal)).name
        (Name.Coherent.CoherentNamed.mul a
          (Name.Coherent.CoherentNamed.mul adjugate
            bReciprocal)).name :=
      Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects a a
        (Name.Coherent.CoherentNamed.mul adjugateB reciprocal)
        (Name.Coherent.CoherentNamed.mul adjugate bReciprocal)
        (Equivalence.NamedEquivalent.refl a.name)
        innerAssociate
    have exposeAAdjugate : Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
        (Name.Coherent.CoherentNamed.mul a
          (Name.Coherent.CoherentNamed.mul adjugate
            bReciprocal)).name
        (Name.Coherent.CoherentNamed.mul
          (Name.Coherent.CoherentNamed.mul a adjugate)
          bReciprocal).name := by
      exact Equivalence.NamedEquivalent.symm (by
        simpa only [bReciprocal,
          Name.Coherent.CoherentNamed.mul] using
          Name.Coherent.Arithmetic.Product.Laws.coherentMul_assoc
            a adjugate bReciprocal)
    have swapTail : Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent bReciprocal.name reciprocalB.name := by
      simpa only [bReciprocal, reciprocalB,
        Name.Coherent.CoherentNamed.mul] using
        Name.Coherent.Arithmetic.Product.Laws.coherentMul_comm b reciprocal
    have replaceTail : Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
        (Name.Coherent.CoherentNamed.mul
          (Name.Coherent.CoherentNamed.mul a adjugate)
          bReciprocal).name
        (Name.Coherent.CoherentNamed.mul
          (Name.Coherent.CoherentNamed.mul a adjugate)
          reciprocalB).name :=
      Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects
        (Name.Coherent.CoherentNamed.mul a adjugate)
        (Name.Coherent.CoherentNamed.mul a adjugate)
        bReciprocal reciprocalB
        (Equivalence.NamedEquivalent.refl _) swapTail
    exact Equivalence.NamedEquivalent.trans exposeInner
      (Equivalence.NamedEquivalent.trans exposeAAdjugate
        replaceTail)
  have replaceAdjugate : Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
      (Name.Coherent.CoherentNamed.mul
        (Name.Coherent.CoherentNamed.mul a adjugate)
        (Name.Coherent.CoherentNamed.mul reciprocal b)).name
      (Name.Coherent.CoherentNamed.mul scalar
        (Name.Coherent.CoherentNamed.mul reciprocal b)).name :=
    Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects
      (Name.Coherent.CoherentNamed.mul a adjugate) scalar
      (Name.Coherent.CoherentNamed.mul reciprocal b)
      (Name.Coherent.CoherentNamed.mul reciprocal b)
      aAdjugate (Equivalence.NamedEquivalent.refl _)
  have cancelScalar : Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
      (Name.Coherent.CoherentNamed.mul scalar
        (Name.Coherent.CoherentNamed.mul reciprocal b)).name
      b.name := by
    apply Equivalence.NamedEquivalent.trans
    · exact Equivalence.NamedEquivalent.symm
        (Name.Coherent.Arithmetic.Product.Laws.coherentMul_assoc scalar reciprocal b)
    · let scalarReciprocal :=
        Name.Coherent.CoherentNamed.mul scalar reciprocal
      have scalarReciprocalOne : Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent scalarReciprocal.name
          (Name.Coherent.CoherentNamed.Coherence.exact 1).name :=
        Equivalence.NamedEquivalent.trans
          (show Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent scalarReciprocal.name
              (Name.Coherent.CoherentNamed.mul reciprocal scalar).name from
            by
                simpa only [scalarReciprocal, Name.Coherent.CoherentNamed.mul]
                  using Name.Coherent.Arithmetic.Product.Laws.coherentMul_comm scalar reciprocal)
          (by
            have cancel :=
              Division.Cancellation.reciprocal_mul_cancel
                scalar inverse.scalarApart
            simpa only [reciprocal, scalar,
              PeriodMatrix.inverseScalar,
              Name.Coherent.CoherentNamed.mul] using cancel)
      change Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
        (Name.Coherent.CoherentNamed.mul scalarReciprocal b).name
        b.name
      exact Equivalence.NamedEquivalent.trans
        (Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects scalarReciprocal
          (Name.Coherent.CoherentNamed.Coherence.exact 1) b b
          scalarReciprocalOne
          (Equivalence.NamedEquivalent.refl b.name))
        (Arithmetic.Mul.coherentMul_one_left b)
  change Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
    (Name.Coherent.CoherentNamed.mul a
      (Name.Coherent.CoherentNamed.mul numerator reciprocal)).name
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
    {frame : Curves.Legendre.Paths.Frame parameter}
    (data : NormalizedFibreData frame) :
    Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
      (Name.Coherent.CoherentNamed.mul data.aPeriod data.ratio).name
      data.bPeriod.name :=
  normalized_a_mul_ratio data.normalized

/-! The direct finite lower certificate prepares a cancellable synchronized
view of the raw `A` period. -/

/-- The coherent approximation obtained by sampling the original A-period name. -/
def sampledAPeriod {parameter : Gaussian}
    {frame : Curves.Legendre.Paths.Frame parameter}
    (data : NormalizedFibreData frame) : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed :=
  Name.Coherent.CoherentNamed.ofApproximation
    (Name.Sampling.approximation data.aPeriod.name)

/-- The retained A-period lower bound controls every possible value of its sampled process. -/
def sampledAPossibleApart {parameter : Gaussian}
    {frame : Curves.Legendre.Paths.Frame parameter}
    (data : NormalizedFibreData frame) :
    Process.Apart.Possible.PossibleApart data.sampledAPeriod.name.process where
  lowerSq := data.aPeriodLower.lowerSq
  positive := data.aPeriodLower.positive
  lower := by
    intro state value possible
    change (Name.Sampling.approximation data.aPeriod.name).Possible
      state value at possible
    rcases possible with ⟨later, _order, rfl⟩
    exact data.aPeriodLower.sample_lower later

/-- Prepare the sampled A-period with its retained possible-value apartness certificate. -/
def preparedAPeriod {parameter : Gaussian}
    {frame : Curves.Legendre.Paths.Frame parameter}
    (data : NormalizedFibreData frame) : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed :=
  Name.Coherent.CoherentNamed.apartify data.sampledAPeriod
    data.sampledAPossibleApart

/-- Read the executable apartness certificate of the prepared A-period. -/
def preparedAPeriodApart {parameter : Gaussian}
    {frame : Curves.Legendre.Paths.Frame parameter}
    (data : NormalizedFibreData frame) : Apart data.preparedAPeriod.name where
  certificate := Process.Apart.Preparation.apartifyApart data.sampledAPossibleApart

/-- The original A-period is equivalent to its sampled and apartness-prepared name. -/
def aPeriod_equivalent_prepared {parameter : Gaussian}
    {frame : Curves.Legendre.Paths.Frame parameter}
    (data : NormalizedFibreData frame) :
    Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent data.aPeriod.name data.preparedAPeriod.name :=
  Equivalence.NamedEquivalent.trans
    (Sequence.Name.Equivalence.named_toSamplingNamed data.aPeriod.name)
    (Name.Coherent.CoherentNamed.apartifyEquivalent
      data.sampledAPeriod data.sampledAPossibleApart)

end

open Purelib in
open Purelib.Riemann.Periods in
/-- Read normalized Legendre fibre data from a period result with a supplied A-entry lower bound.

The bound is transported along the result's exact cached-normalization readback, preserving its original matrix and
period owners. -/
def ofPeriodResult {parameter : Gaussian}
    {frame : Curves.Legendre.Paths.Frame parameter}
    (result : PeriodTheorem.Result
      (Curves.Legendre.Periods.Fibre.frameCurve frame))
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
def scaleVector (scalar : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed) (values : RawPeriodVector) :
    RawPeriodVector := fun coordinate =>
  Name.Coherent.CoherentNamed.mul scalar (values coordinate)

open Purelib.Approximation.Gaussian in
open Purelib.Riemann.Periods in
/-- A finite named sum of scaled entries is equivalent to scaling the original sum.

The constructive recursion keeps the original ordered entries and compares the geometric empty sum with exact zero
before distributing each scalar term. -/
def sumNamed_scale_left : {count : Nat} ->
    (scalar : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed) -> (values : Fin count ->
      Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed) ->
      Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
        (PeriodMatrix.sumNamed fun coordinate =>
          Name.Coherent.CoherentNamed.mul scalar
            (values coordinate)).name
        (Name.Coherent.CoherentNamed.mul scalar
          (PeriodMatrix.sumNamed values)).name
  | 0, scalar, values => by
      let geometricZero := PeriodMatrix.geometricNamed
        (Geometric.GeometricApproximation.exact 0)
      let exactZero := Name.Coherent.CoherentNamed.Coherence.exact 0
      have rightZero : Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
          (Name.Coherent.CoherentNamed.mul scalar geometricZero).name
          exactZero.name :=
        Equivalence.NamedEquivalent.trans
          (Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects scalar scalar
            geometricZero exactZero
            (Equivalence.NamedEquivalent.refl scalar.name)
            Geometric.Coherent.Comparison.geometricZero_equivalent_exact)
          (Arithmetic.Mul.coherentMul_zero_right scalar)
      change Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent geometricZero.name
        (Name.Coherent.CoherentNamed.mul scalar geometricZero).name
      exact Equivalence.NamedEquivalent.trans
        Geometric.Coherent.Comparison.geometricZero_equivalent_exact
        (Equivalence.NamedEquivalent.symm rightZero)
  | count + 1, scalar, values => by
      let tail := fun coordinate : Fin count => values coordinate.succ
      let tailSum := PeriodMatrix.sumNamed tail
      let scaledTail := fun coordinate : Fin count =>
        Name.Coherent.CoherentNamed.mul scalar (tail coordinate)
      have tailEquivalent := sumNamed_scale_left scalar tail
      have replaceTail : Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
          (Name.Coherent.CoherentNamed.add
            (Name.Coherent.CoherentNamed.mul scalar (values 0))
            (PeriodMatrix.sumNamed scaledTail)).name
          (Name.Coherent.CoherentNamed.add
            (Name.Coherent.CoherentNamed.mul scalar (values 0))
            (Name.Coherent.CoherentNamed.mul scalar tailSum)).name :=
        Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects
          (Name.Coherent.CoherentNamed.mul scalar (values 0))
          (Name.Coherent.CoherentNamed.mul scalar (values 0))
          (PeriodMatrix.sumNamed scaledTail)
          (Name.Coherent.CoherentNamed.mul scalar tailSum)
          (Equivalence.NamedEquivalent.refl _) tailEquivalent
      change Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
        (Name.Coherent.CoherentNamed.add
          (Name.Coherent.CoherentNamed.mul scalar (values 0))
          (PeriodMatrix.sumNamed scaledTail)).name
        (Name.Coherent.CoherentNamed.mul scalar
          (Name.Coherent.CoherentNamed.add
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
def matrixAction_scale (matrix : IntegralMatrix) (scalar : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed)
    (values : RawPeriodVector) :
    VectorEquivalent (Approximation.Matrix.Operational.Integral.Action.matrixAction matrix (scaleVector scalar values))
      (scaleVector scalar (Approximation.Matrix.Operational.Integral.Action.matrixAction matrix values)) := by
  intro row
  let terms := fun column : Fin 2 =>
    Name.Coherent.CoherentNamed.mul
      (Approximation.Matrix.Operational.Integral.Basic.integralNamedMatrix matrix row column) (values column)
  have moveScalar : Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
      (PeriodMatrix.sumNamed fun column : Fin 2 =>
        Name.Coherent.CoherentNamed.mul
          (Approximation.Matrix.Operational.Integral.Basic.integralNamedMatrix matrix row column)
          (Name.Coherent.CoherentNamed.mul scalar
            (values column))).name
      (PeriodMatrix.sumNamed fun column : Fin 2 =>
        Name.Coherent.CoherentNamed.mul scalar
          (terms column)).name :=
    PeriodMatrix.sumNamed_respects _ _ fun column =>
      Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws.coherentMul_left_comm
        (Approximation.Matrix.Operational.Integral.Basic.integralNamedMatrix matrix row
        column)
        scalar (values column)
  change Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
    (Approximation.Matrix.Operational.Integral.Action.matrixAction matrix (scaleVector scalar values) row).name
    (Name.Coherent.CoherentNamed.mul scalar
      (Approximation.Matrix.Operational.Integral.Action.matrixAction matrix values row)).name
  rw [Approximation.Matrix.Operational.Integral.Action.matrixAction, PeriodMatrix.matrixMul_apply]
  change Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
    (PeriodMatrix.sumNamed fun column : Fin 2 =>
      Name.Coherent.CoherentNamed.mul
        (Approximation.Matrix.Operational.Integral.Basic.integralNamedMatrix matrix row column)
        (Name.Coherent.CoherentNamed.mul scalar
          (values column))).name
    (Name.Coherent.CoherentNamed.mul scalar
      (Approximation.Matrix.Operational.Integral.Action.matrixAction matrix values row)).name
  rw [Approximation.Matrix.Operational.Integral.Action.matrixAction, PeriodMatrix.matrixMul_apply]
  exact Equivalence.NamedEquivalent.trans moveScalar
    (sumNamed_scale_left scalar terms)

open Purelib.Approximation.Gaussian in
/-- The coherent two-entry vector consisting of exact one followed by the retained ratio. -/
def fractionalVector (tau : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed) : RawPeriodVector :=
  fun coordinate => if coordinate = 0 then
    Name.Coherent.CoherentNamed.Coherence.exact 1
  else tau

open Purelib in
open Purelib.Approximation.Gaussian in
open Purelib.Data in
/-- The original fibre period vector equals A-period times its normalized ratio vector up to named equivalence. -/
def NormalizedFibreData.raw_normalized {parameter : Gaussian}
    {frame : Curves.Legendre.Paths.Frame parameter}
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
@[simp] theorem fractionalVector_zero (tau : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed) :
    fractionalVector tau 0 =
      Name.Coherent.CoherentNamed.Coherence.exact 1 := rfl

/-- The second fractional-vector entry is the original ratio. -/
@[simp] theorem fractionalVector_one (tau : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed) :
    fractionalVector tau 1 = tau := by
  unfold fractionalVector
  rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]

open Purelib in
/-- Read one row of the integral matrix action on the retained fractional vector. -/
def fractionalRow (matrix : IntegralMatrix) (tau : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed)
    (row : Fin 2) : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed :=
  Approximation.Matrix.Operational.Integral.Action.matrixAction matrix (fractionalVector tau) row

/-- Read the first transformed fractional-vector row as the denominator. -/
def fractionalDenominator (matrix : IntegralMatrix) (tau : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed) :
    Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed := fractionalRow matrix tau 0

/-- Read the second transformed fractional-vector row as the numerator. -/
def fractionalNumerator (matrix : IntegralMatrix) (tau : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed) :
    Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed := fractionalRow matrix tau 1

open Purelib in
open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
open Purelib.Riemann.Periods in
/-- Expand an integral matrix row into its two exact-cast coefficient products up to named equivalence.

The original ordered sum and coefficient entries are preserved, with geometric coefficient names compared to the exact
integer casts. -/
def matrixAction_row_two (matrix : IntegralMatrix) (values : RawPeriodVector)
    (row : Fin 2) :
    Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
      (Approximation.Matrix.Operational.Integral.Action.matrixAction matrix values row).name
      (Name.Coherent.CoherentNamed.add
        (Name.Coherent.CoherentNamed.mul
          (Name.Coherent.CoherentNamed.Coherence.exact
            (Cast.integralGaussian (matrix row 0))) (values 0))
        (Name.Coherent.CoherentNamed.mul
          (Name.Coherent.CoherentNamed.Coherence.exact
            (Cast.integralGaussian (matrix row 1))) (values 1))).name := by
  let terms := fun column : Fin 2 =>
    Name.Coherent.CoherentNamed.mul
      (Approximation.Matrix.Operational.Integral.Basic.integralNamedMatrix matrix row column) (values column)
  have exposeSum : Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
      (PeriodMatrix.sumNamed terms).name
      (Name.Coherent.CoherentNamed.add
        (terms 0) (terms 1)).name := sumNamed_two terms
  have coefficientEquivalent : forall column : Fin 2,
      Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
        (Approximation.Matrix.Operational.Integral.Basic.integralNamedMatrix matrix row column).name
        (Name.Coherent.CoherentNamed.Coherence.exact
          (Cast.integralGaussian (matrix row column))).name := by
    intro column
    rw [Approximation.Matrix.Operational.Integral.Basic.integralNamedMatrix_apply]
    exact Geometric.Coherent.Comparison.geometricExact_equivalent_exact _
  have replaceTerms : Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
      (Name.Coherent.CoherentNamed.add
        (terms 0) (terms 1)).name
      (Name.Coherent.CoherentNamed.add
        (Name.Coherent.CoherentNamed.mul
          (Name.Coherent.CoherentNamed.Coherence.exact
            (Cast.integralGaussian (matrix row 0))) (values 0))
        (Name.Coherent.CoherentNamed.mul
          (Name.Coherent.CoherentNamed.Coherence.exact
            (Cast.integralGaussian (matrix row 1))) (values 1))).name :=
    Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects
      (terms 0)
      (Name.Coherent.CoherentNamed.mul
        (Name.Coherent.CoherentNamed.Coherence.exact
          (Cast.integralGaussian (matrix row 0))) (values 0))
      (terms 1)
      (Name.Coherent.CoherentNamed.mul
        (Name.Coherent.CoherentNamed.Coherence.exact
          (Cast.integralGaussian (matrix row 1))) (values 1))
      (Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects
        (Approximation.Matrix.Operational.Integral.Basic.integralNamedMatrix matrix row 0)
        (Name.Coherent.CoherentNamed.Coherence.exact
          (Cast.integralGaussian (matrix row 0)))
        (values 0) (values 0) (coefficientEquivalent 0)
        (Equivalence.NamedEquivalent.refl (values 0).name))
      (Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects
        (Approximation.Matrix.Operational.Integral.Basic.integralNamedMatrix matrix row 1)
        (Name.Coherent.CoherentNamed.Coherence.exact
          (Cast.integralGaussian (matrix row 1)))
        (values 1) (values 1) (coefficientEquivalent 1)
        (Equivalence.NamedEquivalent.refl (values 1).name))
  rw [Approximation.Matrix.Operational.Integral.Action.matrixAction, PeriodMatrix.matrixMul_apply]
  change Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
    (PeriodMatrix.sumNamed terms).name _
  exact Equivalence.NamedEquivalent.trans exposeSum replaceTerms

section
open Purelib
open Purelib.Approximation.Gaussian
/-- The standard loop around one has fractional denominator equivalent to exact one. -/
def one_denominator_one (tau : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed) :
    Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
      (fractionalDenominator Curves.Legendre.Monodromy.oneMatrix tau).name
      (Name.Coherent.CoherentNamed.Coherence.exact 1).name := by
  let one := Name.Coherent.CoherentNamed.Coherence.exact 1
  let zero := Name.Coherent.CoherentNamed.Coherence.exact 0
  have expanded := matrixAction_row_two
    Curves.Legendre.Monodromy.oneMatrix (fractionalVector tau) 0
  change Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
    (fractionalDenominator Curves.Legendre.Monodromy.oneMatrix tau).name
    (Name.Coherent.CoherentNamed.add
      (Name.Coherent.CoherentNamed.mul one one)
      (Name.Coherent.CoherentNamed.mul zero tau)).name at expanded
  have simplifyTerms : Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
      (Name.Coherent.CoherentNamed.add
        (Name.Coherent.CoherentNamed.mul one one)
        (Name.Coherent.CoherentNamed.mul zero tau)).name
      (Name.Coherent.CoherentNamed.add one zero).name :=
    Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects
      (Name.Coherent.CoherentNamed.mul one one) one
      (Name.Coherent.CoherentNamed.mul zero tau) zero
      (Arithmetic.Mul.coherentMul_one_right one)
      (Arithmetic.Mul.coherentMul_zero_left tau)
  exact Equivalence.NamedEquivalent.trans expanded
    (Equivalence.NamedEquivalent.trans simplifyTerms
      (Arithmetic.Add.coherentAdd_zero_right one))

/-- The standard loop around one has numerator equivalent to two plus the retained ratio. -/
def one_numerator_two_add (tau : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed) :
    Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
      (fractionalNumerator Curves.Legendre.Monodromy.oneMatrix tau).name
      (Name.Coherent.CoherentNamed.add
        (Name.Coherent.CoherentNamed.Coherence.exact 2) tau).name := by
  let one := Name.Coherent.CoherentNamed.Coherence.exact 1
  let two := Name.Coherent.CoherentNamed.Coherence.exact 2
  have expanded := matrixAction_row_two
    Curves.Legendre.Monodromy.oneMatrix (fractionalVector tau) 1
  change Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
    (fractionalNumerator Curves.Legendre.Monodromy.oneMatrix tau).name
    (Name.Coherent.CoherentNamed.add
      (Name.Coherent.CoherentNamed.mul two one)
      (Name.Coherent.CoherentNamed.mul one tau)).name at expanded
  exact Equivalence.NamedEquivalent.trans expanded
    (Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects
      (Name.Coherent.CoherentNamed.mul two one) two
      (Name.Coherent.CoherentNamed.mul one tau) tau
      (Arithmetic.Mul.coherentMul_one_right two)
      (Arithmetic.Mul.coherentMul_one_left tau))

end

open Purelib.Approximation.Gaussian in
/-- Add exact two to the retained coherent period ratio. -/
def oneAffineTransform (tau : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed) :
  Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed :=
  Name.Coherent.CoherentNamed.add
    (Name.Coherent.CoherentNamed.Coherence.exact 2) tau

section
open Purelib.Approximation.Gaussian
/-- Apply an integral fractional transformation using the supplied prepared denominator.

The numerator is multiplied by the reciprocal of that exact prepared name and its retained apartness witness;
denominator preparation remains explicit input. -/
def fractionalLinear (matrix : IntegralMatrix) (tau : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed)
    (preparation : Division.Prepared.DenominatorPreparation
      (fractionalDenominator matrix tau)) : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed :=
  Name.Coherent.CoherentNamed.mul
    (fractionalNumerator matrix tau)
    (Name.Coherent.CoherentNamed.div
      (Name.Coherent.CoherentNamed.Coherence.exact 1)
      preparation.prepared preparation.apart)

/-- The prepared denominator times its fractional transformation is equivalent to the original numerator.

Cancellation uses the same denominator preparation and apartness witness that constructed the reciprocal, preserving its
actual executable name. -/
def prepared_denominator_mul_fractionalLinear
    (matrix : IntegralMatrix) (tau : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed)
    (preparation : Division.Prepared.DenominatorPreparation
      (fractionalDenominator matrix tau)) :
    Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
      (Name.Coherent.CoherentNamed.mul
        preparation.prepared
        (fractionalLinear matrix tau preparation)).name
      (fractionalNumerator matrix tau).name := by
  let denominator := preparation.prepared
  let numerator := fractionalNumerator matrix tau
  let reciprocal := Name.Coherent.CoherentNamed.div
    (Name.Coherent.CoherentNamed.Coherence.exact 1) denominator
      preparation.apart
  let reciprocalDenominator :=
    Name.Coherent.CoherentNamed.mul reciprocal denominator
  let one := Name.Coherent.CoherentNamed.Coherence.exact 1
  have rearrange : Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
      (Name.Coherent.CoherentNamed.mul denominator
        (Name.Coherent.CoherentNamed.mul numerator reciprocal)).name
      (Name.Coherent.CoherentNamed.mul numerator
        reciprocalDenominator).name := by
    let numeratorReciprocal :=
      Name.Coherent.CoherentNamed.mul numerator reciprocal
    apply Equivalence.NamedEquivalent.trans
    · simpa only [numeratorReciprocal,
        Name.Coherent.CoherentNamed.mul] using
        Name.Coherent.Arithmetic.Product.Laws.coherentMul_comm
          denominator numeratorReciprocal
    · simpa only [numeratorReciprocal, reciprocalDenominator,
        Name.Coherent.CoherentNamed.mul] using
        Name.Coherent.Arithmetic.Product.Laws.coherentMul_assoc
          numerator reciprocal denominator
  have cancel : Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent reciprocalDenominator.name
      one.name := by
    simpa only [reciprocalDenominator, reciprocal, one,
      Name.Coherent.CoherentNamed.mul] using
      Division.Cancellation.reciprocal_mul_cancel denominator
        preparation.apart
  change Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
    (Name.Coherent.CoherentNamed.mul denominator
      (Name.Coherent.CoherentNamed.mul numerator reciprocal)).name
    numerator.name
  exact Equivalence.NamedEquivalent.trans rearrange
    (Equivalence.NamedEquivalent.trans
      (Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects numerator numerator
        reciprocalDenominator one
        (Equivalence.NamedEquivalent.refl numerator.name) cancel)
      (Arithmetic.Mul.coherentMul_one_right numerator))

/-- The original denominator times the prepared fractional transformation is equivalent to the numerator. -/
def denominator_mul_fractionalLinear
    (matrix : IntegralMatrix) (tau : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed)
    (preparation : Division.Prepared.DenominatorPreparation
      (fractionalDenominator matrix tau)) :
    Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
      (Name.Coherent.CoherentNamed.mul
        (fractionalDenominator matrix tau)
        (fractionalLinear matrix tau preparation)).name
      (fractionalNumerator matrix tau).name :=
  Equivalence.NamedEquivalent.trans
    (Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects
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
def standardZeroDenominator (tau : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed) :
  Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed :=
  fractionalDenominator Curves.Legendre.Monodromy.zeroMatrix
    tau

/-- The fractional denominator for the standard loop around one. -/
def standardOneDenominator (tau : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed) :
  Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed :=
  fractionalDenominator Curves.Legendre.Monodromy.oneMatrix
    tau

/-- The fractional denominator for the standard loop around infinity. -/
def standardInfinityDenominator (tau : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed) :
  Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed :=
  fractionalDenominator Curves.Legendre.Monodromy.infinityMatrix
    tau

end

section
open Purelib.Approximation.Gaussian
/-- A retained executable denominator preparation for the standard loop around zero. -/
def StandardZeroPreparation (tau : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed) : Type 1 :=
  Division.Prepared.DenominatorPreparation (standardZeroDenominator tau)

/-- A retained executable denominator preparation for the standard loop around one. -/
def StandardOnePreparation (tau : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed) : Type 1 :=
  Division.Prepared.DenominatorPreparation (standardOneDenominator tau)

/-- A retained executable denominator preparation for the standard loop around infinity. -/
def StandardInfinityPreparation (tau : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed) : Type 1 :=
  Division.Prepared.DenominatorPreparation (standardInfinityDenominator tau)

end

section
open Purelib
open Purelib.Approximation.Gaussian
/-- Apply the standard zero-loop fractional transformation using its retained denominator preparation. -/
def zeroTransform {tau : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed}
    (preparation : StandardZeroPreparation tau) : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed := by
  change Division.Prepared.DenominatorPreparation
    (fractionalDenominator Curves.Legendre.Monodromy.zeroMatrix tau)
      at preparation
  exact fractionalLinear Curves.Legendre.Monodromy.zeroMatrix
    tau preparation

/-- Apply the standard one-loop fractional transformation using its retained denominator preparation. -/
def oneTransform {tau : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed}
    (preparation : StandardOnePreparation tau) : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed := by
  change Division.Prepared.DenominatorPreparation
    (fractionalDenominator Curves.Legendre.Monodromy.oneMatrix tau)
      at preparation
  exact fractionalLinear Curves.Legendre.Monodromy.oneMatrix
    tau preparation

/-- The prepared one-loop transformation is equivalent to adding two to the original ratio.

The result transports the retained denominator to exact one, cancels its prepared reciprocal, and retains the original
numerator equivalence. -/
def oneTransform_equivalent_affine {tau : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed}
    (preparation : StandardOnePreparation tau) :
    Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent (oneTransform preparation).name
      (oneAffineTransform tau).name := by
  change Division.Prepared.DenominatorPreparation
    (fractionalDenominator Curves.Legendre.Monodromy.oneMatrix tau)
      at preparation
  let one := Name.Coherent.CoherentNamed.Coherence.exact 1
  let transformed := fractionalLinear
    Curves.Legendre.Monodromy.oneMatrix tau preparation
  let numerator := fractionalNumerator
    Curves.Legendre.Monodromy.oneMatrix tau
  have onePrepared : Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent one.name preparation.prepared.name :=
    Equivalence.NamedEquivalent.trans
      (Equivalence.NamedEquivalent.symm
        (one_denominator_one tau)) preparation.equivalent
  have scaled : Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
      (Name.Coherent.CoherentNamed.mul one transformed).name
      numerator.name :=
    Equivalence.NamedEquivalent.trans
      (Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects
        one preparation.prepared transformed transformed onePrepared
        (Equivalence.NamedEquivalent.refl transformed.name))
      (by
          simpa only [transformed, numerator, Name.Coherent.CoherentNamed.mul]
            using (prepared_denominator_mul_fractionalLinear Curves.Legendre.Monodromy.oneMatrix tau preparation))
  change Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent transformed.name (oneAffineTransform tau).name
  exact Equivalence.NamedEquivalent.trans
    (Equivalence.NamedEquivalent.symm
      (Arithmetic.Mul.coherentMul_one_left transformed))
    (Equivalence.NamedEquivalent.trans scaled
      (by
          simpa only [numerator, oneAffineTransform]
            using one_numerator_two_add tau))

/-- Apply the standard infinity-loop fractional transformation using its retained denominator preparation. -/
def infinityTransform {tau : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed}
    (preparation : StandardInfinityPreparation tau) : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed := by
  change Division.Prepared.DenominatorPreparation
    (fractionalDenominator Curves.Legendre.Monodromy.infinityMatrix tau)
      at preparation
  exact fractionalLinear Curves.Legendre.Monodromy.infinityMatrix
    tau preparation

end

open Purelib
/-- The infinity monodromy matrix is a two-sided inverse of the ordered one-times-zero product. -/
theorem infinity_inverse_combined :
    LinearAlgebra.Matrix.Multiplication.mul
        Curves.Legendre.Monodromy.infinityMatrix
        (LinearAlgebra.Matrix.Multiplication.mul
          Curves.Legendre.Monodromy.oneMatrix
          Curves.Legendre.Monodromy.zeroMatrix) =
      LinearAlgebra.Matrix.Multiplication.identity ∧
    LinearAlgebra.Matrix.Multiplication.mul
        (LinearAlgebra.Matrix.Multiplication.mul
          Curves.Legendre.Monodromy.oneMatrix
          Curves.Legendre.Monodromy.zeroMatrix)
        Curves.Legendre.Monodromy.infinityMatrix =
      LinearAlgebra.Matrix.Multiplication.identity :=
  ⟨Curves.Legendre.Monodromy.explicit_loop_product_left,
    Curves.Legendre.Monodromy.explicit_loop_product_right⟩

/-- The retained infinity and combined paths have mutually inverse integral word matrices. -/
theorem reversal_path_matrices {parameter : Gaussian}
    {frame : Curves.Legendre.Paths.Frame parameter}
    (loops : Curves.Legendre.Monodromy.StandardLoops frame) :
    LinearAlgebra.Matrix.Multiplication.mul
        (Topology.Knot.Braid.ThreeStrand.Integral.Words.wordMatrix
          loops.infinityPath.word)
        (Topology.Knot.Braid.ThreeStrand.Integral.Words.wordMatrix
          loops.combinedPath.word) = LinearAlgebra.Matrix.Multiplication.identity ∧
    LinearAlgebra.Matrix.Multiplication.mul
        (Topology.Knot.Braid.ThreeStrand.Integral.Words.wordMatrix
          loops.combinedPath.word)
        (Topology.Knot.Braid.ThreeStrand.Integral.Words.wordMatrix
          loops.infinityPath.word) = LinearAlgebra.Matrix.Multiplication.identity :=
  Curves.Legendre.Monodromy.StandardLoops.reversePath_matrix_identities
    loops.combinedPath

end Purelib.Riemann.Integration.LegendreModularMonodromy
