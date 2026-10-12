module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Subtraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Gaussian.Arithmetic.Sampling
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Apart
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Apart.Preparation
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication.Bridge
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Product
import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Approximation.Gaussian.Table.Basic
public import Purelib.Approximation.Gaussian.Table.CCL.Request
import Purelib.Approximation.Gaussian.Table.Request
import Purelib.Approximation.Matrix
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.List.Flatten
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Vector.Basic
public import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Integration.Program.Gaussian.Sampling
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Multiplication

public import Purelib.LinearAlgebra.Gaussian.QuadraticForm
public import Purelib.LinearAlgebra.Matrix.Inverse.PivotedScaledInverse
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Process.Apart
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Algebra

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib

open Purelib.Geometry

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

public section

/-!
# Persistent finite period matrices

This file assembles the algebraically certified period programs into finite
`A` and `B` matrices of coherent CCL names.  It also gives a constructive
normalization interface: synchronized finite samples compute the canonical
division-free scaled inverse of `A`, and one explicit apartness witness for
its scalar constructs every entry of `A^{-1}B` by finite CCL arithmetic.
-/

namespace Purelib.Riemann.Periods.PeriodMatrix

open Purelib.LinearAlgebra.Gaussian.QuadraticForm

open Purelib.Riemann.Curves.AlgebraicDifferentials

/-- A productive Gaussian CCL name with its retained coherence certificate. -/
abbrev CoherentNamed := Gaussian.Name.Coherent.CoherentNamed
/-- A finite square matrix of coherent Gaussian names. -/
abbrev NamedMatrix (size : Nat) :=
  SquareMatrix CoherentNamed size
/-- Operational equivalence between the original finite requests of two Gaussian names. -/
abbrev NamedEquivalent := Gaussian.Equivalence.NamedEquivalent
/-- The exact rational coordinate type used by period bounds and requests. -/
abbrev Coordinate := Rat.Fraction.Rational
/-- A Gaussian rational sample of a period entry. -/
abbrev Gaussian := Gaussian.Basic.Canonical
/-- A synchronized Gaussian approximation with its retained geometric error bounds. -/
abbrev GeometricApproximation :=
  Gaussian.Geometric.GeometricApproximation
/-- A finite square matrix of synchronized geometric approximations. -/
abbrev GeometricMatrix (size : Nat) :=
  Matrix.GeometricMatrix size

/-- The standard zero-based differential basis `dx/y, x dx/y, ...`. -/
@[expose] def standardDifferential {genus : Nat} (index : Fin genus) :
    Hyperelliptic.Differentials.Basic.Differential genus :=
  ⟨index⟩

set_option genInjectivity false in
/-- All certified `a`- and `b`-period integration programs for one curve and
one common lifted symplectic cycle family. -/
structure PeriodData {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) where
  /-- The original paired lifted symplectic cycle refinements shared by both period matrices. -/ cycles :
    Path.Gaussian.Lifted.Family.PairedCycleRefinements 2 genus
  /-- The certified A-period integration program for each original differential and retained A-cycle. -/ aProgram :
    forall differential cycle : Fin genus,
    Hyperelliptic.Integration.Algebraic.Period.Basis.CertifiedPeriodProgram curve (standardDifferential differential)
      (cycles.aCycle cycle)
  /-- The certified B-period integration program for each original differential and retained B-cycle. -/ bProgram :
    forall differential cycle : Fin genus,
    Hyperelliptic.Integration.Algebraic.Period.Basis.CertifiedPeriodProgram curve (standardDifferential differential)
      (cycles.bCycle cycle)

constructive_injectivity PeriodData

namespace PeriodData

/-- Collect the original certified A-period program outputs in differential-by-cycle order. -/
@[expose] def aMatrix {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve) : NamedMatrix genus :=
  SquareMatrix.matrixOfFn fun differential cycle =>
    (data.aProgram differential cycle).output

/-- Collect the original certified B-period program outputs in differential-by-cycle order. -/
@[expose] def bMatrix {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve) : NamedMatrix genus :=
  SquareMatrix.matrixOfFn fun differential cycle =>
    (data.bProgram differential cycle).output

/-- The indexed A-matrix entry is exactly the corresponding retained integration program output. -/
@[simp] theorem aMatrix_apply {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (data : PeriodData curve)
    (differential cycle : Fin genus) :
    data.aMatrix differential cycle =
      (data.aProgram differential cycle).output := by
  exact SquareMatrix.matrixOfFn_apply _ _ _

/-- The indexed B-matrix entry is exactly the corresponding retained integration program output. -/
@[simp] theorem bMatrix_apply {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (data : PeriodData curve)
    (differential cycle : Fin genus) :
    data.bMatrix differential cycle =
      (data.bProgram differential cycle).output := by
  exact SquareMatrix.matrixOfFn_apply _ _ _

/-- Row-major materialization of any finite named matrix. -/
@[expose] def matrixChannels {genus : Nat} (matrix : NamedMatrix genus) :
    List CoherentNamed :=
  (List.ofFn fun row : Fin genus =>
    List.ofFn fun column : Fin genus => matrix row column).flatMap id

/-- Every indexed named matrix entry occurs in its retained row-major channel list. -/
theorem matrixEntry_mem_channels {genus : Nat} (matrix : NamedMatrix genus)
    (row column : Fin genus) :
    matrix row column ∈ matrixChannels matrix := by
  unfold matrixChannels
  apply Data.List.Flatten.mem_flatMap.mpr
  refine ⟨List.ofFn (fun column : Fin genus => matrix row column), ?_, ?_⟩
  · exact Data.List.OfFn.Basic.mem_ofFn.mpr ⟨row, rfl⟩
  · change matrix row column ∈
      List.ofFn (fun column : Fin genus => matrix row column)
    exact Data.List.OfFn.Basic.mem_ofFn.mpr ⟨column, rfl⟩

/-- One same-budget finite table containing both period matrices. -/
@[expose] def table {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve) : Gaussian.Table.Basic.ChannelTable :=
  ⟨matrixChannels data.aMatrix ++ matrixChannels data.bMatrix⟩

/-- Every retained A-period entry belongs to the original shared period table. -/
theorem aEntry_mem_table {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (differential cycle : Fin genus) :
    data.aMatrix differential cycle ∈ data.table.channels := by
  apply Data.List.Membership.mem_append.mpr
  exact Or.inl (matrixEntry_mem_channels data.aMatrix differential cycle)

/-- Every retained B-period entry belongs to the original shared period table. -/
theorem bEntry_mem_table {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (differential cycle : Fin genus) :
    data.bMatrix differential cycle ∈ data.table.channels := by
  apply Data.List.Membership.mem_append.mpr
  exact Or.inr (matrixEntry_mem_channels data.bMatrix differential cycle)

/-- Every `A` entry answers one common table request with its enclosure,
semantic allowance, persistent bits, and exact parser certificate. -/
theorem aEntry_sharedRequest {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (data : PeriodData curve)
    (differential cycle : Fin genus)
    (target : Rat.Fraction.Rational) (positive : 0 < target)
    (count : Nat) :
    Gaussian.Table.CCL.Request.RequestContract data.table.channels
      (data.aMatrix differential cycle) target positive count :=
  data.table.member_bitstream_and_allowance
    (data.aEntry_mem_table differential cycle) target positive count

/-- The corresponding same-budget contract for every `B` entry. -/
theorem bEntry_sharedRequest {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (data : PeriodData curve)
    (differential cycle : Fin genus)
    (target : Rat.Fraction.Rational) (positive : 0 < target)
    (count : Nat) :
    Gaussian.Table.CCL.Request.RequestContract data.table.channels
      (data.bMatrix differential cycle) target positive count :=
  data.table.member_bitstream_and_allowance
    (data.bEntry_mem_table differential cycle) target positive count

/-- Shared finite refinement of one unnormalized A-period entry. -/
@[expose] def refinedAEntry {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (target : Coordinate) (positive : 0 < target)
    (differential cycle : Fin genus) : Gaussian.Name.Basic.Named :=
  Gaussian.Table.Request.sharedName data.table.channels
    (data.aMatrix differential cycle) target positive

/-- Shared finite refinement of one unnormalized B-period entry. -/
@[expose] def refinedBEntry {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (target : Coordinate) (positive : 0 < target)
    (differential cycle : Fin genus) : Gaussian.Name.Basic.Named :=
  Gaussian.Table.Request.sharedName data.table.channels
    (data.bMatrix differential cycle) target positive

/-- Displayed rational centre of one unnormalized A-period entry. -/
@[expose] def aCenter {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (target : Coordinate) (positive : 0 < target)
    (differential cycle : Fin genus) : Gaussian :=
  let entry := data.refinedAEntry target positive differential cycle
  (entry.process.ball entry.state).center

/-- Displayed rational centre of one unnormalized B-period entry. -/
@[expose] def bCenter {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (target : Coordinate) (positive : 0 < target)
    (differential cycle : Fin genus) : Gaussian :=
  let entry := data.refinedBEntry target positive differential cycle
  (entry.process.ball entry.state).center

/-- Displayed squared enclosure radius of one unnormalized A-period entry. -/
@[expose] def aRadiusSq {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (target : Coordinate) (positive : 0 < target)
    (differential cycle : Fin genus) : Coordinate :=
  let entry := data.refinedAEntry target positive differential cycle
  (entry.process.ball entry.state).radiusSq

/-- Displayed squared enclosure radius of one unnormalized B-period entry. -/
@[expose] def bRadiusSq {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (target : Coordinate) (positive : 0 < target)
    (differential cycle : Fin genus) : Coordinate :=
  let entry := data.refinedBEntry target positive differential cycle
  (entry.process.ball entry.state).radiusSq

/-- The shared A-entry request returns a squared radius strictly below its positive rational target. -/
theorem aRadiusSq_lt_target {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (target : Coordinate) (positive : 0 < target)
    (differential cycle : Fin genus) :
    data.aRadiusSq target positive differential cycle < target := by
  unfold aRadiusSq refinedAEntry
  exact Gaussian.Table.Request.sharedName_radius_lt
    data.table.channels (data.aMatrix differential cycle) positive

/-- The shared B-entry request returns a squared radius strictly below its positive rational target. -/
theorem bRadiusSq_lt_target {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (target : Coordinate) (positive : 0 < target)
    (differential cycle : Fin genus) :
    data.bRadiusSq target positive differential cycle < target := by
  unfold bRadiusSq refinedBEntry
  exact Gaussian.Table.Request.sharedName_radius_lt
    data.table.channels (data.bMatrix differential cycle) positive

/-- One finite Gaussian-rational A-period centre matrix. -/
@[expose] def aCenterMatrix {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (target : Coordinate) (positive : 0 < target) :
    SquareMatrix Gaussian genus :=
  SquareMatrix.matrixOfFn fun differential cycle =>
    data.aCenter target positive differential cycle

/-- One finite Gaussian-rational B-period centre matrix. -/
@[expose] def bCenterMatrix {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (target : Coordinate) (positive : 0 < target) :
    SquareMatrix Gaussian genus :=
  SquareMatrix.matrixOfFn fun differential cycle =>
    data.bCenter target positive differential cycle

end PeriodData

/-- The productive coherent name generated directly by a synchronized finite
geometric approximation. -/
@[expose] def geometricNamed (source : GeometricApproximation) : CoherentNamed :=
  Gaussian.Name.Coherent.CoherentNamed.ofApproximation
    source.toApproximation

/-- Dropping any finite prefix of a geometric stream preserves its operational value.

A comparison against the shifted stream is obtained by
asking reflexivity of the original stream to start the right side at the
corresponding absolute index. -/
@[expose] def geometricDropEquivalent (source : GeometricApproximation)
    (anchor : Nat) :
    Gaussian.Equivalence.Equivalent source.toApproximation
      (source.drop anchor).toApproximation where
  compare := by
    intro leftStart rightStart target positive
    let comparison :=
      (Gaussian.Equivalence.Equivalent.refl source.toApproximation).compare
        leftStart (anchor + rightStart) target positive
    have anchorLeRight : anchor <= comparison.rightIndex := by
      exact (by omega0 : anchor <= anchor + rightStart).trans
        comparison.right_ge
    let shiftedRight := comparison.rightIndex - anchor
    have shiftedIdentity : anchor + shiftedRight = comparison.rightIndex := by
      dsimp only [shiftedRight]
      omega0
    exact
      { leftIndex := comparison.leftIndex
        rightIndex := shiftedRight
        left_ge := comparison.left_ge
        right_ge := by
          have retainedRight := comparison.right_ge
          dsimp only [shiftedRight]
          omega0
        close := by
          intro leftLater rightLater leftOrder rightOrder
          have absoluteRightOrder :
              comparison.rightIndex <= anchor + rightLater := by
            rw [<- shiftedIdentity]
            omega0
          simpa only [Gaussian.Geometric.GeometricApproximation.drop_sample,
            Gaussian.Geometric.GeometricApproximation.toApproximation_sample]
            using comparison.close leftOrder absoluteRightOrder }

/-- The coherent name generated by a finite tail is operationally equivalent
to the name generated by the original geometric stream. -/
@[expose] def geometricNamed_drop_equivalent (source : GeometricApproximation)
    (anchor : Nat) :
    NamedEquivalent (geometricNamed source).name
      (geometricNamed (source.drop anchor)).name := by
  simpa only [geometricNamed,
    Gaussian.Name.Coherent.CoherentNamed.ofApproximation] using
    Gaussian.Sequence.Name.Equivalence.approximationEquivalent_toNamed
      (geometricDropEquivalent source anchor)

/-- Uniform apartness of a nonzero synchronized constant approximation. -/
@[expose] def geometricExactApart (value : Gaussian) (nonzero : value ≠ 0) :
    Gaussian.Name.Basic.Named.Apart
      (geometricNamed
        (Gaussian.Geometric.GeometricApproximation.exact
          value)).name where
  certificate :=
    { lowerSq := Data.Gaussian.Norm.Basic.normSq value
      positive := Gaussian.Norm.Basic.normSq_pos nonzero
      lower := by
        intro state candidate inside
        change Data.Gaussian.Norm.Basic.normSq
          (candidate - value) <=
            Rational.Geometric.Basic.quarterRadius 0 state at inside
        rw [Rational.Geometric.Basic.quarterRadius_eq_mul_pow] at inside
        rw [zero_mul] at inside
        have normZero : Data.Gaussian.Norm.Basic.normSq
            (candidate - value) = 0 :=
          le_antisymm inside
            (Gaussian.Norm.Basic.normSq_nonneg _)
        have differenceZero :=
          Gaussian.Norm.Basic.normSq_eq_zero.mp normZero
        have equal : candidate = value := Gaussian.Basic.gaussian_eq_of_sub_eq_zero differenceZero
        rw [equal] }

/-- Whole-ball apartness in particular supplies the weaker genuine-candidate
apartness accepted by constructive apartification. -/
@[expose] def possibleApartOfNamedApart {name : Gaussian.Name.Basic.Named}
    (apart : Gaussian.Name.Basic.Named.Apart name) :
    Gaussian.Process.Apart.Possible.PossibleApart name.process where
  lowerSq := apart.certificate.lowerSq
  positive := apart.certificate.positive
  lower := by
    intro state value possible
    exact apart.certificate.lower state
      (name.process.possible_inside possible)

/-- Finite recursive addition of coherent names.  The empty sum uses the
same synchronized zero approximation as the matrix identities below. -/
@[expose] def sumNamed : {count : Nat} -> (Fin count -> CoherentNamed) -> CoherentNamed
  | 0, _ => geometricNamed
      (Gaussian.Geometric.GeometricApproximation.exact 0)
  | count + 1, values =>
      Gaussian.Name.Coherent.CoherentNamed.add (values 0)
        (sumNamed fun index : Fin count => values index.succ)

/-- Recursive actual CCL addition realizes the equal-index geometric sum
whenever each displayed summand realizes its synchronized approximation. -/
@[expose] def sumNamed_equivalent_geometricSum {count : Nat}
    (values : Fin count -> CoherentNamed)
    (sources : Fin count -> GeometricApproximation)
    (equivalent : forall entry,
      NamedEquivalent (values entry).name
        (geometricNamed (sources entry)).name) :
    NamedEquivalent (sumNamed values).name
      (geometricNamed
        (Gaussian.Geometric.GeometricApproximation.sum
          sources)).name := by
  induction count with
  | zero =>
      exact Gaussian.Equivalence.NamedEquivalent.refl _
  | succ count inductionHypothesis =>
      let tailValues := fun entry : Fin count => values entry.succ
      let tailSources := fun entry : Fin count => sources entry.succ
      let tailSum := sumNamed tailValues
      let geometricTail := geometricNamed
        (Gaussian.Geometric.GeometricApproximation.sum
          tailSources)
      have tailEquivalent : NamedEquivalent tailSum.name geometricTail.name :=
        inductionHypothesis tailValues tailSources
          (fun entry => equivalent entry.succ)
      have replaceOperands : NamedEquivalent
          (Gaussian.Name.Coherent.CoherentNamed.add
            (values 0) tailSum).name
          (Gaussian.Name.Coherent.CoherentNamed.add
            (geometricNamed (sources 0)) geometricTail).name :=
        Gaussian.Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects
          (values 0) (geometricNamed (sources 0)) tailSum geometricTail
          (equivalent 0) tailEquivalent
      apply Gaussian.Equivalence.NamedEquivalent.trans replaceOperands
      dsimp only [geometricTail, tailSources]
      simpa only [geometricNamed,
        Gaussian.Name.Coherent.CoherentNamed.add,
        Gaussian.Name.Coherent.CoherentNamed.ofApproximation,
        Gaussian.Geometric.GeometricApproximation.sum] using
        Gaussian.Arithmetic.Sampling.addToNamed_equivalent_pointwise
          (sources 0).toApproximation
          (Gaussian.Geometric.GeometricApproximation.sum
            tailSources).toApproximation
          (Gaussian.Geometric.GeometricApproximation.add
            (sources 0)
            (Gaussian.Geometric.GeometricApproximation.sum
              tailSources)).toApproximation
          (by intro index; rfl)

/-- Finite recursive sums respect operational equality term by term. -/
@[expose] def sumNamed_respects {count : Nat}
    (left right : Fin count -> CoherentNamed)
    (equivalent : forall entry,
      NamedEquivalent (left entry).name (right entry).name) :
    NamedEquivalent (sumNamed left).name (sumNamed right).name := by
  induction count with
  | zero => exact Gaussian.Equivalence.NamedEquivalent.refl _
  | succ count inductionHypothesis =>
      change NamedEquivalent
        (Gaussian.Name.Coherent.CoherentNamed.add (left 0)
          (sumNamed fun entry : Fin count => left entry.succ)).name
        (Gaussian.Name.Coherent.CoherentNamed.add (right 0)
          (sumNamed fun entry : Fin count => right entry.succ)).name
      exact Gaussian.Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects
        (left 0) (right 0)
        (sumNamed fun entry : Fin count => left entry.succ)
        (sumNamed fun entry : Fin count => right entry.succ)
        (equivalent 0)
        (inductionHypothesis
          (fun entry : Fin count => left entry.succ)
          (fun entry : Fin count => right entry.succ)
          (fun entry => equivalent entry.succ))

/-- A recursive rational bound for a finite Gaussian sum.  Its shape mirrors
`sumFin_succ`, using the explicit two-term squared-norm triangle bound at each
constructor. -/
@[expose] def sumBound : {count : Nat} -> (Fin count -> Coordinate) -> Coordinate
  | 0, _ => 0
  | count + 1, bounds =>
      2 * (bounds 0 + sumBound fun index : Fin count => bounds index.succ)

/-- The recursive finite-sum squared-norm bound is nonnegative when every summand bound is nonnegative. -/
theorem sumBound_nonneg {count : Nat} (bounds : Fin count -> Coordinate)
    (nonnegative : forall index, 0 <= bounds index) :
    0 <= sumBound bounds := by
  induction count with
  | zero => exact le_rfl
  | succ count inductionHypothesis =>
      change 0 <= 2 *
        (bounds 0 + sumBound (fun index : Fin count => bounds index.succ))
      exact Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (add_nonneg (nonnegative 0)
          (inductionHypothesis (fun index => bounds index.succ)
            (fun index => nonnegative index.succ)))

/-- The squared norm of a finite Gaussian sum is bounded by `sumBound` of
displayed per-entry squared-norm bounds. -/
theorem normSq_sumFin_le_sumBound {count : Nat}
    (values : Fin count -> Gaussian) (bounds : Fin count -> Coordinate)
    (bounded : forall index,
      Data.Gaussian.Norm.Basic.normSq (values index) <= bounds index) :
    Data.Gaussian.Norm.Basic.normSq
        (FiniteSum.Fin.sumFin values) <=
      sumBound bounds := by
  induction count with
  | zero =>
      change Data.Gaussian.Norm.Basic.normSq 0 <= 0
      rw [Gaussian.Norm.Basic.normSq_zero]
  | succ count inductionHypothesis =>
      rw [FiniteSum.Fin.sumFin_succ]
      change Data.Gaussian.Norm.Basic.normSq
          (values 0 + FiniteSum.Fin.sumFin
            (fun index : Fin count => values index.succ)) <=
        2 * (bounds 0 +
          sumBound (fun index : Fin count => bounds index.succ))
      exact
        (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
          (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (add_le_add (bounded 0)
              (inductionHypothesis
                (fun index : Fin count => values index.succ)
                (fun index : Fin count => bounds index.succ)
                (fun index => bounded index.succ))) (by decide))

/-- Recursive sum bounds commute with the shared quarter-power schedule. -/
theorem sumBound_quarterRadius {count : Nat}
    (scales : Fin count -> Coordinate) (index : Nat) :
    sumBound (fun entry =>
        Rational.Geometric.Basic.quarterRadius (scales entry) index) =
      Rational.Geometric.Basic.quarterRadius (sumBound scales) index := by
  induction count with
  | zero =>
      change (0 : Coordinate) = Rational.Geometric.Basic.quarterRadius 0 index
      rw [Rational.Geometric.Basic.quarterRadius_eq_mul_pow]
      ring1
  | succ count inductionHypothesis =>
      change 2 *
          (Rational.Geometric.Basic.quarterRadius (scales 0) index +
            sumBound (fun entry : Fin count =>
              Rational.Geometric.Basic.quarterRadius
                (scales entry.succ) index)) =
        Rational.Geometric.Basic.quarterRadius
          (2 * (scales 0 +
            sumBound (fun entry : Fin count => scales entry.succ))) index
      rw [inductionHypothesis (fun entry : Fin count => scales entry.succ),
        Rational.Geometric.Basic.quarterRadius_eq_mul_pow,
        Rational.Geometric.Basic.quarterRadius_eq_mul_pow,
        Rational.Geometric.Basic.quarterRadius_eq_mul_pow]
      ring1

/-- Error scale for one synchronized finite matrix-product entry. -/
@[expose] def matrixProductErrorScale {size : Nat} (left right : NamedMatrix size)
    (row column : Fin size) : Coordinate :=
  sumBound fun middle =>
    Gaussian.Sequence.Arithmetic.Product.sampledProductErrorScale
      (left row middle).name (right middle column).name

/-- The synchronized matrix-product entry error scale is nonnegative. -/
theorem matrixProductErrorScale_nonneg {size : Nat}
    (left right : NamedMatrix size) (row column : Fin size) :
    0 <= matrixProductErrorScale left right row column :=
  sumBound_nonneg _ fun middle =>
    Gaussian.Sequence.Arithmetic.Product.sampledProductErrorScale_nonneg
      (left row middle).name (right middle column).name

/-- Equal-index finite products, summed at one common index.  This diagnostic
sampler exposes synchronized readings of arbitrary named matrices; it never
silently combines entries taken from unrelated refinement levels. -/
@[expose] def matrixProductApproximation {size : Nat}
    (left right : NamedMatrix size) (row column : Fin size) :
    Gaussian.Sequence.ApproximationData where
  sample index :=
    FiniteSum.Fin.sumFin fun middle =>
      (Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation
        (left row middle).name (right middle column).name).sample index
  radiusSq := Rational.Geometric.Basic.quarterRadius
    (matrixProductErrorScale left right row column)
  radiusSq_nonneg := Rational.Geometric.Basic.quarterRadius_nonneg
    (matrixProductErrorScale_nonneg left right row column)
  later_close := by
    intro earlier later order
    let product := fun middle : Fin size =>
      Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation
        (left row middle).name (right middle column).name
    calc
      Data.Gaussian.Norm.Basic.normSq
          (FiniteSum.Fin.sumFin
              (fun middle => (product middle).sample later) -
            FiniteSum.Fin.sumFin
              (fun middle => (product middle).sample earlier)) =
        Data.Gaussian.Norm.Basic.normSq
          (FiniteSum.Fin.sumFin fun middle =>
            (product middle).sample later -
              (product middle).sample earlier) := by
          rw [FiniteSum.Fin.sumFin_sub]
      _ <= sumBound (fun middle =>
          Rational.Geometric.Basic.quarterRadius
            (Gaussian.Sequence.Arithmetic.Product.sampledProductErrorScale
              (left row middle).name (right middle column).name) earlier) :=
        normSq_sumFin_le_sumBound _ _ fun middle =>
          (product middle).later_close order
      _ = Rational.Geometric.Basic.quarterRadius
          (matrixProductErrorScale left right row column) earlier :=
        sumBound_quarterRadius _ earlier
  refineIndex current target _ :=
    Rational.Geometric.Search.firstQuarterBelow
      (matrixProductErrorScale left right row column) current target
  refineIndex_ge current target _ :=
    Rational.Geometric.Search.firstQuarterBelow_ge
      (matrixProductErrorScale left right row column) current target
  refineIndex_accurate := Rational.Geometric.Search.firstQuarterBelow_accurate
    (matrixProductErrorScale left right row column)
    (matrixProductErrorScale_nonneg left right row column)
  centerBound := sumBound fun middle =>
    (Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation
      (left row middle).name (right middle column).name).centerBound
  centerBound_nonneg := sumBound_nonneg _ fun middle =>
    (Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation
      (left row middle).name
      (right middle column).name).centerBound_nonneg
  sample_bounded := by
    intro index
    exact normSq_sumFin_le_sumBound _ _ fun middle =>
      (Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation
        (left row middle).name
        (right middle column).name).sample_bounded index

/-- A synchronized matrix-product sample is the finite sum of its original equal-index entry products. -/
@[simp] theorem matrixProductApproximation_sample {size : Nat}
    (left right : NamedMatrix size) (row column : Fin size) (index : Nat) :
    (matrixProductApproximation left right row column).sample index =
      FiniteSum.Fin.sumFin fun middle =>
        (Gaussian.Name.Sampling.approximation
          (left row middle).name).sample index *
        (Gaussian.Name.Sampling.approximation
          (right middle column).name).sample index := by
  unfold matrixProductApproximation
  apply FiniteSum.Fin.sumFin_congr
  intro middle
  exact Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation_sample
    (left row middle).name (right middle column).name index

/-- Finite named matrix multiplication as the actual CCL arithmetic
expression tree.  The synchronization theorem below relates this tree to one
equal-index geometric sum, so normalization never assumes that unrelated
refinement levels coincide. -/
@[expose] def matrixMul {size : Nat} (left right : NamedMatrix size) :
    NamedMatrix size :=
  SquareMatrix.matrixOfFn fun row column =>
    sumNamed fun middle =>
      Gaussian.Name.Coherent.CoherentNamed.mul
        (left row middle) (right middle column)

/-- Place the retained coherent scalar on the diagonal and the exact synchronized zero name elsewhere. -/
@[expose] def scaleIdentity {size : Nat} (scalar : CoherentNamed) :
    NamedMatrix size :=
  SquareMatrix.matrixOfFn fun row column =>
    if row = column then scalar
    else geometricNamed
      (Gaussian.Geometric.GeometricApproximation.exact 0)

/-- Read one entry of the original finite CCL matrix multiplication expression tree. -/
@[simp] theorem matrixMul_apply {size : Nat}
    (left right : NamedMatrix size) (row column : Fin size) :
    matrixMul left right row column =
      sumNamed fun middle =>
        Gaussian.Name.Coherent.CoherentNamed.mul
          (left row middle) (right middle column) := by
  exact SquareMatrix.matrixOfFn_apply _ _ _

/-- Read the diagonal scalar or exact off-diagonal zero of the retained named scaled identity. -/
@[simp] theorem scaleIdentity_apply {size : Nat} (scalar : CoherentNamed)
    (row column : Fin size) :
    scaleIdentity scalar row column =
      if row = column then scalar
      else geometricNamed
        (Gaussian.Geometric.GeometricApproximation.exact 0) := by
  exact SquareMatrix.matrixOfFn_apply _ _ _

/-- Entrywise operational equality of finite named matrices. -/
@[expose] def MatrixEquivalent {size : Nat}
    (left right : NamedMatrix size) : Type :=
  forall row column,
    NamedEquivalent (left row column).name (right row column).name

namespace MatrixEquivalent

/-- Construct entrywise operational reflexivity for the original named matrix. -/
@[expose] def refl {size : Nat} (matrix : NamedMatrix size) :
    MatrixEquivalent matrix matrix := fun row column =>
  Gaussian.Equivalence.NamedEquivalent.refl (matrix row column).name

/-- Reverse every retained entrywise operational equivalence. -/
@[expose] def symm {size : Nat} {left right : NamedMatrix size}
    (equivalent : MatrixEquivalent left right) : MatrixEquivalent right left :=
  fun row column =>
    Gaussian.Equivalence.NamedEquivalent.symm
      (equivalent row column)

/-- Compose the original entrywise operational equivalences through their common matrix. -/
@[expose] def trans {size : Nat} {first second third : NamedMatrix size}
    (firstSecond : MatrixEquivalent first second)
    (secondThird : MatrixEquivalent second third) :
    MatrixEquivalent first third := fun row column =>
  Gaussian.Equivalence.NamedEquivalent.trans
    (firstSecond row column) (secondThird row column)

end MatrixEquivalent

/-- Transpose a finite named matrix without changing any entry process. -/
@[expose] def transpose {size : Nat} (matrix : NamedMatrix size) : NamedMatrix size :=
  SquareMatrix.matrixOfFn fun row column => matrix column row

/-- Read the original entry at the reversed indices of a named matrix transpose. -/
@[simp] theorem transpose_apply {size : Nat} (matrix : NamedMatrix size)
    (row column : Fin size) :
    transpose matrix row column = matrix column row :=
  SquareMatrix.matrixOfFn_apply _ _ _

/-- Transposition preserves entrywise operational equality. -/
@[expose] def transpose_respects {size : Nat} {left right : NamedMatrix size}
    (equivalent : MatrixEquivalent left right) :
    MatrixEquivalent (transpose left) (transpose right) := by
  intro row column
  simpa only [transpose_apply] using equivalent column row

/-- Actual finite matrix multiplication respects entrywise operational
equality in both operands. -/
@[expose] def matrixMul_respects {size : Nat}
    (leftOne leftTwo rightOne rightTwo : NamedMatrix size)
    (leftEquivalent : MatrixEquivalent leftOne leftTwo)
    (rightEquivalent : MatrixEquivalent rightOne rightTwo) :
    MatrixEquivalent (matrixMul leftOne rightOne)
      (matrixMul leftTwo rightTwo) := by
  intro row column
  rw [matrixMul_apply, matrixMul_apply]
  apply sumNamed_respects
  intro middle
  exact Gaussian.Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects
    (leftOne row middle) (leftTwo row middle)
    (rightOne middle column) (rightTwo middle column)
    (leftEquivalent row middle) (rightEquivalent middle column)

/-- The synchronized Gaussian matrix displayed by a named matrix at one
finite sampler index. -/
@[expose] def sampledMatrix {size : Nat} (matrix : NamedMatrix size) (index : Nat) :
    SquareMatrix Gaussian size :=
  SquareMatrix.matrixOfFn fun row column =>
    (Gaussian.Name.Sampling.approximation
      (matrix row column).name).sample index

/-- Read the original named entry's finite sample at the shared matrix index. -/
@[simp] theorem sampledMatrix_apply {size : Nat}
    (matrix : NamedMatrix size) (index : Nat) (row column : Fin size) :
    sampledMatrix matrix index row column =
      (Gaussian.Name.Sampling.approximation
        (matrix row column).name).sample index :=
  SquareMatrix.matrixOfFn_apply _ _ _

/-- The witness-sampled `A` matrix entry and the refinement program's own
model sample at the same index are close, with a coefficient-independent
geometric allowance. -/
theorem sampledMatrix_aProgram_close {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (differential cycle : Fin genus) (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq
        (sampledMatrix data.aMatrix index differential cycle -
          ((data.aProgram differential cycle).integral.model index).integralSample) <=
      Rational.Geometric.Basic.quarterRadius
        (max (data.aProgram differential cycle).integral.errorScale 1) index := open Purelib.Integration in by
  rw [show sampledMatrix data.aMatrix index differential cycle =
      (data.aProgram differential cycle).integral.approximation.sample
        (Gaussian.Process.Sampling.stateAt
          (data.aProgram differential cycle).integral.approximation.toProcess (0 : Nat) index) from by
    rw [sampledMatrix_apply, PeriodData.aMatrix_apply]
    rfl]
  exact Program.Gaussian.Basic.RefinementProgram.witness_sample_close
    (data.aProgram differential cycle).integral index

/-- The witness-sampled `B` matrix entry and the refinement program's own
model sample at the same index are close. -/
theorem sampledMatrix_bProgram_close {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (differential cycle : Fin genus) (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq
        (sampledMatrix data.bMatrix index differential cycle -
          ((data.bProgram differential cycle).integral.model index).integralSample) <=
      Rational.Geometric.Basic.quarterRadius
        (max (data.bProgram differential cycle).integral.errorScale 1) index := open Purelib.Integration in by
  rw [show sampledMatrix data.bMatrix index differential cycle =
      (data.bProgram differential cycle).integral.approximation.sample
        (Gaussian.Process.Sampling.stateAt
          (data.bProgram differential cycle).integral.approximation.toProcess (0 : Nat) index) from by
    rw [sampledMatrix_apply, PeriodData.bMatrix_apply]
    rfl]
  exact Program.Gaussian.Basic.RefinementProgram.witness_sample_close
    (data.bProgram differential cycle).integral index

/-- Replace each named entry by its canonical nested finite sampler. -/
@[expose] def geometricMatrixOfNamed {size : Nat} (matrix : NamedMatrix size) :
    GeometricMatrix size :=
  SquareMatrix.matrixOfFn fun row column =>
    Gaussian.Geometric.GeometricApproximation.ofNamed
      (matrix row column).name

/-- Read the canonical nested geometric sampler of the original named matrix entry. -/
@[simp] theorem geometricMatrixOfNamed_apply {size : Nat}
    (matrix : NamedMatrix size) (row column : Fin size) :
    geometricMatrixOfNamed matrix row column =
      Gaussian.Geometric.GeometricApproximation.ofNamed
        (matrix row column).name :=
  SquareMatrix.matrixOfFn_apply _ _ _

/-- Sampling the canonical geometric matrix gives the original named matrix's synchronized sample matrix. -/
theorem sample_geometricMatrixOfNamed {size : Nat}
    (matrix : NamedMatrix size) (index : Nat) :
    Matrix.sampleMatrix
        (geometricMatrixOfNamed matrix) index =
      sampledMatrix matrix index := by
  apply SquareMatrix.matrix_ext
  intro row column
  rw [Matrix.sampleMatrix_apply,
    geometricMatrixOfNamed_apply, sampledMatrix_apply]
  rfl

/-- The canonical synchronized division-free inverse data of a named
matrix.  This is a total finite construction; its scalar may be zero. -/
@[expose] def canonicalScaledInverse {size : Nat} (matrix : NamedMatrix size) :
    Matrix.ScaledInverseApproximation size :=
  SquareMatrix.Inverse.PivotedScaledInverse.completeApproximation
    (geometricMatrixOfNamed matrix)

/-- At each synchronized sample, the squared norm of the canonical scalar
for a one-by-one matrix is exactly the fourth power of the squared norm of
its sole entry. -/
theorem normSq_canonicalScaledInverse_one_scalar_sample
    (matrix : NamedMatrix 1) (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq
        ((canonicalScaledInverse matrix).scalar.sample index) =
      Data.Gaussian.Norm.Basic.normSq
          ((Gaussian.Name.Sampling.approximation
            (matrix 0 0).name).sample index) ^ 4 := by
  rw [canonicalScaledInverse]
  rw [(SquareMatrix.Inverse.PivotedScaledInverse.completeApproximation_sample
    (geometricMatrixOfNamed matrix) index).1]
  rw [SquareMatrix.Inverse.PivotedScaledInverse.normSq_completeScaledInverse_one_scalar]
  rw [Matrix.sampleMatrix_apply,
    geometricMatrixOfNamed_apply]
  rfl

/-- Canonical productive name of the fraction-free inverse scalar. -/
@[expose] def canonicalInverseScalar {size : Nat} (matrix : NamedMatrix size) :
    CoherentNamed :=
  geometricNamed (canonicalScaledInverse matrix).scalar

/-- Canonical productive adjugate matrix, derived rather than supplied. -/
@[expose] def canonicalAdjugate {size : Nat} (matrix : NamedMatrix size) :
    NamedMatrix size :=
  let factors := canonicalScaledInverse matrix
  SquareMatrix.matrixOfFn fun row column =>
    geometricNamed (factors.inverse row column)

/-- Read the coherent name of the original computed scaled-inverse entry. -/
@[simp] theorem canonicalAdjugate_apply {size : Nat}
    (matrix : NamedMatrix size) (row column : Fin size) :
    canonicalAdjugate matrix row column =
      geometricNamed ((canonicalScaledInverse matrix).inverse row column) :=
  SquareMatrix.matrixOfFn_apply _ _ _

set_option genInjectivity false in
/-- A constructive fraction-free inverse certificate may apartify any
coherent scalar source operationally equivalent to the canonical
fraction-free scalar.  In particular, the source can be a certified finite
tail which omits singular coarse approximation centres. -/
structure ScaledInverseCertificate {size : Nat} (matrix : NamedMatrix size) where
  /-- The retained coherent scalar source, possibly obtained by certified finite-prefix deletion. -/ scalarSource :
    CoherentNamed
  /-- Operational equivalence from the canonical inverse scalar to this exact retained scalar source. -/
    sourceEquivalent : NamedEquivalent
    (canonicalInverseScalar matrix).name scalarSource.name
  /-- A positive lower bound for genuine candidates of the retained scalar source process. -/ scalarPossibleApart :
    Gaussian.Process.Apart.Possible.PossibleApart
    scalarSource.name.process

constructive_injectivity ScaledInverseCertificate

set_option genInjectivity false in
/-- A simple synchronized-sample presentation of the remaining inverse
trust boundary.  Every quantified value is an explicit Gaussian rational at
one finite sampler index. -/
structure ScalarCandidateLowerCertificate {size : Nat}
    (matrix : NamedMatrix size) where
  /-- The retained rational squared-norm floor for every sample of the canonical scaled-inverse scalar. -/ lowerSq :
    Coordinate
  /-- The retained squared-norm floor is strictly positive. -/ positive : 0 < lowerSq
  /-- Every finite synchronized sample of the canonical scaled-inverse scalar satisfies the retained squared-norm
floor. -/
  sample_lower : forall index,
    lowerSq <= Data.Gaussian.Norm.Basic.normSq
      ((canonicalScaledInverse matrix).scalar.sample index)

constructive_injectivity ScalarCandidateLowerCertificate

set_option genInjectivity false in
/-- A uniform candidate lower bound for the sole entry of a one-by-one named
matrix.  This is the exact genus-one A-period nonvanishing obligation before
the pivot-complete scalar's fourth-power encoding is applied. -/
structure OneByOneEntryCandidateLowerCertificate
    (matrix : NamedMatrix 1) where
  /-- The retained rational squared-norm floor for every sample of the sole original matrix entry. -/ lowerSq :
    Coordinate
  /-- The retained squared-norm floor is strictly positive. -/ positive : 0 < lowerSq
  /-- Every finite synchronized sample of the sole original matrix entry satisfies the retained squared-norm floor. -/
    sample_lower : forall index,
    lowerSq <= Data.Gaussian.Norm.Basic.normSq
      ((Gaussian.Name.Sampling.approximation
        (matrix 0 0).name).sample index)

constructive_injectivity OneByOneEntryCandidateLowerCertificate

namespace OneByOneEntryCandidateLowerCertificate

/-- Raise the entry lower bound to the fourth power prescribed by the exact
dimension-one pivot-complete inverse calculation. -/
@[expose] def toScalarCandidateLowerCertificate {matrix : NamedMatrix 1}
    (certificate : OneByOneEntryCandidateLowerCertificate matrix) :
    ScalarCandidateLowerCertificate matrix where
  lowerSq := certificate.lowerSq ^ 4
  positive := Purelib.Data.Rat.Fraction.Order.Arithmetic.pow_pos_direct
    certificate.positive 4
  sample_lower := by
    intro index
    rw [normSq_canonicalScaledInverse_one_scalar_sample]
    exact Purelib.Data.Rat.Fraction.Order.Arithmetic.pow_le_pow_direct
      certificate.positive.le (certificate.sample_lower index) 4

end OneByOneEntryCandidateLowerCertificate

set_option genInjectivity false in
/-- A uniform positive rational projection of the sole entry of a one-by-one
matrix.  The direction is not required to be a unit vector; its exact squared
norm is retained so finite Cauchy--Schwarz can recover a norm lower bound. -/
structure OneByOneEntryDirectionalLowerCertificate
    (matrix : NamedMatrix 1) where
  /-- The original rational projection direction, retained without unit normalization. -/ direction :
    Gaussian.Basic.Canonical
  /-- The retained projection direction has strictly positive squared norm. -/ directionNormSqPositive :
    0 < Data.Gaussian.Norm.Basic.normSq direction
  /-- The retained uniform rational lower bound on projected entry samples. -/ lower : Coordinate
  /-- The retained projection lower bound is strictly positive. -/ positive : 0 < lower
  /-- Every synchronized sample of the sole original matrix entry satisfies the retained directed projection bound. -/
    sample_lower : forall index,
    lower <=
      direction.re *
          ((Gaussian.Name.Sampling.approximation
            (matrix 0 0).name).sample index).re +
        direction.im *
          ((Gaussian.Name.Sampling.approximation
            (matrix 0 0).name).sample index).im

constructive_injectivity OneByOneEntryDirectionalLowerCertificate

namespace OneByOneEntryDirectionalLowerCertificate

/-- A uniform oriented projection gives a uniform squared-norm lower without
choosing a square root or normalizing the displayed rational direction. -/
@[expose] def toOneByOneEntryCandidateLowerCertificate {matrix : NamedMatrix 1}
    (certificate : OneByOneEntryDirectionalLowerCertificate matrix) :
    OneByOneEntryCandidateLowerCertificate matrix where
  lowerSq := certificate.lower ^ 2 /
    Data.Gaussian.Norm.Basic.normSq certificate.direction
  positive := Purelib.Data.Rat.Fraction.Order.Field.div_pos_direct
    (Purelib.Data.Rat.Fraction.Order.Arithmetic.pow_pos_direct certificate.positive 2)
    certificate.directionNormSqPositive
  sample_lower := by
    intro index
    let sample :=
      (Gaussian.Name.Sampling.approximation
        (matrix 0 0).name).sample index
    let projection :=
      certificate.direction.re * sample.re +
        certificate.direction.im * sample.im
    have lowerSqLeProjectionSq :
        certificate.lower ^ 2 <= projection ^ 2 :=
      Purelib.Data.Rat.Fraction.Order.Arithmetic.pow_le_pow_direct certificate.positive.le
        (certificate.sample_lower index) 2
    have projectionSqLe : projection ^ 2 <=
        Data.Gaussian.Norm.Basic.normSq certificate.direction *
          Data.Gaussian.Norm.Basic.normSq sample :=
      Gaussian.Norm.Bounds.projection_sq_le_normSq_mul
        certificate.direction sample
    apply (Purelib.Data.Rat.Fraction.Order.Field.div_le_iff_pos
      certificate.directionNormSqPositive).2
    exact (lowerSqLeProjectionSq.trans projectionSqLe).trans_eq (by ring1)

end OneByOneEntryDirectionalLowerCertificate

/-- A generic tail estimate for a geometric Gaussian approximation.  One
anchor value and the approximation's built-in later-movement bound control
the squared norm of every later sample. -/
private theorem geometric_tail_normSq_lower
    (source : GeometricApproximation) {anchor index : Nat}
    (order : anchor <= index) :
    Data.Gaussian.Norm.Basic.normSq (source.sample anchor) / 2 -
        Rational.Geometric.Basic.quarterRadius source.errorScale anchor <=
      Data.Gaussian.Norm.Basic.normSq (source.sample index) := by
  have movementForward := source.later_close order
  have reverseDifference :
      source.sample anchor - source.sample index =
        -(source.sample index - source.sample anchor) := by
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.sub_re,
        Gaussian.Basic.sub_im,
        Gaussian.Basic.neg_re,
        Gaussian.Basic.neg_im] <;> ring1
  have movement :
      Data.Gaussian.Norm.Basic.normSq
          (source.sample anchor - source.sample index) <=
        Rational.Geometric.Basic.quarterRadius source.errorScale anchor := by
    rw [reverseDifference, Gaussian.Norm.Basic.normSq_neg]
    exact movementForward
  have triangle :=
    Gaussian.Norm.Bounds.half_normSq_sub_le_normSq_sub
      (source.sample anchor) (source.sample index)
  have translated := Rat.Fraction.Order.Arithmetic.add_le_add_right_direct
    (triangle.trans movement)
    (Data.Gaussian.Norm.Basic.normSq (source.sample index) -
      Rational.Geometric.Basic.quarterRadius source.errorScale anchor)
  have leftIdentity :
      (Data.Gaussian.Norm.Basic.normSq (source.sample anchor) / 2 -
          Data.Gaussian.Norm.Basic.normSq (source.sample index)) +
        (Data.Gaussian.Norm.Basic.normSq (source.sample index) -
          Rational.Geometric.Basic.quarterRadius source.errorScale anchor) =
      Data.Gaussian.Norm.Basic.normSq (source.sample anchor) / 2 -
        Rational.Geometric.Basic.quarterRadius source.errorScale anchor := by ring1
  have rightIdentity :
      Rational.Geometric.Basic.quarterRadius source.errorScale anchor +
        (Data.Gaussian.Norm.Basic.normSq (source.sample index) -
          Rational.Geometric.Basic.quarterRadius source.errorScale anchor) =
      Data.Gaussian.Norm.Basic.normSq (source.sample index) := by ring1
  rw [leftIdentity, rightIdentity] at translated
  exact translated

/-- The geometric approximation carried by the sole entry of a one-by-one
named matrix. -/
@[expose] def oneByOneEntryApproximation (matrix : NamedMatrix 1) :
    GeometricApproximation :=
  Gaussian.Geometric.GeometricApproximation.ofNamed
    (matrix 0 0).name

set_option genInjectivity false in
/-- A finite prefix/tail presentation of genus-one A-period separation.  All
fields are rational checks at finitely many displayed samples. -/
structure OneByOneEntrySeparationCertificate
    (matrix : NamedMatrix 1) where
  /-- The exact retained sample index separating the checked prefix from the geometric tail. -/ anchor : Nat
  /-- The retained rational squared-norm floor for samples strictly before the anchor. -/ prefixLowerSq : Coordinate
  /-- The retained prefix squared-norm floor is strictly positive. -/ prefixPositive : 0 < prefixLowerSq
  /-- Every displayed sample strictly before the retained anchor satisfies the prefix floor. -/ prefix_lower : forall
    index, index < anchor ->
    prefixLowerSq <= Data.Gaussian.Norm.Basic.normSq
      ((oneByOneEntryApproximation matrix).sample index)
  /-- The original sole original matrix entry has strictly positive norm clearance beyond its retained anchor's
    geometric error. -/ tailPositive :
    0 < Data.Gaussian.Norm.Basic.normSq
          ((oneByOneEntryApproximation matrix).sample anchor) / 2 -
        Rational.Geometric.Basic.quarterRadius
          (oneByOneEntryApproximation matrix).errorScale anchor

constructive_injectivity OneByOneEntrySeparationCertificate

namespace OneByOneEntrySeparationCertificate

/-- At anchor zero the prefix is empty, so one strict rational clearance
check constructs the complete finite separation record. -/
@[expose] def ofAnchorZero {matrix : NamedMatrix 1}
    (tailPositive :
      0 < Data.Gaussian.Norm.Basic.normSq
            ((oneByOneEntryApproximation matrix).sample 0) / 2 -
          Rational.Geometric.Basic.quarterRadius
            (oneByOneEntryApproximation matrix).errorScale 0) :
    OneByOneEntrySeparationCertificate matrix where
  anchor := 0
  prefixLowerSq := 1
  prefixPositive := by decide
  prefix_lower := by
    intro index before
    exact (Nat.not_lt_zero index before).elim
  tailPositive := tailPositive

/-- At anchor zero, one positive projected endpoint and one conservative
clearance check supply the complete finite entry-separation certificate.
This is the theorem-facing adapter for compact oriented cycle estimates. -/
@[expose] def ofAnchorZeroDirectional {matrix : NamedMatrix 1}
    (direction : Gaussian.Basic.Canonical)
    (directionNormSqPositive :
      0 < Data.Gaussian.Norm.Basic.normSq direction)
    (lower : Coordinate) (lowerPositive : 0 < lower)
    (projectionLower :
      lower <=
        direction.re * ((oneByOneEntryApproximation matrix).sample 0).re +
          direction.im * ((oneByOneEntryApproximation matrix).sample 0).im)
    (clearancePositive :
      0 <
        (lower ^ 2 /
          Data.Gaussian.Norm.Basic.normSq direction) / 2 -
        Rational.Geometric.Basic.quarterRadius
          (oneByOneEntryApproximation matrix).errorScale 0) :
    OneByOneEntrySeparationCertificate matrix := by
  let sample := (oneByOneEntryApproximation matrix).sample 0
  let projection :=
    direction.re * sample.re + direction.im * sample.im
  have lowerSqLeProjectionSq : lower ^ 2 <= projection ^ 2 :=
    Rat.Fraction.Order.Arithmetic.pow_le_pow_direct lowerPositive.le
      projectionLower 2
  have projectionSqLe : projection ^ 2 <=
      Data.Gaussian.Norm.Basic.normSq direction *
        Data.Gaussian.Norm.Basic.normSq sample :=
    Gaussian.Norm.Bounds.projection_sq_le_normSq_mul
      direction sample
  have normLower :
      lower ^ 2 /
          Data.Gaussian.Norm.Basic.normSq direction <=
        Data.Gaussian.Norm.Basic.normSq sample := by
    apply (Rat.Fraction.Order.Field.div_le_iff_pos
      directionNormSqPositive).2
    exact (lowerSqLeProjectionSq.trans projectionSqLe).trans_eq (by ring1)
  have halfLower :
      (lower ^ 2 /
          Data.Gaussian.Norm.Basic.normSq direction) / 2 <=
        Data.Gaussian.Norm.Basic.normSq sample / 2 := by
    simp only [Rat.Fraction.Field.div_eq_mul_inv_direct]
    exact Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      normLower
      (Rat.Fraction.Order.Field.inv_pos_direct
        (by decide : (0 : Coordinate) < 2)).le
  apply ofAnchorZero
  exact clearancePositive.trans_le
    (Rat.Fraction.Order.Arithmetic.sub_le_sub_right_direct halfLower _)

/-- Take the exact rational minimum of the retained entry prefix floor and anchor tail clearance. -/
@[expose] def lowerSq {matrix : NamedMatrix 1}
    (certificate : OneByOneEntrySeparationCertificate matrix) :
    Coordinate :=
  min certificate.prefixLowerSq
    (Data.Gaussian.Norm.Basic.normSq
          ((oneByOneEntryApproximation matrix).sample certificate.anchor) / 2 -
      Rational.Geometric.Basic.quarterRadius
        (oneByOneEntryApproximation matrix).errorScale certificate.anchor)

/-- The common minimum of the retained prefix floor and anchor tail clearance is strictly positive. -/
theorem lowerSq_positive {matrix : NamedMatrix 1}
    (certificate : OneByOneEntrySeparationCertificate matrix) :
    0 < certificate.lowerSq :=
  Rat.Fraction.Order.Basic.lt_min certificate.prefixPositive certificate.tailPositive

/-- Expand the finite entry check to the uniform entry lower certificate. -/
@[expose] def toOneByOneEntryCandidateLowerCertificate {matrix : NamedMatrix 1}
    (certificate : OneByOneEntrySeparationCertificate matrix) :
    OneByOneEntryCandidateLowerCertificate matrix where
  lowerSq := certificate.lowerSq
  positive := certificate.lowerSq_positive
  sample_lower := by
    intro index
    change certificate.lowerSq <=
      Data.Gaussian.Norm.Basic.normSq
        ((oneByOneEntryApproximation matrix).sample index)
    by_cases beforeAnchor : index < certificate.anchor
    · exact (Rat.Fraction.Order.Basic.min_le_left _ _).trans
        (certificate.prefix_lower index beforeAnchor)
    · exact (Rat.Fraction.Order.Basic.min_le_right _ _).trans
        (geometric_tail_normSq_lower
          (oneByOneEntryApproximation matrix)
          (Nat.le_of_not_gt beforeAnchor))

/-- The complete dimension-one inverse lower certificate follows by the
exact fourth-power scalar calculation. -/
@[expose] def toScalarCandidateLowerCertificate {matrix : NamedMatrix 1}
    (certificate : OneByOneEntrySeparationCertificate matrix) :
    ScalarCandidateLowerCertificate matrix :=
  (certificate.toOneByOneEntryCandidateLowerCertificate).toScalarCandidateLowerCertificate

end OneByOneEntrySeparationCertificate

set_option genInjectivity false in
/-- Finite presentation of inverse-scalar separation.  The caller checks a
positive lower bound on the finite prefix strictly before `anchor` and one
strict rational clearance inequality at the anchor.  The displayed geometric
tail movement then supplies every later sample automatically. -/
structure ScalarSeparationCertificate {size : Nat}
    (matrix : NamedMatrix size) where
  /-- The exact retained sample index separating the checked prefix from the geometric tail. -/ anchor : Nat
  /-- The retained rational squared-norm floor for samples strictly before the anchor. -/ prefixLowerSq : Coordinate
  /-- The retained prefix squared-norm floor is strictly positive. -/ prefixPositive : 0 < prefixLowerSq
  /-- Every displayed sample strictly before the retained anchor satisfies the prefix floor. -/ prefix_lower : forall
    index, index < anchor ->
    prefixLowerSq <= Data.Gaussian.Norm.Basic.normSq
      ((canonicalScaledInverse matrix).scalar.sample index)
  /-- The original canonical inverse scalar has strictly positive norm clearance beyond its retained anchor's geometric
    error. -/ tailPositive :
    0 < Data.Gaussian.Norm.Basic.normSq
          ((canonicalScaledInverse matrix).scalar.sample anchor) / 2 -
        Rational.Geometric.Basic.quarterRadius
          (canonicalScaledInverse matrix).scalar.errorScale anchor

constructive_injectivity ScalarSeparationCertificate

/-- Computed positive candidate for the squared norm of a finite sample
prefix.  The empty prefix uses one; a successor takes the exact rational
minimum with the newly displayed sample. -/
@[expose] def scalarPrefixLowerSq (source : GeometricApproximation) :
    Nat -> Coordinate
  | 0 => 1
  | count + 1 => min (scalarPrefixLowerSq source count)
      (Data.Gaussian.Norm.Basic.normSq (source.sample count))

/-- Pointwise nonvanishing of the displayed finite prefix makes its computed
rational minimum strictly positive. -/
theorem scalarPrefixLowerSq_positive (source : GeometricApproximation)
    (count : Nat)
    (sampleNonzero : forall index, index < count -> source.sample index ≠ 0) :
    0 < scalarPrefixLowerSq source count := by
  induction count with
  | zero =>
      change (0 : Coordinate) < 1
      decide
  | succ count inductionHypothesis =>
      unfold scalarPrefixLowerSq
      apply Rat.Fraction.Order.Basic.lt_min
      · exact inductionHypothesis (fun index before =>
          sampleNonzero index (by omega0))
      · exact Gaussian.Norm.Basic.normSq_pos
          (sampleNonzero count (by omega0))

/-- The computed prefix minimum lies below every sample it contains. -/
theorem scalarPrefixLowerSq_le (source : GeometricApproximation)
    {count index : Nat} (before : index < count) :
    scalarPrefixLowerSq source count <=
      Data.Gaussian.Norm.Basic.normSq (source.sample index) := by
  induction count with
  | zero => exact (Nat.not_lt_zero index before).elim
  | succ count inductionHypothesis =>
      unfold scalarPrefixLowerSq
      by_cases last : index = count
      · subst index
        exact Rat.Fraction.Order.Basic.min_le_right _ _
      · have earlier : index < count := by omega0
        exact (Rat.Fraction.Order.Basic.min_le_left _ _).trans (inductionHypothesis earlier)

namespace ScalarSeparationCertificate

/-- If every synchronized scalar sample is already known to be nonzero, the
finite prefix fields are computed rather than supplied.  One checked anchor
clearance is then the only remaining separation datum. -/
@[expose] def ofSampleNonzero {size : Nat} {matrix : NamedMatrix size}
    (anchor : Nat)
    (sampleNonzero : forall index,
      (canonicalScaledInverse matrix).scalar.sample index ≠ 0)
    (tailPositive :
      0 < Data.Gaussian.Norm.Basic.normSq
            ((canonicalScaledInverse matrix).scalar.sample anchor) / 2 -
          Rational.Geometric.Basic.quarterRadius
            (canonicalScaledInverse matrix).scalar.errorScale anchor) :
    ScalarSeparationCertificate matrix where
  anchor := anchor
  prefixLowerSq := scalarPrefixLowerSq
    (canonicalScaledInverse matrix).scalar anchor
  prefixPositive := scalarPrefixLowerSq_positive
    (canonicalScaledInverse matrix).scalar anchor
      (fun index _before => sampleNonzero index)
  prefix_lower := by
    intro index before
    exact scalarPrefixLowerSq_le
      (canonicalScaledInverse matrix).scalar before
  tailPositive := tailPositive

/-- Rational lower bound shared by the checked prefix and coherent tail. -/
@[expose] def lowerSq {size : Nat} {matrix : NamedMatrix size}
    (certificate : ScalarSeparationCertificate matrix) : Coordinate :=
  min certificate.prefixLowerSq
    (Data.Gaussian.Norm.Basic.normSq
          ((canonicalScaledInverse matrix).scalar.sample certificate.anchor) /
        2 -
      Rational.Geometric.Basic.quarterRadius
        (canonicalScaledInverse matrix).scalar.errorScale certificate.anchor)

/-- The common minimum of the retained prefix floor and anchor tail clearance is strictly positive. -/
theorem lowerSq_positive {size : Nat} {matrix : NamedMatrix size}
    (certificate : ScalarSeparationCertificate matrix) :
    0 < certificate.lowerSq :=
  Rat.Fraction.Order.Basic.lt_min certificate.prefixPositive certificate.tailPositive

/-- The retained scalar anchor clearance bounds every later original synchronized sample from below. -/
private theorem tail_lower {size : Nat} {matrix : NamedMatrix size}
    (certificate : ScalarSeparationCertificate matrix)
    {index : Nat} (order : certificate.anchor <= index) :
    Data.Gaussian.Norm.Basic.normSq
          ((canonicalScaledInverse matrix).scalar.sample certificate.anchor) /
        2 -
      Rational.Geometric.Basic.quarterRadius
          (canonicalScaledInverse matrix).scalar.errorScale
          certificate.anchor <=
      Data.Gaussian.Norm.Basic.normSq
        ((canonicalScaledInverse matrix).scalar.sample index) := by
  exact geometric_tail_normSq_lower
    (canonicalScaledInverse matrix).scalar order

/-- The finite prefix/tail presentation expands into the established uniform
candidate lower certificate. -/
@[expose] def toScalarCandidateLowerCertificate {size : Nat}
    {matrix : NamedMatrix size}
    (certificate : ScalarSeparationCertificate matrix) :
    ScalarCandidateLowerCertificate matrix where
  lowerSq := certificate.lowerSq
  positive := certificate.lowerSq_positive
  sample_lower := by
    intro index
    by_cases beforeAnchor : index < certificate.anchor
    · exact (Rat.Fraction.Order.Basic.min_le_left _ _).trans
        (certificate.prefix_lower index beforeAnchor)
    · exact (Rat.Fraction.Order.Basic.min_le_right _ _).trans
        (certificate.tail_lower (Nat.le_of_not_gt beforeAnchor))

end ScalarSeparationCertificate

namespace ScalarCandidateLowerCertificate

/-- Uniform finite-sample separation supplies candidate apartness; later
whole-ball apartness is derived by the ordinary apartification controller. -/
@[expose] def toScaledInverseCertificate {size : Nat} {matrix : NamedMatrix size}
    (certificate : ScalarCandidateLowerCertificate matrix) :
    ScaledInverseCertificate matrix where
  scalarSource := canonicalInverseScalar matrix
  sourceEquivalent := Gaussian.Equivalence.NamedEquivalent.refl _
  scalarPossibleApart :=
    { lowerSq := certificate.lowerSq
      positive := certificate.positive
      lower := by
        intro state value possible
        change
          (canonicalScaledInverse matrix).scalar.toApproximation.Possible
            state value at possible
        rcases possible with ⟨later, _order, rfl⟩
        exact certificate.sample_lower later }

/-- Every original synchronized inverse-scalar sample is nonzero under the retained positive uniform floor. -/
theorem sample_scalar_nonzero {size : Nat} {matrix : NamedMatrix size}
    (certificate : ScalarCandidateLowerCertificate matrix) (index : Nat) :
    (canonicalScaledInverse matrix).scalar.sample index ≠ 0 := by
  intro scalarZero
  have positiveNorm := certificate.positive.trans_le
    (certificate.sample_lower index)
  rw [scalarZero, Gaussian.Norm.Basic.normSq_zero] at positiveNorm
  exact lt_irrefl 0 positiveNorm

/-- Every synchronized finite A-matrix sample has trivial left kernel.  This
is the exact finite-dimensional nondegeneracy conclusion consumed before
normalization. -/
theorem sampledMatrix_leftKernel_trivial {size : Nat}
    {matrix : NamedMatrix size}
    (certificate : ScalarCandidateLowerCertificate matrix) (index : Nat)
    (vector : Data.Vector Gaussian size)
    (kernel : forall row,
      SquareMatrix.Multiplication.matrixVector
        (sampledMatrix matrix index) vector row = 0) :
    forall row, vector row = 0 := by
  let sampled := sampledMatrix matrix index
  let computed :=
    SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse sampled
  have scalarSample :
      (canonicalScaledInverse matrix).scalar.sample index = computed.scalar := by
    unfold canonicalScaledInverse computed sampled
    have samples :=
      SquareMatrix.Inverse.PivotedScaledInverse.completeApproximation_sample
        (geometricMatrixOfNamed matrix) index
    rw [sample_geometricMatrixOfNamed] at samples
    exact samples.1
  have scalarNonzero : computed.scalar ≠ 0 := by
    intro computedZero
    apply certificate.sample_scalar_nonzero index
    rw [scalarSample, computedZero]
  intro row
  have productZero : computed.scalar * vector row = 0 := by
    calc
      computed.scalar * vector row =
          SquareMatrix.Multiplication.matrixVector
            (SquareMatrix.Multiplication.scaleIdentity computed.scalar)
              vector row := by
        simpa only [Data.Vector.Basic.vectorOfFn_apply] using
          (Data.Vector.Basic.vector_eq_at
            (SquareMatrix.Multiplication.matrixVector_scaleIdentity
              computed.scalar vector) row).symm
      _ = SquareMatrix.Multiplication.matrixVector
            (SquareMatrix.Multiplication.mul computed.inverse sampled)
              vector row := by
        rw [computed.left_identity]
      _ = SquareMatrix.Multiplication.matrixVector computed.inverse
            (SquareMatrix.Multiplication.matrixVector sampled vector) row :=
        Data.Vector.Basic.vector_eq_at
          (SquareMatrix.Multiplication.matrixVector_mul
            computed.inverse sampled vector) row
      _ = 0 := by
        rw [SquareMatrix.Multiplication.matrixVector_apply]
        rw [FiniteSum.Fin.sumFin_congr
          (right := fun _ => (0 : Gaussian)) (fun column => by
            rw [show SquareMatrix.Multiplication.matrixVector sampled
                vector column = 0 by
              exact kernel column]
            exact mul_zero _)]
        exact FiniteSum.Fin.sumFin_zero
  by_cases vectorZero : vector row = 0
  · exact vectorZero
  · exact (Gaussian.Field.mul_ne_zero_direct
      scalarNonzero vectorZero productZero).elim

end ScalarCandidateLowerCertificate

/-! ## Tail-only inverse separation -/

/-- The exact rational clearance tested at one proposed inverse-scalar tail
anchor.  Positivity says that the anchor centre is farther from zero than all
subsequent geometric movement allowed by the approximation. -/
@[expose] def scalarTailClearanceAt {size : Nat} (matrix : NamedMatrix size)
    (anchor : Nat) : Coordinate :=
  let inverse := canonicalScaledInverse matrix
  Data.Gaussian.Norm.Basic.normSq (inverse.scalar.sample anchor) / 2 -
    Rational.Geometric.Basic.quarterRadius
      inverse.scalar.errorScale anchor

/-- Genus-one presentation of the inverse-scalar tail clearance.  Its centre
is computed directly from the sole matrix entry; only the already-certified
inverse error scale is retained. -/
@[expose] def oneByOneEntryTailClearanceAt (matrix : NamedMatrix 1)
    (anchor : Nat) : Coordinate :=
  Data.Gaussian.Norm.Basic.normSq
      ((oneByOneEntryApproximation matrix).sample anchor) ^ 4 / 2 -
    Rational.Geometric.Basic.quarterRadius
      (canonicalScaledInverse matrix).scalar.errorScale anchor

/-- The one-entry fourth-power clearance equals the canonical scaled-inverse scalar clearance exactly. -/
theorem oneByOneEntryTailClearanceAt_eq_scalarTailClearanceAt
    (matrix : NamedMatrix 1) (anchor : Nat) :
    oneByOneEntryTailClearanceAt matrix anchor =
      scalarTailClearanceAt matrix anchor := by
  unfold oneByOneEntryTailClearanceAt
  dsimp only [scalarTailClearanceAt]
  rw [normSq_canonicalScaledInverse_one_scalar_sample]
  unfold oneByOneEntryApproximation
  rw [Gaussian.Geometric.GeometricApproximation.ofNamed_sample]

set_option genInjectivity false in
/-- One finite tail-clearance check for the canonical fraction-free inverse
scalar.  Unlike `ScalarSeparationCertificate`, this record makes no
claim about the discarded prefix. -/
structure ScalarTailSeparationCertificate {size : Nat}
    (matrix : NamedMatrix size) where
  /-- The exact original scalar sample index after which geometric tail clearance is certified. -/ anchor : Nat
  /-- The retained scalar anchor has strictly positive rational tail clearance. -/ tailPositive : 0 <
    scalarTailClearanceAt matrix anchor

constructive_injectivity ScalarTailSeparationCertificate

namespace ScalarCandidateLowerCertificate

/-- A uniform scalar lower bound determines a finite tail anchor without a
search through candidate centres.  The chosen quarter-radius is already
strictly below half the certified squared-norm floor. -/
@[expose] def tailAnchor {size : Nat} {matrix : NamedMatrix size}
    (certificate : ScalarCandidateLowerCertificate matrix) : Nat :=
  Rational.Geometric.Search.firstQuarterBelow
    (canonicalScaledInverse matrix).scalar.errorScale 0
      (certificate.lowerSq / 2)

/-- The canonical anchor selected from a uniform lower certificate has
strictly positive tail clearance. -/
theorem tailAnchor_clearance_positive {size : Nat}
    {matrix : NamedMatrix size}
    (certificate : ScalarCandidateLowerCertificate matrix) :
    0 < scalarTailClearanceAt matrix certificate.tailAnchor := by
  let scalar := (canonicalScaledInverse matrix).scalar
  let anchor := certificate.tailAnchor
  have halfPositive : 0 < certificate.lowerSq / 2 :=
    Rat.Fraction.Order.Field.div_pos_direct certificate.positive (by decide)
  have radiusSmall :
      Rational.Geometric.Basic.quarterRadius scalar.errorScale anchor <
        certificate.lowerSq / 2 := by
    exact Rational.Geometric.Search.firstQuarterBelow_accurate scalar.errorScale
      scalar.errorScale_nonneg 0 (certificate.lowerSq / 2) halfPositive
  have lowerHalfLeSampleHalf :
      certificate.lowerSq / 2 <=
        Data.Gaussian.Norm.Basic.normSq
            (scalar.sample anchor) / 2 := by
    simp only [Rat.Fraction.Field.div_eq_mul_inv_direct]
    exact Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (certificate.sample_lower anchor)
      (Rat.Fraction.Order.Field.inv_pos_direct
        (by decide : (0 : Coordinate) < 2)).le
  have radiusBelowSampleHalf :
      Rational.Geometric.Basic.quarterRadius scalar.errorScale anchor <
        Data.Gaussian.Norm.Basic.normSq
            (scalar.sample anchor) / 2 :=
    radiusSmall.trans_le lowerHalfLeSampleHalf
  unfold scalarTailClearanceAt
  dsimp only
  exact Rat.Fraction.Order.Arithmetic.sub_pos_direct radiusBelowSampleHalf

/-- Forget the stronger uniform separation only after selecting a certified
tail anchor.  This adapter lets tail-oriented clients share the same
apartification interface without executing a bounded scan. -/
@[expose] def toScalarTailSeparationCertificate {size : Nat}
    {matrix : NamedMatrix size}
    (certificate : ScalarCandidateLowerCertificate matrix) :
    ScalarTailSeparationCertificate matrix where
  anchor := certificate.tailAnchor
  tailPositive := certificate.tailAnchor_clearance_positive

end ScalarCandidateLowerCertificate

/-- Executably test one proposed tail anchor.  The successful branch returns
the proof-bearing separation certificate produced by the same rational
comparison. -/
@[expose] def scalarTailSeparationAt? {size : Nat} (matrix : NamedMatrix size)
    (anchor : Nat) : Option (ScalarTailSeparationCertificate matrix) :=
  if positive : 0 < scalarTailClearanceAt matrix anchor then
    some { anchor := anchor, tailPositive := positive }
  else none

/-- The single-anchor check succeeds exactly when its retained rational tail clearance is positive. -/
theorem scalarTailSeparationAt?_isSome_iff {size : Nat}
    (matrix : NamedMatrix size) (anchor : Nat) :
    (scalarTailSeparationAt? matrix anchor).isSome = true ↔
      0 < scalarTailClearanceAt matrix anchor := by
  unfold scalarTailSeparationAt?
  by_cases positive : 0 < scalarTailClearanceAt matrix anchor
  · rewrite [dif_pos positive]
    exact ⟨fun _ => positive, fun _ => Eq.refl _⟩
  · rewrite [dif_neg positive]
    constructor
    · intro impossible
      exact Bool.noConfusion impossible
    · intro contradictory
      exact False.elim (positive contradictory)

set_option genInjectivity false in
/-- A tail certificate found within an explicit finite search bound.  The
strict bound is retained so successful scans can be audited without replaying
the recursion. -/
structure BoundedScalarTailSeparationCertificate {size : Nat}
    (matrix : NamedMatrix size) (bound : Nat) where
  /-- The actual successful scalar tail certificate returned by the finite bounded check. -/ certificate :
    ScalarTailSeparationCertificate matrix
  /-- The retained successful anchor lies strictly within the original search bound. -/ anchor_lt : certificate.anchor <
    bound

constructive_injectivity BoundedScalarTailSeparationCertificate

/-- Test exactly one caller-selected anchor already known to lie in a finite
bound.  This is the direct counterpart of the newest-first prefix scan and
performs no checks at any other index. -/
@[expose] def scalarTailSeparationAtWithin? {size : Nat} (matrix : NamedMatrix size)
    {bound : Nat} (anchor : Nat) (within : anchor < bound) :
    Option (BoundedScalarTailSeparationCertificate matrix bound) :=
  if positive : 0 < scalarTailClearanceAt matrix anchor then
    some
      { certificate := { anchor := anchor, tailPositive := positive }
        anchor_lt := within }
  else none

/-- Direct bounded genus-one check using the sole entry rather than a generic
sampled-matrix inversion.  The fourth-power identity transports success to
the canonical scalar certificate expected by the normalization API. -/
@[expose] def oneByOneEntryTailSeparationAtWithin? (matrix : NamedMatrix 1)
    {bound : Nat} (anchor : Nat) (within : anchor < bound) :
    Option (BoundedScalarTailSeparationCertificate matrix bound) :=
  if positive : 0 < oneByOneEntryTailClearanceAt matrix anchor then
    some
      { certificate :=
          { anchor := anchor
            tailPositive := by
              rw [← oneByOneEntryTailClearanceAt_eq_scalarTailClearanceAt]
              exact positive }
        anchor_lt := within }
  else none

/-- Scan all displayed anchors below `bound`, newest first.  This is an
ordinary terminating search over exact rational inequalities; it introduces
no unbounded minimization or choice. -/
@[expose] def scalarTailSeparationWithin? {size : Nat} (matrix : NamedMatrix size) :
    (bound : Nat) ->
      Option (BoundedScalarTailSeparationCertificate matrix bound)
  | 0 => none
  | bound + 1 =>
      match found : scalarTailSeparationAt? matrix bound with
      | some certificate =>
          some
            { certificate := certificate
              anchor_lt := by
                have anchorEqual : certificate.anchor = bound := by
                  unfold scalarTailSeparationAt? at found
                  split at found
                  · cases found
                    rfl
                  · contradiction
                rw [anchorEqual]
                exact Nat.lt_succ_self bound }
      | none =>
          match scalarTailSeparationWithin? matrix bound with
          | some earlier =>
              some
                { certificate := earlier.certificate
                  anchor_lt := earlier.anchor_lt.trans
                    (Nat.lt_succ_self bound) }
          | none => none

namespace ScalarTailSeparationCertificate

/-- The positive rational lower bound visible from the selected tail anchor. -/
@[expose] def lowerSq {size : Nat} {matrix : NamedMatrix size}
    (certificate : ScalarTailSeparationCertificate matrix) : Coordinate :=
  Data.Gaussian.Norm.Basic.normSq
        ((canonicalScaledInverse matrix).scalar.sample certificate.anchor) / 2 -
      Rational.Geometric.Basic.quarterRadius
        (canonicalScaledInverse matrix).scalar.errorScale certificate.anchor

/-- The retained scalar tail squared-norm floor is strictly positive. -/
theorem lowerSq_positive {size : Nat} {matrix : NamedMatrix size}
    (certificate : ScalarTailSeparationCertificate matrix) :
    0 < certificate.lowerSq :=
  certificate.tailPositive

/-- Every retained canonical scalar centre is nonzero.  No statement is made
about the discarded coarse prefix. -/
theorem sample_nonzero_of_anchor_le {size : Nat} {matrix : NamedMatrix size}
    (certificate : ScalarTailSeparationCertificate matrix) (index : Nat)
    (order : certificate.anchor <= index) :
    (canonicalScaledInverse matrix).scalar.sample index ≠ 0 := by
  intro sampleZero
  have lower := geometric_tail_normSq_lower
    (canonicalScaledInverse matrix).scalar order
  change certificate.lowerSq <=
    Data.Gaussian.Norm.Basic.normSq
      ((canonicalScaledInverse matrix).scalar.sample index) at lower
  rw [sampleZero, Gaussian.Norm.Basic.normSq_zero] at lower
  exact (not_lt_of_ge lower certificate.lowerSq_positive).elim

/-- Coherent scalar source obtained by deleting the uncertified finite
prefix of the canonical synchronized inverse stream. -/
@[expose] def scalarSource {size : Nat} {matrix : NamedMatrix size}
    (certificate : ScalarTailSeparationCertificate matrix) : CoherentNamed :=
  geometricNamed
    ((canonicalScaledInverse matrix).scalar.drop certificate.anchor)

/-- Tail deletion changes finite presentation but not operational value. -/
@[expose] def sourceEquivalent {size : Nat} {matrix : NamedMatrix size}
    (certificate : ScalarTailSeparationCertificate matrix) :
    NamedEquivalent (canonicalInverseScalar matrix).name
      certificate.scalarSource.name :=
  geometricNamed_drop_equivalent
    (canonicalScaledInverse matrix).scalar certificate.anchor

/-- Apartify the tail process.  Every candidate of that restricted process
is an explicitly later canonical sample, so the anchor triangle estimate
supplies the same positive lower bound without inspecting any discarded
centre. -/
@[expose] def toScaledInverseCertificate {size : Nat} {matrix : NamedMatrix size}
    (certificate : ScalarTailSeparationCertificate matrix) :
    ScaledInverseCertificate matrix where
  scalarSource := certificate.scalarSource
  sourceEquivalent := certificate.sourceEquivalent
  scalarPossibleApart :=
    { lowerSq := certificate.lowerSq
      positive := certificate.lowerSq_positive
      lower := by
        intro state value possible
        change
          ((canonicalScaledInverse matrix).scalar.drop
            certificate.anchor).toApproximation.Possible state value at possible
        rcases possible with ⟨later, _order, rfl⟩
        change certificate.lowerSq <=
          Data.Gaussian.Norm.Basic.normSq
            ((canonicalScaledInverse matrix).scalar.sample
              (certificate.anchor + later))
        exact geometric_tail_normSq_lower
          (canonicalScaledInverse matrix).scalar (by omega0) }

end ScalarTailSeparationCertificate

namespace ScaledInverseCertificate

/-- Apartify the retained scalar source using its original genuine-candidate separation certificate. -/
@[expose] def scalar {size : Nat} {matrix : NamedMatrix size}
    (inverse : ScaledInverseCertificate matrix) : CoherentNamed :=
  Gaussian.Name.Coherent.CoherentNamed.apartify
    inverse.scalarSource inverse.scalarPossibleApart

/-- The prepared scalar is uniformly apart on every displayed ball. -/
@[expose] def scalarApart {size : Nat} {matrix : NamedMatrix size}
    (inverse : ScaledInverseCertificate matrix) :
    Gaussian.Name.Basic.Named.Apart inverse.scalar.name where
  certificate := Gaussian.Process.Apart.Preparation.apartifyApart
    inverse.scalarPossibleApart

/-- Apartification changes the finite process representation but preserves
the scalar's operational value. -/
@[expose] def canonicalScalarEquivalent {size : Nat} {matrix : NamedMatrix size}
    (inverse : ScaledInverseCertificate matrix) :
    NamedEquivalent (canonicalInverseScalar matrix).name inverse.scalar.name :=
  Gaussian.Equivalence.NamedEquivalent.trans inverse.sourceEquivalent
    (Gaussian.Name.Coherent.CoherentNamed.apartifyEquivalent
      inverse.scalarSource inverse.scalarPossibleApart)

/-- Read the canonical computed adjugate of the original named matrix. -/
@[expose] def adjugate {size : Nat} {matrix : NamedMatrix size}
    (_inverse : ScaledInverseCertificate matrix) : NamedMatrix size :=
  canonicalAdjugate matrix

/-- Equal-index geometric matrix multiplication. -/
@[expose] def geometricProductEntry {size : Nat}
    (left right : GeometricMatrix size) (row column : Fin size) :
    GeometricApproximation :=
  Gaussian.Geometric.GeometricApproximation.sum fun middle =>
    Gaussian.Geometric.GeometricApproximation.mul
      (left row middle) (right middle column)

/-- An equal-index geometric product entry samples to the original finite Gaussian matrix product. -/
@[simp] theorem geometricProductEntry_sample {size : Nat}
    (left right : GeometricMatrix size) (row column : Fin size)
    (index : Nat) :
    (geometricProductEntry left right row column).sample index =
      SquareMatrix.Multiplication.mul
        (Matrix.sampleMatrix left index)
        (Matrix.sampleMatrix right index)
        row column := by
  rw [SquareMatrix.Multiplication.mul_apply]
  unfold geometricProductEntry
  rw [Gaussian.Geometric.GeometricApproximation.sum_sample]
  apply FiniteSum.Fin.sumFin_congr
  intro middle
  rewrite [Gaussian.Geometric.GeometricApproximation.mul_sample,
    Matrix.sampleMatrix_apply, Matrix.sampleMatrix_apply]
  exact Eq.refl _

/-- Matrix-level synchronized geometric product. -/
@[expose] def geometricProductMatrix {size : Nat}
    (left right : GeometricMatrix size) : GeometricMatrix size :=
  SquareMatrix.matrixOfFn fun row column =>
    geometricProductEntry left right row column

/-- Read the synchronized finite-sum product assigned to the original pair of matrix indices. -/
@[simp] theorem geometricProductMatrix_apply {size : Nat}
    (left right : GeometricMatrix size) (row column : Fin size) :
    geometricProductMatrix left right row column =
      geometricProductEntry left right row column :=
  SquareMatrix.matrixOfFn_apply _ _ _

/-- Transpose synchronized geometric entries without resampling. -/
@[expose] def geometricTranspose {size : Nat} (matrix : GeometricMatrix size) :
    GeometricMatrix size :=
  SquareMatrix.matrixOfFn fun row column => matrix column row

/-- Read the original geometric entry at the reversed matrix indices. -/
@[simp] theorem geometricTranspose_apply {size : Nat}
    (matrix : GeometricMatrix size) (row column : Fin size) :
    geometricTranspose matrix row column = matrix column row :=
  SquareMatrix.matrixOfFn_apply _ _ _

/-- Sampling the synchronized geometric product gives the product of the two original equal-index sample matrices. -/
theorem sample_geometricProductMatrix {size : Nat}
    (left right : GeometricMatrix size) (index : Nat) :
    Matrix.sampleMatrix
        (geometricProductMatrix left right) index =
      SquareMatrix.Multiplication.mul
        (Matrix.sampleMatrix left index)
        (Matrix.sampleMatrix right index) := by
  apply SquareMatrix.matrix_ext
  intro row column
  rw [Matrix.sampleMatrix_apply,
    geometricProductMatrix_apply, geometricProductEntry_sample]

/-- Transposing a synchronized product reverses its factors sample by sample. -/
theorem geometricProduct_transpose_sample {size : Nat}
    (left right : GeometricMatrix size) (row column : Fin size)
    (index : Nat) :
    (geometricProductMatrix left right column row).sample index =
      (geometricProductMatrix (geometricTranspose right)
        (geometricTranspose left) row column).sample index := by
  rw [geometricProductMatrix_apply, geometricProductMatrix_apply,
    geometricProductEntry_sample, geometricProductEntry_sample,
    SquareMatrix.Multiplication.mul_apply,
    SquareMatrix.Multiplication.mul_apply]
  apply FiniteSum.Fin.sumFin_congr
  intro middle
  rewrite [Matrix.sampleMatrix_apply, Matrix.sampleMatrix_apply,
    Matrix.sampleMatrix_apply, Matrix.sampleMatrix_apply,
    geometricTranspose_apply, geometricTranspose_apply]
  exact Gaussian.Basic.mul_comm _ _

/-- Wrap every synchronized geometric entry as a coherent productive name. -/
@[expose] def geometricNamedMatrix {size : Nat} (matrix : GeometricMatrix size) :
    NamedMatrix size :=
  SquareMatrix.matrixOfFn fun row column =>
    geometricNamed (matrix row column)

/-- Read the coherent name generated from the exact original geometric matrix entry. -/
@[simp] theorem geometricNamedMatrix_apply {size : Nat}
    (matrix : GeometricMatrix size) (row column : Fin size) :
    geometricNamedMatrix matrix row column =
      geometricNamed (matrix row column) :=
  SquareMatrix.matrixOfFn_apply _ _ _

/-- Every name is operationally equivalent to the geometric wrapper of its
canonical nested sampler. -/
@[expose] def named_equivalent_geometricOfNamed (value : CoherentNamed) :
    NamedEquivalent value.name
      (geometricNamed
        (Gaussian.Geometric.GeometricApproximation.ofNamed
          value.name)).name := by
  apply Gaussian.Equivalence.NamedEquivalent.trans
    (Gaussian.Sequence.Name.Equivalence.named_toSamplingNamed value.name)
  simpa only [geometricNamed,
    Gaussian.Name.Coherent.CoherentNamed.ofApproximation] using
    Gaussian.Sequence.Name.Equivalence.approximationEquivalent_toNamed
      (Gaussian.Sequence.Equivalence.approximationEquivalentOfSamplesEq
        (Gaussian.Name.Sampling.approximation value.name)
        (Gaussian.Geometric.GeometricApproximation.ofNamed
          value.name).toApproximation (by intro index; rfl))

/-- Actual finite matrix arithmetic realizes the synchronized geometric
product whenever both entry families realize their geometric sources. -/
@[expose] def matrixMul_equivalent_geometricProduct {size : Nat}
    (left right : NamedMatrix size)
    (leftSource rightSource : GeometricMatrix size)
    (leftEquivalent : forall row column,
      NamedEquivalent (left row column).name
        (geometricNamed (leftSource row column)).name)
    (rightEquivalent : forall row column,
      NamedEquivalent (right row column).name
        (geometricNamed (rightSource row column)).name)
    (row column : Fin size) :
    NamedEquivalent (matrixMul left right row column).name
      (geometricNamed
        (geometricProductEntry leftSource rightSource row column)).name := by
  rw [matrixMul_apply]
  apply sumNamed_equivalent_geometricSum
  intro middle
  let leftGeometric := geometricNamed (leftSource row middle)
  let rightGeometric := geometricNamed (rightSource middle column)
  have replaceOperands : NamedEquivalent
      (Gaussian.Name.Coherent.CoherentNamed.mul
        (left row middle) (right middle column)).name
      (Gaussian.Name.Coherent.CoherentNamed.mul
        leftGeometric rightGeometric).name :=
    Gaussian.Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects
      (left row middle) leftGeometric
      (right middle column) rightGeometric
      (leftEquivalent row middle) (rightEquivalent middle column)
  apply Gaussian.Equivalence.NamedEquivalent.trans replaceOperands
  simpa only [leftGeometric, rightGeometric, geometricNamed,
    Gaussian.Name.Coherent.CoherentNamed.mul,
    Gaussian.Name.Coherent.CoherentNamed.ofApproximation] using
    Gaussian.Sequence.Arithmetic.Multiplication.Bridge.mulToNamed_equivalent_pointwise
      (leftSource row middle).toApproximation
      (rightSource middle column).toApproximation
      (Gaussian.Geometric.GeometricApproximation.mul
        (leftSource row middle) (rightSource middle column)).toApproximation
      (by intro index; rfl)

/-- Matrix-level form of the synchronized geometric realization theorem. -/
@[expose] def matrixMul_equivalent_geometricProductMatrix {size : Nat}
    (left right : NamedMatrix size)
    (leftSource rightSource : GeometricMatrix size)
    (leftEquivalent : forall row column,
      NamedEquivalent (left row column).name
        (geometricNamed (leftSource row column)).name)
    (rightEquivalent : forall row column,
      NamedEquivalent (right row column).name
        (geometricNamed (rightSource row column)).name) :
    MatrixEquivalent (matrixMul left right)
      (geometricNamedMatrix
        (geometricProductMatrix leftSource rightSource)) := by
  intro row column
  rw [geometricNamedMatrix_apply,
    geometricProductMatrix_apply]
  exact matrixMul_equivalent_geometricProduct left right
    leftSource rightSource leftEquivalent rightEquivalent row column

/-- Two synchronized geometric approximations with identical finite samples
produce operationally equivalent coherent names. -/
@[expose] def geometricNamed_equivalent_of_samples
    (left right : GeometricApproximation)
    (samples : forall index, left.sample index = right.sample index) :
    NamedEquivalent (geometricNamed left).name (geometricNamed right).name := by
  simpa only [geometricNamed,
    Gaussian.Name.Coherent.CoherentNamed.ofApproximation] using
    Gaussian.Sequence.Name.Equivalence.approximationEquivalent_toNamed
      (Gaussian.Sequence.Equivalence.approximationEquivalentOfSamplesEq
        left.toApproximation right.toApproximation samples)

/-- Actual multiplication of two coherent names realizes any synchronized
geometric product realizing its two operands. -/
@[expose] def coherentMul_equivalent_geometricMul
    (left right : CoherentNamed)
    (leftSource rightSource : GeometricApproximation)
    (leftEquivalent : NamedEquivalent left.name
      (geometricNamed leftSource).name)
    (rightEquivalent : NamedEquivalent right.name
      (geometricNamed rightSource).name) :
    NamedEquivalent
      (Gaussian.Name.Coherent.CoherentNamed.mul left right).name
      (geometricNamed
        (Gaussian.Geometric.GeometricApproximation.mul
          leftSource rightSource)).name := by
  let leftGeometric := geometricNamed leftSource
  let rightGeometric := geometricNamed rightSource
  have replaceOperands : NamedEquivalent
      (Gaussian.Name.Coherent.CoherentNamed.mul left right).name
      (Gaussian.Name.Coherent.CoherentNamed.mul
        leftGeometric rightGeometric).name :=
    Gaussian.Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects
      left leftGeometric right rightGeometric
      leftEquivalent rightEquivalent
  apply Gaussian.Equivalence.NamedEquivalent.trans replaceOperands
  simpa only [leftGeometric, rightGeometric, geometricNamed,
    Gaussian.Name.Coherent.CoherentNamed.mul,
    Gaussian.Name.Coherent.CoherentNamed.ofApproximation] using
    Gaussian.Sequence.Arithmetic.Multiplication.Bridge.mulToNamed_equivalent_pointwise
      leftSource.toApproximation rightSource.toApproximation
      (Gaussian.Geometric.GeometricApproximation.mul
        leftSource rightSource).toApproximation
      (by intro index; rfl)

/-- A whole named matrix is operationally its canonical synchronized sampler
matrix. -/
@[expose] def matrix_equivalent_geometricOfNamed {size : Nat}
    (matrix : NamedMatrix size) :
    MatrixEquivalent matrix
      (geometricNamedMatrix (geometricMatrixOfNamed matrix)) := by
  intro row column
  rw [geometricNamedMatrix_apply, geometricMatrixOfNamed_apply]
  exact named_equivalent_geometricOfNamed (matrix row column)

/-- Associativity of synchronized geometric matrix products, exposed as
operational equality of their generated CCL matrices. -/
@[expose] def geometricProductMatrix_assoc {size : Nat}
    (first second third : GeometricMatrix size) :
    MatrixEquivalent
      (geometricNamedMatrix
        (geometricProductMatrix
          (geometricProductMatrix first second) third))
      (geometricNamedMatrix
        (geometricProductMatrix first
          (geometricProductMatrix second third))) := by
  intro row column
  rw [geometricNamedMatrix_apply, geometricNamedMatrix_apply]
  apply geometricNamed_equivalent_of_samples
  intro index
  have associated :
      Matrix.sampleMatrix
          (geometricProductMatrix
            (geometricProductMatrix first second) third) index =
        Matrix.sampleMatrix
          (geometricProductMatrix first
            (geometricProductMatrix second third)) index := by
    rw [sample_geometricProductMatrix, sample_geometricProductMatrix,
      sample_geometricProductMatrix, sample_geometricProductMatrix]
    exact SquareMatrix.Multiplication.mul_assoc _ _ _
  simpa only [Matrix.sampleMatrix_apply] using
    SquareMatrix.matrix_eq_at associated row column

/-- Actual finite CCL matrix multiplication is associative up to operational
equality.  The proof synchronizes all three inputs, applies the exact finite
Gaussian matrix theorem at every index, and returns to the arithmetic trees. -/
@[expose] def matrixMul_assoc {size : Nat}
    (first second third : NamedMatrix size) :
    MatrixEquivalent (matrixMul (matrixMul first second) third)
      (matrixMul first (matrixMul second third)) := by
  let firstSource := geometricMatrixOfNamed first
  let secondSource := geometricMatrixOfNamed second
  let thirdSource := geometricMatrixOfNamed third
  let firstSecondSource :=
    geometricProductMatrix firstSource secondSource
  let secondThirdSource :=
    geometricProductMatrix secondSource thirdSource
  have firstEquivalent := matrix_equivalent_geometricOfNamed first
  have secondEquivalent := matrix_equivalent_geometricOfNamed second
  have thirdEquivalent := matrix_equivalent_geometricOfNamed third
  have firstSecondEquivalent : MatrixEquivalent
      (matrixMul first second)
      (geometricNamedMatrix firstSecondSource) := by
    exact matrixMul_equivalent_geometricProductMatrix first second
      firstSource secondSource
      (fun row column => by
        simpa only [geometricNamedMatrix_apply] using
          firstEquivalent row column)
      (fun row column => by
        simpa only [geometricNamedMatrix_apply] using
          secondEquivalent row column)
  have secondThirdEquivalent : MatrixEquivalent
      (matrixMul second third)
      (geometricNamedMatrix secondThirdSource) := by
    exact matrixMul_equivalent_geometricProductMatrix second third
      secondSource thirdSource
      (fun row column => by
        simpa only [geometricNamedMatrix_apply] using
          secondEquivalent row column)
      (fun row column => by
        simpa only [geometricNamedMatrix_apply] using
          thirdEquivalent row column)
  have leftEquivalent : MatrixEquivalent
      (matrixMul (matrixMul first second) third)
      (geometricNamedMatrix
        (geometricProductMatrix firstSecondSource thirdSource)) :=
    matrixMul_equivalent_geometricProductMatrix
      (matrixMul first second) third firstSecondSource thirdSource
      (fun row column => by
        simpa only [geometricNamedMatrix_apply] using
          firstSecondEquivalent row column)
      (fun row column => by
        simpa only [geometricNamedMatrix_apply] using
          thirdEquivalent row column)
  have rightEquivalent : MatrixEquivalent
      (matrixMul first (matrixMul second third))
      (geometricNamedMatrix
        (geometricProductMatrix firstSource secondThirdSource)) :=
    matrixMul_equivalent_geometricProductMatrix
      first (matrixMul second third) firstSource secondThirdSource
      (fun row column => by
        simpa only [geometricNamedMatrix_apply] using
          firstEquivalent row column)
      (fun row column => by
        simpa only [geometricNamedMatrix_apply] using
          secondThirdEquivalent row column)
  exact MatrixEquivalent.trans leftEquivalent
    (MatrixEquivalent.trans
      (geometricProductMatrix_assoc firstSource secondSource thirdSource)
      (MatrixEquivalent.symm rightEquivalent))

/-- Transposition reverses actual finite CCL matrix multiplication up to
operational equality. -/
@[expose] def matrixMul_transpose {size : Nat} (left right : NamedMatrix size) :
    MatrixEquivalent (transpose (matrixMul left right))
      (matrixMul (transpose right) (transpose left)) := by
  let leftSource := geometricMatrixOfNamed left
  let rightSource := geometricMatrixOfNamed right
  have leftSourceEquivalent := matrix_equivalent_geometricOfNamed left
  have rightSourceEquivalent := matrix_equivalent_geometricOfNamed right
  have normalizeLeft : MatrixEquivalent
      (transpose (matrixMul left right))
      (geometricNamedMatrix
        (geometricTranspose
          (geometricProductMatrix leftSource rightSource))) := by
    intro row column
    rw [transpose_apply, geometricNamedMatrix_apply,
      geometricTranspose_apply, geometricProductMatrix_apply]
    exact matrixMul_equivalent_geometricProduct left right
      leftSource rightSource
      (fun sourceRow sourceColumn => by
        simpa only [geometricNamedMatrix_apply] using
          leftSourceEquivalent sourceRow sourceColumn)
      (fun sourceRow sourceColumn => by
        simpa only [geometricNamedMatrix_apply] using
          rightSourceEquivalent sourceRow sourceColumn)
      column row
  have transposeSamples : MatrixEquivalent
      (geometricNamedMatrix
        (geometricTranspose
          (geometricProductMatrix leftSource rightSource)))
      (geometricNamedMatrix
        (geometricProductMatrix (geometricTranspose rightSource)
          (geometricTranspose leftSource))) := by
    intro row column
    rw [geometricNamedMatrix_apply, geometricNamedMatrix_apply,
      geometricTranspose_apply]
    apply geometricNamed_equivalent_of_samples
    intro index
    exact geometricProduct_transpose_sample leftSource rightSource
      row column index
  have normalizeRight : MatrixEquivalent
      (matrixMul (transpose right) (transpose left))
      (geometricNamedMatrix
        (geometricProductMatrix (geometricTranspose rightSource)
          (geometricTranspose leftSource))) :=
    matrixMul_equivalent_geometricProductMatrix
      (transpose right) (transpose left)
      (geometricTranspose rightSource) (geometricTranspose leftSource)
      (fun row column => by
        rw [transpose_apply, geometricTranspose_apply]
        simpa only [geometricNamedMatrix_apply] using
          rightSourceEquivalent column row)
      (fun row column => by
        rw [transpose_apply, geometricTranspose_apply]
        simpa only [geometricNamedMatrix_apply] using
          leftSourceEquivalent column row)
  exact MatrixEquivalent.trans normalizeLeft
    (MatrixEquivalent.trans transposeSamples
      (MatrixEquivalent.symm normalizeRight))

/-- Multiply every matrix entry by one coherent scalar on the left. -/
@[expose] def scalarMul {size : Nat} (scalar : CoherentNamed)
    (matrix : NamedMatrix size) : NamedMatrix size :=
  SquareMatrix.matrixOfFn fun row column =>
    Gaussian.Name.Coherent.CoherentNamed.mul scalar (matrix row column)

/-- Read the original left scalar multiplication of the retained named matrix entry. -/
@[simp] theorem scalarMul_apply {size : Nat} (scalar : CoherentNamed)
    (matrix : NamedMatrix size) (row column : Fin size) :
    scalarMul scalar matrix row column =
      Gaussian.Name.Coherent.CoherentNamed.mul scalar
        (matrix row column) :=
  SquareMatrix.matrixOfFn_apply _ _ _

/-- Synchronized geometric scaled identity. -/
@[expose] def geometricScaleIdentity {size : Nat}
    (scalar : GeometricApproximation) : GeometricMatrix size :=
  SquareMatrix.matrixOfFn fun row column =>
    if row = column then scalar
    else Gaussian.Geometric.GeometricApproximation.exact 0

/-- Read the diagonal geometric scalar or exact off-diagonal zero of the synchronized scaled identity. -/
@[simp] theorem geometricScaleIdentity_apply {size : Nat}
    (scalar : GeometricApproximation) (row column : Fin size) :
    geometricScaleIdentity scalar row column =
      if row = column then scalar
      else Gaussian.Geometric.GeometricApproximation.exact 0 :=
  SquareMatrix.matrixOfFn_apply _ _ _

/-- Every synchronized sample of a geometric scaled identity is the exact
finite Gaussian scaled identity. -/
theorem sample_geometricScaleIdentity {size : Nat}
    (scalar : GeometricApproximation) (index : Nat) :
    Matrix.sampleMatrix
        (geometricScaleIdentity (size := size) scalar) index =
      SquareMatrix.Multiplication.scaleIdentity (n := size)
        (scalar.sample index) := by
  apply SquareMatrix.matrix_ext
  intro row column
  rw [Matrix.sampleMatrix_apply,
    geometricScaleIdentity_apply,
    SquareMatrix.Multiplication.scaleIdentity_apply]
  by_cases equal : row = column
  · rewrite [if_pos equal, if_pos equal]
    exact Eq.refl _
  · rewrite [if_neg equal, if_neg equal]
    exact Eq.refl _

/-- The named scaled identity realizes the synchronized scaled identity of
the scalar's canonical sampler. -/
@[expose] def scaleIdentity_equivalent_geometric {size : Nat}
    (scalar : CoherentNamed) :
    MatrixEquivalent (scaleIdentity (size := size) scalar)
      (geometricNamedMatrix (size := size)
        (geometricScaleIdentity (size := size)
          (Gaussian.Geometric.GeometricApproximation.ofNamed
            scalar.name))) := by
  intro row column
  rw [scaleIdentity_apply, geometricNamedMatrix_apply,
    geometricScaleIdentity_apply]
  by_cases equal : row = column
  · simp only [if_pos equal]
    exact named_equivalent_geometricOfNamed scalar
  · simp only [if_neg equal]
    exact Gaussian.Equivalence.NamedEquivalent.refl _

/-- A scaled identity on the left acts by entrywise scalar multiplication at
the operational finite-request layer. -/
@[expose] def scaleIdentity_mul {size : Nat} (scalar : CoherentNamed)
    (matrix : NamedMatrix size) :
    MatrixEquivalent (matrixMul (scaleIdentity scalar) matrix)
      (scalarMul scalar matrix) := by
  let scalarSource :=
    Gaussian.Geometric.GeometricApproximation.ofNamed
      scalar.name
  let identitySource : GeometricMatrix size :=
    geometricScaleIdentity scalarSource
  let matrixSource := geometricMatrixOfNamed matrix
  have normalizeProduct : MatrixEquivalent
      (matrixMul (scaleIdentity scalar) matrix)
      (geometricNamedMatrix
        (geometricProductMatrix identitySource matrixSource)) :=
    matrixMul_equivalent_geometricProductMatrix
      (scaleIdentity scalar) matrix identitySource matrixSource
      (fun row column => by
        simpa only [geometricNamedMatrix_apply,
          identitySource, scalarSource] using
          scaleIdentity_equivalent_geometric scalar row column)
      (fun row column => by
        simpa only [geometricNamedMatrix_apply] using
          matrix_equivalent_geometricOfNamed matrix row column)
  intro row column
  have productSamples : forall index,
      (geometricProductMatrix identitySource matrixSource row column).sample
          index =
        (Gaussian.Geometric.GeometricApproximation.mul
          scalarSource (matrixSource row column)).sample index := by
    intro index
    calc
      (geometricProductMatrix identitySource matrixSource row column).sample
          index =
          SquareMatrix.Multiplication.mul
            (Matrix.sampleMatrix
              identitySource index)
            (Matrix.sampleMatrix
              matrixSource index) row column :=
        by
          rw [geometricProductMatrix_apply]
          exact geometricProductEntry_sample identitySource matrixSource
            row column index
      _ = scalarSource.sample index *
          (Matrix.sampleMatrix
            matrixSource index) row column := by
        rw [show Matrix.sampleMatrix
              identitySource index =
              SquareMatrix.Multiplication.scaleIdentity
                (scalarSource.sample index) by
          exact sample_geometricScaleIdentity scalarSource index]
        simpa only [SquareMatrix.matrixOfFn_apply] using
          SquareMatrix.matrix_eq_at
            (SquareMatrix.Multiplication.scaleIdentity_mul
              (scalarSource.sample index)
              (Matrix.sampleMatrix
                matrixSource index)) row column
      _ = scalarSource.sample index *
          (matrixSource row column).sample index := by
        rw [Matrix.sampleMatrix_apply]
      _ = (Gaussian.Geometric.GeometricApproximation.mul
          scalarSource (matrixSource row column)).sample index := rfl
  have geometricProductEquivalent : NamedEquivalent
      (geometricNamed
        (geometricProductMatrix identitySource matrixSource row column)).name
      (geometricNamed
        (Gaussian.Geometric.GeometricApproximation.mul
          scalarSource (matrixSource row column))).name :=
    geometricNamed_equivalent_of_samples _ _ productSamples
  have normalizeEntry : NamedEquivalent
      (scalarMul scalar matrix row column).name
      (geometricNamed
        (Gaussian.Geometric.GeometricApproximation.mul
          scalarSource (matrixSource row column))).name := by
    rw [scalarMul_apply]
    exact coherentMul_equivalent_geometricMul scalar (matrix row column)
      scalarSource (matrixSource row column)
      (by
          simpa only [scalarSource]
            using named_equivalent_geometricOfNamed scalar)
      (by
          simpa only [matrixSource, geometricMatrixOfNamed_apply]
            using named_equivalent_geometricOfNamed (matrix row column))
  exact Gaussian.Equivalence.NamedEquivalent.trans
    (middle := (geometricNamed (geometricProductMatrix identitySource matrixSource row column)).name)
    (by
        simpa only [geometricNamedMatrix_apply, geometricProductMatrix_apply]
          using normalizeProduct row column)
    (Gaussian.Equivalence.NamedEquivalent.trans
      (middle := (geometricNamed
        (Gaussian.Geometric.GeometricApproximation.mul
          scalarSource (matrixSource row column))).name)
      (by
          simpa only [geometricProductMatrix_apply]
            using geometricProductEquivalent)
      (Gaussian.Equivalence.NamedEquivalent.symm normalizeEntry))

/-- A scaled identity on the right has the same entrywise scalar action; the
finite Gaussian commutativity step is made explicit. -/
@[expose] def matrixMul_scaleIdentity {size : Nat} (matrix : NamedMatrix size)
    (scalar : CoherentNamed) :
    MatrixEquivalent (matrixMul matrix (scaleIdentity scalar))
      (scalarMul scalar matrix) := by
  let scalarSource :=
    Gaussian.Geometric.GeometricApproximation.ofNamed
      scalar.name
  let identitySource : GeometricMatrix size :=
    geometricScaleIdentity scalarSource
  let matrixSource := geometricMatrixOfNamed matrix
  have normalizeProduct : MatrixEquivalent
      (matrixMul matrix (scaleIdentity scalar))
      (geometricNamedMatrix
        (geometricProductMatrix matrixSource identitySource)) :=
    matrixMul_equivalent_geometricProductMatrix
      matrix (scaleIdentity scalar) matrixSource identitySource
      (fun row column => by
        simpa only [geometricNamedMatrix_apply] using
          matrix_equivalent_geometricOfNamed matrix row column)
      (fun row column => by
        simpa only [geometricNamedMatrix_apply,
          identitySource, scalarSource] using
          scaleIdentity_equivalent_geometric scalar row column)
  intro row column
  have productSamples : forall index,
      (geometricProductMatrix matrixSource identitySource row column).sample
          index =
        (Gaussian.Geometric.GeometricApproximation.mul
          scalarSource (matrixSource row column)).sample index := by
    intro index
    calc
      (geometricProductMatrix matrixSource identitySource row column).sample
          index =
          SquareMatrix.Multiplication.mul
            (Matrix.sampleMatrix
              matrixSource index)
            (Matrix.sampleMatrix
              identitySource index) row column :=
        by
          rw [geometricProductMatrix_apply]
          exact geometricProductEntry_sample matrixSource identitySource
            row column index
      _ = (Matrix.sampleMatrix
            matrixSource index) row column * scalarSource.sample index := by
        rw [show Matrix.sampleMatrix
              identitySource index =
              SquareMatrix.Multiplication.scaleIdentity
                (scalarSource.sample index) by
          exact sample_geometricScaleIdentity scalarSource index]
        simpa only [SquareMatrix.matrixOfFn_apply] using
          SquareMatrix.matrix_eq_at
            (SquareMatrix.Multiplication.mul_scaleIdentity
              (Matrix.sampleMatrix
                matrixSource index) (scalarSource.sample index)) row column
      _ = (matrixSource row column).sample index * scalarSource.sample index := by
        rw [Matrix.sampleMatrix_apply]
      _ = scalarSource.sample index * (matrixSource row column).sample index :=
        Gaussian.Basic.mul_comm _ _
      _ = (Gaussian.Geometric.GeometricApproximation.mul
          scalarSource (matrixSource row column)).sample index := rfl
  have geometricProductEquivalent : NamedEquivalent
      (geometricNamed
        (geometricProductMatrix matrixSource identitySource row column)).name
      (geometricNamed
        (Gaussian.Geometric.GeometricApproximation.mul
          scalarSource (matrixSource row column))).name :=
    geometricNamed_equivalent_of_samples _ _ productSamples
  have normalizeEntry : NamedEquivalent
      (scalarMul scalar matrix row column).name
      (geometricNamed
        (Gaussian.Geometric.GeometricApproximation.mul
          scalarSource (matrixSource row column))).name := by
    rw [scalarMul_apply]
    exact coherentMul_equivalent_geometricMul scalar (matrix row column)
      scalarSource (matrixSource row column)
      (by
          simpa only [scalarSource]
            using named_equivalent_geometricOfNamed scalar)
      (by
          simpa only [matrixSource, geometricMatrixOfNamed_apply]
            using named_equivalent_geometricOfNamed (matrix row column))
  exact Gaussian.Equivalence.NamedEquivalent.trans
    (middle := (geometricNamed (geometricProductMatrix matrixSource identitySource row column)).name)
    (by
        simpa only [geometricNamedMatrix_apply, geometricProductMatrix_apply]
          using normalizeProduct row column)
    (Gaussian.Equivalence.NamedEquivalent.trans
      (middle := (geometricNamed
        (Gaussian.Geometric.GeometricApproximation.mul
          scalarSource (matrixSource row column))).name)
      (by
          simpa only [geometricProductMatrix_apply]
            using geometricProductEquivalent)
      (Gaussian.Equivalence.NamedEquivalent.symm normalizeEntry))

/-- Transposition fixes a scaled identity operationally. -/
@[expose] def transpose_scaleIdentity {size : Nat} (scalar : CoherentNamed) :
    MatrixEquivalent
      (transpose (size := size) (scaleIdentity (size := size) scalar))
      (scaleIdentity (size := size) scalar) := by
  intro row column
  rw [transpose_apply, scaleIdentity_apply, scaleIdentity_apply]
  by_cases equal : row = column
  · subst column
    exact Gaussian.Equivalence.NamedEquivalent.refl _
  · simp only [if_neg equal, if_neg (Ne.symm equal)]
    exact Gaussian.Equivalence.NamedEquivalent.refl _

/-- The synchronized left product is the canonical scaled identity at every
finite source index. -/
theorem left_geometric_sample_identity {size : Nat}
    (matrix : NamedMatrix size) (index : Nat) (row column : Fin size) :
    (geometricProductEntry (canonicalScaledInverse matrix).inverse
        (geometricMatrixOfNamed matrix) row column).sample index =
      if row = column then
        (canonicalScaledInverse matrix).scalar.sample index else 0 := by
  let source := geometricMatrixOfNamed matrix
  let computed := canonicalScaledInverse matrix
  let sampled :=
    Matrix.sampleMatrix source index
  calc
    (geometricProductEntry computed.inverse source row column).sample index =
        SquareMatrix.Multiplication.mul
          (Matrix.sampleMatrix
            computed.inverse index) sampled row column :=
      geometricProductEntry_sample computed.inverse source row column index
    _ = SquareMatrix.Multiplication.mul
          (SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse
            sampled).inverse
          sampled row column := by
      rw [show Matrix.sampleMatrix
          computed.inverse index =
            (SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse
              sampled).inverse by
        exact
          (SquareMatrix.Inverse.PivotedScaledInverse.completeApproximation_sample
            source index).2]
    _ = SquareMatrix.Multiplication.scaleIdentity
          (SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse
            sampled).scalar
          row column :=
      SquareMatrix.matrix_eq_at
        (SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse_left_identity
          sampled)
        row column
    _ = if row = column then
          (SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse
            sampled).scalar else 0 :=
      SquareMatrix.Multiplication.scaleIdentity_apply _ row column
    _ = if row = column then computed.scalar.sample index else 0 := by
      by_cases equal : row = column
      · simp only [if_pos equal]
        exact
          (SquareMatrix.Inverse.PivotedScaledInverse.completeApproximation_sample
            source index).1.symm
      · rewrite [if_neg equal, if_neg equal]
        exact Eq.refl _

/-- The synchronized right product satisfies the symmetric identity. -/
theorem right_geometric_sample_identity {size : Nat}
    (matrix : NamedMatrix size) (index : Nat) (row column : Fin size) :
    (geometricProductEntry (geometricMatrixOfNamed matrix)
        (canonicalScaledInverse matrix).inverse row column).sample index =
      if row = column then
        (canonicalScaledInverse matrix).scalar.sample index else 0 := by
  let source := geometricMatrixOfNamed matrix
  let computed := canonicalScaledInverse matrix
  let sampled :=
    Matrix.sampleMatrix source index
  calc
    (geometricProductEntry source computed.inverse row column).sample index =
        SquareMatrix.Multiplication.mul sampled
          (Matrix.sampleMatrix
            computed.inverse index) row column :=
      geometricProductEntry_sample source computed.inverse row column index
    _ = SquareMatrix.Multiplication.mul sampled
          (SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse
            sampled).inverse
          row column := by
      rw [show Matrix.sampleMatrix
          computed.inverse index =
            (SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse
              sampled).inverse by
        exact
          (SquareMatrix.Inverse.PivotedScaledInverse.completeApproximation_sample
            source index).2]
    _ = SquareMatrix.Multiplication.scaleIdentity
          (SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse
            sampled).scalar
          row column :=
      SquareMatrix.matrix_eq_at
        (SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse_right_identity
          sampled)
        row column
    _ = if row = column then
          (SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse
            sampled).scalar else 0 :=
      SquareMatrix.Multiplication.scaleIdentity_apply _ row column
    _ = if row = column then computed.scalar.sample index else 0 := by
      by_cases equal : row = column
      · simp only [if_pos equal]
        exact
          (SquareMatrix.Inverse.PivotedScaledInverse.completeApproximation_sample
            source index).1.symm
      · rewrite [if_neg equal, if_neg equal]
        exact Eq.refl _

/-- The left scaled-inverse identity for the unprepared canonical scalar is
derived from the total synchronized construction and the generic finite
Gaussian matrix theorem. -/
@[expose] def left_identity_canonical {size : Nat} {matrix : NamedMatrix size}
    (inverse : ScaledInverseCertificate matrix) (row column : Fin size) :
    NamedEquivalent (matrixMul inverse.adjugate matrix row column).name
      (scaleIdentity (canonicalInverseScalar matrix) row column).name := by
  let source := geometricMatrixOfNamed matrix
  let computed := canonicalScaledInverse matrix
  have productEquivalent : NamedEquivalent
      (matrixMul inverse.adjugate matrix row column).name
      (geometricNamed
        (geometricProductEntry computed.inverse source row column)).name :=
    matrixMul_equivalent_geometricProduct
      inverse.adjugate matrix computed.inverse source
      (fun leftRow leftColumn => by
        simpa only [adjugate, canonicalAdjugate_apply, computed,
          canonicalScaledInverse] using
          Gaussian.Equivalence.NamedEquivalent.refl
            (geometricNamed
              ((SquareMatrix.Inverse.PivotedScaledInverse.completeApproximation
                (geometricMatrixOfNamed matrix)).inverse
                  leftRow leftColumn)).name)
      (fun rightRow rightColumn => by
        simpa only [source, geometricMatrixOfNamed_apply] using
          named_equivalent_geometricOfNamed
            (matrix rightRow rightColumn))
      row column
  apply Gaussian.Equivalence.NamedEquivalent.trans productEquivalent
  by_cases equal : row = column
  · subst column
    rw [scaleIdentity_apply, if_pos rfl]
    apply geometricNamed_equivalent_of_samples
    intro index
    have identity := left_geometric_sample_identity matrix index row row
    rewrite [if_pos (Eq.refl row)] at identity
    exact identity
  · rw [scaleIdentity_apply, if_neg equal]
    apply geometricNamed_equivalent_of_samples
    intro index
    have identity := left_geometric_sample_identity matrix index row column
    rw [if_neg equal] at identity
    exact identity

/-- The corresponding right identity for the unprepared scalar. -/
@[expose] def right_identity_canonical {size : Nat} {matrix : NamedMatrix size}
    (inverse : ScaledInverseCertificate matrix) (row column : Fin size) :
    NamedEquivalent (matrixMul matrix inverse.adjugate row column).name
      (scaleIdentity (canonicalInverseScalar matrix) row column).name := by
  let source := geometricMatrixOfNamed matrix
  let computed := canonicalScaledInverse matrix
  have productEquivalent : NamedEquivalent
      (matrixMul matrix inverse.adjugate row column).name
      (geometricNamed
        (geometricProductEntry source computed.inverse row column)).name :=
    matrixMul_equivalent_geometricProduct
      matrix inverse.adjugate source computed.inverse
      (fun leftRow leftColumn => by
        simpa only [source, geometricMatrixOfNamed_apply] using
          named_equivalent_geometricOfNamed
            (matrix leftRow leftColumn))
      (fun rightRow rightColumn => by
        simpa only [adjugate, canonicalAdjugate_apply, computed,
          canonicalScaledInverse] using
          Gaussian.Equivalence.NamedEquivalent.refl
            (geometricNamed
              ((SquareMatrix.Inverse.PivotedScaledInverse.completeApproximation
                (geometricMatrixOfNamed matrix)).inverse
                  rightRow rightColumn)).name)
      row column
  apply Gaussian.Equivalence.NamedEquivalent.trans productEquivalent
  by_cases equal : row = column
  · subst column
    rw [scaleIdentity_apply, if_pos rfl]
    apply geometricNamed_equivalent_of_samples
    intro index
    have identity := right_geometric_sample_identity matrix index row row
    rewrite [if_pos (Eq.refl row)] at identity
    exact identity
  · rw [scaleIdentity_apply, if_neg equal]
    apply geometricNamed_equivalent_of_samples
    intro index
    have identity := right_geometric_sample_identity matrix index row column
    rw [if_neg equal] at identity
    exact identity

/-- Operational equality of scalar names lifts entrywise to their scaled
identity matrices. -/
@[expose] def scaleIdentity_respects {size : Nat} (left right : CoherentNamed)
    (equivalent : NamedEquivalent left.name right.name) :
    MatrixEquivalent (scaleIdentity (size := size) left)
      (scaleIdentity (size := size) right) := by
  intro row column
  rw [scaleIdentity_apply, scaleIdentity_apply]
  by_cases equal : row = column
  · simp only [if_pos equal]
    exact equivalent
  · simp only [if_neg equal]
    exact Gaussian.Equivalence.NamedEquivalent.refl _

/-- Apartification preserves the left scaled-inverse identity while making
the scalar safe for productive reciprocal construction. -/
@[expose] def left_identity {size : Nat} {matrix : NamedMatrix size}
    (inverse : ScaledInverseCertificate matrix) (row column : Fin size) :
    NamedEquivalent (matrixMul inverse.adjugate matrix row column).name
      (scaleIdentity inverse.scalar row column).name :=
  Gaussian.Equivalence.NamedEquivalent.trans
    (left_identity_canonical inverse row column)
    (scaleIdentity_respects (size := size)
      (canonicalInverseScalar matrix) inverse.scalar
      inverse.canonicalScalarEquivalent row column)

/-- The prepared scalar likewise preserves the right scaled-inverse
identity. -/
@[expose] def right_identity {size : Nat} {matrix : NamedMatrix size}
    (inverse : ScaledInverseCertificate matrix) (row column : Fin size) :
    NamedEquivalent (matrixMul matrix inverse.adjugate row column).name
      (scaleIdentity inverse.scalar row column).name :=
  Gaussian.Equivalence.NamedEquivalent.trans
    (right_identity_canonical inverse row column)
    (scaleIdentity_respects (size := size)
      (canonicalInverseScalar matrix) inverse.scalar
      inverse.canonicalScalarEquivalent row column)

end ScaledInverseCertificate

/-- The one shared reciprocal of the fraction-free inverse scalar. -/
@[expose] def inverseScalar {size : Nat} {matrix : NamedMatrix size}
    (inverse : ScaledInverseCertificate matrix) : CoherentNamed :=
  Gaussian.Name.Coherent.CoherentNamed.div
    (Gaussian.Name.Coherent.CoherentNamed.Coherence.exact 1)
    inverse.scalar inverse.scalarApart

/-- Construct `A^{-1}B` entrywise as `(adj(A) B) * (1 / det(A))`.
Factoring out one shared reciprocal makes operational congruence of normalized
entries a direct consequence of multiplication congruence. -/
@[expose] def normalize {size : Nat} (a b : NamedMatrix size)
    (inverse : ScaledInverseCertificate a) : NamedMatrix size :=
  let adjugate := inverse.adjugate
  let numerator := matrixMul adjugate b
  let reciprocal := inverseScalar inverse
  SquareMatrix.matrixOfFn fun row column =>
    Gaussian.Name.Coherent.CoherentNamed.mul
      (numerator row column) reciprocal

/-- Read a normalized entry as its original adjugate-product numerator times the shared retained scalar reciprocal. -/
@[simp] theorem normalize_apply {size : Nat} (a b : NamedMatrix size)
    (inverse : ScaledInverseCertificate a) (row column : Fin size) :
    normalize a b inverse row column =
      Gaussian.Name.Coherent.CoherentNamed.mul
        (matrixMul inverse.adjugate b row column)
        (inverseScalar inverse) := by
  exact SquareMatrix.matrixOfFn_apply _ _ _

set_option genInjectivity false in
/-- Period data plus the finite nondegeneracy certificate needed to construct
its normalized period matrix. -/
structure NormalizedPeriodData {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) extends PeriodData curve where
  /-- The retained scaled-inverse certificate for this exact original A-period matrix. -/ aInverse :
    ScaledInverseCertificate toPeriodData.aMatrix

constructive_injectivity NormalizedPeriodData

namespace NormalizedPeriodData

/-- Form normalized period data from any operationally valid fraction-free
inverse presentation, including one obtained by certified tail deletion. -/
@[expose] def ofScaledInverse {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverse : ScaledInverseCertificate data.aMatrix) :
    NormalizedPeriodData curve where
  toPeriodData := data
  aInverse := inverse

/-- Normalization retains this exact raw period owner. -/
theorem ofScaledInverse_periodData {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (inverse : ScaledInverseCertificate data.aMatrix) :
    (ofScaledInverse data inverse).toPeriodData = data := rfl

/-- The displayed inverse is retained, including its actual scalar source. -/
theorem ofScaledInverse_aInverse {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (inverse : ScaledInverseCertificate data.aMatrix) :
    (ofScaledInverse data inverse).aInverse = inverse := rfl

/-- Construct the normalized period matrix from the original A/B owners and retained inverse certificate. -/
@[expose] def omega {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : NormalizedPeriodData curve) : NamedMatrix genus :=
  normalize data.toPeriodData.aMatrix data.toPeriodData.bMatrix data.aInverse

set_option genInjectivity false in
/-- Operational symmetry is the finite constructive first bilinear relation. -/
structure SymmetryCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (data : NormalizedPeriodData curve) where
  /-- Operational equivalence between every retained normalized entry and its transposed entry. -/ symmetric : forall
    row column : Fin genus,
    NamedEquivalent (data.omega row column).name
      (data.omega column row).name

constructive_injectivity SymmetryCertificate

set_option genInjectivity false in
/-- Fraction-free form of the first bilinear relation after applying the
canonically derived adjugate: the numerator `adj(A) B` is operationally
symmetric. -/
structure NumeratorSymmetryCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (data : NormalizedPeriodData curve) where
  /-- Operational equivalence between each original adjugate-product numerator and its transposed entry. -/ symmetric :
    forall row column : Fin genus,
    NamedEquivalent
      (matrixMul data.aInverse.adjugate data.toPeriodData.bMatrix
        row column).name
      (matrixMul data.aInverse.adjugate data.toPeriodData.bMatrix
        column row).name

constructive_injectivity NumeratorSymmetryCertificate

/-- Numerator symmetry implies symmetry of the normalized period matrix by
multiplying both entries by the same persistent reciprocal scalar. -/
@[expose] def symmetryOfNumerator {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (data : NormalizedPeriodData curve)
    (certificate : NumeratorSymmetryCertificate data) :
    SymmetryCertificate data where
  symmetric := by
    intro row column
    simpa only [omega, normalize_apply,
      Gaussian.Name.Coherent.CoherentNamed.mul] using
      Gaussian.Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects
        (matrixMul data.aInverse.adjugate data.toPeriodData.bMatrix row column)
        (matrixMul data.aInverse.adjugate data.toPeriodData.bMatrix column row)
        (inverseScalar data.aInverse) (inverseScalar data.aInverse)
        (certificate.symmetric row column)
        (Gaussian.Equivalence.NamedEquivalent.refl
          (inverseScalar data.aInverse).name)

/-- One shared finite table for the normalized period matrix. -/
@[expose] def omegaTable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : NormalizedPeriodData curve) : Gaussian.Table.Basic.ChannelTable :=
  ⟨PeriodData.matrixChannels data.omega⟩

/-- Every retained normalized period entry occurs in its original shared request table. -/
theorem omegaEntry_mem_table {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (data : NormalizedPeriodData curve)
    (row column : Fin genus) :
    data.omega row column ∈ data.omegaTable.channels :=
  PeriodData.matrixEntry_mem_channels data.omega row column

/-- Every normalized entry answers a finite shared-table request with its
enclosure, allowance, persistent prefix, and exact parser certificate. -/
theorem omegaEntry_sharedRequest {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (data : NormalizedPeriodData curve)
    (row column : Fin genus)
    (target : Rat.Fraction.Rational) (positive : 0 < target)
    (count : Nat) :
    Gaussian.Table.CCL.Request.RequestContract data.omegaTable.channels
      (data.omega row column) target positive count :=
  data.omegaTable.member_bitstream_and_allowance
    (data.omegaEntry_mem_table row column) target positive count

/-- Refine the original normalized entry through its shared table at the supplied positive rational target. -/
@[expose] def refinedOmegaEntry {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (data : NormalizedPeriodData curve)
    (target : Rat.Fraction.Rational) (positive : 0 < target)
    (row column : Fin genus) : Gaussian.Name.Basic.Named :=
  Gaussian.Table.Request.sharedName data.omegaTable.channels
    (data.omega row column) target positive

/-- Retain one normalized entry's shared refinement and evaluated ball.

The request is indexed by the original normalized matrix, its ordered channel
table, bounded row and column, and positive target. Both numerical readings
and their strict accuracy certificate come from the same returned ball. -/
@[expose] def prepareOmegaEntry {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (data : NormalizedPeriodData curve)
    (target : Rat.Fraction.Rational) (positive : 0 < target) (row column : Fin genus) :
    Gaussian.Table.Request.PreparedEntry data.omegaTable.channels (data.omega row column) target positive :=
  Gaussian.Table.Request.prepareEntry data.omegaTable.channels (data.omega row column) target positive

/-- The prepared entry retains exactly the original shared normalized-entry name. -/
theorem prepareOmegaEntry_name {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (data : NormalizedPeriodData curve)
    (target : Rat.Fraction.Rational) (positive : 0 < target) (row column : Fin genus) :
    (data.prepareOmegaEntry target positive row column).name = data.refinedOmegaEntry target positive row column :=
  (data.prepareOmegaEntry target positive row column).name_eq

/-- The prepared ball reads back to the ball of the original normalized-entry request. -/
theorem prepareOmegaEntry_ball {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (data : NormalizedPeriodData curve)
    (target : Rat.Fraction.Rational) (positive : 0 < target) (row column : Fin genus) :
    (data.prepareOmegaEntry target positive row column).ball =
      (data.refinedOmegaEntry target positive row column).process.ball
        (data.refinedOmegaEntry target positive row column).state :=
  (data.prepareOmegaEntry target positive row column).ball_readback

/-- Read the exact Gaussian center returned by the shared normalized-entry request. -/
@[expose] def omegaCenter {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : NormalizedPeriodData curve)
    (target : Rat.Fraction.Rational) (positive : 0 < target)
    (row column : Fin genus) : Gaussian.Basic.Canonical :=
  let entry := data.refinedOmegaEntry target positive row column
  (entry.process.ball entry.state).center

/-- Read the squared radius returned by the original shared normalized-entry request. -/
@[expose] def omegaRadiusSq {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : NormalizedPeriodData curve)
    (target : Rat.Fraction.Rational) (positive : 0 < target)
    (row column : Fin genus) : Rat.Fraction.Rational :=
  let entry := data.refinedOmegaEntry target positive row column
  (entry.process.ball entry.state).radiusSq

/-- Every returned normalized-entry squared radius is nonnegative. -/
theorem omegaRadiusSq_nonneg {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (data : NormalizedPeriodData curve)
    (target : Rat.Fraction.Rational) (positive : 0 < target)
    (row column : Fin genus) :
    0 <= data.omegaRadiusSq target positive row column := by
  unfold omegaRadiusSq
  exact ((data.refinedOmegaEntry target positive row column).process.ball
    (data.refinedOmegaEntry target positive row column).state).radiusSq_nonneg

/-- The shared finite request makes every displayed squared entry radius
strictly smaller than its rational request target. -/
theorem omegaRadiusSq_lt_target {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (data : NormalizedPeriodData curve)
    (target : Rat.Fraction.Rational) (positive : 0 < target)
    (row column : Fin genus) :
    data.omegaRadiusSq target positive row column < target := by
  unfold omegaRadiusSq refinedOmegaEntry
  exact Gaussian.Table.Request.sharedName_radius_lt
    data.omegaTable.channels (data.omega row column) positive

/-- The prepared center preserves the original normalized-entry scalar readback. -/
theorem prepareOmegaEntry_center {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (data : NormalizedPeriodData curve)
    (target : Rat.Fraction.Rational) (positive : 0 < target) (row column : Fin genus) :
    (data.prepareOmegaEntry target positive row column).center = data.omegaCenter target positive row column :=
  congrArg Gaussian.Enclosure.Ball.center (data.prepareOmegaEntry_ball target positive row column)

/-- The prepared radius preserves the original normalized-entry scalar readback. -/
theorem prepareOmegaEntry_radiusSq {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (data : NormalizedPeriodData curve)
    (target : Rat.Fraction.Rational) (positive : 0 < target) (row column : Fin genus) :
    (data.prepareOmegaEntry target positive row column).radiusSq = data.omegaRadiusSq target positive row column :=
  congrArg Gaussian.Enclosure.Ball.radiusSq (data.prepareOmegaEntry_ball target positive row column)

end NormalizedPeriodData

set_option genInjectivity false in
/-- A finite box certificate for one requested positivity check.  It proves
the strict rational lower bound for every matrix of readings consistent with
the finitely returned CCL balls, not for an assumed completed matrix. -/
structure PositiveRequestCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (data : NormalizedPeriodData curve)
    (vector : RationalVector genus) (_nonzero : NonzeroVector vector)
    (target : Coordinate) (positive : 0 < target) where
  /-- The retained positive rational target used by the actual shared matrix refinement. -/ refinementTarget :
    Coordinate
  /-- The retained shared refinement target is strictly positive. -/ refinementPositive : 0 < refinementTarget
  /-- The retained shared refinement target is strictly below the original request. -/ refinement_lt_target :
    refinementTarget < target
  /-- The retained rational strict lower bound for the imaginary quadratic form. -/ epsilon : Coordinate
  /-- The retained quadratic-form lower bound is strictly positive. -/ epsilon_positive : 0 < epsilon
  /-- Every Gaussian matrix compatible with the returned original entry balls satisfies the strict quadratic-form
bound. -/
  compatible_positive : forall candidate : GaussianMatrix genus,
    (forall row column : Fin genus,
      Data.Gaussian.Norm.Basic.normSq
          (candidate row column -
            data.omegaCenter refinementTarget refinementPositive row column) <=
        data.omegaRadiusSq refinementTarget refinementPositive row column) ->
    epsilon < imaginaryQuadraticForm vector candidate

constructive_injectivity PositiveRequestCertificate

namespace PositiveRequestCertificate

/-- In particular, the finite rational centre matrix has the certified
positive lower bound. -/
theorem center_positive {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : NormalizedPeriodData curve} {vector : RationalVector genus}
    {nonzero : NonzeroVector vector} {target : Coordinate}
    {positive : 0 < target}
    (certificate : PositiveRequestCertificate data vector nonzero target positive) :
    certificate.epsilon < imaginaryQuadraticForm vector
      (SquareMatrix.matrixOfFn fun row column =>
        data.omegaCenter certificate.refinementTarget
          certificate.refinementPositive row column) := by
  apply certificate.compatible_positive
  intro row column
  rw [SquareMatrix.matrixOfFn_apply,
    Gaussian.Basic.sub_self,
    Gaussian.Norm.Basic.normSq_zero]
  exact data.omegaRadiusSq_nonneg certificate.refinementTarget
    certificate.refinementPositive row column

end PositiveRequestCertificate

set_option genInjectivity false in
/-- Pointwise constructive positive-definiteness at every finite request. -/
structure PointwisePositivity {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (data : NormalizedPeriodData curve) where
  /-- Produce the retained finite matrix-box positivity certificate for each nonzero rational vector and positive
    request. -/ certify : forall (vector : RationalVector genus) (nonzero : NonzeroVector vector)
    (target : Coordinate) (positive : 0 < target),
    PositiveRequestCertificate data vector nonzero target positive

constructive_injectivity PointwisePositivity

set_option genInjectivity false in
/-- The finite constructive Riemann bilinear relations for the normalized
period matrix. -/
structure BilinearRelationsCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (data : NormalizedPeriodData curve) where
  /-- The retained operational symmetry of the original fraction-free numerator matrix. -/ numeratorSymmetry :
    NormalizedPeriodData.NumeratorSymmetryCertificate data
  /-- The retained finite-request positivity constructor for the original normalized matrix. -/ positivity :
    PointwisePositivity data

constructive_injectivity BilinearRelationsCertificate

namespace BilinearRelationsCertificate

/-- Derive normalized matrix symmetry from the retained numerator symmetry using the original shared reciprocal. -/
@[expose] def symmetry {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : NormalizedPeriodData curve}
    (certificate : BilinearRelationsCertificate data) :
    NormalizedPeriodData.SymmetryCertificate data :=
  data.symmetryOfNumerator certificate.numeratorSymmetry

end BilinearRelationsCertificate

end Purelib.Riemann.Periods.PeriodMatrix
