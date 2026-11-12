module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodCanonical
public import Purelib.Riemann.Periods.WeightedPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Readings.PreparedPrimitiveSamples.Numerator
import Purelib.Tactic.Ring

import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Ordinary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PathChartRoutes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RouteChartRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Surface.Sewing.SewingRetraction
/-! # Actual full-numerator chart comparison and fixed-word mesh allocation

The retained grid word determines the mesh charge before any new
primitive/model observation. Actual Some chart-contact caches pay the
canonical source change on the very same supplied primitive bank.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodCanonical

open Purelib
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation (Data)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential (Ordinary)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.LiftedMesh.PathFaces (MeshWordReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RouteChartRequests (RouteChartRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Cast.Order
open Purelib.Data.Rat.Fraction.Order
open Purelib.Riemann.Readings
open Purelib.Riemann.Periods
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh (PathFaces)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)

/-- The thirty-second share of a positive canonical cochain target is positive. -/
theorem cochainShare_positive {target : Rational} (positive : 0 < target) : 0 < target / 32 :=
  Field.div_pos_direct positive (natCast_pos_direct (n := 32) (Nat.zero_lt_succ 31))

/-- Choose an actual new word target satisfying its independent public target and fixed-grid mesh requirement.

The count is the retained global period word length, fixed before any
primitive-mesh accuracy request. A later fragment count only subdivides
this already chosen positive target through the original per-term rule.
-/
@[expose] def wordAllowance (wordTarget cochainTarget : Rational) (count : Nat) : Rational :=
  min wordTarget (Aggregate.perTerm (cochainTarget / 32) count / 16)

/-- Both positive public targets give a positive internal word allocation. -/
theorem wordAllowance_positive {wordTarget cochainTarget : Rational}
    (wordPositive : 0 < wordTarget) (cochainPositive : 0 < cochainTarget) (count : Nat) :
    0 < wordAllowance wordTarget cochainTarget count :=
  Fraction.Order.Basic.lt_min wordPositive (Field.div_pos_direct
    (Aggregate.perTerm_positive
      (Field.div_pos_direct cochainPositive (natCast_pos_direct (n := 32) (Nat.zero_lt_succ 31))) count)
    (natCast_pos_direct (n := 16) (Nat.zero_lt_succ 15)))

/-- The internal word request preserves the independent public word target. -/
theorem wordAllowance_le (wordTarget cochainTarget : Rational) (count : Nat) :
    wordAllowance wordTarget cochainTarget count ≤ wordTarget := Fraction.Order.Basic.min_le_left _ _

/-- The actual per-fragment tolerance pays the retained fixed-grid count-squared mesh charge.

No count from the budget-dependent rectangular mesh is used. Increasing a
numerical stage alone does not change this bound: the genuine new word
request selects its tolerance before either new observation family.
-/
theorem meshCharge_lt {wordTarget cochainTarget : Rational}
    (wordPositive : 0 < wordTarget) (cochainPositive : 0 < cochainTarget) (count fragments : Nat) :
    Aggregate.countCoordinate count * (Aggregate.countCoordinate count *
      (16 * Aggregate.perTerm (wordAllowance wordTarget cochainTarget count) fragments)) < cochainTarget / 32 := by
  have selectedPositive := wordAllowance_positive wordPositive cochainPositive count
  have localBound := Aggregate.perTerm_le selectedPositive.le fragments
  have chosen : wordAllowance wordTarget cochainTarget count ≤
      Aggregate.perTerm (cochainTarget / 32) count / 16 := Fraction.Order.Basic.min_le_right _ _
  have tolerance : 16 * Aggregate.perTerm (wordAllowance wordTarget cochainTarget count) fragments ≤
      Aggregate.perTerm (cochainTarget / 32) count :=
    (Arithmetic.mul_le_mul_of_nonneg_left_direct (localBound.trans chosen)
      (natCast_pos_direct (n := 16) (Nat.zero_lt_succ 15)).le).trans_eq (by
        rewrite [Fraction.Field.mul_comm]
        exact Fraction.Field.div_mul_cancel_of_ne _ _ (rationalNatCastNonzero (value := 16) (Nat.zero_lt_succ 15)))
  exact Aggregate.count_mul_allowance_lt (Nat.le_refl count)
    (Field.div_pos_direct cochainPositive (natCast_pos_direct (n := 32) (Nat.zero_lt_succ 31))) tolerance

/-- Select a genuine public word target also sufficient for two actual fresh-cycle mesh words.

Both fixed grid-word counts are known before the one P bank. The old
word's subsequent wordAllowance may reduce this target further. No fixed
existing request, tolerance or observation stage is relabelled.
-/
@[expose] def pairedWordTarget (wordTarget freshTarget : Rational) (firstCount lastCount : Nat) : Rational :=
  min wordTarget (min (Aggregate.perTerm freshTarget firstCount / 16)
    (Aggregate.perTerm freshTarget lastCount / 16))

/-- Positive independent word and fresh-cycle targets give a positive actual paired request. -/
theorem pairedWordTarget_positive {wordTarget freshTarget : Rational}
    (wordPositive : 0 < wordTarget) (freshPositive : 0 < freshTarget) (firstCount lastCount : Nat) :
    0 < pairedWordTarget wordTarget freshTarget firstCount lastCount :=
  Fraction.Order.Basic.lt_min wordPositive (Fraction.Order.Basic.lt_min
    (Field.div_pos_direct (Aggregate.perTerm_positive freshPositive firstCount)
      (natCast_pos_direct (n := 16) (Nat.zero_lt_succ 15)))
    (Field.div_pos_direct (Aggregate.perTerm_positive freshPositive lastCount)
      (natCast_pos_direct (n := 16) (Nat.zero_lt_succ 15))))

/-- The genuine paired request preserves its independent public word target. -/
theorem pairedWordTarget_le (wordTarget freshTarget : Rational) (firstCount lastCount : Nat) :
    pairedWordTarget wordTarget freshTarget firstCount lastCount ≤ wordTarget :=
  Fraction.Order.Basic.min_le_left _ _

/-- The first literal fresh word count supplies its actual pre-bank tolerance cap. -/
theorem pairedWordTarget_first (wordTarget freshTarget : Rational) (firstCount lastCount : Nat) :
    pairedWordTarget wordTarget freshTarget firstCount lastCount ≤ Aggregate.perTerm freshTarget firstCount / 16 :=
  (Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)

/-- The second literal fresh word count supplies its independent actual pre-bank tolerance cap. -/
theorem pairedWordTarget_last (wordTarget freshTarget : Rational) (firstCount lastCount : Nat) :
    pairedWordTarget wordTarget freshTarget firstCount lastCount ≤ Aggregate.perTerm freshTarget lastCount / 16 :=
  (Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_right _ _)

/-- An internally selected word request pays the actual count-squared mesh charge at any retained fragment count. -/
theorem meshCharge_of_word_le {wordTarget freshTarget : Rational}
    (wordPositive : 0 < wordTarget) (freshPositive : 0 < freshTarget) (count fragments : Nat)
    (selected : wordTarget ≤ Aggregate.perTerm freshTarget count / 16) :
    Aggregate.countCoordinate count * (Aggregate.countCoordinate count *
      (16 * Aggregate.perTerm wordTarget fragments)) < freshTarget := by
  have tolerance : 16 * Aggregate.perTerm wordTarget fragments ≤ Aggregate.perTerm freshTarget count :=
    (Arithmetic.mul_le_mul_of_nonneg_left_direct
      ((Aggregate.perTerm_le wordPositive.le fragments).trans selected)
      (natCast_pos_direct (n := 16) (Nat.zero_lt_succ 15)).le).trans_eq (by
        rewrite [Fraction.Field.mul_comm]
        exact Fraction.Field.div_mul_cancel_of_ne _ _
          (rationalNatCastNonzero (value := 16) (Nat.zero_lt_succ 15)))
  exact Aggregate.count_mul_allowance_lt (Nat.le_refl count) freshPositive tolerance

/-- The same old-word numerical tolerance pays the FIRST actual fresh mesh count, with no second bank. -/
theorem firstMeshCharge_lt {wordTarget cochainTarget freshTarget : Rational}
    (wordPositive : 0 < wordTarget) (cochainPositive : 0 < cochainTarget) (freshPositive : 0 < freshTarget)
    (oldCount fragments firstCount lastCount : Nat) :
    Aggregate.countCoordinate firstCount * (Aggregate.countCoordinate firstCount *
      (16 * Aggregate.perTerm
        (wordAllowance (pairedWordTarget wordTarget freshTarget firstCount lastCount) cochainTarget oldCount)
        fragments)) < freshTarget :=
  meshCharge_of_word_le
    (wordAllowance_positive (pairedWordTarget_positive wordPositive freshPositive firstCount lastCount)
      cochainPositive oldCount) freshPositive firstCount fragments
    ((wordAllowance_le _ _ oldCount).trans (pairedWordTarget_first wordTarget freshTarget firstCount lastCount))

/-- The SAME actual old-word numerical tolerance pays the full SECOND fresh mesh count independently. -/
theorem lastMeshCharge_lt {wordTarget cochainTarget freshTarget : Rational}
    (wordPositive : 0 < wordTarget) (cochainPositive : 0 < cochainTarget) (freshPositive : 0 < freshTarget)
    (oldCount fragments firstCount lastCount : Nat) :
    Aggregate.countCoordinate lastCount * (Aggregate.countCoordinate lastCount *
      (16 * Aggregate.perTerm
        (wordAllowance (pairedWordTarget wordTarget freshTarget firstCount lastCount) cochainTarget oldCount)
        fragments)) < freshTarget :=
  meshCharge_of_word_le
    (wordAllowance_positive (pairedWordTarget_positive wordPositive freshPositive firstCount lastCount)
      cochainPositive oldCount) freshPositive lastCount fragments
    ((wordAllowance_le _ _ oldCount).trans (pairedWordTarget_last wordTarget freshTarget firstCount lastCount))

/-- Select a genuine source-programme tolerance paying two fresh mesh words and independent public targets.

All counts are fixed original current-grid words. This is a new positive
request, selected before the source/model rule or P bank is observed. Its
sixteenth and quarter are the existing programme comparison's literal
word and cochain requests.
-/
@[expose] def programmeTarget (programmeCap wordTarget cochainTarget freshTarget : Rational)
    (firstCount lastCount : Nat) : Rational :=
  min programmeCap (min (16 * pairedWordTarget wordTarget freshTarget firstCount lastCount)
    (4 * cochainTarget))

/-- Positive independent caps give a positive actual programme request before observations. -/
theorem programmeTarget_positive {programmeCap wordTarget cochainTarget freshTarget : Rational}
    (programmePositive : 0 < programmeCap) (wordPositive : 0 < wordTarget)
    (cochainPositive : 0 < cochainTarget) (freshPositive : 0 < freshTarget) (firstCount lastCount : Nat) :
    0 < programmeTarget programmeCap wordTarget cochainTarget freshTarget firstCount lastCount :=
  Fraction.Order.Basic.lt_min programmePositive (Fraction.Order.Basic.lt_min
    (Arithmetic.mul_pos_direct (natCast_pos_direct (n := 16) (Nat.zero_lt_succ 15))
      (pairedWordTarget_positive wordPositive freshPositive firstCount lastCount))
    (Arithmetic.mul_pos_direct (natCast_pos_direct (n := 4) (Nat.zero_lt_succ 3)) cochainPositive))

/-- The actual programme request preserves the independently supplied programme cap. -/
theorem programmeTarget_le (programmeCap wordTarget cochainTarget freshTarget : Rational)
    (firstCount lastCount : Nat) :
    programmeTarget programmeCap wordTarget cochainTarget freshTarget firstCount lastCount ≤ programmeCap :=
  Fraction.Order.Basic.min_le_left _ _

/-- The original programme's actual sixteenth request pays the two retained fresh mesh caps. -/
theorem programmeTarget_word (programmeCap wordTarget cochainTarget freshTarget : Rational)
    (firstCount lastCount : Nat) :
    (programmeTarget programmeCap wordTarget cochainTarget freshTarget firstCount lastCount / 4) / 4 ≤
      pairedWordTarget wordTarget freshTarget firstCount lastCount := by
  have sixteenPositive := natCast_pos_direct (n := 16) (Nat.zero_lt_succ 15)
  have cap : programmeTarget programmeCap wordTarget cochainTarget freshTarget firstCount lastCount ≤
      16 * pairedWordTarget wordTarget freshTarget firstCount lastCount :=
    (Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)
  have divide : programmeTarget programmeCap wordTarget cochainTarget freshTarget firstCount lastCount / 16 ≤
      pairedWordTarget wordTarget freshTarget firstCount lastCount :=
    (Field.div_le_iff_pos sixteenPositive).mpr
      (cap.trans_eq (Fraction.Field.mul_comm _ _))
  have same : (programmeTarget programmeCap wordTarget cochainTarget freshTarget firstCount lastCount / 4) / 4 =
      programmeTarget programmeCap wordTarget cochainTarget freshTarget firstCount lastCount / 16 := by
    apply Fraction.Field.mul_right_cancel_of_ne
      (rationalNatCastNonzero (value := 16) (Nat.zero_lt_succ 15))
    have fourNonzero := rationalNatCastNonzero (value := 4) (Nat.zero_lt_succ 3)
    have outer := Fraction.Field.div_mul_cancel_of_ne
      (programmeTarget programmeCap wordTarget cochainTarget freshTarget firstCount lastCount / 4) 4 fourNonzero
    have inner := Fraction.Field.div_mul_cancel_of_ne
      (programmeTarget programmeCap wordTarget cochainTarget freshTarget firstCount lastCount) 4 fourNonzero
    have both : ((programmeTarget programmeCap wordTarget cochainTarget freshTarget firstCount lastCount / 4) / 4) *
        16 = programmeTarget programmeCap wordTarget cochainTarget freshTarget firstCount lastCount :=
      (show ((programmeTarget programmeCap wordTarget cochainTarget freshTarget firstCount lastCount / 4) / 4) *
          16 = (((programmeTarget programmeCap wordTarget cochainTarget freshTarget firstCount lastCount / 4) / 4) *
          4) * 4 by ring1).trans ((congrArg (fun amount : Rational => amount * 4) outer).trans inner)
    exact both.trans (Fraction.Field.div_mul_cancel_of_ne _ _
      (rationalNatCastNonzero (value := 16) (Nat.zero_lt_succ 15))).symm
  exact same.trans_le divide

/-- The actual original programme quarter request preserves the independent public cochain target. -/
theorem programmeTarget_cochain (programmeCap wordTarget cochainTarget freshTarget : Rational)
    (firstCount lastCount : Nat) :
    programmeTarget programmeCap wordTarget cochainTarget freshTarget firstCount lastCount / 4 ≤ cochainTarget :=
  (Field.div_le_iff_pos (natCast_pos_direct (n := 4) (Nat.zero_lt_succ 3))).mpr
    (((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_right _ _)).trans_eq
      (Fraction.Field.mul_comm _ _))

/-- The actual sixteenth request also preserves its independently supplied public word target. -/
theorem programmeTarget_word_le (programmeCap wordTarget cochainTarget freshTarget : Rational)
    (firstCount lastCount : Nat) :
    (programmeTarget programmeCap wordTarget cochainTarget freshTarget firstCount lastCount / 4) / 4 ≤ wordTarget :=
  (programmeTarget_word programmeCap wordTarget cochainTarget freshTarget firstCount lastCount).trans
    (pairedWordTarget_le wordTarget freshTarget firstCount lastCount)

/-- The genuine programme request pays the first fresh mesh on the original single-bank numerical tolerance. -/
theorem programmeTarget_firstMesh_lt {programmeCap wordTarget cochainTarget freshTarget : Rational}
    (programmePositive : 0 < programmeCap) (wordPositive : 0 < wordTarget)
    (cochainPositive : 0 < cochainTarget) (freshPositive : 0 < freshTarget)
    (oldCount fragments firstCount lastCount : Nat) :
    let requested := programmeTarget programmeCap wordTarget cochainTarget freshTarget firstCount lastCount
    Aggregate.countCoordinate firstCount * (Aggregate.countCoordinate firstCount *
      (16 * Aggregate.perTerm (wordAllowance ((requested / 4) / 4) (requested / 4) oldCount) fragments)) <
      freshTarget := by
  let requested := programmeTarget programmeCap wordTarget cochainTarget freshTarget firstCount lastCount
  have requestPositive := programmeTarget_positive programmePositive wordPositive cochainPositive freshPositive
    firstCount lastCount
  have quarterPositive := Field.div_pos_direct requestPositive (natCast_pos_direct (n := 4) (Nat.zero_lt_succ 3))
  exact meshCharge_of_word_le
    (wordAllowance_positive (Field.div_pos_direct quarterPositive
      (natCast_pos_direct (n := 4) (Nat.zero_lt_succ 3))) quarterPositive oldCount)
    freshPositive firstCount fragments
    ((wordAllowance_le _ _ oldCount).trans
      ((programmeTarget_word programmeCap wordTarget cochainTarget freshTarget firstCount lastCount).trans
        (pairedWordTarget_first wordTarget freshTarget firstCount lastCount)))

/-- The SAME request and tolerance pay the whole second fresh word without another reference or P bank. -/
theorem programmeTarget_lastMesh_lt {programmeCap wordTarget cochainTarget freshTarget : Rational}
    (programmePositive : 0 < programmeCap) (wordPositive : 0 < wordTarget)
    (cochainPositive : 0 < cochainTarget) (freshPositive : 0 < freshTarget)
    (oldCount fragments firstCount lastCount : Nat) :
    let requested := programmeTarget programmeCap wordTarget cochainTarget freshTarget firstCount lastCount
    Aggregate.countCoordinate lastCount * (Aggregate.countCoordinate lastCount *
      (16 * Aggregate.perTerm (wordAllowance ((requested / 4) / 4) (requested / 4) oldCount) fragments)) <
      freshTarget := by
  let requested := programmeTarget programmeCap wordTarget cochainTarget freshTarget firstCount lastCount
  have requestPositive := programmeTarget_positive programmePositive wordPositive cochainPositive freshPositive
    firstCount lastCount
  have quarterPositive := Field.div_pos_direct requestPositive (natCast_pos_direct (n := 4) (Nat.zero_lt_succ 3))
  exact meshCharge_of_word_le
    (wordAllowance_positive (Field.div_pos_direct quarterPositive
      (natCast_pos_direct (n := 4) (Nat.zero_lt_succ 3))) quarterPositive oldCount)
    freshPositive lastCount fragments
    ((wordAllowance_le _ _ oldCount).trans
      ((programmeTarget_word programmeCap wordTarget cochainTarget freshTarget firstCount lastCount).trans
        (pairedWordTarget_last wordTarget freshTarget firstCount lastCount)))

/-- The actual literal period-allocation denominator is positive after its owned cast readback. -/
private theorem periodDenominator_positive : (0 : Rational) < 128 := by
  change (0 : Rational) < ((128 : Nat) : Rational)
  rewrite [Fraction.Cast.natCast_eq_fromInt 128]
  decide +kernel

/-- The actual literal allocation denominator is at least one under the same owned readback. -/
private theorem periodDenominator_atLeastOne : (1 : Rational) ≤ 128 := by
  change ((1 : Nat) : Rational) ≤ ((128 : Nat) : Rational)
  rewrite [Fraction.Cast.natCast_eq_fromInt 1, Fraction.Cast.natCast_eq_fromInt 128]
  decide +kernel

/-- The literal 106-share charge is strictly below the retained 128-share denominator. -/
private theorem periodCharge_lt_denominator : (106 : Rational) < 128 := by
  change ((106 : Nat) : Rational) < ((128 : Nat) : Rational)
  rewrite [Fraction.Cast.natCast_eq_fromInt 106, Fraction.Cast.natCast_eq_fromInt 128]
  decide +kernel

/-- The positive internal share used by original-source and fresh-period comparisons on one bank. -/
@[expose] def periodShare (requested : Rational) : Rational := requested / 128

/-- A positive public request gives a genuinely positive period comparison share. -/
theorem periodShare_positive {requested : Rational} (positive : 0 < requested) : 0 < periodShare requested :=
  Field.div_pos_direct positive periodDenominator_positive

/-- The actual period comparison share preserves its independent public cap. -/
theorem periodShare_le {requested : Rational} (nonnegative : 0 ≤ requested) : periodShare requested ≤ requested :=
  Field.divide_le_self nonnegative periodDenominator_atLeastOne

/-- The original model, route, chart and mesh comparison coefficients leave a strict requested-error margin.

The cached fresh model/cochain comparison pays 22 shares. The original
period/model bridge pays at most four more, and the original source/cochain
bridge pays one. The two original squared-norm triangle estimates consume
106 shares, strictly below the chosen 128-share public target. A signed
basis-coordinate combination has a separate coefficient-mass allocation.
No movement mass is divided, including the zero-movement case.
-/
theorem programmePeriod_error_lt {requested : Rational} (positive : 0 < requested) :
    2 * (periodShare requested + 2 * (4 * periodShare requested + 22 * periodShare requested)) < requested := by
  have sharePositive := periodShare_positive positive
  have strict := Arithmetic.mul_lt_mul_of_pos_left_direct sharePositive
    periodCharge_lt_denominator
  have cancelled := Fraction.Field.div_mul_cancel_of_ne requested 128
    periodDenominator_positive.ne'
  exact (show 2 * (periodShare requested + 2 * (4 * periodShare requested + 22 * periodShare requested)) =
    periodShare requested * 106 by ring1).trans_lt (strict.trans_eq cancelled)

section WeightedAllocation

variable {firstCount lastCount : Nat} {firstWeights : Data.Vector Int firstCount}
    {lastWeights : Data.Vector Int lastCount}
    (first : WeightedPeriods.Coefficients firstWeights) (last : WeightedPeriods.Coefficients lastWeights)

/-- The actual literal fresh-programme coefficient 52 is positive under its owned cast readback. -/
private theorem periodComponentFactor_positive : (0 : Rational) < 52 := by
  change (0 : Rational) < ((52 : Nat) : Rational)
  rewrite [Fraction.Cast.natCast_eq_fromInt 52]
  decide +kernel

/-- Select a genuine common component share using both actual signed coefficient masses before any fresh requests.

The old/fresh coordinate rows retain their original coefficient caches.
Each mass-plus-one denominator supports a zero row without division by
its mass. All fresh geometry, points and observations are selected later
using this actual share.
-/
@[expose] def weightedPeriodShare (requested : Rational) : Rational :=
  min (periodShare requested) (min (first.perComponent (requested / 4) / 52)
    (last.perComponent (requested / 4) / 52))

/-- Positive public tolerance gives a genuinely positive weighted component share, including zero coefficients. -/
theorem weightedPeriodShare_positive {requested : Rational} (positive : 0 < requested) :
    0 < weightedPeriodShare first last requested :=
  Fraction.Order.Basic.lt_min (periodShare_positive positive) (Fraction.Order.Basic.lt_min
    (Field.div_pos_direct
      (first.perComponent_positive (Field.div_pos_direct positive (by decide : (0 : Rational) < 4)))
      periodComponentFactor_positive)
    (Field.div_pos_direct
      (last.perComponent_positive (Field.div_pos_direct positive (by decide : (0 : Rational) < 4)))
      periodComponentFactor_positive))

/-- The selected weighted share preserves the independent unweighted public period cap. -/
theorem weightedPeriodShare_le (requested : Rational) :
    weightedPeriodShare first last requested ≤ periodShare requested := Fraction.Order.Basic.min_le_left _ _

/-- The actual first coefficient mass is paid by the selected common fresh-programme allowance. -/
theorem weightedPeriodShare_first (requested : Rational) :
    52 * weightedPeriodShare first last requested ≤ first.perComponent (requested / 4) := by
  have selected : weightedPeriodShare first last requested ≤ first.perComponent (requested / 4) / 52 :=
    (Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)
  exact (Arithmetic.mul_le_mul_of_nonneg_left_direct selected periodComponentFactor_positive.le).trans_eq
    ((Fraction.Field.mul_comm _ _).trans
      (Fraction.Field.div_mul_cancel_of_ne _ _ periodComponentFactor_positive.ne'))

/-- The actual second coefficient mass is independently paid by that SAME share. -/
theorem weightedPeriodShare_last (requested : Rational) :
    52 * weightedPeriodShare first last requested ≤ last.perComponent (requested / 4) := by
  have selected : weightedPeriodShare first last requested ≤ last.perComponent (requested / 4) / 52 :=
    (Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_right _ _)
  exact (Arithmetic.mul_le_mul_of_nonneg_left_direct selected periodComponentFactor_positive.le).trans_eq
    ((Fraction.Field.mul_comm _ _).trans
      (Fraction.Field.div_mul_cancel_of_ne _ _ periodComponentFactor_positive.ne'))

/-- The same selected share also pays the independent original-source quarter target. -/
theorem weightedPeriodShare_le_quarter {requested : Rational} (nonnegative : 0 ≤ requested) :
    weightedPeriodShare first last requested ≤ requested / 4 := by
  have factor : (4 : Rational) ≤ 128 := by
    change ((4 : Nat) : Rational) ≤ ((128 : Nat) : Rational)
    rewrite [Fraction.Cast.natCast_eq_fromInt 4, Fraction.Cast.natCast_eq_fromInt 128]
    decide +kernel
  exact (weightedPeriodShare_le first last requested).trans
    (Field.div_le_div_of_cross periodDenominator_positive (by decide : (0 : Rational) < 4)
      (Arithmetic.mul_le_mul_of_nonneg_left_direct factor nonnegative))

end WeightedAllocation

/-- Three independently paid routing, mesh and chart errors fit their positive public cochain target. -/
theorem three_error_lt {target : Rational} (positive : 0 < target) :
    2 * (target / 32 + 2 * (target / 32 + target / 32)) < target := by
  have sharePositive := Field.div_pos_direct positive (natCast_pos_direct (n := 32) (Nat.zero_lt_succ 31))
  have strict := Arithmetic.mul_lt_mul_of_pos_left_direct sharePositive
    (natCast_lt_direct (m := 10) (n := 32) (by decide))
  have cancelled := Fraction.Field.div_mul_cancel_of_ne target 32
    (rationalNatCastNonzero (value := 32) (Nat.zero_lt_succ 31))
  exact (show 2 * (target / 32 + 2 * (target / 32 + target / 32)) = target / 32 * 10 by ring1).trans_lt
    (strict.trans_eq cancelled)

/-- The full routing, mesh, chart and fresh-cochain charges fit their positive public target. -/
theorem four_error_lt {target : Rational} (positive : 0 < target) :
    2 * (2 * (target / 32 + 2 * (target / 32 + target / 32)) + target / 32) < target := by
  have sharePositive := Field.div_pos_direct positive (natCast_pos_direct (n := 32) (Nat.zero_lt_succ 31))
  have strict := Arithmetic.mul_lt_mul_of_pos_left_direct sharePositive
    (natCast_lt_direct (m := 22) (n := 32) (by decide))
  have cancelled := Fraction.Field.div_mul_cancel_of_ne target 32
    (rationalNatCastNonzero (value := 32) (Nat.zero_lt_succ 31))
  exact (show 2 * (2 * (target / 32 + 2 * (target / 32 + target / 32)) + target / 32) =
    target / 32 * 22 by ring1).trans_lt (strict.trans_eq cancelled)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : Data curve}
    {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
    {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid}
    {vertices : RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid}
    {edges : RootIsolation.SquareRoot.Grid.RootEdgeBank frames} {mesh : LiftedMesh vertices edges base.faces}
    {source : Differential genus} {domains : FaceDomainBank frames base.faces.regulars}
    {polynomial : Option (Ordinary curve.polynomial)} {points : List Canonical}
    {tolerance : Rational} {stage : Nat}
    {budgets : FaceMeshBudgets source points tolerance
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial source polynomial) domains}
    {numerics : FacePrimitiveBank source stage
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial source polynomial) domains}
    {shared : FaceSharedMeshes budgets numerics}
    {ambient : Geometry.Rational.Box} {first last : Canonical}
    {path : ClearPath curve.polynomial ambient first last} {assigned : PathFaces mesh path}

/-- Actual full-numerator chart caches and retained shared-mesh readings pay the canonical-word discrepancy.

The original corner and mesh readings, actual triangle cache and post-bank
contact products all use the literal supplied P primitive bank. Its
independent offsets and numerical stage are not replaced or normalized.
-/
theorem comparison_bound (readings : MeshWordReadings shared assigned)
    {target : Rational} (charts : RouteChartRequest assigned.routeSpine source domains target polynomial)
    (later : charts.index ≤ stage) (triangles : TriangleReadings numerics mesh)
    (compared : charts.Comparisons numerics triangles) :
    normSq (wordValue (CanonicalEdgeValues.edgeValuation mesh triangles.values) assigned.indexed - readings.value) <
      2 * (target + readings.bound) := by
  have chart := charts.comparison_accurate later compared
  rewrite [assigned.routeSpine_values, ← readings.cornerValue_eq_triangles triangles] at chart
  rewrite [show wordValue (CanonicalEdgeValues.edgeValuation mesh triangles.values) assigned.indexed - readings.value =
    (wordValue (CanonicalEdgeValues.edgeValuation mesh triangles.values) assigned.indexed - readings.cornerValue) +
      (readings.cornerValue - readings.value) by ring1]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    (Arithmetic.mul_lt_mul_of_pos_left_direct (natCast_pos_direct (n := 2) (Nat.zero_lt_succ 1))
      ((Arithmetic.add_lt_add_right_direct chart _).trans_le
        (Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) readings.accurate)))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodCanonical
