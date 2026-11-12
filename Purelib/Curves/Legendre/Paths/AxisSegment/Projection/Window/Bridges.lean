module

public import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window
public import Purelib.Geometry.Rational.Box.Interior.Transport
public import Purelib.Data.Rat.Bounds.Gap
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Paths.Frame.Gaps
import Purelib.Curves.Legendre.Paths.Owners
import Purelib.Geometry.Rational.Box.Outside.Transport
import Purelib.Geometry.Rational.Box.Outside
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Fin
import Purelib.Data.Fin.Cases
import Purelib.Data.Fin.Two
import Purelib.Data.Vector.Dependent
import Purelib.RootIsolation.Owner.Bridge.Basic
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Original owner bridges within root-derived windows

The original window radius pays each moving-owner and selected outside-side
gap. Point displacement preserves those same boxes and side directions,
and the resulting original moving-factor clearance pays the actual
displacement between any two retained window parameters.
-/

public section

namespace Purelib.Curves.Legendre.Paths.AxisSegment.ProjectionCollision.OwnerWindow

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.RootIsolation
open Fraction.Order

/-- The same cached radius pays the original moving-owner gap and both retained fixed-owner outside-side gaps. -/
theorem radius_pays_gaps {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision) :
    4 * window.radius ≤ window.frame.branchGap 1 ∧
      4 * window.radius ≤ (window.sides.get 0).gap ∧ 4 * window.radius ≤ (window.sides.get 1).gap := by
  rewrite [window.radius_eq]
  exact window.frame.displacementRadius_pays_gaps window.sides

/-- The cached positive radius is below the original moving-root interior gap. -/
theorem radius_lt_moving_gap {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision) :
    window.radius < window.frame.branchGap 1 :=
  Bounds.Gap.radius_lt_gap window.radius_positive window.radius_pays_gaps.1

/-- The cached radius is below the gap of each same retained original moving-root outside side. -/
theorem radius_lt_side_gap {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision) (index : Fin 2) :
    window.radius < (window.sides.get index).gap := by
  rcases Fin.Two.finTwo_cases index with zero | one
  · subst index
    exact Bounds.Gap.radius_lt_gap window.radius_positive window.radius_pays_gaps.2.1
  · subst index
    exact Bounds.Gap.radius_lt_gap window.radius_positive window.radius_pays_gaps.2.2

/-- Every original window point stays within the same cached radius in each original coordinate. -/
theorem coordinate_bounds {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision)
    (parameter : Coordinate) (inside : window.parameters.Contains parameter) :
    -window.radius ≤ (segment.pointAt parameter).re - (segment.pointAt collision.val).re ∧
      (segment.pointAt parameter).re - (segment.pointAt collision.val).re ≤ window.radius ∧
      -window.radius ≤ (segment.pointAt parameter).im - (segment.pointAt collision.val).im ∧
      (segment.pointAt parameter).im - (segment.pointAt collision.val).im ≤ window.radius := by
  have bounded := Gaussian.Norm.Bounds.coordinate_bounds_of_normSq_le window.radius_positive.le
    (window.normSq_lt parameter inside).le
  exact bounded

/-- Every original branch at a window parameter lies strictly inside its same retained anchor owner box. -/
theorem root_strictContains {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision)
    (parameter : Coordinate) (inside : window.parameters.Contains parameter) (label : Fin 3) :
    (window.frame.rootOwner label).box.StrictContains (branchPoint (segment.pointAt parameter) label) := by
  rcases Fin.Cases.three label with zero | moving | one
  · subst label
    exact window.frame.rootStrictContains 0
  · subst label
    exact Box.Interior.strictContains_of_near window.radius_lt_moving_gap (window.coordinate_bounds parameter inside)
  · subst label
    exact window.frame.rootStrictContains 2

/-- Transport the same stored original moving-root outside side to an actual window parameter.

The original fixed-branch owner index, box and side direction are retained.
The same cached window radius and whole-window coordinate bounds prove the
transport without running another outside-side selection. -/
@[expose] def movingSideAt {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision)
    (parameter : Coordinate) (inside : window.parameters.Contains parameter) (index : Fin 2) :
    Box.OutsideSide (window.frame.rootOwner (Fin.skipIndex 1 index)).box (segment.pointAt parameter) :=
  (window.sides.get index).rebase (segment.pointAt parameter) window.radius
    (window.radius_lt_side_gap index) (window.coordinate_bounds parameter inside)

/-- The actual transported moving-root side retains the proved remaining-gap squared clearance. -/
theorem movingSideAt_margin_lower {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    (window : OwnerWindow collision)
    (parameter : Coordinate) (inside : window.parameters.Contains parameter) (index : Fin 2) :
    ((window.sides.get index).gap - window.radius) ^ 2 ≤ (window.movingSideAt parameter inside index).margin := by
  unfold movingSideAt
  exact (window.sides.get index).rebase_margin_lower _ _ _ _

/-- Motion between any two original window points is below four squares of that same cached radius. -/
theorem pointAt_normSq_sub_lt {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision)
    (source target : Coordinate) (sourceInside : window.parameters.Contains source)
    (targetInside : window.parameters.Contains target) :
    Gaussian.Norm.Basic.normSq (segment.pointAt source - segment.pointAt target) < 4 * window.radius ^ 2 := by
  have through := Gaussian.Norm.Bounds.normSq_sub_le_via
    (segment.pointAt source) (segment.pointAt collision.val) (segment.pointAt target)
  rewrite [Gaussian.Norm.Bounds.normSq_sub_symm (segment.pointAt collision.val) (segment.pointAt target)] at through
  have summed := Arithmetic.add_lt_add_direct
    (window.normSq_lt source sourceInside) (window.normSq_lt target targetInside)
  have paid := Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Coordinate) < 2) summed
  exact through.trans_lt (paid.trans_eq (by ring1))

/-- Select original outside sides for the actual roots at a window parameter on the same retained owner box.

Moving-root sides on the fixed owners come from the retained side cache and
its direction-preserving transport. The unmoved zero and one roots use
their original anchor-frame sides on that same box. -/
@[expose] def outsideSidesAt {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision)
    (parameter : Coordinate) (inside : window.parameters.Contains parameter) (label rootLabel : Fin 3)
    (different : rootLabel ≠ label) :
    Box.OutsideSide (window.frame.rootOwner label).box (branchPoint (segment.pointAt parameter) rootLabel) := by
  by_cases movingOwner : label = 1
  · subst label
    by_cases zeroRoot : rootLabel = 0
    · subst rootLabel
      exact window.frame.rootOutsideSide 1 0 (by decide)
    · have oneRoot : rootLabel = 2 := by
        rcases Fin.Cases.three rootLabel with zero | moving | one
        · exact (zeroRoot zero).elim
        · exact (different moving).elim
        · exact one
      subst rootLabel
      exact window.frame.rootOutsideSide 1 2 (by decide)
  · by_cases zeroOwner : label = 0
    · subst label
      by_cases movingRoot : rootLabel = 1
      · subst rootLabel
        exact window.movingSideAt parameter inside 0
      · have oneRoot : rootLabel = 2 := by
          rcases Fin.Cases.three rootLabel with zero | moving | one
          · exact (different zero).elim
          · exact (movingRoot moving).elim
          · exact one
        subst rootLabel
        exact window.frame.rootOutsideSide 0 2 (by decide)
    · have oneOwner : label = 2 := by
        rcases Fin.Cases.three label with zero | moving | one
        · exact (zeroOwner zero).elim
        · exact (movingOwner moving).elim
        · exact one
      subst label
      by_cases movingRoot : rootLabel = 1
      · subst rootLabel
        exact window.movingSideAt parameter inside 1
      · have zeroRoot : rootLabel = 0 := by
          rcases Fin.Cases.three rootLabel with zero | moving | one
          · exact zero
          · exact (movingRoot moving).elim
          · exact (different one).elim
        subst rootLabel
        exact window.frame.rootOutsideSide 2 0 (by decide)

/-- The zero-owner moving factor uses the same transported first original side. -/
theorem outsideSidesAt_zero_moving {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    (window : OwnerWindow collision)
    (parameter : Coordinate) (inside : window.parameters.Contains parameter) :
    window.outsideSidesAt parameter inside 0 1 (by decide) = window.movingSideAt parameter inside 0 := rfl

/-- The one-owner moving factor uses the same transported second original side. -/
theorem outsideSidesAt_one_moving {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    (window : OwnerWindow collision)
    (parameter : Coordinate) (inside : window.parameters.Contains parameter) :
    window.outsideSidesAt parameter inside 2 1 (by decide) = window.movingSideAt parameter inside 1 := rfl

/-- The original factor vectors at one window parameter, indexed by their same original frame owner boxes. -/
abbrev FactorsAt {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision) (parameter : Coordinate) :=
  Vector.DependentVector (fun label : Fin 3 =>
    BranchFactors (segment.pointAt parameter) (window.frame.rootOwner label).box label)

/-- Materialize all original source factors once at an actual retained window parameter.

Each logical owner label retains its original anchor box. The same proved
strict containment and retained outside sides construct the three original
factor certificates stored in its original dependent vector. -/
@[expose] def factorsAt {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision)
    (parameter : Coordinate) (inside : window.parameters.Contains parameter) : FactorsAt window parameter :=
  Vector.DependentVector.ofFn (fun label => branchFactors (segment.pointAt parameter)
    (window.frame.rootOwner label).box label (window.root_strictContains parameter inside label)
      (window.outsideSidesAt parameter inside label))

/-- Reading one original source factor vector preserves its same window parameter, frame box and logical label. -/
theorem factorsAt_get {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision)
    (parameter : Coordinate) (inside : window.parameters.Contains parameter) (label : Fin 3) :
    (window.factorsAt parameter inside).get label = branchFactors (segment.pointAt parameter)
      (window.frame.rootOwner label).box label (window.root_strictContains parameter inside label)
        (window.outsideSidesAt parameter inside label) := by
  unfold factorsAt
  exact Vector.DependentVector.ofFn_get _ _

/-- Every actual source moving-factor bound pays four squares of the same retained window radius. -/
theorem factorsAt_moving_bound {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    (window : OwnerWindow collision)
    (parameter : Coordinate) (inside : window.parameters.Contains parameter) (label : Fin 3) :
    4 * window.radius ^ 2 < (((window.factorsAt parameter inside).get label).get 1).val.bound := by
  rewrite [factorsAt_get, branchFactors_get]
  rcases Fin.Cases.three label with zero | moving | one
  · subst label
    rewrite [branchFactorCertificate_bound_of_ne _ _ _ _ _ _ (by decide), outsideSidesAt_zero_moving]
    exact (Bounds.Gap.four_radius_sq_lt_remaining_gap_sq
      window.radius_positive window.radius_pays_gaps.2.1).trans_le
        (window.movingSideAt_margin_lower parameter inside 0)
  · subst label
    rewrite [branchFactorCertificate_bound_self]
    exact (Bounds.Gap.four_radius_sq_lt_remaining_gap_sq window.radius_positive window.radius_pays_gaps.1).trans_le
      (Box.Interior.squared_gaps_lower_of_near window.radius_lt_moving_gap (window.coordinate_bounds parameter inside))
  · subst label
    rewrite [branchFactorCertificate_bound_of_ne _ _ _ _ _ _ (by decide), outsideSidesAt_one_moving]
    exact (Bounds.Gap.four_radius_sq_lt_remaining_gap_sq
      window.radius_positive window.radius_pays_gaps.2.2).trans_le
        (window.movingSideAt_margin_lower parameter inside 1)

/-- Exact box and source-clearance readback of an original bridge from its same source factor vector. -/
@[expose] def BridgeAgreement {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision)
    (source target : Coordinate) (label : Fin 3)
    (factors : BranchFactors (segment.pointAt source) (window.frame.rootOwner label).box label)
    (bridge : Owner.Bridge.Basic.OwnerBridge (polynomial (segment.pointAt source))
      (polynomial (segment.pointAt target))) : Prop :=
  bridge.box = (window.frame.rootOwner label).box ∧
    bridge.leftClearance.bound = (factors.get 0).val.bound * (factors.get 1).val.bound * (factors.get 2).val.bound

/-- An original source-to-target bridge with exact readback to its retained frame box and source factors. -/
abbrev BridgeAt {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision)
    (source target : Coordinate) (label : Fin 3)
    (factors : BranchFactors (segment.pointAt source) (window.frame.rootOwner label).box label) :=
  {bridge : Owner.Bridge.Basic.OwnerBridge (polynomial (segment.pointAt source))
      (polynomial (segment.pointAt target)) // BridgeAgreement window source target label factors bridge}

/-- Construct the original bridge and its same box and clearance readbacks from one retained source factor vector. -/
@[expose] def bridgeAt {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision)
    (source target : Coordinate) (label : Fin 3)
    (factors : BranchFactors (segment.pointAt source) (window.frame.rootOwner label).box label)
    (small : Gaussian.Norm.Basic.normSq (segment.pointAt source - segment.pointAt target) <
      (factors.get 1).val.bound) : BridgeAt window source target label factors := by
  let bridge := branchBridge (segment.pointAt source) (segment.pointAt target)
    (window.frame.rootOwner label).box label (window.frame.rootOwner label).proper factors small
  refine ⟨bridge, ?_, ?_⟩
  · exact branchBridge_box (segment.pointAt source) (segment.pointAt target)
      (window.frame.rootOwner label).box label (window.frame.rootOwner label).proper factors small
  · exact branchBridge_leftClearance_bound (segment.pointAt source) (segment.pointAt target)
      (window.frame.rootOwner label).box label (window.frame.rootOwner label).proper factors small

/-- Original source factors and original source-to-target bridges sharing those same retained frame boxes.

The stored factor vectors retain their actual source parameter. Each original
bridge has that same logical owner box and its source clearance is the product
of the same stored factor bounds. Neither endpoint polynomial is replaced. -/
abbrev BridgesAt {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision)
    (source target : Coordinate) :=
  Σ factors : FactorsAt window source,
    Vector.DependentVector (fun label : Fin 3 => BridgeAt window source target label (factors.get label))

/-- Build all three original owner bridges between actual parameters of the same retained root-derived window.

The source factors are materialized once. Their actual moving-factor bounds
pay the whole source-to-target displacement. Sharp factor-move dominance and
finite Rouché transfer construct both endpoint clearances and winding laws;
the original bridges retain the same frame boxes and source-factor cache. -/
@[expose] def bridgesAt {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision)
    (source target : Coordinate) (sourceInside : window.parameters.Contains source)
    (targetInside : window.parameters.Contains target) : BridgesAt window source target := by
  let factors : FactorsAt window source := window.factorsAt source sourceInside
  refine ⟨factors, Vector.DependentVector.ofFn ?_⟩
  intro label
  have small : Gaussian.Norm.Basic.normSq (segment.pointAt source - segment.pointAt target) <
      ((factors.get label).get 1).val.bound :=
    (window.pointAt_normSq_sub_lt source target sourceInside targetInside).trans
      (window.factorsAt_moving_bound source sourceInside label)
  exact window.bridgeAt source target label (factors.get label) small

namespace BridgesAt

/-- Read the same materialized original source factors retained by the bridge family. -/
@[expose] def factors {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} {window : OwnerWindow collision}
    {source target : Coordinate}
    (bridges : BridgesAt window source target) : FactorsAt window source := bridges.1

/-- Read one stored original source-to-target bridge at its same logical branch label. -/
@[expose] def get {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} {window : OwnerWindow collision}
    {source target : Coordinate}
    (bridges : BridgesAt window source target) (label : Fin 3) :
    Owner.Bridge.Basic.OwnerBridge (polynomial (segment.pointAt source)) (polynomial (segment.pointAt target)) :=
  (bridges.2.get label).val

/-- Every stored original bridge retains that same original anchor-frame box. -/
theorem get_box {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} {window : OwnerWindow collision}
    {source target : Coordinate}
    (bridges : BridgesAt window source target) (label : Fin 3) :
    (bridges.get label).box = (window.frame.rootOwner label).box := (bridges.2.get label).property.1

/-- Every stored original bridge consumes its same retained original source-factor clearance bounds. -/
theorem get_leftClearance_bound {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    {window : OwnerWindow collision} {source target : Coordinate} (bridges : BridgesAt window source target)
    (label : Fin 3) : (bridges.get label).leftClearance.bound =
      ((bridges.factors.get label).get 0).val.bound * ((bridges.factors.get label).get 1).val.bound *
        ((bridges.factors.get label).get 2).val.bound := (bridges.2.get label).property.2

end BridgesAt

/-- Building the original bridge family retains the same complete materialized source-factor cache. -/
theorem bridgesAt_factors {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision)
    (source target : Coordinate) (sourceInside : window.parameters.Contains source)
    (targetInside : window.parameters.Contains target) :
    (window.bridgesAt source target sourceInside targetInside).factors = window.factorsAt source sourceInside := rfl

end Purelib.Curves.Legendre.Paths.AxisSegment.ProjectionCollision.OwnerWindow
