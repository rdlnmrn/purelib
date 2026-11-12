module

public import Purelib.Curves.Legendre.Paths.AxisSegment.Projection
public import Purelib.Curves.Legendre.Paths.AxisSegment.Window
public import Purelib.Curves.Legendre.Paths.Frame.Gaps
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Paths.Frame
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Coordinates.Rotation
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-!
# Root-derived windows at original projected collisions

Intrinsic avoidance supplies the original anchor frame. Its moving-root
interior gap and cached fixed-owner outside sides compute the displacement
radius, which is retained with its exact defining equality. The existing
parameter-window operation then pays this same root-derived allowance.
-/

public section

namespace Purelib.Curves.Legendre.Paths.AxisSegment.ProjectionCollision

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Data.Gaussian.Coordinates
open Fraction.Order

/-- An original anchor frame, its stored moving-root sides and radius, and the parameter interval they certify.

The existing objects retain their original parameter and frame indices.
The radius cache has its exact defining equality. Every parameter of the
original proper unit window has squared displacement below that same
stored radius squared, and the window contains the original collision. -/
abbrev OwnerWindow {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    (collision : ProjectionCollision segment slope reading) :=
  Σ frame : Paths.Frame (segment.pointAt collision.val),
    Σ sides : Paths.Frame.MovingSides frame,
      Σ radius : {value : Coordinate // value = frame.displacementRadius sides},
        {interval : Interval.Bounds //
          0 ≤ interval.lower ∧ interval.lower < interval.upper ∧ interval.upper ≤ 1 ∧
          interval.Contains collision.val ∧
          ∀ parameter : Coordinate, interval.Contains parameter →
            Gaussian.Norm.Basic.normSq (segment.pointAt parameter - segment.pointAt collision.val) < radius.val ^ 2}


namespace OwnerWindow

/-- Prepare an original parameter window from its retained anchor frame and internally computed side and radius caches.

The original frame keeps its actual projection chart, owners and parameter
index. Its two owner-derived outside sides and displacement radius are
computed once. Their same squared radius pays the original closed-unit
parameter window, including either original unit endpoint. -/
@[expose] def ofFrame {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    (collision : ProjectionCollision segment slope reading) (frame : Paths.Frame (segment.pointAt collision.val)) :
    OwnerWindow collision := by
  let sides := frame.movingSides
  let radius := frame.displacementRadius sides
  have radiusPositive := frame.displacementRadius_positive sides
  have allowancePositive : 0 < radius ^ 2 := Arithmetic.exact_rational_sq_pos radiusPositive.ne'
  let unitBounds := And.intro collision.property.1 collision.property.2.1
  let parameters := segment.window collision.val (radius ^ 2) unitBounds allowancePositive
  refine ⟨frame, sides, ⟨radius, rfl⟩, parameters, ?_⟩
  have bounds := segment.window_bounds collision.val (radius ^ 2) unitBounds allowancePositive
  exact ⟨bounds.1, bounds.2.1, bounds.2.2,
    segment.window_contains_anchor collision.val (radius ^ 2) unitBounds allowancePositive,
    fun parameter inside => segment.window_normSq_lt collision.val (radius ^ 2)
      unitBounds allowancePositive parameter inside⟩


/-- Read the same retained original frame at the window's collision parameter. -/
@[expose] def frame {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision) :
    Paths.Frame (segment.pointAt collision.val) := window.1

/-- Read the original stored moving-root side vector indexed by that same retained frame. -/
@[expose] def sides {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision) :
    Paths.Frame.MovingSides window.frame := window.2.1

/-- Read the original cached displacement radius without recomputing its gap minimum. -/
@[expose] def radius {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision) : Coordinate :=
  window.2.2.1.val

/-- Read the same retained original rational parameter interval. -/
@[expose] def parameters {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision) : Interval.Bounds :=
  window.2.2.2.val

/-- The stored radius is exactly the displacement radius of the same original frame and side cache. -/
theorem radius_eq {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision) :
    window.radius = window.frame.displacementRadius window.sides := window.2.2.1.property

/-- The same retained original displacement radius is strictly positive. -/
theorem radius_positive {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision) : 0 < window.radius := by
  rewrite [window.radius_eq]
  exact window.frame.displacementRadius_positive window.sides

/-- The original window is proper and contained in the closed unit parameter interval. -/
theorem bounds {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision) :
    0 ≤ window.parameters.lower ∧ window.parameters.lower < window.parameters.upper ∧ window.parameters.upper ≤ 1 :=
  ⟨window.2.2.2.property.1, window.2.2.2.property.2.1, window.2.2.2.property.2.2.1⟩

/-- The retained original parameter interval contains that same collision parameter. -/
theorem contains_collision {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision) :
    window.parameters.Contains collision.val := window.2.2.2.property.2.2.2.1

/-- Every original point in the retained parameter window pays the same cached root-derived squared radius. -/
theorem normSq_lt {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (window : OwnerWindow collision)
    (parameter : Coordinate) (inside : window.parameters.Contains parameter) :
    Gaussian.Norm.Basic.normSq (segment.pointAt parameter - segment.pointAt collision.val) < window.radius ^ 2 :=
  window.2.2.2.property.2.2.2.2 parameter inside

/-- Original frame-window preparation retains the complete same anchor frame. -/
theorem ofFrame_frame {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    (collision : ProjectionCollision segment slope reading) (frame : Paths.Frame (segment.pointAt collision.val)) :
    (ofFrame collision frame).frame = frame := rfl

/-- Original frame-window preparation retains that same frame's materialized outside-side vector. -/
theorem ofFrame_sides {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    (collision : ProjectionCollision segment slope reading) (frame : Paths.Frame (segment.pointAt collision.val)) :
    (ofFrame collision frame).sides = frame.movingSides := rfl

/-- Original frame-window preparation retains the same original parameter-window operation and squared radius. -/
theorem ofFrame_parameters {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    (collision : ProjectionCollision segment slope reading) (frame : Paths.Frame (segment.pointAt collision.val)) :
    let window := ofFrame collision frame
    window.parameters = segment.window collision.val (window.radius ^ 2)
      ⟨collision.property.1, collision.property.2.1⟩
      (Arithmetic.exact_rational_sq_pos window.radius_positive.ne') := rfl

end OwnerWindow

/-- Prepare an original root-derived window from intrinsic branch avoidance at any original unit anchor.

The original point-frame constructor computes its owners at the retained
anchor parameter and retained positive cap. The two outside sides and their displacement radius
are cached once; their same radius squared pays the whole original parameter
window. No numerical clearance or successful window certificate is supplied. -/
@[expose] def prepareOwnerWindow {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (cap : {value : Coordinate // 0 < value} := ⟨1, by decide⟩) : OwnerWindow collision :=
  OwnerWindow.ofFrame collision (Paths.Frame.ofParameter (segment.pointAt collision.val)
    (avoidsZero collision.val collision.property.1 collision.property.2.1)
    (avoidsOne collision.val collision.property.1 collision.property.2.1) cap)

/-- Root-window preparation retains the same original point frame at its actual collision parameter. -/
theorem prepareOwnerWindow_frame {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (cap : {value : Coordinate // 0 < value} := ⟨1, by decide⟩) :
    (collision.prepareOwnerWindow avoidsZero avoidsOne cap).frame =
      Paths.Frame.ofParameter (segment.pointAt collision.val)
        (avoidsZero collision.val collision.property.1 collision.property.2.1)
        (avoidsOne collision.val collision.property.1 collision.property.2.1) cap := rfl

/-- Root-window preparation retains the same materialized moving-root side vector of that original anchor frame. -/
theorem prepareOwnerWindow_sides {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (cap : {value : Coordinate // 0 < value} := ⟨1, by decide⟩) :
    (collision.prepareOwnerWindow avoidsZero avoidsOne cap).sides =
      (collision.prepareOwnerWindow avoidsZero avoidsOne cap).frame.movingSides := rfl

/-- Root-window preparation uses the existing parameter-window operation and its same cached squared radius. -/
theorem prepareOwnerWindow_parameters {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (cap : {value : Coordinate // 0 < value} := ⟨1, by decide⟩) :
    let window := collision.prepareOwnerWindow avoidsZero avoidsOne cap
    window.parameters = segment.window collision.val (window.radius ^ 2)
      ⟨collision.property.1, collision.property.2.1⟩
      (Arithmetic.exact_rational_sq_pos window.radius_positive.ne') := rfl

/-- Root-window preparation at the initial original parameter retains that same lower unit endpoint. -/
theorem prepareOwnerWindow_lower_zero {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) (atStart : collision.val = 0)
    (cap : {value : Coordinate // 0 < value} := ⟨1, by decide⟩) :
    (collision.prepareOwnerWindow avoidsZero avoidsOne cap).parameters.lower = 0 := by
  let allowance := (collision.prepareOwnerWindow avoidsZero avoidsOne cap).radius ^ 2
  have positive : 0 < allowance := Arithmetic.exact_rational_sq_pos
    (collision.prepareOwnerWindow avoidsZero avoidsOne cap).radius_positive.ne'
  rewrite [prepareOwnerWindow_parameters (cap := cap)]
  change max 0 (collision.val - segment.windowRadius collision.val allowance) = 0
  rewrite [atStart]
  exact segment.window_lower_zero allowance positive

/-- Root-window preparation at the final original parameter retains that same upper unit endpoint. -/
theorem prepareOwnerWindow_upper_one {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) (atFinish : collision.val = 1)
    (cap : {value : Coordinate // 0 < value} := ⟨1, by decide⟩) :
    (collision.prepareOwnerWindow avoidsZero avoidsOne cap).parameters.upper = 1 := by
  let allowance := (collision.prepareOwnerWindow avoidsZero avoidsOne cap).radius ^ 2
  have positive : 0 < allowance := Arithmetic.exact_rational_sq_pos
    (collision.prepareOwnerWindow avoidsZero avoidsOne cap).radius_positive.ne'
  rewrite [prepareOwnerWindow_parameters (cap := cap)]
  change min 1 (collision.val + segment.windowRadius collision.val allowance) = 1
  rewrite [atFinish]
  exact segment.window_upper_one allowance positive

/-- The computed original root window contains its same projected collision strictly between its endpoints. -/
theorem prepareOwnerWindow_anchor_interior {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (interior : 0 < collision.val ∧ collision.val < 1)
    (cap : {value : Coordinate // 0 < value} := ⟨1, by decide⟩) :
    let window := collision.prepareOwnerWindow avoidsZero avoidsOne cap
    window.parameters.lower < collision.val ∧ collision.val < window.parameters.upper := by
  dsimp only
  let window := collision.prepareOwnerWindow avoidsZero avoidsOne cap
  rewrite [prepareOwnerWindow_parameters (cap := cap)]
  exact segment.window_anchor_interior collision.val (window.radius ^ 2)
    interior (Arithmetic.exact_rational_sq_pos window.radius_positive.ne')

/-- Both endpoints of the same computed original root window miss its retained collision reading.

Strict anchor containment excludes equality with either endpoint parameter.
Injectivity of the original affine projection then excludes that same
collision reading at both actual original window endpoints. -/
theorem prepareOwnerWindow_endpoints_miss {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (finishMisses : (Rotation.rotate slope finish).re ≠ reading)
    (cap : {value : Coordinate // 0 < value} := ⟨1, by decide⟩) :
    let window := collision.prepareOwnerWindow avoidsZero avoidsOne cap
    (Rotation.rotate slope (segment.pointAt window.parameters.lower)).re ≠ reading ∧
      (Rotation.rotate slope (segment.pointAt window.parameters.upper)).re ≠ reading := by
  have anchor := collision.prepareOwnerWindow_anchor_interior avoidsZero avoidsOne
    (collision.interior startMisses finishMisses) cap
  constructor
  · intro hits
    have same := collision.parameter_eq startMisses _ hits
    exact (lt_irrefl _ (anchor.1.trans_eq same.symm)).elim
  · intro hits
    have same := collision.parameter_eq startMisses _ hits
    exact (lt_irrefl _ (same.trans_lt anchor.2)).elim

end Purelib.Curves.Legendre.Paths.AxisSegment.ProjectionCollision
