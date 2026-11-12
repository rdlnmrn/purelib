module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport
public import Purelib.Polynomial.Clearance.Box.Region.Point
public import Purelib.Riemann.Paths.ClearBoxPaths
public import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Arithmetic
public import Purelib.Approximation.AccuracyRequest
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Actual cleared spatial connectors on a retained radial quarter

The original requested-time readings supply their actual spatial endpoints.
An existing full cubic preparation supplies the complete source certificate,
and the original root-channel attachment constructs an additional continuation
owner with its source comparison. A computed local polynomial-clear square
and chart-time payment construct actual spatial L edges through the original
ClearBoxPaths.Route container.

These edges retain the original target reading separately. Agreement of a
continued full-cubic endpoint with that original target, uniform primitive
coverage, chart-to-spatial integral comparison and canonical cut attachment
are distinct later certificates. The original chart-time cells are unchanged.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Paths
open Purelib.Polynomial.Clearance.Box.Region
open Purelib.Approximation
open Purelib.Approximation.Rational

variable {site : Fin 2} {parameter : Canonical} {scale : Fraction.Rational}
variable {quarter : UnitCircuitQuarter} {positive : 0 < scale}
variable {actual : Quarter site parameter scale quarter positive}
variable {first last : Fraction.Rational} {firstInside : FixedRootBoxPath.Inside first}
variable {lastInside : FixedRootBoxPath.Inside last}

/-- The actual spatial coordinate of the original quarter at the retained chart time. -/
@[expose] def coordinate (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational)
    (quarter : UnitCircuitQuarter) (positive : 0 < scale) (time : Fraction.Rational) : Canonical :=
  (Radial.point site parameter scale (Waist.direction quarter time) positive).base

/-- Every physical quarter coordinate lies in the original nodal box under its retained scale and parameter bounds.

This reads the same original radial point at the displayed quarter time.
The coordinate's declared type remains available when its implementation
is locally protected during dependent cache construction.
-/
theorem coordinate_inside (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational)
    (quarter : UnitCircuitQuarter) (positive : 0 < scale)
    (lower : (1 : Fraction.Rational) ≤ scale) (upper : scale ≤ (2 : Fraction.Rational))
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational))
    (time : Fraction.Rational) : (spatialBox site).Contains (coordinate site parameter scale quarter positive time) :=
  Radial.point_inside site parameter scale (Waist.direction quarter time) positive lower upper bound

/-- The exact original full-cubic certificate type above the retained source spatial coordinate. -/
@[expose] def SourceRoot (_reading : Reading actual first firstInside) : Type 1 :=
  CertifiedSquareRoot.Certificate ((Paths.polynomial parameter).eval
    (coordinate site parameter scale quarter positive first))

/-- The cached full-cubic source certificate and its genuine additional continuation-owner attachment.

The exact subtype equations retain the completed factories on the supplied
original preparation. The source product channel and added continuation owner
remain distinct inputs to their operational comparison; neither replaces the
original quarter Reading, cofactor owner or complete preparation cache.
-/
@[expose] def Source (reading : Reading actual first firstInside)
    (prepared : Gaussian.Division.Prepared reading.lift.value) : Type 1 :=
  Σ root : { root : SourceRoot reading //
      root = CertifiedSquareRoot.Certificate.ofPrepared reading.lift.value reading.lift.square prepared },
    { attached : SquareRootChannelOwnership.Attachment root.val.value
        ((Paths.polynomial parameter).eval (coordinate site parameter scale quarter positive first)) //
      attached = SquareRootChannelOwnership.attach root.val }

namespace Source

open Purelib.Data.Rat.Fraction.Order

variable {reading : Reading actual first firstInside}
variable {prepared : Gaussian.Division.Prepared reading.lift.value}

/-- Retain the identical completed full-cubic certificate and attachment, including their exact factory equations. -/
@[expose] def ofAttached (root : SourceRoot reading)
    (retained : root = CertifiedSquareRoot.Certificate.ofPrepared reading.lift.value reading.lift.square prepared)
    (attached : SquareRootChannelOwnership.Attachment root.value
      ((Paths.polynomial parameter).eval (coordinate site parameter scale quarter positive first)))
    (attached_eq : attached = SquareRootChannelOwnership.attach root) : Source reading prepared :=
  ⟨⟨root, retained⟩, ⟨attached, attached_eq⟩⟩

/-- Attach a supplied completed original full-cubic certificate without rebuilding its preparation or certificate. -/
def ofRoot (root : SourceRoot reading)
    (retained : root = CertifiedSquareRoot.Certificate.ofPrepared reading.lift.value reading.lift.square prepared) :
    Source reading prepared :=
  let attached := SquareRootChannelOwnership.attach root
  ofAttached root retained attached rfl

/-- Construct the full cubic certificate once on the identical preparation, then attach that cached root once. -/
def build (reading : Reading actual first firstInside)
    (prepared : Gaussian.Division.Prepared reading.lift.value) : Source reading prepared :=
  let root := CertifiedSquareRoot.Certificate.ofPrepared reading.lift.value reading.lift.square prepared
  ofRoot root rfl

/-- Read the complete original full-cubic source certificate retained by the cached attachment. -/
@[expose] def root (source : Source reading prepared) : SourceRoot reading := source.1.val

/-- Read the genuine retained continuation owner and its original source-to-owner comparison. -/
@[expose] def attached (source : Source reading prepared) : SquareRootChannelOwnership.Attachment source.root.value
    ((Paths.polynomial parameter).eval (coordinate site parameter scale quarter positive first)) := source.2.val

/-- The full source certificate is the exact original factory on the unchanged supplied preparation. -/
theorem root_eq (source : Source reading prepared) :
    source.root = CertifiedSquareRoot.Certificate.ofPrepared reading.lift.value reading.lift.square prepared :=
  source.1.property

/-- The source certificate keeps the complete original prepared product denominator value. -/
theorem root_value (source : Source reading prepared) : source.root.value = prepared.denominator := by
  rewrite [source.root_eq]
  exact CertifiedSquareRoot.Certificate.ofPrepared_value reading.lift.value reading.lift.square prepared

/-- The additional owner and its comparison are the exact retained completed original attachment. -/
theorem attached_eq (source : Source reading prepared) :
    source.attached = SquareRootChannelOwnership.attach source.root := source.2.property

/-- Retaining a completed certificate stores the identical supplied complete certificate value. -/
theorem ofAttached_root (root : SourceRoot reading)
    (retained : root = CertifiedSquareRoot.Certificate.ofPrepared reading.lift.value reading.lift.square prepared)
    (attached : SquareRootChannelOwnership.Attachment root.value
      ((Paths.polynomial parameter).eval (coordinate site parameter scale quarter positive first)))
    (attached_eq : attached = SquareRootChannelOwnership.attach root) :
    (ofAttached root retained attached attached_eq).root = root := rfl

/-- Retaining a completed attachment stores the identical supplied owner and original operational comparison. -/
theorem ofAttached_attached (root : SourceRoot reading)
    (retained : root = CertifiedSquareRoot.Certificate.ofPrepared reading.lift.value reading.lift.square prepared)
    (attached : SquareRootChannelOwnership.Attachment root.value
      ((Paths.polynomial parameter).eval (coordinate site parameter scale quarter positive first)))
    (attached_eq : attached = SquareRootChannelOwnership.attach root) :
    (ofAttached root retained attached attached_eq).attached = attached := rfl

/-- The actual original cubic product channel agrees with the exact retained additional continuation-owner channel. -/
def agrees (source : Source reading prepared) : Gaussian.Equivalence.NamedEquivalent reading.lift.value.name
    (source.attached.owner.certificate source.attached.owner.parameterNonzero).value.name :=
  Gaussian.Equivalence.NamedEquivalent.trans
    (Gaussian.Equivalence.NamedEquivalent.transport rfl
      (congrArg (fun root : SourceRoot reading => root.value.name) source.root_eq).symm
      (CertifiedSquareRoot.Certificate.ofPrepared_agrees reading.lift.value reading.lift.square prepared))
    source.attached.equivalent

/-- The exact original spatial source has nonzero full cubic value. -/
theorem nonroot (source : Source reading prepared) :
    (Paths.polynomial parameter).eval (coordinate site parameter scale quarter positive first) ≠ 0 :=
  SquareRootChannelOwnership.parameter_nonzero source.root

/-- The exact computed local source square carrying the original full-cubic region clearance. -/
@[expose] def box (source : Source reading prepared) :=
  Point.box (Paths.polynomial parameter) (coordinate site parameter scale quarter positive first) source.nonroot

/-- Construct the quantitative clearance on that same original source square. -/
def clearance (source : Source reading prepared) :
    Polynomial.Clearance.Box.Region.RegionClearance (Paths.polynomial parameter) source.box :=
  Point.clearance (Paths.polynomial parameter) (coordinate site parameter scale quarter positive first) source.nonroot

/-- The original quarter's exact squared chart-time budget. -/
@[expose] def timeScale (_source : Source reading prepared) : Fraction.Rational :=
  (25 / 4) * Norm.Basic.normSq (halfGap site parameter)

/-- The original quarter's chart-time budget is nonnegative. -/
theorem timeScale_nonnegative (source : Source reading prepared) : 0 ≤ source.timeScale :=
  Arithmetic.mul_nonneg_direct (by decide +kernel) (Norm.Basic.normSq_nonneg _)

/-- The positive chart-time request computing how close an actual endpoint must be to the original source. -/
@[expose] def timeRequest (source : Source reading prepared) : AccuracyRequest :=
  ⟨Point.radius (Paths.polynomial parameter) (coordinate site parameter scale quarter positive first) ^ 2 /
      (1 + source.timeScale),
    Fraction.Order.Field.div_pos_direct
      (Arithmetic.pow_pos_direct
        (Point.radius_positive _ _ source.nonroot) 2)
      (Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide +kernel) source.timeScale_nonnegative)⟩

/-- The computed finite dyadic chart index pays the original source's actual spatial clearance request. -/
@[expose] def minimum (source : Source reading prepared) : Nat :=
  Geometric.Search.firstQuarterBelow 1 0 source.timeRequest.tolerance

/-- The original chart-time accuracy payment places the actual spatial endpoint in the same cleared source square. -/
theorem target_inside_of_payment (source : Source reading prepared)
    (payment : (last - first) ^ 2 ≤ source.timeRequest.tolerance) :
    source.box.Contains (coordinate site parameter scale quarter positive last) := by
  have paid := (Fraction.Order.Field.le_div_iff_pos
    (Arithmetic.add_pos_of_pos_of_nonneg_direct
      (by decide +kernel : (0 : Fraction.Rational) < 1) source.timeScale_nonnegative)).mp payment
  have spatial := quarter_base_distance_le site parameter scale quarter positive actual.data.lower actual.data.upper
    last first
  apply Point.contains_of_distance (Paths.polynomial parameter)
    (coordinate site parameter scale quarter positive first) source.nonroot
  apply spatial.trans
  have factor : source.timeScale ≤ 1 + source.timeScale := by
    have bound := Arithmetic.add_le_add_right_direct
      (by decide +kernel : (0 : Fraction.Rational) ≤ 1) source.timeScale
    rewrite [Fraction.Field.zero_add] at bound
    exact bound
  calc
    _ ≤ (1 + source.timeScale) * (last - first) ^ 2 :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct factor
        (Arithmetic.sq_nonneg_direct (last - first))
    _ = (last - first) ^ 2 * (1 + source.timeScale) := Fraction.Field.mul_comm _ _
    _ ≤ _ := paid

/-- The source's computed dyadic squared-width payment places that same original endpoint in its cleared square. -/
theorem target_inside (source : Source reading prepared)
    (payment : (last - first) ^ 2 ≤ Geometric.Basic.quarterRadius 1 source.minimum) :
    source.box.Contains (coordinate site parameter scale quarter positive last) :=
  source.target_inside_of_payment (payment.trans
    (Geometric.Search.firstQuarterBelow_accurate
      1 (by decide +kernel) 0 source.timeRequest.tolerance source.timeRequest.positive).le)

/-- Construct the actual spatial in-box L route between the two unchanged original quarter coordinates.

The existing Route constructor supplies its exact endpoints, region-clear
axis edges, complete in-box containment and zero/one/two-leg count. The actual
spatial endpoints come from the original quarter coordinate law; a separate
Connector retains the supplied original target root-reading cache.
-/
def geometry (source : Source reading prepared)
    (payment : (last - first) ^ 2 ≤ Geometric.Basic.quarterRadius 1 source.minimum) :
    ClearBoxPaths.Route (Paths.polynomial parameter) source.box
      (coordinate site parameter scale quarter positive first)
      (coordinate site parameter scale quarter positive last) :=
  ClearBoxPaths.Route.build source.clearance _ _ (Point.center_inside _ _ source.nonroot)
    (source.target_inside payment)

/-- The exact retained original target reading and its newly constructed actual cleared spatial route.

The original target cache is stored unchanged beside the original Route
container. Its complete route equation retains the computed local clearance
factory; no target cubic owner is identified with a later continued owner.
-/
@[expose] def Connector (source : Source reading prepared) (target : Reading actual last lastInside)
    (payment : (last - first) ^ 2 ≤ Geometric.Basic.quarterRadius 1 source.minimum) : Type 1 :=
  { retained : Reading actual last lastInside // retained = target } ×
    { route : ClearBoxPaths.Route (Paths.polynomial parameter) source.box
        (coordinate site parameter scale quarter positive first)
        (coordinate site parameter scale quarter positive last) // route = source.geometry payment }

/-- Store the exact supplied original target and actual cleared spatial geometry without querying either root again. -/
@[expose] def connect (source : Source reading prepared) (target : Reading actual last lastInside)
    (payment : (last - first) ^ 2 ≤ Geometric.Basic.quarterRadius 1 source.minimum) :
    source.Connector target payment :=
  let route := source.geometry payment
  ⟨⟨target, rfl⟩, ⟨route, rfl⟩⟩

namespace Connector

variable {source : Source reading prepared} {suppliedTarget : Reading actual last lastInside}
variable {payment : (last - first) ^ 2 ≤ Geometric.Basic.quarterRadius 1 source.minimum}

/-- Read the identical original complete target quarter Reading, preserving its separate cofactor and cubic owners. -/
@[expose] def target (connector : source.Connector suppliedTarget payment) :
    Reading actual last lastInside := connector.1.val

/-- The retained target is the entire supplied original Reading, rather than an equal endpoint replacement. -/
theorem target_eq (connector : source.Connector suppliedTarget payment) : connector.target = suppliedTarget :=
  connector.1.property

/-- Read the actual original cleared spatial Route container retained by this connector. -/
@[expose] def geometry (connector : source.Connector suppliedTarget payment) :
    ClearBoxPaths.Route (Paths.polynomial parameter) source.box
      (coordinate site parameter scale quarter positive first)
      (coordinate site parameter scale quarter positive last) := connector.2.val

/-- The route is the complete original in-box factory on the identical paid endpoints and local clearance. -/
theorem geometry_eq (connector : source.Connector suppliedTarget payment) :
    connector.geometry = source.geometry payment := connector.2.property

/-- Connecting keeps the supplied original target query as one complete cache. -/
theorem connect_target (source : Source reading prepared) (targetReading : Reading actual last lastInside)
    (payment : (last - first) ^ 2 ≤ Geometric.Basic.quarterRadius 1 source.minimum) :
    (source.connect targetReading payment).target = targetReading := rfl

/-- The connected route is the original constructed spatial geometry on that same retained request payment. -/
theorem connect_geometry (source : Source reading prepared) (targetReading : Reading actual last lastInside)
    (payment : (last - first) ^ 2 ≤ Geometric.Basic.quarterRadius 1 source.minimum) :
    (source.connect targetReading payment).geometry = source.geometry payment := rfl

end Connector

end Source

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial
