module

import all Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

/-! # Complete original moved-Route constructor

Import-all reduces the original unexposed Geometry.detour body solely for
this private quantified complete former-value regression.
-/

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Polynomial.Clearance.Box.Region (RegionClearance)
open Purelib.Polynomial.Bounds (Horner)
open Purelib.Approximation
open Purelib.RootIsolation
open Purelib.Data.List (DependentProduct)
open Purelib.Integration.Path.Dyadic

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2} {actual : Quarter site parameter 2 quarter positive}
variable {first last : Fraction.Rational} {firstInside : FixedRootBoxPath.Inside first}
variable {lastInside : FixedRootBoxPath.Inside last}

variable {reading : Reading actual first firstInside} {targetReading : Reading actual last lastInside}
variable {regular : parameter ≠ criticalValue site}
variable {payment : (last - first) ^ 2 ≤ Approximation.Rational.Geometric.Basic.quarterRadius 1 7}

namespace Geometry

open Purelib.Geometry.Rational.Box.Square
open Purelib.Geometry.Rational.Box.Refinement
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider (AxisClearances)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (VerticalLine HorizontalLine)
open Purelib.Polynomial.Geometry.Grid

/-- The complete historical moved Route, retained only for the whole-constructor kernel comparison. -/
private def formerDetour {degreeBound : Nat} {ambient : Box}
    (geometry : Geometry reading targetReading regular payment)
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (clearances : AxisClearances elimination)
    {firstAmbient : (neighborhood site parameter regular
      (coordinate site parameter 2 quarter positive first)).Refines ambient}
    {lastAmbient : (neighborhood site parameter regular
      (coordinate site parameter 2 quarter positive last)).Refines ambient}
    (source : Lines elimination clearances regular
      (coordinate site parameter 2 quarter positive first) firstAmbient)
    (target : Lines elimination clearances regular
      (coordinate site parameter 2 quarter positive last) lastAmbient) :
    ClearBoxPaths.Route (Paths.polynomial parameter) (box site parameter quarter first regular)
      source.point target.point :=
  ClearBoxPaths.Route.build geometry.clearance source.point target.point (by
    have smaller : Radial.Clearance.radius site parameter / 32 < Radial.Clearance.radius site parameter := by
      apply (Fraction.Order.Field.div_lt_iff_pos (by decide +kernel : (0 : Fraction.Rational) < 32)).mpr
      calc
        Radial.Clearance.radius site parameter = 1 * Radial.Clearance.radius site parameter := by ring1
        _ < 32 * Radial.Clearance.radius site parameter :=
          Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
            (by decide +kernel : (1 : Fraction.Rational) < 32)
            (Radial.Clearance.radius_positive site parameter regular)
        _ = Radial.Clearance.radius site parameter * 32 := by ring1
    exact (StrictInterior.refines (Centered.centeredSquare_strictInterior_of_lt
      (coordinate site parameter 2 quarter positive first)
      (Fraction.Order.Field.div_pos_direct (Radial.Clearance.radius_positive site parameter regular)
        (by decide +kernel)).le (Radial.Clearance.radius_positive site parameter regular).le
          smaller)).contains source.point_inside) (by
    exact (StrictInterior.refines (Radial.Clearance.quarter_target_neighborhood_strictInterior
      site parameter quarter regular first last payment)).contains target.point_inside)

/-- Factoring the original endpoint proofs preserves the complete Route value. -/
private theorem detour_whole_former {degreeBound : Nat} {ambient : Box}
    (geometry : Geometry reading targetReading regular payment)
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (clearances : AxisClearances elimination)
    {firstAmbient : (neighborhood site parameter regular
      (coordinate site parameter 2 quarter positive first)).Refines ambient}
    {lastAmbient : (neighborhood site parameter regular
      (coordinate site parameter 2 quarter positive last)).Refines ambient}
    (source : Lines elimination clearances regular
      (coordinate site parameter 2 quarter positive first) firstAmbient)
    (target : Lines elimination clearances regular
      (coordinate site parameter 2 quarter positive last) lastAmbient) :
    geometry.detour elimination clearances source target =
      formerDetour geometry elimination clearances source target := (rfl)

end Geometry

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
