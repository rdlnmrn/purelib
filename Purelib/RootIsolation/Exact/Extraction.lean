module

import Purelib.Polynomial.Clearance.Box.Region.Basic
public import Purelib.RootIsolation.State.Raw.FromRegion
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Grid.Central.Basic
public import Purelib.Polynomial.Winding.Box.Grid.Central.Build
public import Purelib.RootIsolation.Newton.Extraction.Initial.Build
import Purelib.RootIsolation.Track.Basic
public import Purelib.RootIsolation.Track.Newton.Build
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Lattice
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Line.Restriction
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.Refinement.Basic
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Newton.Refinement

import Purelib.Data.Int.Order
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.Data

/-!
# Extracting a track and its central complement

The original positive clear region supplies one checked Newton extraction.
The retained state and line clearances determine its exact eight-cell grid.
-/

namespace Purelib.RootIsolation.Exact.Extraction

set_option genInjectivity false in
/-- Retain one extracted winding-one track and its original eight-cell complement.

The supplied positive region indexes the retained grid. Its center is the
same track's initial box, with the original strict-interior certificate. -/
public structure RegionExtraction
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (ambient : Box)
    (selected : Clearance.Box.Region.ClearRegion p ambient) where
  /-- The actual retained winding-one track on the original polynomial and ambient box. -/ track :
    Track.Basic.WindingOneTrack p ambient
  /-- The exact central eight-cell complement between the original selected box and retained initial track box. -/ grid
    : Polynomial.Winding.Box.Grid.Central.Basic.Arrangement p selected.box track.initial.box
  /-- The retained initial track box lies strictly inside the original selected region. -/ centerStrict :
    track.initial.box.StrictInterior selected.box

constructive_injectivity RegionExtraction

/-- Extract a winding-one track and its exact central complement from the original positive-winding region.

The original checked Newton extraction supplies a strict inner state; its retained line clearances build the eight-cell
grid inside the same selected region. -/
@[expose] public def extractRegion
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (selected : Clearance.Box.Region.ClearRegion p ambient)
    (positive : 0 < Winding.Box.Basic.quadrupledBoxWinding p selected.box) :
    Exact.Extraction.RegionExtraction p ambient selected := by
  let raw := selected.raw (by
    intro equal
    have impossible : (0 : Int) < 0 := equal ▸ positive
    exact Int.Order.lt_irrefl 0 impossible)
  let onePositive : (0 : Fraction.Rational) < 1 :=
    Fraction.Cast.Order.natCast_pos_direct (n := 1) (by decide)
  let extracted := Newton.Extraction.Initial.Build.extract degreeAtLeastTwo
    squarefree elimination raw onePositive
  let centerState := extracted.state
  let track := Track.Newton.Build.ofInitial degreeAtLeastTwo
    squarefree elimination centerState
  let grid : Polynomial.Winding.Box.Grid.Central.Basic.Arrangement p selected.box centerState.box :=
    Winding.Box.Grid.Central.Build.build selected.clearance centerState.proper extracted.strict
      (centerState.ambientLeftClearance.restrict selected.refinesAmbient)
      (centerState.ambientRightClearance.restrict selected.refinesAmbient)
      (centerState.ambientBottomClearance.restrict selected.refinesAmbient)
      (centerState.ambientTopClearance.restrict selected.refinesAmbient)
  exact
    { track := track
      grid := by
        simpa only [track, Track.Newton.Build.ofInitial,
          centerState] using grid
      centerStrict := by
        simpa only [track, Track.Newton.Build.ofInitial,
          centerState, raw, Clearance.Box.Region.ClearRegion.raw] using extracted.strict }

end Purelib.RootIsolation.Exact.Extraction
