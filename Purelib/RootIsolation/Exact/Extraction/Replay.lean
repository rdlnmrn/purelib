module
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Grid.Central.Build
public import Purelib.Polynomial.Winding.Box.Region.Sum
public import Purelib.RootIsolation.Exact.Extraction
public import Purelib.RootIsolation.Exact.State
import Purelib.RootIsolation.Refinement.Basic
import Purelib.RootIsolation.Track.Newton.Build

import Purelib.Data.Rat.Fraction.Order
import Purelib.RootIsolation.Newton.Extraction.Initial.Build
public import Purelib.Data.Int.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Clearance.Box.Line.Restriction
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Winding.Box.Grid.Central.Basic
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.State.Raw.FromRegion
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

public section

/-!
# Exact isolation steps from checked extraction checkpoints

Rebuild the numerical fields of an isolation state and retain the original
track constructors.  Equality is to the canonical step, not to an arbitrary
equivalent root family.  Proof-only references to that step disappear from
the executable replay.  This imports only existing finite isolation modules.
-/

namespace Purelib.RootIsolation.Exact.Extraction.Replay

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound
  : Nat}
variable (degreeAtLeastTwo : 2 ≤ p.natDegree) (squarefree :
  Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
  (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)

/-- The same finite track and eight-cell grid as the original extraction,
constructed directly from its checked initial winding-one state. -/
@[expose] def extraction (selected : Clearance.Box.Region.ClearRegion p ambient)
    (positive : 0 < Winding.Box.Basic.quadrupledBoxWinding p selected.box)
    (value : Refinement (selected.raw (by
      intro zero
      have impossible : (0 : Int) < 0 := zero ▸ positive
      exact Purelib.Data.Int.Order.lt_irrefl 0 impossible)) 1) :
    Exact.Extraction.RegionExtraction p ambient selected :=
  let track := Track.Newton.Build.ofInitial degreeAtLeastTwo squarefree elimination value.state
  let grid := Winding.Box.Grid.Central.Build.build selected.clearance value.state.proper value.strict
    (value.state.ambientLeftClearance.restrict selected.refinesAmbient)
    (value.state.ambientRightClearance.restrict selected.refinesAmbient)
    (value.state.ambientBottomClearance.restrict selected.refinesAmbient)
    (value.state.ambientTopClearance.restrict selected.refinesAmbient)
  ⟨track, grid, value.strict⟩

/-- Replaying the retained canonical initial extraction reproduces the original track and central grid exactly. -/
theorem extraction_eq (selected : Clearance.Box.Region.ClearRegion p ambient)
    (positive : 0 < Winding.Box.Basic.quadrupledBoxWinding p selected.box)
    (value : Refinement (selected.raw (by
      intro zero
      have impossible : (0 : Int) < 0 := zero ▸ positive
      exact Purelib.Data.Int.Order.lt_irrefl 0 impossible)) 1)
    (same : value = Newton.Extraction.Initial.Build.extract degreeAtLeastTwo squarefree elimination
      (selected.raw (by
        intro zero
        have impossible : (0 : Int) < 0 := zero ▸ positive
        exact Purelib.Data.Int.Order.lt_irrefl 0 impossible)) (by decide)) :
    Exact.Extraction.Replay.extraction degreeAtLeastTwo squarefree elimination selected positive value =
      Exact.Extraction.extractRegion degreeAtLeastTwo squarefree elimination selected positive := by
  cases same
  rfl

section Steps

variable (state : Exact.State.IsolationState p ambient)
  (nonnegative : ∀ region ∈ state.regions, 0 ≤ Winding.Box.Basic.quadrupledBoxWinding p region.box)
  (positive : 0 < Winding.Box.Region.Sum.totalRaw state.regions)
end Steps

section Runs

variable {state : Exact.State.IsolationState p ambient}
end Runs
end Purelib.RootIsolation.Exact.Extraction.Replay

end
