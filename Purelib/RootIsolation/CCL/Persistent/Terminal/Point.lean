module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RootIsolation.CCL.Persistent.State.Basic
import Purelib.RootIsolation.Track.Basic
public import Purelib.RootIsolation.Track.Exclusion.Point
import Purelib.Data.CCL.Encoding.Parser.State
import Purelib.Data.Gaussian.Field
import Purelib.Data.List.BinaryPrefix.Basic
public import Purelib.Data.List.Append
import Purelib.Geometry.CCL.Parser.Formula.Advance
import Purelib.Geometry.CCL.Parser.Formula.Input
import Purelib.Geometry.Projective.Hermitian.Formula.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.RootIsolation.CCL.Persistent.Sample.Basic
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

public section

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Resolving rational terminal samples on a persistent CCL track

Every displayed Gaussian-rational sample has a finite CCL terminal.  Reaching
that terminal while constructing a persistent prefix therefore does not by
itself mean that the polynomial root is rational.  This module makes the
necessary distinction executable: evaluate the polynomial at the displayed
terminal point; return an exact root when it vanishes, otherwise perform one
coefficient-computed winding-one refinement that excludes that point.
-/

namespace Purelib.RootIsolation.CCL.Persistent.Terminal.Point

set_option genInjectivity false in
/-- A same-prefix refinement that proves the previously terminal displayed
sample is no longer in the numerical box. -/
structure Escaped
    {p : CoefficientPolynomial} {ambient : Box}
    (current : State p ambient) where
  /-- The retained persistent state after excluding the previously terminal sample. -/ state :
    State p ambient
  /-- The returned state refines the original box and preserves its raw prefix. -/ refines :
    CCL.Persistent.State.Basic.StateRefines state current
  /-- The original state's displayed terminal sample is outside the returned numerical box. -/ excluded :
    ¬state.numerical.box.Contains current.currentSample.point

constructive_injectivity Escaped

set_option genInjectivity false in
/-- Result of inspecting a local affine-terminal decision. -/
inductive Resolution
    {p : CoefficientPolynomial} {ambient : Box}
    (current : State p ambient) where
  /-- The locally terminal displayed sample is a certified exact root in the original box. -/ | exact (root :
    CCL.Persistent.State.Basic.ExactRootIn p current.numerical.box)
  /-- A retained same-prefix refinement excludes the original terminal sample. -/ | escaped (result :
    Escaped current)

constructive_injectivity Resolution

/-- If the current compatible sample is locally terminal, decide whether it
is an exact polynomial root.  A nonroot is removed by one explicit shrinking
track request while the existing persistent prefix is retained. -/
@[expose] def resolve?
    {p : CoefficientPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : Track.Basic.WindingOneTrack p ambient) (current : State p ambient) :
    Option (Resolution current) :=
  let sample := current.currentSample
  match sample.nextDecision.decision with
  | .next _ _ _ => none
  | .terminal _ =>
      if root : p.eval sample.point = 0 then
        some (.exact ⟨sample.point, root, sample.inside⟩)
      else
        let numerical :=
          Track.Exclusion.Point.refinePastPoint
            track current.numerical sample.point root
        let boxRefines :=
          Track.Exclusion.Point.refinePastPoint_refines
            track current.numerical sample.point root
        let state := current.refine numerical boxRefines
        some (.escaped
          { state := state
            refines := ⟨boxRefines, ⟨[], Purelib.Data.List.Append.append_nil current.word⟩⟩
            excluded := by
              exact Track.Exclusion.Point.refinePastPoint_excludes
                degreePositive track current.numerical sample.point root })

set_option genInjectivity false in
/-- Result of resolving one fixed affine point against a winding-one state.
An exact root is returned only when the point is in the current box;
otherwise the returned state finitely certifies that the point is outside. -/
inductive PointResolution
    {p : CoefficientPolynomial} {ambient : Box}
    (current : State p ambient) (point : Gaussian.Basic.Canonical) where
  /-- A certified exact root retained inside the original current box. -/ | exact (root :
    CCL.Persistent.State.Basic.ExactRootIn p current.numerical.box)
  /-- A same-word refinement with a proof that the specified original point lies outside its box. -/ | excluded (state :
    State p ambient)
      (boxRefines : state.numerical.box.Refines current.numerical.box)
      (word_eq : state.word = current.word)
      (outside : ¬state.numerical.box.Contains point)

constructive_injectivity PointResolution

/-- Decide a fixed candidate.  A nonroot is excluded by one
coefficient-computed track refinement; an already-outside exact root needs no
refinement. -/
@[expose] def resolvePoint
    {p : CoefficientPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : Track.Basic.WindingOneTrack p ambient) (current : State p ambient)
    (point : Gaussian.Basic.Canonical) : PointResolution current point := by
  if root : p.eval point = 0 then
    if inside : current.numerical.box.Contains point then
      exact .exact ⟨point, root, inside⟩
    else
      exact .excluded current
        (Box.refines_refl current.numerical.box) rfl
        inside
  else
    let numerical :=
      Track.Exclusion.Point.refinePastPoint
        track current.numerical point root
    let boxRefines :=
      Track.Exclusion.Point.refinePastPoint_refines
        track current.numerical point root
    let state := current.refine numerical boxRefines
    exact .excluded state boxRefines rfl
      (Track.Exclusion.Point.refinePastPoint_excludes
        degreePositive track current.numerical point root)
end Purelib.RootIsolation.CCL.Persistent.Terminal.Point

end
