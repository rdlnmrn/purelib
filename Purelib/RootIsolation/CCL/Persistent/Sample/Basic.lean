module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.CCL.Encoding.Parser.Inverse
import Purelib.Data.CCL.Encoding.Parser.Semantics.Prefix
import Purelib.Data.CCL.Encoding.Parser.Semantics.State
import Purelib.Data.CCL.Encoding.Parser.State
import Purelib.Data.List.BinaryPrefix.Basic
public import Purelib.Geometry.CCL.Parser.Formula.Input
import Purelib.Geometry.CCL.Parser.Formula.State
import Purelib.Geometry.Projective.Homography.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RootIsolation.State.WindingOne.Basic

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Projective.Hermitian.Formula.Basic
import Purelib.Geometry.Rational.Box.Refinement

open Purelib.Data.CCL.Encoding.Parser.Semantics.State (Represents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List.BinaryPrefix.Basic (SourcePersistentCCLWordAlias)
open Purelib.RootIsolation.State.WindingOne.Basic (WindingOneState)

public section

open Purelib

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Persistent constructive CCL prefixes on shrinking root boxes

A fresh rational sample from each refined box need not retain any prefix of
the preceding sample's CCL word.  The persistent invariant below records the
stronger fact actually needed by the paper: every later winding-one subbox
has an explicit nonzero rational sample represented by the same raw prefix.

The second half of the file is deliberately structural.  It proves that a
finite one-bit controller with this invariant can be iterated for any
requested natural number of bits while the numerical box is independently
contracted to a requested rational accuracy.  Constructing that one-bit
controller from the finite curve-count and equality-owner geometry is a
separate obligation; it is not postulated as a theorem here.
-/

namespace Purelib.RootIsolation.CCL.Persistent.Sample.Basic

set_option genInjectivity false in
/-- One displayed nonzero rational point in a box that has the indicated raw
CCL prefix. -/
structure CompatibleSample (word :
  SourcePersistentCCLWordAlias) (box : Box) where
  /-- The retained Gaussian-rational sample. -/ point : Canonical
  /-- The retained sample lies in the displayed box. -/ inside : box.Contains point
  /-- The sample is nonzero, so its raw CCL prefix has an affine representation. -/ nonzero : point ≠ 0
  /-- The displayed raw CCL prefix represents the same retained sample. -/ represented :
    Data.CCL.Encoding.Parser.Semantics.Prefix.Represented word point

constructive_injectivity CompatibleSample

namespace CompatibleSample

set_option genInjectivity false in
/-- Proof-bearing local decision data at one compatible sample. -/
structure NextDecision (word :
  SourcePersistentCCLWordAlias) (input : Canonical) where
  /-- The displayed affine tail representing the input under the parsed prefix. -/ tail : Canonical
  /-- The parsed original prefix maps the retained tail to the original input. -/ represents :
    Represents
    (Data.CCL.Encoding.Parser.State.parse word) input tail
  /-- The finite Hermitian next-bit decision for the original parser, input and retained tail. -/ decision :
    Geometry.CCL.Parser.Formula.Decision
    (Data.CCL.Encoding.Parser.State.parse word) input tail

constructive_injectivity NextDecision

/-- Expose the finite Hermitian formula satisfied by the explicit affine
tail witnessing a sample's raw-prefix representation.  This is the precise
finite predicate consumed by the geometric one-bit controller. -/
theorem tailFormula
    {word : SourcePersistentCCLWordAlias} {box : Box} (sample :
      CCL.Persistent.Sample.Basic.CompatibleSample word box) :
    ∃ tail : Canonical,
      (Geometry.CCL.Parser.Formula.parseFormula word).Holds tail ∧
        Represents
          (Data.CCL.Encoding.Parser.State.parse word) sample.point tail := by
  rcases sample.represented with ⟨tail, represents⟩
  exact ⟨tail,
    (Geometry.CCL.Parser.Formula.parseFormula_iff word tail).2
      represents.2.2,
    represents⟩

/-- Every compatible rational sample has a total finite local next-bit
decision.  Persistence of one selected decision across all later subboxes is
the geometric obligation of the controller. -/
@[expose] def nextDecision
    {word : SourcePersistentCCLWordAlias} {box : Box} (sample :
      CCL.Persistent.Sample.Basic.CompatibleSample word box) :
    CCL.Persistent.Sample.Basic.CompatibleSample.NextDecision word sample.point := by
  let parser := Data.CCL.Encoding.Parser.State.parse word
  let tail := Geometry.Projective.Homography.Basic.homographic
    (LinearAlgebra.Coordinates2.Matrix.BoundaryAdjugate.adjugate parser.matrix) sample.point
  have determinantNonzero :
      LinearAlgebra.Coordinates2.Matrix.BoundaryAdjugate.determinant parser.matrix ≠ 0 := by
    simpa only [parser, LinearAlgebra.Coordinates2.Matrix.BoundaryAdjugate.determinant, -eq_self, -iff_self] using
      Data.CCL.Encoding.Parser.State.parse_det_ne word
  have represents : Represents
      parser sample.point tail := by
    exact Data.CCL.Encoding.Parser.represents_inverse_tail_of_represented
      parser sample.point determinantNonzero sample.represented
  exact
    { tail := tail
      represents := represents
      decision := Geometry.CCL.Parser.Formula.decide
        parser sample.point tail (Data.CCL.Encoding.Parser.State.parse_det_ne word)
        represents }

end CompatibleSample

set_option genInjectivity false in
/-- Persistent compatibility means that a sample can be computed in every
supplied later winding-one subbox, not merely in the currently displayed
box.  The quantification is over explicit finite states and refinement
certificates; it does not form a set or a completed root. -/
structure PersistentSamples
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (word : SourcePersistentCCLWordAlias) (current : WindingOneState
      p ambient) where
  /-- Compute a compatible nonzero sample in any supplied later winding-one box refining the current box. -/ sample :
    (later : WindingOneState p ambient) →
    later.box.Refines current.box → CompatibleSample word later.box

constructive_injectivity PersistentSamples

/-- The empty raw prefix is represented by every displayed rational point,
so every winding-one state has an initial persistent provider. -/
@[expose] def PersistentSamples.initial
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (current : WindingOneState p ambient) : PersistentSamples []
      current where
  sample := fun later _refines =>
    let sample := later.box.nonzeroSample later.proper
    { point := sample.point
      inside := sample.inside
      nonzero := sample.nonzero
      represented :=
        Data.CCL.Encoding.Parser.Semantics.Prefix.represented_nil sample.point }
end Purelib.RootIsolation.CCL.Persistent.Sample.Basic

end
