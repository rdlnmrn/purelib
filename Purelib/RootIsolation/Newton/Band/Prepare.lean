module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.State.Raw
import Purelib.Data.Rat.Bounds.Radius
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Square.Centered.Interior
import Purelib.Polynomial.Clearance.Box.Boundary.Lines
public import Purelib.Polynomial.Clearance.Box.Line.Elimination.Band
import Purelib.Polynomial.Clearance.Box.ProtectedRadius
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Budget.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Band
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.Polynomial.Winding.Box.Newton.Band
public import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.RootIsolation.Newton.Extraction.Basic
public import Purelib.RootIsolation.Newton.Extraction.Build
public import Purelib.RootIsolation.Newton.Extraction.Geometry
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Clearance.Box.Line.Restriction
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Band.Basic
public import Purelib.Geometry.Rational.Box.Band.Bounds
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Band.Parameters
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction

open Purelib.Polynomial.Dense.Gaussian.Newton.Box.Budget

open Purelib.Polynomial.Clearance.Box.Line.Elimination

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-! Complete the original Newton-band and winding-state constructors around
a restored exact local extraction. No different cut or track is selected. -/
namespace Purelib.RootIsolation.Newton.Band.Prepare

open Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic (SquarefreeCertificate)

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.Polynomial.Clearance.Box.Line.Basic (VerticalLineClearance HorizontalLineClearance)
open Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor

/-- A retained local Newton output equal to the original extraction result on the same state and request. -/
abbrev Core {p :
  CoefficientPolynomial} {ambient :
  Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree) (squarefree : SquarefreeCertificate
      p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p ambient) {epsilon : Fraction.Rational} (positive : 0 < epsilon) :=
  {value : Extraction.Basic.Output squarefree current epsilon //
    value = Extraction.Build.extract degreeAtLeastTwo squarefree elimination current positive}

/-- Read the actual geometric fields of a retained original complete extraction.

The source, radius and Newton point are consumed from the supplied cache.
Its whole-output identity supplies the original radius equation in erased
proof data, without executing another extraction producer.
-/
def Core.geometry
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound : Nat}
    {degreeAtLeastTwo : 2 ≤ p.natDegree} {squarefree : SquarefreeCertificate p}
    {elimination : AxisEliminationCertificate p degreeBound}
    {current : State.Raw.RawWindingState p ambient} {epsilon : Fraction.Rational} {positive : 0 < epsilon}
    (saved : Core degreeAtLeastTwo squarefree elimination current positive) :
    Extraction.Geometry squarefree current epsilon :=
  Extraction.Geometry.ofOutput saved.val (by rewrite [saved.property]; rfl)

/-- Reading retained core geometry preserves its actual original source. -/
theorem Core.geometry_source
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound : Nat}
    {degreeAtLeastTwo : 2 ≤ p.natDegree} {squarefree : SquarefreeCertificate p}
    {elimination : AxisEliminationCertificate p degreeBound}
    {current : State.Raw.RawWindingState p ambient} {epsilon : Fraction.Rational} {positive : 0 < epsilon}
    (saved : Core degreeAtLeastTwo squarefree elimination current positive) :
    saved.geometry.source = saved.val.source := rfl

/-- Reading retained core geometry preserves its actual original radius. -/
theorem Core.geometry_radius
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound : Nat}
    {degreeAtLeastTwo : 2 ≤ p.natDegree} {squarefree : SquarefreeCertificate p}
    {elimination : AxisEliminationCertificate p degreeBound}
    {current : State.Raw.RawWindingState p ambient} {epsilon : Fraction.Rational} {positive : 0 < epsilon}
    (saved : Core degreeAtLeastTwo squarefree elimination current positive) :
    saved.geometry.radius = saved.val.radius := rfl

/-- Reading retained core geometry preserves its actual original Newton point. -/
theorem Core.geometry_point
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound : Nat}
    {degreeAtLeastTwo : 2 ≤ p.natDegree} {squarefree : SquarefreeCertificate p}
    {elimination : AxisEliminationCertificate p degreeBound}
    {current : State.Raw.RawWindingState p ambient} {epsilon : Fraction.Rational} {positive : 0 < epsilon}
    (saved : Core degreeAtLeastTwo squarefree elimination current positive) :
    saved.geometry.newton.point = saved.val.newton.point := rfl

namespace Lines

variable {p : CoefficientPolynomial} {degreeBound : Nat}
  (elimination : AxisEliminationCertificate p degreeBound)
  (ambient : Box) (center : Gaussian.Basic.Canonical) {radius : Fraction.Rational} (positive : 0 < radius)

/-- A saved full-line clearance equal to the original left band-side certificate. -/
abbrev Left := {value : VerticalLineClearance p ambient
  (Elimination.Axis.Band.selectedBand elimination center radius positive).box.xLower //
    value = Band.selectedBandLeftClearance elimination ambient center positive}

/-- A saved full-line clearance equal to the original right band-side certificate. -/
abbrev Right := {value : VerticalLineClearance p ambient
  (Elimination.Axis.Band.selectedBand elimination center radius positive).box.xUpper //
    value = Band.selectedBandRightClearance elimination ambient center positive}

/-- A saved full-line clearance equal to the original bottom band-side certificate. -/
abbrev Bottom := {value : HorizontalLineClearance p ambient
  (Elimination.Axis.Band.selectedBand elimination center radius positive).box.yLower //
    value = Band.selectedBandBottomClearance elimination ambient center positive}

/-- A saved full-line clearance equal to the original top band-side certificate. -/
abbrev Top := {value : HorizontalLineClearance p ambient
  (Elimination.Axis.Band.selectedBand elimination center radius positive).box.yUpper //
    value = Band.selectedBandTopClearance elimination ambient center positive}

end Lines

set_option genInjectivity false in
/-- The exact original current-box and fixed-ambient line certificates of a Newton band.

Each side retains both original ambient contexts. Its complete line-clearance
records carry equality to the original selected-side constructors. -/
structure Lines {p : CoefficientPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (current ambient : Box) (center : Gaussian.Basic.Canonical) {radius : Fraction.Rational}
    (positive : 0 < radius) where
  /-- The original left line in the current and fixed ambient boxes. -/
  left : Lines.Left elimination current center positive × Lines.Left elimination ambient center positive
  /-- The original right line in the current and fixed ambient boxes. -/
  right : Lines.Right elimination current center positive × Lines.Right elimination ambient center positive
  /-- The original bottom line in the current and fixed ambient boxes. -/
  bottom : Lines.Bottom elimination current center positive × Lines.Bottom elimination ambient center positive
  /-- The original top line in the current and fixed ambient boxes. -/
  top : Lines.Top elimination current center positive × Lines.Top elimination ambient center positive

constructive_injectivity Lines

/-- Identify the center and radius of the same retained eight band-line certificates. -/
def Lines.identify {p : CoefficientPolynomial} {degreeBound : Nat}
    {elimination : AxisEliminationCertificate p degreeBound}
    {current ambient : Box} {center target : Gaussian.Basic.Canonical} {radius targetRadius : Fraction.Rational}
    {positive : 0 < radius} (lines : Lines elimination current ambient center positive)
    (sameCenter : center = target) (sameRadius : radius = targetRadius) (targetPositive : 0 < targetRadius) :
    Lines elimination current ambient target targetPositive := by
  cases sameCenter
  cases sameRadius
  exact lines

/-- Identifying unchanged center and radius retains the original complete line cache. -/
theorem Lines.identify_self {p : CoefficientPolynomial} {degreeBound : Nat}
    {elimination : AxisEliminationCertificate p degreeBound}
    {current ambient : Box} {center : Gaussian.Basic.Canonical} {radius : Fraction.Rational} {positive : 0 < radius}
    (lines : Lines elimination current ambient center positive) : lines.identify rfl rfl positive = lines := rfl

/-- Construct the exact original eight line certificates for the selected Newton band. -/
def Lines.canonical {p : CoefficientPolynomial}
    {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (current ambient : Box) (center : Gaussian.Basic.Canonical) {radius : Fraction.Rational}
    (positive : 0 < radius) : Lines elimination current ambient center positive where
  left := ⟨⟨Band.selectedBandLeftClearance elimination current center positive, rfl⟩,
    ⟨Band.selectedBandLeftClearance elimination ambient center positive, rfl⟩⟩
  right := ⟨⟨Band.selectedBandRightClearance elimination current center positive, rfl⟩,
    ⟨Band.selectedBandRightClearance elimination ambient center positive, rfl⟩⟩
  bottom := ⟨⟨Band.selectedBandBottomClearance elimination current center positive, rfl⟩,
    ⟨Band.selectedBandBottomClearance elimination ambient center positive, rfl⟩⟩
  top := ⟨⟨Band.selectedBandTopClearance elimination current center positive, rfl⟩,
    ⟨Band.selectedBandTopClearance elimination ambient center positive, rfl⟩⟩

/-- Construct the original Newton output using its actual retained selected band and eight original lines.

The band and complete line certificates are consumed directly. Only coordinate
indices are transported along the whole original-band equality; neither band
selection nor line-clearance preparation is repeated. The original exposed
construction body remains available for the default constructor's reduction. -/
def fromGeometryWithBand
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p ambient) {epsilon : Fraction.Rational}
    (core : Extraction.Geometry squarefree current epsilon)
    (band : Box.Band.Basic.BandBox core.newton.point core.radius)
    (sameBand : band = Elimination.Axis.Band.selectedBand elimination
      core.newton.point core.radius core.radiusPositive)
    (lines : Lines elimination current.box ambient core.newton.point core.radiusPositive) :
    Basic.Output squarefree current epsilon := open Purelib in by
  have radius_eq := core.radius_eq
  let source := core.source
  let r := core.radius
  let center := core.newton.point
  have center_eq : center = anchorNewtonCenter p source.box := core.newton.point_eq
  have radiusPositive : 0 < r := core.radiusPositive
  have displacementSmall : Gaussian.Norm.Basic.normSq (center - source.box.anchor) ≤ r ^ 2 := by
    rewrite [center_eq]
    exact core.displacementSmall
  have bandTaylorSmall := core.bandTaylorSmall
  have twoPositive : (0 : Fraction.Rational) < 2 :=
    Cast.Order.natCast_pos_direct (n := 2) (by decide)
  have twiceRadiusPositive : 0 < 2 * r :=
    Order.Arithmetic.mul_pos_direct twoPositive radiusPositive
  have twiceRadiusNonnegative : 0 ≤ 2 * r := twiceRadiusPositive.le
  have twiceRadiusLeProtected :
      2 * r ≤ Clearance.Box.ProtectedRadius.protectedBoundaryRadius p current.box current.clearance := by
    change 2 * core.radius ≤ _
    rewrite [radius_eq]
    exact Squarefree.extractionRadius_twice_le_protected squarefree current.box
      current.clearance epsilon
  have radiusLeTwice : r ≤ 2 * r :=
    (Bounds.Radius.radius_lt_twice radiusPositive).le
  have radiusSquareLeTwice : r ^ 2 ≤ (2 * r) ^ 2 :=
    Order.Arithmetic.pow_le_pow_direct radiusPositive.le
      radiusLeTwice 2
  have displacementForOuter :
      Gaussian.Norm.Basic.normSq (center - source.box.anchor) ≤ (2 * r) ^ 2 :=
    displacementSmall.trans radiusSquareLeTwice
  let outerSquare := Box.Square.Centered.Affine.centeredSquare center (2 * r) twiceRadiusNonnegative
  have outerStrict : outerSquare.StrictInterior current.box :=
    Box.Square.Centered.Interior.centeredSquare_strictInterior twiceRadiusPositive
      twiceRadiusLeProtected core.stripBounds displacementForOuter
  have bandRefinesOuter : band.box.Refines outerSquare := by
    exact band.refines_outerSquare radiusPositive.le
  have bandStrict : band.box.StrictInterior current.box :=
    Box.Refinement.StrictInterior.of_refines outerStrict bandRefinesOuter
  have bandRefinesCurrent : band.box.Refines current.box := Box.Refinement.StrictInterior.refines
      bandStrict
  have bandRefinesAmbient : band.box.Refines ambient :=
    bandRefinesCurrent.trans current.refinesAmbient
  have bandProper : band.box.Proper := band.proper radiusPositive
  have leftEq := congrArg (fun value => value.box.xLower) sameBand
  have rightEq := congrArg (fun value => value.box.xUpper) sameBand
  have bottomEq := congrArg (fun value => value.box.yLower) sameBand
  have topEq := congrArg (fun value => value.box.yUpper) sameBand
  let leftLine := leftEq.symm ▸ lines.left.1.val
  let rightLine := rightEq.symm ▸ lines.right.1.val
  let bottomLine := bottomEq.symm ▸ lines.bottom.1.val
  let topLine := topEq.symm ▸ lines.top.1.val
  let ambientLeftLine := leftEq.symm ▸ lines.left.2.val
  let ambientRightLine := rightEq.symm ▸ lines.right.2.val
  let ambientBottomLine := bottomEq.symm ▸ lines.bottom.2.val
  let ambientTopLine := topEq.symm ▸ lines.top.2.val
  let bandClearance : Clearance.Box.Boundary.Basic.BoundaryClearance p band.box :=
    Clearance.Box.Boundary.Lines.boundaryOfLines
    (VerticalLineClearance.restrict leftLine bandRefinesCurrent)
    (VerticalLineClearance.restrict rightLine bandRefinesCurrent)
    (HorizontalLineClearance.restrict bottomLine bandRefinesCurrent)
    (HorizontalLineClearance.restrict topLine bandRefinesCurrent)
  have windingFour : Winding.Box.Basic.quadrupledBoxWinding p band.box = 4 := by
    cases sameBand
    have originalRefines := bandRefinesCurrent
    have originalDisplacement := displacementSmall
    change Winding.Box.Basic.quadrupledBoxWinding p
      (Elimination.Axis.Band.selectedBand elimination center r radiusPositive).box = 4
    rewrite [center_eq]
    change (Elimination.Axis.Band.selectedBand elimination center r radiusPositive).box.Refines
      current.box at originalRefines
    rewrite [center_eq] at originalRefines originalDisplacement
    exact Winding.Box.Newton.Band.quadrupledBoxWinding_eq_four_of_newtonBand degreeAtLeastTwo core.newton
      source.refinesAmbient radiusPositive _ originalRefines originalDisplacement bandTaylorSmall
  have radiusEighth : r ≤ (1 / 8 : Fraction.Rational) * epsilon := by
    change core.radius ≤ _
    rewrite [radius_eq]
    exact Squarefree.extractionRadius_le_eighth
      squarefree current.box current.clearance
      epsilon
  have radiusSquare : r ^ 2 ≤ ((1 / 8 : Fraction.Rational) * epsilon) ^ 2 :=
    Order.Arithmetic.pow_le_pow_direct radiusPositive.le
      radiusEighth 2
  have thirtyTwoNonnegative : (0 : Fraction.Rational) ≤ 32 :=
    (Cast.Order.natCast_pos_direct
      (n := 32) (by decide)).le
  have epsilonSquareNonnegative :=
    Order.Arithmetic.sq_nonneg_direct epsilon
  have halfSquare : (1 / 2 : Fraction.Rational) * epsilon ^ 2 ≤ epsilon ^ 2 := by
    calc
      (1 / 2 : Fraction.Rational) * epsilon ^ 2 ≤ 1 * epsilon ^ 2 :=
        Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (show (1 / 2 : Fraction.Rational) ≤ 1 by decide)
          epsilonSquareNonnegative
      _ = epsilon ^ 2 := by ring1
  have diagonalHalf :
      band.box.diagonalSq ≤ (1 / 2 : Fraction.Rational) * epsilon ^ 2 := by
    have coefficientIdentity :
        (32 : Fraction.Rational) * (1 / 8) ^ 2 = 1 / 2 := by
      have eightNonzero : (8 : Fraction.Rational) ≠ 0 :=
        (Cast.Order.natCast_pos_direct
          (n := 8) (by decide)).ne'
      have twoNonzero : (2 : Fraction.Rational) ≠ 0 :=
        (Cast.Order.natCast_pos_direct
          (n := 2) (by decide)).ne'
      have eighthCancel : (1 / 8 : Fraction.Rational) * 8 = 1 :=
        Field.div_mul_cancel_of_ne 1 8 eightNonzero
      have halfCancel : (1 / 2 : Fraction.Rational) * 2 = 1 :=
        Field.div_mul_cancel_of_ne 1 2 twoNonzero
      apply Field.mul_right_cancel_of_ne twoNonzero
      calc
        ((32 : Fraction.Rational) * (1 / 8) ^ 2) * 2 =
            ((1 / 8 : Fraction.Rational) * 8) * ((1 / 8) * 8) := by ring1
        _ = 1 := by rw [eighthCancel]; ring1
        _ = (1 / 2 : Fraction.Rational) * 2 := halfCancel.symm
    calc
      band.box.diagonalSq ≤ 32 * r ^ 2 := band.diagonalSq_le radiusPositive
      _ ≤ 32 * ((1 / 8 : Fraction.Rational) * epsilon) ^ 2 :=
        Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          radiusSquare thirtyTwoNonnegative
      _ = (32 * (1 / 8 : Fraction.Rational) ^ 2) * epsilon ^ 2 := by ring1
      _ = (1 / 2 : Fraction.Rational) * epsilon ^ 2 := by
        rw [coefficientIdentity]
  have diagonal : band.box.diagonalSq ≤ epsilon ^ 2 :=
    diagonalHalf.trans halfSquare
  let canonicalBand := band.recenter center_eq
  exact
    { source := source
      radius := r
      radiusPositive := radiusPositive
      band := canonicalBand
      newton := core.newton
      displacementSmall := by
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using core.displacementSmall
      strictCurrent := bandStrict
      refinesAmbient := bandRefinesAmbient
      proper := bandProper
      leftLineClearance := leftLine
      rightLineClearance := rightLine
      bottomLineClearance := bottomLine
      topLineClearance := topLine
      ambientLeftClearance := ambientLeftLine
      ambientRightClearance := ambientRightLine
      ambientBottomClearance := ambientBottomLine
      ambientTopClearance := ambientTopLine
      clearance := bandClearance
      rawWindingFour := windingFour
      diagonalSq_le_half := diagonalHalf
      diagonalSq_le := diagonal }

/-- Select the original band once and complete it using the retained original line certificates.

The selected band is passed to the shared supplied-band constructor. Its
original fields, bounds and exposed reduction are preserved. -/
def fromGeometryWithLines
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p ambient) {epsilon : Fraction.Rational}
    (core : Extraction.Geometry squarefree current epsilon)
    (lines : Lines elimination current.box ambient core.newton.point core.radiusPositive) :
    Basic.Output squarefree current epsilon :=
  let band := Elimination.Axis.Band.selectedBand elimination core.newton.point core.radius core.radiusPositive
  fromGeometryWithBand degreeAtLeastTwo squarefree elimination current core band rfl lines

/-- Construct the original Newton band from its retained extraction and eight original line certificates.

The original coordinate scans, geometric witnesses and quantitative bounds are
retained. Every current-box and fixed-ambient clearance is consumed from the
supplied exact cache; the canonical clearance providers are not executed. -/
def fromCoreWithLines
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p ambient) {epsilon : Fraction.Rational}
    (epsilonPositive : 0 < epsilon)
    (saved : Core degreeAtLeastTwo squarefree elimination current epsilonPositive)
    (lines : Lines elimination current.box ambient
      (anchorNewtonCenter p saved.val.source.box)
      (Squarefree.extractionRadius_pos squarefree current.clearance current.proper
        epsilonPositive)) : Basic.Output squarefree current epsilon :=
  fromGeometryWithLines degreeAtLeastTwo squarefree elimination current saved.geometry
    (lines.identify saved.geometry.newton.point_eq.symm saved.geometry.radius_eq.symm saved.geometry.radiusPositive)

/-- Construct the same original band using its retained radius, Newton point and canonical line certificates. -/
def fromGeometry
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p ambient) {epsilon : Fraction.Rational}
    (geometry : Extraction.Geometry squarefree current epsilon) :
    Basic.Output squarefree current epsilon :=
  fromGeometryWithLines degreeAtLeastTwo squarefree elimination current geometry
    (Lines.canonical elimination current.box ambient geometry.newton.point geometry.radiusPositive)

/-- Supplying the complete original line cache returns the complete band of the same retained geometry. -/
theorem fromGeometryWithLines_eq
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p ambient) {epsilon : Fraction.Rational}
    (geometry : Extraction.Geometry squarefree current epsilon)
    (lines : Lines elimination current.box ambient geometry.newton.point geometry.radiusPositive) :
    fromGeometryWithLines degreeAtLeastTwo squarefree elimination current geometry lines =
      fromGeometry degreeAtLeastTwo squarefree elimination current geometry := by
  rcases lines with ⟨⟨⟨left, leftEq⟩, ⟨ambientLeft, ambientLeftEq⟩⟩,
    ⟨⟨right, rightEq⟩, ⟨ambientRight, ambientRightEq⟩⟩,
    ⟨⟨bottom, bottomEq⟩, ⟨ambientBottom, ambientBottomEq⟩⟩,
    ⟨⟨top, topEq⟩, ⟨ambientTop, ambientTopEq⟩⟩⟩
  cases leftEq
  cases ambientLeftEq
  cases rightEq
  cases ambientRightEq
  cases ambientBottomEq
  cases bottomEq
  cases topEq
  cases ambientTopEq
  rfl

/-- Construct the original selected Newton band and its eight canonical line certificates.

The retained extraction supplies the same source and Newton centre. The
canonical line constructor feeds the exact-cache constructor, preserving every
original executable band field and geometric certificate. -/
def fromCore
    {p : CoefficientPolynomial} {ambient : Box}
    {degreeBound : Nat} (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p ambient) {epsilon : Fraction.Rational}
    (positive : 0 < epsilon) (saved : Core degreeAtLeastTwo squarefree elimination current positive) :
    Basic.Output squarefree current epsilon :=
  fromGeometry degreeAtLeastTwo squarefree elimination current saved.geometry

/-- Supplying the complete original line cache returns the complete original Newton band. -/
theorem fromCoreWithLines_eq
    {p : CoefficientPolynomial} {ambient : Box}
    {degreeBound : Nat} (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p ambient) {epsilon : Fraction.Rational}
    (positive : 0 < epsilon) (saved : Core degreeAtLeastTwo squarefree elimination current positive)
    (lines : Lines elimination current.box ambient
      (anchorNewtonCenter p saved.val.source.box)
      (Squarefree.extractionRadius_pos squarefree current.clearance current.proper
        positive)) :
    fromCoreWithLines degreeAtLeastTwo squarefree elimination current positive saved lines =
      fromCore degreeAtLeastTwo squarefree elimination current positive saved := by
  rcases saved with ⟨core, same⟩
  cases same
  rcases lines with ⟨⟨⟨left, leftEq⟩, ⟨ambientLeft, ambientLeftEq⟩⟩,
    ⟨⟨right, rightEq⟩, ⟨ambientRight, ambientRightEq⟩⟩,
    ⟨⟨bottom, bottomEq⟩, ⟨ambientBottom, ambientBottomEq⟩⟩,
    ⟨⟨top, topEq⟩, ⟨ambientTop, ambientTopEq⟩⟩⟩
  cases leftEq
  cases ambientLeftEq
  cases rightEq
  cases ambientRightEq
  cases bottomEq
  cases ambientBottomEq
  cases topEq
  cases ambientTopEq
  rfl

end Purelib.RootIsolation.Newton.Band.Prepare

end

public section

namespace Purelib.RootIsolation.Newton.Band.Prepare

open Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Dense.Gaussian.Squarefree.Basic (SquarefreeCertificate)
open Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)

variable {p : CoefficientPolynomial} {ambient : Box} {degreeBound : Nat}
  (degreeAtLeastTwo : 2 ≤ p.natDegree) (squarefree : SquarefreeCertificate p)
  (elimination : AxisEliminationCertificate p degreeBound)
  (current : State.Raw.RawWindingState p ambient) {epsilon : Fraction.Rational}
  (core : Extraction.Geometry squarefree current epsilon)
  (band : Box.Band.Basic.BandBox core.newton.point core.radius)
  (sameBand : band = Elimination.Axis.Band.selectedBand elimination
    core.newton.point core.radius core.radiusPositive)
  (lines : Lines elimination current.box ambient core.newton.point core.radiusPositive)

/-- Read back the supplied band and its box alongside the complete original output equality. -/
private theorem fromGeometryWithBand_readbacks :
    (fromGeometryWithBand degreeAtLeastTwo squarefree elimination current core band sameBand lines).band =
        band.recenter core.newton.point_eq ∧
    (fromGeometryWithBand degreeAtLeastTwo squarefree elimination current core band sameBand lines).box =
        band.box ∧
    fromGeometryWithBand degreeAtLeastTwo squarefree elimination current core band sameBand lines =
      fromGeometryWithLines degreeAtLeastTwo squarefree elimination current core lines := by
  constructor
  · rfl
  constructor
  · rfl
  · cases sameBand
    rfl

/-- The supplied-band constructor retains the actual band with only its original Newton-centre identification. -/
theorem fromGeometryWithBand_band :
    (fromGeometryWithBand degreeAtLeastTwo squarefree elimination current core band sameBand lines).band =
      band.recenter core.newton.point_eq :=
  (fromGeometryWithBand_readbacks degreeAtLeastTwo squarefree elimination current core band sameBand lines).1

/-- The supplied-band constructor returns the exact original cached box. -/
theorem fromGeometryWithBand_box :
    (fromGeometryWithBand degreeAtLeastTwo squarefree elimination current core band sameBand lines).box = band.box :=
  (fromGeometryWithBand_readbacks degreeAtLeastTwo squarefree elimination current core band sameBand lines).2.1

/-- Supplying the retained original band preserves the complete original Newton output. -/
theorem fromGeometryWithBand_eq :
    fromGeometryWithBand degreeAtLeastTwo squarefree elimination current core band sameBand lines =
      fromGeometryWithLines degreeAtLeastTwo squarefree elimination current core lines :=
  (fromGeometryWithBand_readbacks degreeAtLeastTwo squarefree elimination current core band sameBand lines).2.2

end Purelib.RootIsolation.Newton.Band.Prepare

end
