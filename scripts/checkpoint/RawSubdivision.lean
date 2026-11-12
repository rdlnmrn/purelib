module

public import scripts.checkpoint.RootRefinement
public import Purelib.Approximation.Gaussian.Sequence.SamplePrefix
public import Purelib.RootIsolation.Track.Approximation.Sampling
import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.RootIsolation.Track.Newton.Refinement
import Purelib.RootIsolation.Track.Basic
public import Purelib.RootIsolation.Subdivision.WindingOne
public import Purelib.RootIsolation.Newton.Search.Dyadic
public import Purelib.RootIsolation.Track.Accelerated
public import Purelib.Polynomial.Clearance.Box.Grid.Four.Replay.Lines
public import Purelib.RootIsolation.Subdivision.Raw.Selection.Replay
public import Purelib.RootIsolation.Newton.Band.Prepare
public import Purelib.RootIsolation.FTA.Squarefree.Prepare
public import Purelib.RootIsolation.Newton.Band.Replay
public import Purelib.RootIsolation.Newton.Band.State.Replay
public import Purelib.RootIsolation.Newton.Extraction.Source.Replay
import Purelib.RootIsolation.Subdivision.Raw.Rebase
import Purelib.Polynomial.Elimination.Axis.Cuts
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider
import Purelib.System.FilePath
import Purelib.Data.String.Basic
import Purelib.System.IO

public section

namespace RawSubdivisionCheckpoint

open Purelib.Riemann.RootContinuation
open Purelib.Data.Rat.Bounds

open Purelib
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation
open Purelib.Approximation.Gaussian
open Purelib.RootIsolation.Newton.Band.Prepare
open Purelib.Polynomial.Elimination.Axis
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.Polynomial.Clearance.Box.Line
open Purelib.Polynomial.Clearance.Box.Line.Basic (VerticalLineClearance HorizontalLineClearance)
open Purelib.Polynomial.Clearance.Box.Line.Elimination
open Purelib.Polynomial.Elimination.Axis.Preparation renaming Prepared -> AxisPreparation
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> GaussianCoordinate
open Purelib.Geometry.Rational.Box.Band.Basic (BandBox)

open Purelib.Data (Json)
open Purelib.Data.Json (toJson)
open scoped Purelib.Data.String
open IntegrationCheckpoint
open Purelib.System.FilePath (join)

variable {p : CoefficientPolynomial}
  {ambient : Box} {degreeBound : Nat}

variable {m : Type → Type} [Monad m] [MonadLiftT IO m] [MonadLiftT BaseIO m]
  [MonadExceptOf IO.Error m]

/-- An original raw state after exactly the retained forward-subdivision depth. -/
abbrev Refined
    (elimination : AxisEliminationCertificate p degreeBound)
    (depth : Nat) (current : State.Raw.RawWindingState p ambient) :=
  { value : State.Raw.RawWindingState p ambient //
    value = Subdivision.Raw.Iteration.Forward.refineForwardN elimination depth current }

/-- Restore the original safe-cut grid from saved, independently checked line-clearance columns.

The loader receives the original finite safe coordinates and source box. Both
restored complete certificates are consumed by the exact grid constructor;
no canonical clearance provider is executed by this operation.
-/
@[expose] def grid
    (elimination : AxisEliminationCertificate p degreeBound)
    (loader : RootRefinementCheckpoint.ClearanceLoader elimination
      (.canonical elimination) m)
    (directory : System.FilePath) (current : State.Raw.RawWindingState p ambient) :
    m (Clearance.Box.Grid.Four.Replay.Checked elimination current.box current.proper) := do
  let x := Elimination.Axis.Cuts.verticalSafeCoordinate elimination current.box current.proper
  let y := Elimination.Axis.Cuts.horizontalSafeCoordinate elimination current.box current.proper
  let vertical ← loader.vertical (join directory "vertical") current.box x
    (Elimination.Axis.Cuts.verticalSafeCoordinate_spec elimination current.box current.proper).1
  let horizontal ← loader.horizontal (join directory "horizontal") current.box y
    (Elimination.Axis.Cuts.horizontalSafeCoordinate_spec elimination current.box current.proper).1
  return Clearance.Box.Grid.Four.Replay.fromLines elimination current.box current.proper
    ⟨x, rfl⟩ ⟨y, rfl⟩ vertical horizontal

/-- Restore one original raw step using saved columns and three original ordered winding chains.

Column and winding loaders enforce their saved-only policies independently.
Every scalar is checked against its exact original operands before the original
first-nonzero child is reconstructed. The returned state retains equality to
the complete original refinement step.
-/
@[expose] def step
    (elimination : AxisEliminationCertificate p degreeBound)
    (loader : RootRefinementCheckpoint.ClearanceLoader elimination
      (.canonical elimination) m)
    (winding : WindingCheckpoint.Control m)
    (directory : System.FilePath) (current : State.Raw.RawWindingState p ambient) :
    m (Refined elimination 1 current) := do
  let saved ← grid elimination loader directory current
  let cells := Isolation.RawSubdivisionReplay.grid elimination current saved
  let lowerLeft ← WindingCheckpoint.box winding (join directory "lower-left") p cells.lowerLeft.box
  let upperLeft ← WindingCheckpoint.box winding (join directory "upper-left") p cells.upperLeft.box
  let lowerRight ← WindingCheckpoint.box winding (join directory "lower-right") p cells.lowerRight.box
  let restored := Subdivision.Raw.Selection.Replay.step cells lowerLeft upperLeft lowerRight
  return ⟨restored,
    Subdivision.Raw.Selection.Replay.step_eq elimination saved lowerLeft upperLeft lowerRight⟩

/-- Restore a finite original forward refinement with atomic checkpoints for each column and winding division.

Each recursive call consumes the just-restored original state. A fresh process
can reuse every completed operand-bound certificate. Missing or corrupt data
keeps the existing loaders' exact failed request and original operands.
-/
@[expose] def refineForward
    (elimination : AxisEliminationCertificate p degreeBound)
    (loader : RootRefinementCheckpoint.ClearanceLoader elimination
      (.canonical elimination) m)
    (winding : WindingCheckpoint.Control m)
    (directory : System.FilePath) :
    (depth index : Nat) → (current : State.Raw.RawWindingState p ambient) →
      m (Refined elimination depth current)
  | 0, _, current => pure ⟨current, rfl⟩
  | depth + 1, index, current => do
      let next ← step elimination loader winding (join directory s!"step-{index}") current
      let tail ← refineForward elimination loader winding directory depth (index + 1) next.val
      return ⟨tail.val, tail.property.trans
        (congrArg (Subdivision.Raw.Iteration.Forward.refineForwardN elimination depth) next.property)⟩

/-- Both original vertical clearances at one coordinate, sharing the same elimination owner. -/
abbrev VerticalPair (elimination : AxisEliminationCertificate p degreeBound)
    (current ambient : Box) (coordinate : Rational) (safe : elimination.vertical.eval coordinate ≠ 0) :=
  {value : VerticalLineClearance p current coordinate //
      value = (.canonical elimination : Provider.AxisClearances elimination).vertical
        current coordinate safe} ×
  {value : VerticalLineClearance p ambient coordinate //
      value = (.canonical elimination : Provider.AxisClearances elimination).vertical
        ambient coordinate safe}

/-- Both original horizontal clearances at one coordinate, sharing the same elimination owner. -/
abbrev HorizontalPair (elimination : AxisEliminationCertificate p degreeBound)
    (current ambient : Box) (coordinate : Rational) (safe : elimination.horizontal.eval coordinate ≠ 0) :=
  {value : HorizontalLineClearance p current coordinate //
      value = (.canonical elimination : Provider.AxisClearances elimination).horizontal
        current coordinate safe} ×
  {value : HorizontalLineClearance p ambient coordinate //
      value = (.canonical elimination : Provider.AxisClearances elimination).horizontal
        ambient coordinate safe}

/-- Construct both original ambient-context vertical clearances from one saved exact column.

The supplied elimination cache is exactly the original separated constructor.
One checked column is retained, and its complete cofactor certificate supplies
both line bounds without a second column producer or column reload. -/
@[expose] def pairedVerticalWithDegree
    (p : CoefficientPolynomial)
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree)
    {degreeBound : Nat} (elimination : AxisEliminationCertificate p degreeBound)
    (degreeEq : degreeBound = Separated.separatedEliminationDegree p)
    (same : elimination.castDegree degreeEq =
      Separated.separatedAxisEliminationCertificate p nonzero positive)
    (control : ClearanceCheckpoint.Control m) (directory : System.FilePath) (current ambient : Box)
    (coordinate : Data.Rat.Fraction.Rational) (safe : elimination.vertical.eval coordinate ≠ 0) :
    m ({value : Clearance.Box.Line.Basic.VerticalLineClearance p current coordinate //
        value = (.canonical elimination : Clearance.Box.Line.Elimination.Provider.AxisClearances elimination).vertical
          current coordinate safe} ×
      {value : Clearance.Box.Line.Basic.VerticalLineClearance p ambient coordinate //
        value = (.canonical elimination : Clearance.Box.Line.Elimination.Provider.AxisClearances elimination).vertical
          ambient coordinate safe}) := do
  have originalSafe : (Elimination.Separated.Scalar.scalarEliminant p).eval coordinate ≠ 0 := by
    cases degreeEq
    change elimination = _ at same
    rewrite [same] at safe
    exact safe
  let column ← ClearanceCheckpoint.load control directory p positive coordinate
  let coprime := column.vertical nonzero originalSafe
  have coprimeEq : coprime.val = elimination.vertical_coprime coordinate safe := by
    cases degreeEq
    change elimination = _ at same
    cases same
    exact coprime.property.trans
      (Separated.Replay.computeVertical p nonzero positive coordinate originalSafe).property.symm
  let inner := Bezout.verticalOfCoprime p current coordinate coprime.val
  let outer := Bezout.verticalOfCoprime p ambient coordinate coprime.val
  return ⟨⟨inner, congrArg (Bezout.verticalOfCoprime p current coordinate) coprimeEq⟩,
    ⟨outer, congrArg (Bezout.verticalOfCoprime p ambient coordinate) coprimeEq⟩⟩

/-- Construct both original ambient-context horizontal clearances from one saved quarter-turn column.

The actual quarter-turned source, degree witness and coordinate are retained.
One checked original column supplies both complete line certificates. -/
@[expose] def pairedHorizontalWithDegree
    (p : CoefficientPolynomial)
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree)
    {degreeBound : Nat} (elimination : AxisEliminationCertificate p degreeBound)
    (degreeEq : degreeBound = Separated.separatedEliminationDegree p)
    (same : elimination.castDegree degreeEq =
      Separated.separatedAxisEliminationCertificate p nonzero positive)
    (control : ClearanceCheckpoint.Control m) (directory : System.FilePath) (current ambient : Box)
    (coordinate : Data.Rat.Fraction.Rational) (safe : elimination.horizontal.eval coordinate ≠ 0) :
    m ({value : Clearance.Box.Line.Basic.HorizontalLineClearance p current coordinate //
        value = (.canonical elimination : Clearance.Box.Line.Elimination.Provider.AxisClearances elimination).horizontal
          current coordinate safe} ×
      {value : Clearance.Box.Line.Basic.HorizontalLineClearance p ambient coordinate //
        value = (.canonical elimination : Clearance.Box.Line.Elimination.Provider.AxisClearances elimination).horizontal
          ambient coordinate safe}) := do
  have originalSafe : (Separated.Eliminant.horizontalEliminant p).eval coordinate ≠ 0 := by
    cases degreeEq
    change elimination = _ at same
    rewrite [same] at safe
    exact safe
  let rotated := Dense.Gaussian.Substitution.QuarterTurn.quarterTurn p
  have rotatedPositive : 0 < rotated.natDegree := by
    rewrite [Dense.Gaussian.Substitution.QuarterTurn.quarterTurn_natDegree p nonzero]
    exact positive
  let column ← ClearanceCheckpoint.load control directory rotated rotatedPositive coordinate
  let coprime := Separated.Replay.horizontal p nonzero positive coordinate originalSafe column
  have coprimeEq : coprime.val = elimination.horizontal_coprime coordinate safe := by
    cases degreeEq
    change elimination = _ at same
    cases same
    exact coprime.property.trans
      (Separated.Replay.computeHorizontal p nonzero positive coordinate originalSafe).property.symm
  let inner := Bezout.horizontalOfCoprime p current coordinate coprime.val
  let outer := Bezout.horizontalOfCoprime p ambient coordinate coprime.val
  return ⟨⟨inner, congrArg (Bezout.horizontalOfCoprime p current coordinate) coprimeEq⟩,
    ⟨outer, congrArg (Bezout.horizontalOfCoprime p ambient coordinate) coprimeEq⟩⟩

/-- Restore all eight selected-band lines through supplied paired column readers.

The actual retained band fixes the original left, right, bottom and top order.
Each reader returns both box contexts at its same coordinate, keeping their
complete canonical clearance identities without repeating its column read. -/
@[expose] def bandLinesUsing
    (elimination : AxisEliminationCertificate p degreeBound)
    (vertical : (directory : System.FilePath) → (current ambient : Box) → (coordinate : Rational) →
      (safe : elimination.vertical.eval coordinate ≠ 0) → m (VerticalPair elimination current ambient coordinate safe))
    (horizontal : (directory : System.FilePath) → (current ambient : Box) → (coordinate : Rational) →
      (safe : elimination.horizontal.eval coordinate ≠ 0) →
        m (HorizontalPair elimination current ambient coordinate safe))
    (directory : System.FilePath) (current ambient : Box)
    (center : GaussianCoordinate) {radius : Rational} (radiusPositive : 0 < radius)
    (band : BandBox center radius)
    (sameBand : band = Elimination.Axis.Band.selectedBand elimination center radius radiusPositive) :
    m (Lines elimination current ambient center radiusPositive) := do
  have leftSafe : elimination.vertical.eval band.box.xLower ≠ 0 := by
    rewrite [sameBand]
    exact Elimination.Axis.Band.selectedBand_left_nonzero elimination center radiusPositive
  have rightSafe : elimination.vertical.eval band.box.xUpper ≠ 0 := by
    rewrite [sameBand]
    exact Elimination.Axis.Band.selectedBand_right_nonzero elimination center radiusPositive
  have bottomSafe : elimination.horizontal.eval band.box.yLower ≠ 0 := by
    rewrite [sameBand]
    exact Elimination.Axis.Band.selectedBand_bottom_nonzero elimination center radiusPositive
  have topSafe : elimination.horizontal.eval band.box.yUpper ≠ 0 := by
    rewrite [sameBand]
    exact Elimination.Axis.Band.selectedBand_top_nonzero elimination center radiusPositive
  let left ← vertical
    (join directory "left") current ambient band.box.xLower leftSafe
  let right ← vertical
    (join directory "right") current ambient band.box.xUpper rightSafe
  let bottom ← horizontal
    (join directory "bottom") current ambient band.box.yLower bottomSafe
  let top ← horizontal
    (join directory "top") current ambient band.box.yUpper topSafe
  let left : Lines.Left elimination current center radiusPositive ×
      Lines.Left elimination ambient center radiusPositive := by
    cases sameBand
    exact left
  let right : Lines.Right elimination current center radiusPositive ×
      Lines.Right elimination ambient center radiusPositive := by
    cases sameBand
    exact right
  let bottom : Lines.Bottom elimination current center radiusPositive ×
      Lines.Bottom elimination ambient center radiusPositive := by
    cases sameBand
    exact bottom
  let top : Lines.Top elimination current center radiusPositive ×
      Lines.Top elimination ambient center radiusPositive := by
    cases sameBand
    exact top
  return ⟨left, right, bottom, top⟩

/-- Restore all eight original lines using the actual retained selected band.

The four paired columns use its literal coordinates in original left, right,
bottom, top order. Only certificate indices are transported; no coordinate
scan or alternative selected band is computed by this action.
-/
@[expose] def bandLinesFromBand
    (p : CoefficientPolynomial)
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree)
    {degreeBound : Nat} (elimination : AxisEliminationCertificate p degreeBound)
    (degreeEq : degreeBound = Separated.separatedEliminationDegree p)
    (same : elimination.castDegree degreeEq =
      Separated.separatedAxisEliminationCertificate p nonzero positive)
    (control : ClearanceCheckpoint.Control m) (directory : System.FilePath) (current ambient : Box)
    (center : Data.Gaussian.Basic.Canonical) {radius : Data.Rat.Fraction.Rational} (radiusPositive : 0 < radius)
    (band : Geometry.Rational.Box.Band.Basic.BandBox center radius)
    (sameBand : band = Elimination.Axis.Band.selectedBand elimination center radius radiusPositive) :
    m (Lines elimination current ambient center radiusPositive) :=
  bandLinesUsing elimination
    (pairedVerticalWithDegree p nonzero positive elimination degreeEq same control)
    (pairedHorizontalWithDegree p nonzero positive elimination degreeEq same control)
    directory current ambient center radiusPositive band sameBand

/-- Restore both original prepared-axis vertical clearances from one checked column.

The retained inverse and coordinate supply one complete cofactor certificate.
Both box bounds consume that same certificate; no second read or producer is
needed for the ambient context. -/
@[expose] def pairedVerticalPrepared
    (p : CoefficientPolynomial) (axes : AxisPreparation p)
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree)
    (control : ClearanceCheckpoint.Control m) (directory : System.FilePath) (current ambient : Box)
    (coordinate : Rational)
    (safe : (axes.certificate nonzero positive).vertical.eval coordinate ≠ 0) :
    m (VerticalPair (axes.certificate nonzero positive) current ambient coordinate safe) := do
  let column ← ClearanceCheckpoint.loadFromPrepared control directory p positive coordinate
    axes.vertical safe
  let coprime := column.verticalFromPrepared axes.vertical nonzero safe
  let inner := Bezout.verticalOfCoprime p current coordinate coprime.val
  let outer := Bezout.verticalOfCoprime p ambient coordinate coprime.val
  return ⟨⟨inner, congrArg (Bezout.verticalOfCoprime p current coordinate) coprime.property⟩,
    ⟨outer, congrArg (Bezout.verticalOfCoprime p ambient coordinate) coprime.property⟩⟩

/-- Restore both original prepared-axis horizontal clearances from one checked quarter-turn column.

The actual source's horizontal preparation supplies its same cofactor
certificate. Both original box contexts reuse that certificate and its
original coordinate, without another column read or inverse construction. -/
@[expose] def pairedHorizontalPrepared
    (p : CoefficientPolynomial) (axes : AxisPreparation p)
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree)
    (control : ClearanceCheckpoint.Control m) (directory : System.FilePath) (current ambient : Box)
    (coordinate : Rational)
    (safe : (axes.certificate nonzero positive).horizontal.eval coordinate ≠ 0) :
    m (HorizontalPair (axes.certificate nonzero positive) current ambient coordinate safe) := do
  let rotated := Dense.Gaussian.Substitution.QuarterTurn.quarterTurn p
  have rotatedPositive : 0 < rotated.natDegree := by
    rewrite [Dense.Gaussian.Substitution.QuarterTurn.quarterTurn_natDegree p nonzero]
    exact positive
  let column ← ClearanceCheckpoint.loadFromPrepared control directory rotated rotatedPositive coordinate
    axes.horizontal safe
  let coprime := Separated.Replay.horizontalFromPrepared p axes.horizontal nonzero positive
    coordinate safe column
  let inner := Bezout.horizontalOfCoprime p current coordinate coprime.val
  let outer := Bezout.horizontalOfCoprime p ambient coordinate coprime.val
  return ⟨⟨inner, congrArg (Bezout.horizontalOfCoprime p current coordinate) coprime.property⟩,
    ⟨outer, congrArg (Bezout.horizontalOfCoprime p ambient coordinate) coprime.property⟩⟩

/-- Restore all eight original prepared-axis band lines from four retained columns.

The shared selected-band action consumes the same original prepared axes in
both directions. Each column supplies the current and ambient line bounds,
and every line retains the original prepared certificate identity. -/
@[expose] def bandLinesPrepared
    (p : CoefficientPolynomial) (axes : AxisPreparation p)
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree)
    (control : ClearanceCheckpoint.Control m) (directory : System.FilePath) (current ambient : Box)
    (center : GaussianCoordinate) {radius : Rational} (radiusPositive : 0 < radius)
    (band : BandBox center radius)
    (sameBand : band = Elimination.Axis.Band.selectedBand
      (axes.certificate nonzero positive) center radius radiusPositive) :
    m (Lines (axes.certificate nonzero positive) current ambient center radiusPositive) :=
  bandLinesUsing (axes.certificate nonzero positive)
    (pairedVerticalPrepared p axes nonzero positive control) (pairedHorizontalPrepared p axes nonzero positive control)
    directory current ambient center radiusPositive band sameBand

/-- Restore the eight original Newton-band lines from four retained original clearance columns.

Each selected side is shared by its current-box and fixed-ambient line bounds.
The original elimination cache and selected-band coordinates are consumed
directly; no alternative band or cofactor certificate is substituted. -/
@[expose] def bandLinesWithDegree
    (p : CoefficientPolynomial)
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree)
    {degreeBound : Nat} (elimination : AxisEliminationCertificate p degreeBound)
    (degreeEq : degreeBound = Separated.separatedEliminationDegree p)
    (same : elimination.castDegree degreeEq =
      Separated.separatedAxisEliminationCertificate p nonzero positive)
    (control : ClearanceCheckpoint.Control m) (directory : System.FilePath) (current ambient : Box)
    (center : Data.Gaussian.Basic.Canonical) {radius : Data.Rat.Fraction.Rational} (radiusPositive : 0 < radius) :
    m (Lines elimination current ambient center radiusPositive) :=
  let band := Elimination.Axis.Band.selectedBand elimination center radius radiusPositive
  bandLinesFromBand p nonzero positive elimination degreeEq same control directory current ambient
    center radiusPositive band rfl

/-- Supplying the actual selected band preserves the complete original ordered checkpoint action. -/
theorem bandLinesFromBand_eq
    (p : CoefficientPolynomial)
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree)
    {degreeBound : Nat} (elimination : AxisEliminationCertificate p degreeBound)
    (degreeEq : degreeBound = Separated.separatedEliminationDegree p)
    (same : elimination.castDegree degreeEq =
      Separated.separatedAxisEliminationCertificate p nonzero positive)
    (control : ClearanceCheckpoint.Control m) (directory : System.FilePath) (current ambient : Box)
    (center : Data.Gaussian.Basic.Canonical) {radius : Data.Rat.Fraction.Rational} (radiusPositive : 0 < radius)
    (band : Geometry.Rational.Box.Band.Basic.BandBox center radius)
    (sameBand : band = Elimination.Axis.Band.selectedBand elimination center radius radiusPositive) :
    bandLinesFromBand p nonzero positive elimination degreeEq same control directory current ambient center
      radiusPositive band sameBand =
      bandLinesWithDegree p nonzero positive elimination degreeEq same control directory current ambient center
        radiusPositive := by
  cases sameBand
  rfl

/-- Construct the original fixed-bound vertical pair from one retained column. -/
@[expose] def pairedVertical
    (p : CoefficientPolynomial)
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree)
    (elimination : AxisEliminationCertificate p (Separated.separatedEliminationDegree p))
    (same : elimination = Separated.separatedAxisEliminationCertificate p nonzero positive)
    (control : ClearanceCheckpoint.Control m) (directory : System.FilePath) (current ambient : Box)
    (coordinate : Data.Rat.Fraction.Rational) (safe : elimination.vertical.eval coordinate ≠ 0) :=
  pairedVerticalWithDegree p nonzero positive elimination rfl same control directory current ambient coordinate safe

/-- Construct the original fixed-bound horizontal pair from one retained column. -/
@[expose] def pairedHorizontal
    (p : CoefficientPolynomial)
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree)
    (elimination : AxisEliminationCertificate p (Separated.separatedEliminationDegree p))
    (same : elimination = Separated.separatedAxisEliminationCertificate p nonzero positive)
    (control : ClearanceCheckpoint.Control m) (directory : System.FilePath) (current ambient : Box)
    (coordinate : Data.Rat.Fraction.Rational) (safe : elimination.horizontal.eval coordinate ≠ 0) :=
  pairedHorizontalWithDegree p nonzero positive elimination rfl same control directory current ambient coordinate safe

/-- Restore the original fixed-bound Newton lines from four retained columns. -/
@[expose] def bandLines
    (p : CoefficientPolynomial)
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree)
    (elimination : AxisEliminationCertificate p (Separated.separatedEliminationDegree p))
    (same : elimination = Separated.separatedAxisEliminationCertificate p nonzero positive)
    (control : ClearanceCheckpoint.Control m) (directory : System.FilePath) (current ambient : Box)
    (center : Data.Gaussian.Basic.Canonical) {radius : Data.Rat.Fraction.Rational} (radiusPositive : 0 < radius) :=
  bandLinesWithDegree p nonzero positive elimination rfl same control directory current ambient center radiusPositive

/-- Bind a root-refinement request to its exact original numerical source before loading any saved stages.

The header is written once. A different polynomial, ambient box, current box,
boundary, depth or accuracy is rejected with both retained JSON records. Code
and byte provenance remain separate execution receipts.
-/
@[expose] def bindRequest (directory : System.FilePath)
    (p : CoefficientPolynomial)
    (ambient : Box) (current : State.Raw.RawWindingState p ambient) (epsilon : Data.Rat.Fraction.Rational)
    (depth : Nat) : IO Unit := do
  IO.FS.createDirAll directory
  let header := Json.mkObj
    [("protocol", toJson "original-raw-forward-refinement-v1"),
      ("polynomial", toJson (p.coeffs.map gaussianData)),
      ("ambient", toJson (RootStateCheckpoint.boxData ambient)),
      ("current", toJson (RootStateCheckpoint.boxData current.box)),
      ("boundary", toJson (fractionData current.clearance.bound)),
      ("epsilon", toJson (fractionData epsilon)), ("depth", toJson depth)]
  let path := join directory "request.json"
  if ← path.pathExists then
    let saved : Json ← loadJson path
    if saved == header then pure ()
    else
      saveJson (join directory "invalid-request.json")
        (Json.mkObj [("kind", toJson "saved original refinement request differs"),
          ("saved", saved), ("expected", header)])
      throw (IO.userError "saved original refinement request differs; exact records retained")
  else saveJson path header

/-- Restore the complete original Newton band through supplied same-certificate band-line readers.

The raw source, subdivision depth and selected cuts use the actual retained
elimination certificate. The supplied paired readers restore the eight
original lines; complete extraction equality includes the boundary,
strict containment and ambient clearances. -/
@[expose] def bandWithLines
    (input : FTA.Squarefree.Input p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (loader : RootRefinementCheckpoint.ClearanceLoader elimination (.canonical elimination) m)
    (winding : WindingCheckpoint.Control m)
    (loadLines : (directory : System.FilePath) → (current ambient : Box) → (center : GaussianCoordinate) →
      {radius : Rational} → (radiusPositive : 0 < radius) → (band : BandBox center radius) →
      (sameBand : band = Elimination.Axis.Band.selectedBand elimination center radius radiusPositive) →
        m (Lines elimination current ambient center radiusPositive))
    (directory : System.FilePath) (current : State.Raw.RawWindingState p ambient)
    (epsilon : Rational) (positive : 0 < epsilon) :
    m {value : Newton.Band.Basic.Output input.squarefree current epsilon //
      value = Newton.Band.Build.extract input.degreeAtLeastTwo input.squarefree elimination current positive} := do
  let depth := Newton.Extraction.Source.Replay.depth input.squarefree current epsilon
  bindRequest directory p ambient current epsilon depth
  profile directory s!"COMPLETE original Newton source budget {depth}; retained elimination degree {degreeBound}"
  let saved ← refineForward elimination loader winding (join directory "raw") depth 0
    (Subdivision.Raw.Rebase.initial current)
  let source := Newton.Extraction.Source.Replay.source input.squarefree elimination current epsilon positive saved
  let geometry := Newton.Extraction.Geometry.fromSource input.degreeAtLeastTwo input.squarefree current
    positive source
  let band := Elimination.Axis.Band.selectedBand elimination geometry.newton.point geometry.radius
    geometry.radiusPositive
  let lines ← loadLines
    (join directory "band") current.box ambient geometry.newton.point geometry.radiusPositive band rfl
  let result := Newton.Band.Prepare.fromGeometryWithBand input.degreeAtLeastTwo input.squarefree elimination current
    geometry band rfl lines
  return ⟨result,
    ((Newton.Band.Prepare.fromGeometryWithBand_eq input.degreeAtLeastTwo input.squarefree elimination current
      geometry band rfl lines).trans
      (Newton.Band.Prepare.fromGeometryWithLines_eq input.degreeAtLeastTwo input.squarefree elimination current
        geometry lines)).trans
      (Newton.Band.Replay.fromSource_eq input.degreeAtLeastTwo input.squarefree elimination current positive source
        (Newton.Extraction.Source.Replay.source_eq input.squarefree elimination current epsilon positive saved))⟩

/-- Restore the complete original Newton band from saved original subdivision and line certificates.

The actual raw source, depth, accuracy and elimination cache are retained.
Four checked columns supply all eight original band lines. The returned band
is equal to the original extraction on those same inputs, including its
boundary, strict containment and ambient clearances.
-/
@[expose] def bandWithDegree
    (input : FTA.Squarefree.Input p)
    {degreeBound : Nat} (elimination : AxisEliminationCertificate p degreeBound)
    (degreeEq : degreeBound = input.eliminationDegree)
    (same : elimination.castDegree degreeEq = input.elimination)
    (loader : RootRefinementCheckpoint.ClearanceLoader elimination (.canonical elimination) m)
    (columns : ClearanceCheckpoint.Control m) (winding : WindingCheckpoint.Control m)
    (directory : System.FilePath) (current : State.Raw.RawWindingState p ambient)
    (epsilon : Data.Rat.Fraction.Rational) (positive : 0 < epsilon) :
    m {value : Newton.Band.Basic.Output input.squarefree current epsilon //
      value = Newton.Band.Build.extract input.degreeAtLeastTwo input.squarefree elimination current positive} :=
  bandWithLines input elimination loader winding
    (bandLinesFromBand p input.nonzero input.degreePositive elimination degreeEq same columns)
    directory current epsilon positive

/-- Restore the complete original Newton band using its retained elimination degree.

The same two cached polynomials supply the finite search bound. Only the
certificate's bound index is transported; the source, depth, selected cuts,
line columns and complete original extraction are unchanged.
-/
@[expose] def band
    (input : FTA.Squarefree.Input p)
    (elimination : AxisEliminationCertificate p input.eliminationDegree)
    (same : elimination = input.elimination)
    (loader : RootRefinementCheckpoint.ClearanceLoader elimination (.canonical elimination) m)
    (columns : ClearanceCheckpoint.Control m) (winding : WindingCheckpoint.Control m)
    (directory : System.FilePath) (current : State.Raw.RawWindingState p ambient)
    (epsilon : Data.Rat.Fraction.Rational) (positive : 0 < epsilon) :
    m {value : Newton.Band.Basic.Output input.squarefree current epsilon //
      value = Newton.Band.Build.extract input.degreeAtLeastTwo input.squarefree elimination current positive} := do
  let degree := elimination.degree
  have degreeEq : degree = input.eliminationDegree := input.elimination_degree_eq elimination same
  let cached := elimination.castDegree degreeEq.symm
  have cachedEq : cached.castDegree degreeEq = input.elimination :=
    (elimination.castDegree_inverse degreeEq.symm).trans same
  let cachedLoader := RootRefinementCheckpoint.ClearanceLoader.castDegree degreeEq.symm elimination loader
  let saved ← bandWithDegree input cached degreeEq cachedEq cachedLoader columns winding directory current epsilon
    positive
  have resultEq := saved.property.trans
    (Newton.Band.Replay.extract_castDegree degreeEq.symm input.degreeAtLeastTwo input.squarefree elimination
      current positive)
  return ⟨saved.val, resultEq⟩

/-- Restore an original Newton state through a supplied complete original band reader.

The reader retains the same source state, positive accuracy request and
elimination certificate. The original state constructor consumes that exact
band, preserving all numerical fields and its complete refinement identity. -/
@[expose] def refineUsing
    (input : FTA.Squarefree.Input p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (readBand : (directory : System.FilePath) → (current : State.Raw.RawWindingState p ambient) →
      (epsilon : Rational) → (positive : 0 < epsilon) →
      m {value : Newton.Band.Basic.Output input.squarefree current epsilon //
        value = Newton.Band.Build.extract input.degreeAtLeastTwo input.squarefree elimination current positive})
    (directory : System.FilePath) (current : State.WindingOne.Basic.WindingOneState p ambient)
    (epsilon : Rational) (positive : 0 < epsilon) :
    m {value : State.WindingOne.Basic.WindingOneState p ambient //
      value = Track.Newton.Refinement.refineState input.degreeAtLeastTwo input.squarefree elimination current
        epsilon positive} := do
  let saved ← readBand directory current.raw epsilon positive
  let result := Newton.Band.State.state input.squarefree current epsilon saved.val
  return ⟨result, Newton.Band.State.Replay.state_eq input.degreeAtLeastTwo input.squarefree elimination current epsilon
    positive saved.val saved.property⟩

/-- Restore the complete original Newton refinement from its checked saved band.

The raw-stage and line checkpoints are consumed by `band`. The original
winding-one state constructor then reads that same retained complete band;
the original request and exact refinement result are preserved.
-/
@[expose] def refine
    (input : FTA.Squarefree.Input p)
    (elimination : AxisEliminationCertificate p input.eliminationDegree)
    (same : elimination = input.elimination)
    (loader : RootRefinementCheckpoint.ClearanceLoader elimination (.canonical elimination) m)
    (columns : ClearanceCheckpoint.Control m) (winding : WindingCheckpoint.Control m)
    (directory : System.FilePath) (current : State.WindingOne.Basic.WindingOneState p ambient)
    (epsilon : Data.Rat.Fraction.Rational) (positive : 0 < epsilon) :
    m {value : State.WindingOne.Basic.WindingOneState p ambient //
      value = Track.Newton.Refinement.refineState input.degreeAtLeastTwo input.squarefree elimination current
        epsilon positive} :=
  refineUsing input elimination (band input elimination same loader columns winding) directory current epsilon positive

/-- Restore the original same-preparation Newton refinement from retained prepared columns and winding divisions.

The retained axis certificate is used for both raw subdivision and all eight
band lines. The current state, accuracy and complete original refinement
result keep their original polynomial and ambient owners. -/
@[expose] def refinePrepared
    (input : FTA.Squarefree.Input p) (axes : AxisPreparation p)
    (columns : ClearanceCheckpoint.Control m) (winding : WindingCheckpoint.Control m)
    (directory : System.FilePath) (current : State.WindingOne.Basic.WindingOneState p ambient)
    (epsilon : Rational) (positive : 0 < epsilon) :
    m {value : State.WindingOne.Basic.WindingOneState p ambient //
      value = Track.Newton.Refinement.refineState input.degreeAtLeastTwo input.squarefree
        (axes.certificate input.nonzero input.degreePositive) current epsilon positive} :=
  let elimination := axes.certificate input.nonzero input.degreePositive
  let loader := RootRefinementCheckpoint.ClearanceLoader.prepared columns p axes input.nonzero input.degreePositive
  refineUsing input elimination
    (bandWithLines input elimination loader winding
      (bandLinesPrepared p axes input.nonzero input.degreePositive columns)) directory current epsilon positive

/-- Restore one exact original track refinement through the same retained Newton checkpoint action.

The supplied pointwise law identifies this original track's policy. The same
cached elimination, loader, current state and positive radius are consumed by
`refine`; only its original result identity is transported to the track.
-/
@[expose] def refineTrack
    (input : FTA.Squarefree.Input p)
    (elimination : AxisEliminationCertificate p input.eliminationDegree)
    (same : elimination = input.elimination)
    (loader : RootRefinementCheckpoint.ClearanceLoader elimination (.canonical elimination) m)
    (columns : ClearanceCheckpoint.Control m) (winding : WindingCheckpoint.Control m)
    (directory : System.FilePath) (track : Track.Basic.WindingOneTrack p ambient)
    (canonical : ∀ current epsilon positive, track.refine current epsilon positive =
      Track.Newton.Refinement.refineState input.degreeAtLeastTwo input.squarefree input.elimination
        current epsilon positive)
    (current : State.WindingOne.Basic.WindingOneState p ambient)
    (epsilon : Data.Rat.Fraction.Rational) (positive : 0 < epsilon) :
    m { state : State.WindingOne.Basic.WindingOneState p ambient //
      state = track.refine current epsilon positive } := do
  let saved ← refine input elimination same loader columns winding directory current epsilon positive
  return ⟨saved.val,
    (saved.property.trans (congrArg (fun certificate => Track.Newton.Refinement.refineState
      input.degreeAtLeastTwo input.squarefree certificate current epsilon positive) same)).trans
      (canonical current epsilon positive).symm⟩

/-- Restore a finite prefix of the original deterministic root track from checked saved refinements.

Every entry stores the complete original winding-one state at its actual
track index. Successive states use the original accuracy request and the
same refinement checkpoint procedure. The last retained state is not
refined further, and extending the prefix reuses each saved column and
winding request under its original operands. An optional exact elimination
cache supplies that same retained value to each demanded refinement; zero-
and one-state prefixes do not force any elimination construction.
-/
def rootPrefix
    (input : FTA.Squarefree.Input p)
    (loader : RootRefinementCheckpoint.ClearanceLoader input.elimination (.canonical input.elimination) IO)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) (track : Track.Basic.WindingOneTrack p ambient)
    (refinement : ∀ current epsilon positive, track.refine current epsilon positive =
      Track.Newton.Refinement.refineState input.degreeAtLeastTwo input.squarefree input.elimination
        current epsilon positive)
    (count : Nat)
    (cached : Option {value : AxisEliminationCertificate p input.eliminationDegree //
      value = input.elimination} := none) :
    IO (List (CoherentRoot.StateCache.Entry track)) := do
  let retained : Unit → {value : AxisEliminationCertificate p input.eliminationDegree //
      value = input.elimination} := fun _ => match cached with
    | none => ⟨input.elimination, rfl⟩
    | some retained => retained
  let rec restore : (remaining index : Nat) → (current : State.WindingOne.Basic.WindingOneState p ambient) →
      current = CoherentRoot.state track index →
      IO (List (CoherentRoot.StateCache.Entry track))
    | 0, _, _, _ => pure []
    | remaining + 1, index, current, currentEq => do
        let entry := CoherentRoot.StateCache.Entry.ofState track index current currentEq
        match remaining with
        | 0 => pure [entry]
        | _ + 1 =>
            let epsilon := AccuracyRadius.accuracyRadius
              (CoherentRoot.stepTarget track index)
            let positive := AccuracyRadius.accuracyRadius_pos
              (CoherentRoot.stepTarget_positive track index)
            let retained := retained ()
            let cachedLoader := RootRefinementCheckpoint.ClearanceLoader.cast retained.property.symm loader
            have cachedRefinement (current) (epsilon) (positive) :
                track.refine current epsilon positive =
                  Track.Newton.Refinement.refineState input.degreeAtLeastTwo input.squarefree retained.val
                    current epsilon positive :=
              (refinement current epsilon positive).trans
                (congrArg (fun elimination =>
                  Track.Newton.Refinement.refineState input.degreeAtLeastTwo input.squarefree elimination
                    current epsilon positive) retained.property.symm)
            let next ← refine input retained.val retained.property cachedLoader columns winding
              (join directory s!"state-{index + 1}") current epsilon positive
            have nextEq : next.val = CoherentRoot.state track (index + 1) :=
              next.property.trans ((cachedRefinement current epsilon positive).symm.trans
                (congrArg (fun state => track.refine state epsilon positive) currentEq))
            let tail ← restore remaining (index + 1) next.val nextEq
            pure (entry :: tail)
  restore count 0 track.initial rfl

/-- Exact supplied elimination data preserves the complete original prefix-replay action.

The action consumes the supplied value in every refinement and retains the
same original track, accuracy requests, state indices and ordered failures.
-/
theorem rootPrefix_cached_eq_default
    (input : FTA.Squarefree.Input p)
    (loader : RootRefinementCheckpoint.ClearanceLoader input.elimination (.canonical input.elimination) IO)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) (track : Track.Basic.WindingOneTrack p ambient)
    (refinement : ∀ current epsilon positive, track.refine current epsilon positive =
      Track.Newton.Refinement.refineState input.degreeAtLeastTwo input.squarefree input.elimination
        current epsilon positive)
    (count : Nat) (cached : Option {value : AxisEliminationCertificate p input.eliminationDegree //
      value = input.elimination}) :
    rootPrefix input loader columns winding directory track refinement count cached =
      rootPrefix input loader columns winding directory track refinement count := by
  cases cached with
  | none => rfl
  | some retained =>
      rcases retained with ⟨value, same⟩
      cases same
      rfl

/-- Restore actual observations of the original productive sampling trajectory at unchanged indices.

Stage zero genuinely refines the supplied track's initial state. Every next
stage refines its actual predecessor at the original unit-scale sampling
request. The finite table retains the exact original arithmetic name and
uses checked raw, band and line checkpoints at distinct sample paths.
-/
def samplingPrefix
    (input : FTA.Squarefree.Input p)
    (loader : RootRefinementCheckpoint.ClearanceLoader input.elimination (.canonical input.elimination) IO)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) (track : Track.Basic.WindingOneTrack p ambient)
    (refinement : ∀ current epsilon positive, track.refine current epsilon positive =
      Track.Newton.Refinement.refineState input.degreeAtLeastTwo input.squarefree input.elimination
        current epsilon positive)
    (count : Nat)
    (cached : Option {value : AxisEliminationCertificate p input.eliminationDegree //
      value = input.elimination} := none) :
    IO (Sequence.SamplePrefix
      (Name.Sampling.approximation (Track.Approximation.Name.initialNamed track))) := do
  let original := Name.Sampling.approximation (Track.Approximation.Name.initialNamed track)
  match count with
  | 0 => return Sequence.SamplePrefix.ofEntries original []
  | count + 1 =>
      let retained : {value : AxisEliminationCertificate p input.eliminationDegree //
          value = input.elimination} := match cached with
        | none => ⟨input.elimination, rfl⟩
        | some retained => retained
      let cachedLoader := RootRefinementCheckpoint.ClearanceLoader.cast retained.property.symm loader
      have cachedRefinement (current) (epsilon) (positive) :
          track.refine current epsilon positive =
            Track.Newton.Refinement.refineState input.degreeAtLeastTwo input.squarefree retained.val
              current epsilon positive :=
        (refinement current epsilon positive).trans
          (congrArg (fun elimination =>
            Track.Newton.Refinement.refineState input.degreeAtLeastTwo input.squarefree elimination
              current epsilon positive) retained.property.symm)
      let rec restore : (remaining index : Nat) → (current : State.WindingOne.Basic.WindingOneState p ambient) →
          current = Track.Approximation.Sampling.stateAt track index →
          IO (List (Sequence.SamplePrefix.Entry original))
        | 0, _, _, _ => pure []
        | remaining + 1, index, current, currentEq => do
            let entry : Sequence.SamplePrefix.Entry original :=
              ⟨index, current.box.anchor,
                (congrArg (fun state : State.WindingOne.Basic.WindingOneState p ambient => state.box.anchor)
                  currentEq).trans (Track.Approximation.Sampling.sample_eq_anchor track index).symm⟩
            match remaining with
            | 0 => pure [entry]
            | _ + 1 =>
                let target := Process.Sampling.refinementTarget (index + 1)
                let positive := AccuracyRadius.accuracyRadius_pos
                  (Process.Sampling.refinementTarget_pos (index + 1))
                let epsilon := AccuracyRadius.accuracyRadius target
                let next ← refine input retained.val retained.property cachedLoader columns winding
                  (join directory s!"sample-{index + 1}") current epsilon positive
                have nextEq : next.val = Track.Approximation.Sampling.stateAt track (index + 1) :=
                  next.property.trans ((cachedRefinement current epsilon positive).symm.trans
                    (congrArg (fun state => track.refine state epsilon positive) currentEq))
                let tail ← restore remaining (index + 1) next.val nextEq
                pure (entry :: tail)
      let epsilon := AccuracyRadius.accuracyRadius
        (Process.Sampling.refinementTarget 0)
      let positive := AccuracyRadius.accuracyRadius_pos
        (Process.Sampling.refinementTarget_pos 0)
      let first ← refine input retained.val retained.property cachedLoader columns winding
        (join directory "sample-0") track.initial epsilon positive
      have firstEq : first.val = Track.Approximation.Sampling.stateAt track 0 :=
        first.property.trans (cachedRefinement track.initial epsilon positive).symm
      let entries ← restore (count + 1) 0 first.val firstEq
      return Sequence.SamplePrefix.ofEntries original entries

/-- Exact retained elimination data preserves the complete productive sampling checkpoint action. -/
theorem samplingPrefix_cached_eq_default
    (input : FTA.Squarefree.Input p)
    (loader : RootRefinementCheckpoint.ClearanceLoader input.elimination (.canonical input.elimination) IO)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) (track : Track.Basic.WindingOneTrack p ambient)
    (refinement : ∀ current epsilon positive, track.refine current epsilon positive =
      Track.Newton.Refinement.refineState input.degreeAtLeastTwo input.squarefree input.elimination
        current epsilon positive)
    (count : Nat) (cached : Option {value : AxisEliminationCertificate p input.eliminationDegree //
      value = input.elimination}) :
    samplingPrefix input loader columns winding directory track refinement count cached =
      samplingPrefix input loader columns winding directory track refinement count := by
  cases cached with
  | none => rfl
  | some retained =>
      rcases retained with ⟨value, same⟩
      cases same
      rfl
/-- Restore one new-policy subdivision step from full ambient columns and exact winding readbacks.

Both coordinates and the four-grid are retained once. The three winding
loaders inspect those actual child boxes; the replay constructor consumes the
same grid and complete ambient lines without executing their pure producers.
-/
private def subdivisionStep (input : FTA.Squarefree.Input p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (loader : RootRefinementCheckpoint.ClearanceLoader elimination (.canonical elimination) m)
    (winding : WindingCheckpoint.Control m) (directory : System.FilePath)
    (current : State.WindingOne.Basic.WindingOneState p ambient) :
    m {value : Subdivision.WindingOne.Step current //
      value = Subdivision.WindingOne.refineOnce input elimination current} := do
  let cuts := Subdivision.WindingOne.coordinates elimination current
  let vertical ← loader.vertical (join directory "vertical") ambient cuts.x cuts.vertical_spec.1
  let horizontal ← loader.horizontal (join directory "horizontal") ambient cuts.y cuts.horizontal_spec.1
  let grid := Subdivision.WindingOne.gridFromLines elimination current cuts vertical.val horizontal.val
  let lowerLeft ← WindingCheckpoint.box winding (join directory "lower-left") p grid.lowerLeft.box
  let upperLeft ← WindingCheckpoint.box winding (join directory "upper-left") p grid.upperLeft.box
  let lowerRight ← WindingCheckpoint.box winding (join directory "lower-right") p grid.lowerRight.box
  let result := Subdivision.WindingOne.fromReadings input elimination current cuts vertical.val horizontal.val
    grid rfl lowerLeft upperLeft lowerRight
  return ⟨result, (Subdivision.WindingOne.fromReadings_eq_fromLines input elimination current cuts
    vertical.val horizontal.val grid rfl lowerLeft upperLeft lowerRight).trans
    (Subdivision.WindingOne.fromLines_eq_refineOnce input elimination current cuts (.canonical elimination)
      vertical.val horizontal.val vertical.property horizontal.property)⟩

/-- Restore the same finite first-accepted scan under the column and winding loaders' independent policies. -/
private def scanSubdivision (input : FTA.Squarefree.Input p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (loader : RootRefinementCheckpoint.ClearanceLoader elimination (.canonical elimination) m)
    (winding : WindingCheckpoint.Control m) (directory : System.FilePath)
    (origin : State.WindingOne.Basic.WindingOneState p ambient) (epsilon : Data.Rat.Fraction.Rational) :
    (fuel index : Nat) → (current : State.WindingOne.Basic.WindingOneState p ambient) →
    (nested : current.box.Refines origin.box) →
    (terminal : (4 / 9 : Data.Rat.Fraction.Rational) ^ fuel * current.box.diagonalSq ≤
      Subdivision.WindingOne.threshold origin epsilon) →
    m {value : Subdivision.WindingOne.Result origin epsilon current fuel //
      value = Subdivision.WindingOne.scan input elimination (.canonical elimination) origin epsilon
        fuel current nested terminal}
  | 0, _, current, nested, terminal => do
      let accepted := Subdivision.WindingOne.accepted_of_threshold input origin current nested (by
        rewrite [pow_zero, one_mul] at terminal
        exact terminal)
      return ⟨⟨current, accepted.1, accepted.2, .done current, 0, rfl, Nat.le_refl 0⟩, rfl⟩
  | fuel + 1, index, current, nested, terminal => do
      if accepted : Subdivision.WindingOne.Accepted origin epsilon current then
        return ⟨⟨current, accepted.1, accepted.2, .done current, 0, rfl, Nat.zero_le _⟩, by
          rewrite [Subdivision.WindingOne.scan_succ, dif_pos accepted]
          rfl⟩
      else
        let ⟨next, nextEq⟩ ← subdivisionStep input elimination loader winding
          (join directory s!"step-{index}") current
        let ⟨following, followingEq⟩ ← scanSubdivision input elimination loader winding directory origin epsilon
          fuel (index + 1) next.state (next.nested.trans nested) (next.remaining_bound fuel terminal)
        return ⟨⟨following.state, following.strict, following.accurate,
          .advance next accepted following.trace, following.steps + 1,
          congrArg (fun count => count + 1) following.steps_eq,
          Nat.succ_le_succ following.bounded⟩, by
            cases nextEq
            cases followingEq
            rewrite [Subdivision.WindingOne.scan_succ, dif_neg accepted]
            rfl⟩

/-- Bind only the distinct subdivision policy to its original finite request before loading any stages.

Saved-only headers must already exist. Column and winding generation policies
remain independently enforced by the supplied loader and winding control;
profile appends, readback summaries and exact missing/invalid diagnostics are
permitted by those existing checkpoint operations.
-/
private def bindSubdivisionRequest (requireSavedHeader : Bool) (directory : System.FilePath)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : State.WindingOne.Basic.WindingOneState p ambient) (epsilon : Data.Rat.Fraction.Rational)
    (depth : Nat) : IO Unit := do
  IO.FS.createDirAll directory
  let header := Json.mkObj
    [("protocol", toJson "winding-one-subdivision-refinement-v1"),
      ("polynomial", toJson (p.coeffs.map gaussianData)),
      ("ambient", toJson (RootStateCheckpoint.boxData ambient)),
      ("current", toJson (RootStateCheckpoint.boxData current.box)),
      ("boundary", toJson (fractionData current.clearance.bound)),
      ("ambientLines", toJson ([current.ambientLeftClearance.bound, current.ambientRightClearance.bound,
        current.ambientBottomClearance.bound, current.ambientTopClearance.bound].map fractionData)),
      ("epsilon", toJson (fractionData epsilon)), ("depthBound", toJson depth),
      ("eliminationDegreeBound", toJson degreeBound),
      ("verticalEliminant", toJson (WindingCheckpoint.polynomialData elimination.vertical)),
      ("horizontalEliminant", toJson (WindingCheckpoint.polynomialData elimination.horizontal))]
  let path := join directory "request.json"
  if ← path.pathExists then
    let saved : Json ← loadJson path
    unless saved == header do
      saveJson (join directory "invalid-request.json")
        (Json.mkObj [("kind", toJson "saved subdivision request differs"),
          ("saved", saved), ("expected", header)])
      throw (IO.userError "saved subdivision request differs; exact records retained")
  else if requireSavedHeader then
    saveJson (join directory "missing-request.json") header
    throw (IO.userError "missing subdivision request; header generation forbidden")
  else saveJson path header

/-- Restore a complete new-policy subdivision result with its original trace, count and computed finite guarantee.

The result equals the total subdivision request on these same owners and
inputs. Full ambient columns and the exact three winding chains are restored
per step; no Newton state or old Newton request is adopted. Header, column and
winding saved-only policies are explicit and independent.
-/
def subdivisionResult (input : FTA.Squarefree.Input p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (loader : RootRefinementCheckpoint.ClearanceLoader elimination (.canonical elimination) m)
    (winding : WindingCheckpoint.Control m) (requireSavedHeader : Bool)
    (directory : System.FilePath) (current : State.WindingOne.Basic.WindingOneState p ambient)
    (epsilon : Data.Rat.Fraction.Rational) (positive : 0 < epsilon) :
    m {value : Subdivision.WindingOne.Result current epsilon current
        (Subdivision.WindingOne.depthBound current epsilon) //
      value = Subdivision.WindingOne.request input elimination current (epsilon := epsilon) positive} := do
  let bound := Subdivision.WindingOne.depthBound current epsilon
  bindSubdivisionRequest requireSavedHeader directory elimination current epsilon bound
  let saved ← scanSubdivision input elimination loader winding directory current epsilon bound 0 current
    (Box.refines_refl _) (Subdivision.WindingOne.depthBound_sufficient current positive)
  profile directory s!"COMPLETE winding-one subdivision steps {saved.val.steps}; finite bound {bound}"
  return ⟨saved.val, saved.property.trans (Subdivision.WindingOne.request_eq_scan
    input elimination current (epsilon := epsilon) positive).symm⟩

/-- Restore the actual strict, accurate refinement from the versioned subdivision checkpoints.

This projection consumes the same completed result and retained state; it does
not schedule another refinement or replace the original current raw owner.
-/
def refineSubdivision (input : FTA.Squarefree.Input p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (loader : RootRefinementCheckpoint.ClearanceLoader elimination (.canonical elimination) m)
    (winding : WindingCheckpoint.Control m) (requireSavedHeader : Bool)
    (directory : System.FilePath) (current : State.WindingOne.Basic.WindingOneState p ambient)
    (epsilon : Data.Rat.Fraction.Rational) (positive : 0 < epsilon) : m (Refinement current.raw epsilon) := do
  let result ← subdivisionResult input elimination loader winding requireSavedHeader directory current epsilon positive
  return ⟨result.val.state, result.val.strict, result.val.accurate⟩

/-- Restore one dyadic proposal using the unchanged old candidate-band and line replay.

Only the target passed to that checker is eight times the speculative radius.
Its accepted state is checked directly at the original epsilon before returning.
Missing or invalid column/winding records remain errors, never rejections.
-/
private def dyadicCandidate (elimination : AxisEliminationCertificate p degreeBound)
    (loader : RootRefinementCheckpoint.ClearanceLoader elimination (.canonical elimination) m)
    (winding : WindingCheckpoint.Control m) (directory : System.FilePath)
    (current : State.Raw.RawWindingState p ambient) (epsilon : Data.Rat.Fraction.Rational)
    (center : Data.Gaussian.Basic.Canonical) :
    m {value : Option (Refinement current epsilon) // value =
      Newton.Search.Dyadic.check elimination current epsilon center
        (Newton.Search.Dyadic.radius current epsilon center)} := do
  IO.FS.createDirAll directory
  let r := Newton.Search.Dyadic.radius current epsilon center
  if positive : 0 < r then
    if within : r ≤ Box.Budget.Center.radius current.box epsilon center then
      match Newton.Search.Center.Replay.prepare elimination current (8 * r) center (.canonical elimination) with
      | .rejected _reason equation =>
          profile directory "REJECTED dyadic candidate geometry"
          return ⟨none, by unfold Newton.Search.Dyadic.check; rewrite [if_pos positive, if_pos within, equation]; rfl⟩
      | .pending pending =>
          let index ← WindingCheckpoint.box winding (join directory "winding") p pending.band.box
          let outcome ← if four : index.val = 4 then do
              let lines ← RootRefinementCheckpoint.restoreLines elimination current (8 * r) (.canonical elimination)
                loader center pending (join directory "clearances")
              pure (pending.finish elimination current (8 * r) center (.canonical elimination) index (fun _ => lines))
            else pure (pending.finish elimination current (8 * r) center (.canonical elimination) index
              (fun impossible => (four impossible).elim))
          match outcome with
          | .accepted value equation =>
              if accurate : value.state.box.diagonalSq ≤ epsilon ^ 2 then
                profile directory "ACCEPTED dyadic candidate at original accuracy"
                return ⟨some ⟨value.state, value.strict, accurate⟩, by
                  unfold Newton.Search.Dyadic.check
                  rewrite [if_pos positive, if_pos within, ← equation]
                  dsimp only
                  rewrite [dif_pos accurate]
                  rfl⟩
              else
                profile directory "REJECTED dyadic candidate original accuracy"
                return ⟨none, by
                  unfold Newton.Search.Dyadic.check
                  rewrite [if_pos positive, if_pos within, ← equation]
                  dsimp only
                  rewrite [dif_neg accurate]
                  rfl⟩
          | .rejected _reason equation =>
              profile directory "REJECTED dyadic candidate winding"
              return ⟨none, by
                unfold Newton.Search.Dyadic.check
                rewrite [if_pos positive, if_pos within, ← equation]
                rfl⟩
    else
      profile directory "REJECTED dyadic radius budget"
      return ⟨none, by unfold Newton.Search.Dyadic.check; rewrite [if_pos positive, if_neg within]; rfl⟩
  else
    profile directory "REJECTED nonpositive dyadic radius"
    return ⟨none, by unfold Newton.Search.Dyadic.check; rewrite [if_neg positive]; rfl⟩

/-- Restore the same bounded dyadic search while recomputing its cheap exact scalar proposals. -/
private def searchDyadic (elimination : AxisEliminationCertificate p degreeBound)
    (loader : RootRefinementCheckpoint.ClearanceLoader elimination (.canonical elimination) m)
    (winding : WindingCheckpoint.Control m) (directory : System.FilePath)
    (current : State.Raw.RawWindingState p ambient) (epsilon basis : Data.Rat.Fraction.Rational) :
    (fuel index bits : Nat) → (proposal : Data.Gaussian.Basic.Canonical) →
    m {value : Option (Refinement current epsilon) // value =
      Newton.Search.Dyadic.search elimination current epsilon basis (.canonical elimination) fuel bits proposal}
  | 0, _, _, _ => pure ⟨none, rfl⟩
  | fuel + 1, index, bits, proposal => do
      let center := Approximation.Gaussian.Grid.Box.roundedCenter current.box basis bits proposal
      let candidate ← dyadicCandidate elimination loader winding (join directory s!"proposal-{index}")
        current epsilon center
      match found : candidate.val with
      | some accepted =>
          return ⟨some accepted, by
            rewrite [Newton.Search.Dyadic.search_succ]
            dsimp only
            rewrite [← candidate.property, found]
            rfl⟩
      | none =>
          if zero : Data.Gaussian.Basic.value
              (Polynomial.Dense.Gaussian.Derivative.Evaluation.derivativeEval p center) = 0 then
            profile directory s!"INCONCLUSIVE dyadic zero derivative at proposal {index}"
            return ⟨none, by
              rewrite [Newton.Search.Dyadic.search_succ]
              dsimp only
              rewrite [← candidate.property, found]
              dsimp only
              rewrite [if_pos zero]
              rfl⟩
          else
            let next := Data.Gaussian.Basic.value (Polynomial.Dense.Gaussian.Newton.Basic.newtonCenter p center)
            let following ← searchDyadic elimination loader winding directory current epsilon basis
              fuel (index + 1) (bits + 2) next
            return ⟨following.val, by
              rewrite [Newton.Search.Dyadic.search_succ]
              dsimp only
              rewrite [← candidate.property, found]
              dsimp only
              rewrite [if_neg zero]
              exact following.property⟩

/-- Bind the new dyadic-candidate policy independently of every legacy Newton and subdivision request. -/
private def bindDyadicRequest (requireSavedHeader : Bool) (directory : System.FilePath)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : State.WindingOne.Basic.WindingOneState p ambient) (epsilon : Data.Rat.Fraction.Rational) : IO Unit := do
  IO.FS.createDirAll directory
  let header := Json.mkObj
    [("protocol", toJson "dyadic-candidate-subdivision-refinement-v1"),
      ("polynomial", toJson (p.coeffs.map gaussianData)),
      ("ambient", toJson (RootStateCheckpoint.boxData ambient)),
      ("current", toJson (RootStateCheckpoint.boxData current.box)),
      ("boundary", toJson (fractionData current.clearance.bound)),
      ("ambientLines", toJson ([current.ambientLeftClearance.bound, current.ambientRightClearance.bound,
        current.ambientBottomClearance.bound, current.ambientTopClearance.bound].map fractionData)),
      ("epsilon", toJson (fractionData epsilon)), ("proposals", toJson (6 : Nat)),
      ("eliminationDegreeBound", toJson degreeBound),
      ("verticalEliminant", toJson (WindingCheckpoint.polynomialData elimination.vertical)),
      ("horizontalEliminant", toJson (WindingCheckpoint.polynomialData elimination.horizontal))]
  let path := join directory "request.json"
  if ← path.pathExists then
    let saved : Json ← loadJson path
    unless saved == header do
      saveJson (join directory "invalid-request.json") (saved, header)
      throw (IO.userError "saved dyadic-candidate request differs; exact records retained")
  else if requireSavedHeader then
    saveJson (join directory "missing-request.json") header
    throw (IO.userError "missing dyadic-candidate request; header generation forbidden")
  else saveJson path header

/-- Replay the exact bounded dyadic attempt on its retained raw winding owner.

All budget gates and six ordered proposals match the pure finite attempt.
Cheap proposals are recomputed; expensive column and winding records obey the
supplied controls. A finite rejection remains `none`; the caller owns request
binding and any subsequent total fallback.
-/
def attemptDyadic (elimination : AxisEliminationCertificate p degreeBound)
    (loader : RootRefinementCheckpoint.ClearanceLoader elimination (.canonical elimination) m)
    (winding : WindingCheckpoint.Control m) (directory : System.FilePath)
    (current : State.Raw.RawWindingState p ambient) (epsilon : Data.Rat.Fraction.Rational) :
    m {value : Option (Refinement current epsilon) // value =
      Newton.Search.Dyadic.attempt elimination current epsilon} := do
  let basis := Newton.Search.Dyadic.gridBudget current epsilon
  if positive : 0 < basis then
    if widthX : basis ≤ current.box.widthX then
      if widthY : basis ≤ current.box.widthY then
        let saved ← searchDyadic elimination loader winding directory current epsilon basis
          6 0 0 ⟨(current.box.xLower + current.box.xUpper) / 2,
            (current.box.yLower + current.box.yUpper) / 2⟩
        return ⟨saved.val, by
          unfold Newton.Search.Dyadic.attempt
          rewrite [if_pos positive, if_pos widthX, if_pos widthY]
          exact saved.property⟩
      else
        return ⟨none, by
          unfold Newton.Search.Dyadic.attempt
          rewrite [if_pos positive, if_pos widthX, if_neg widthY]
          rfl⟩
    else
      return ⟨none, by
        unfold Newton.Search.Dyadic.attempt
        rewrite [if_pos positive, if_neg widthX]
        rfl⟩
  else
    return ⟨none, by
      unfold Newton.Search.Dyadic.attempt
      rewrite [if_neg positive]
      rfl⟩

/-- Replay the complete dyadic total-policy refinement on the unchanged current state and request.

Cheap scalar proposals are recomputed. Accepted proposals retain the complete
original refinement; finite rejection restores the full subdivision result.
Both branches identify the same pure total policy, including every retained
state field. Header, column and winding replay controls stay independent.
-/
def dyadicResult (input : FTA.Squarefree.Input p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (loader : RootRefinementCheckpoint.ClearanceLoader elimination (.canonical elimination) m)
    (winding : WindingCheckpoint.Control m) (requireSavedHeader : Bool)
    (directory : System.FilePath) (current : State.WindingOne.Basic.WindingOneState p ambient)
    (epsilon : Data.Rat.Fraction.Rational) (positive : 0 < epsilon) :
    m {value : Refinement current.raw epsilon // value =
      Track.Accelerated.dyadicRefinement elimination
        (Subdivision.WindingOne.ofInitial input elimination current) current epsilon positive} := do
  bindDyadicRequest requireSavedHeader directory elimination current epsilon
  let candidate ← attemptDyadic elimination loader winding (join directory "candidates") current.raw epsilon
  match found : candidate.val with
  | some accepted =>
      return ⟨accepted, (Track.Accelerated.dyadicRefinement_of_some elimination
        (Subdivision.WindingOne.ofInitial input elimination current) current epsilon positive
        (.canonical elimination) accepted (candidate.property.symm.trans found)).symm⟩
  | none =>
      profile directory "FALLBACK after finite dyadic candidate attempt"
      let saved ← subdivisionResult input elimination loader winding requireSavedHeader
        (join directory "subdivision") current epsilon positive
      return ⟨⟨saved.val.state, saved.val.strict, saved.val.accurate⟩, by
        rewrite [Track.Accelerated.dyadicRefinement_of_none elimination
          (Subdivision.WindingOne.ofInitial input elimination current) current epsilon positive
          (.canonical elimination) (candidate.property.symm.trans found)]
        exact congrArg (fun result : Subdivision.WindingOne.Result current epsilon current
          (Subdivision.WindingOne.depthBound current epsilon) =>
            (⟨result.state, result.strict, result.accurate⟩ : Refinement current.raw epsilon)) saved.property⟩

/-- Restore the actual dyadic refinement while retaining the checked complete-result construction.

This projection preserves the existing assignment interface. State and sample
readers consume `dyadicResult` when they also need its exact total-policy law.
-/
def refineDyadic (input : FTA.Squarefree.Input p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (loader : RootRefinementCheckpoint.ClearanceLoader elimination (.canonical elimination) m)
    (winding : WindingCheckpoint.Control m) (requireSavedHeader : Bool)
    (directory : System.FilePath) (current : State.WindingOne.Basic.WindingOneState p ambient)
    (epsilon : Data.Rat.Fraction.Rational) (positive : 0 < epsilon) : m (Refinement current.raw epsilon) := do
  return (← dyadicResult input elimination loader winding requireSavedHeader directory current epsilon positive).val

end RawSubdivisionCheckpoint
