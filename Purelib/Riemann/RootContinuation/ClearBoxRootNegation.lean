module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.RootContinuation.SquareRootNegation
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.Paths.PreparedPathClosure
import Purelib.Riemann.Paths.PreparedPathWinding
public import Purelib.Riemann.RootContinuation.RootPathTransport
public import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Polynomial.Clearance.Box.Region

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Riemann.RootContinuation.ClearBoxRootTransport
public import Purelib.Riemann.RootContinuation.RootOwnerNegation
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Tactic.QuotientFreeOmega

@[expose] public section

/-!
# Opposite actual roots after contained face transports

Two retained source occurrences remain distinct along contained paths to a
common endpoint. A reverse transport is used only in the erased winding
proof. The executable result retains both endpoint classifications and the
negative-root cache in the shared endpoint frame.
-/

namespace Purelib.Riemann.RootContinuation.ClearBoxRootNegation.SquareRootTrace

open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame OwnerSelection NameSelection)
open Purelib.Riemann.RootContinuation.RootOwnerNegation (NamedNegation)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.RootContinuation.RootPathTransport (PathTransport)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial -> Dense

open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Geometry.Rational (Box)

open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Paths in
open Purelib.Riemann.RootContinuation in
/-- The original zero-winding return transport recovers the retained source-sheet index. -/
private theorem return_index {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {returnAmbient : Box}
    {start finish : Basic.Canonical} {backPath : Polynomial.Geometry.ClearPath polynomial returnAmbient finish start}
    {firstFrame : OwnerFrame (polynomial.eval start)} {lastFrame : OwnerFrame (polynomial.eval finish)}
    {index : Fin 2} {last : Owner (polynomial.eval finish)}
    (reference : WindingOneLoop polynomial start)
    (traced : OwnerPath polynomial start (firstFrame.owners index) finish last)
    (selected : OwnerSelection lastFrame.owners last)
    (backward : PathTransport backPath lastFrame firstFrame)
    (cancel : Winding.Polygon.Basic.chainRaw polynomial start traced.vertices + PreparedPathWinding.ClearPath.rawWinding
      backPath = 0) :
    backward.target selected.index = index := by
  let joined := traced.append
    ((RootPathTransport.OwnerPath.join polynomial finish last (lastFrame.owners selected.index)
      selected.equivalent).append
      (backward.row selected.index).joined)
  have winding : Winding.Polygon.Basic.chainRaw polynomial start joined.vertices = 8 * (0 : Int) := by
    rw [RootPathTransport.OwnerPath.append_winding, RootPathTransport.OwnerPath.append_winding,
      RootPathTransport.OwnerPath.join_winding, RootPathTransport.TransportRow.joined_winding]
    omega0
  exact firstFrame.distinguish _ _ (OwnerLoopMonodromy.OwnerPath.rootEquivalent_of_even_with_reference reference joined
    0 winding)

open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Paths in
/-- Equal-winding traces from opposite original sheets select opposite retained target-frame indices.

The actual backward transport returns each selected finish to its original source sheet; their distinct source indices
rule out a common target selection. -/
theorem OwnerPath.selections_opposite {polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {returnAmbient : Box}
    {start finish : Basic.Canonical} {backPath : Polynomial.Geometry.ClearPath polynomial returnAmbient finish start}
    {source : OwnerFrame (polynomial.eval start)} {frame : OwnerFrame (polynomial.eval finish)}
    {sheet : Fin 2} {firstOwner lastOwner : Owner (polynomial.eval finish)}
    (first : OwnerPath polynomial start (source.owners sheet) finish firstOwner)
    (reference : WindingOneLoop polynomial start)
    (second : OwnerPath polynomial start (source.owners (BranchCutLifts.otherSheet sheet)) finish lastOwner)
    (left : OwnerSelection frame.owners firstOwner) (right : OwnerSelection frame.owners lastOwner)
    (backward : PathTransport backPath frame source)
    (firstCancel : Winding.Polygon.Basic.chainRaw polynomial start first.vertices +
      PreparedPathWinding.ClearPath.rawWinding backPath = 0)
    (secondCancel : Winding.Polygon.Basic.chainRaw polynomial start second.vertices +
      PreparedPathWinding.ClearPath.rawWinding backPath = 0) :
    right.index = BranchCutLifts.otherSheet left.index := by
  have firstReturn := return_index reference first left backward firstCancel
  have secondReturn := return_index reference second right backward secondCancel
  have different : right.index ≠ left.index := by
    intro equal
    have same := firstReturn.symm.trans ((congrArg backward.target equal.symm).trans secondReturn)
    have values := congrArg Fin.val same
    have bound := sheet.isLt
    change sheet.val = 1 - sheet.val at values
    omega0
  have values : right.index.val ≠ left.index.val := fun equal => different (Fin.ext equal)
  have leftBound := left.index.isLt
  have rightBound := right.index.isLt
  apply Fin.ext
  change right.index.val = 1 - left.index.val
  omega0

namespace OwnerFrame

open Purelib.Approximation.Gaussian in
open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Data.Gaussian in
set_option genInjectivity false in
/-- Two original name selections with an opposite-index equation and retained negation attachment.

The same two-name frame and owner-name projection index the exact selections and the negative-channel witness. -/
structure SelectedNegation {parameter : Basic.Canonical}
    (names : Fin 2 → Name.Basic.Named)
    (name : Owner parameter → Name.Basic.Named)
    (firstName lastName : Name.Basic.Named) where
  /-- The original frame selection of the first retained name. -/ first : NameSelection names firstName
  /-- The original frame selection of the last retained name. -/ last : NameSelection names lastName
  /-- The last selected index is exactly the opposite of the first. -/ index_eq : last.index = BranchCutLifts.otherSheet
    first.index
  /-- The actual negative-channel attachment for the first original frame index. -/ negative : NamedNegation names name
    first.index

constructive_injectivity SelectedNegation

open Purelib.Data.Gaussian in
/-- Negation evidence for the two original owners selected in one retained frame. -/
abbrev OppositeOwners {parameter : Basic.Canonical} (frame : OwnerFrame parameter) (first last : Owner parameter) :=
  SelectedNegation (parameter := parameter) (fun index => ownerName (frame.owners index))
    (@ownerName parameter) (ownerName first) (ownerName last)

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
open Purelib.Riemann.RootContinuation in
/-- The negation of the first original owner's name is equivalent to the last owner's name. -/
def OppositeOwners.equivalent {parameter : Basic.Canonical} {frame : OwnerFrame parameter}
    {first last : Owner parameter} (data : OppositeOwners frame first last) :
    Equivalence.NamedEquivalent (Name.Basic.Named.neg (ownerName first)) (ownerName last) := by
  let initial := SquareRootNegation.neg_equivalent
    (first.certificate first.parameterNonzero).value
    ((frame.owners data.first.index).certificate (frame.owners data.first.index).parameterNonzero).value
    data.first.equivalent
  apply initial.trans
  apply (RootOwnerNegation.Negation.equivalent (frame := frame) data.negative).trans
  have final := data.last.equivalent.symm
  simpa only [data.index_eq] using final

end OwnerFrame

end Purelib.Riemann.RootContinuation.ClearBoxRootNegation.SquareRootTrace

namespace Purelib.Riemann.RootContinuation.ClearBoxRootNegation.TracedPath

open Purelib.Geometry.Rational (Box)
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame OwnerSelection)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Riemann.RootContinuation.RootPathTransport (PathTransport)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial -> Dense
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {firstAmbient
  secondAmbient :
  Box} {start finish : Purelib.Data.Gaussian.Basic.Canonical}
  {firstPath : Polynomial.Geometry.ClearPath polynomial firstAmbient start finish}
  {secondPath : Polynomial.Geometry.ClearPath polynomial secondAmbient start finish}
  {source : OwnerFrame (polynomial.eval start)} {sheet : Fin 2}

open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Riemann.Paths in
open Purelib.Riemann.RootContinuation in
/-- Equal-winding traces from opposite original sheets select opposite retained target-frame indices.

The actual backward transport returns each selected finish to its original source sheet; their distinct source indices
rule out a common target selection. -/
theorem selections_opposite (reference : WindingOneLoop polynomial start)
    (within : firstPath.WithinAmbient)
    (first : TracedPath firstPath (source.owners sheet))
    (second : TracedPath secondPath (source.owners (BranchCutLifts.otherSheet sheet)))
    (frame : OwnerFrame (polynomial.eval finish))
    (left : OwnerSelection frame.owners first.finishOwner) (right : OwnerSelection frame.owners second.finishOwner)
    (winding : PreparedPathWinding.ClearPath.rawWinding firstPath = PreparedPathWinding.ClearPath.rawWinding secondPath)
      :
    right.index = BranchCutLifts.otherSheet left.index := by
  let backward := PathTransport.build (BranchCutLifts.ClearPath.reverse firstPath)
    (BranchCutLifts.ClearPath.reverse_withinAmbient firstPath within) frame source
  have cancel : PreparedPathWinding.ClearPath.rawWinding firstPath + PreparedPathWinding.ClearPath.rawWinding
    (BranchCutLifts.ClearPath.reverse firstPath) = 0 := by
    rw [PreparedPathClosure.ClearPath.rawWinding_reverse]
    omega0
  apply ClearBoxRootNegation.SquareRootTrace.OwnerPath.selections_opposite first.trace.get reference second.trace.get
    left right backward
  · rw [PreparedPathWinding.PreparedClearPathModels.TracedPath.winding_original first]
    exact cancel
  · rw [PreparedPathWinding.PreparedClearPathModels.TracedPath.winding_original second, ← winding]
    exact cancel

open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Clearance.Box in
open Purelib.Riemann.Paths in
open Purelib.Riemann.RootContinuation in
/-- Retain opposite-owner evidence for opposite-sheet traces contained in one certified clear box.

The original endpoint frame selections and negative-channel attachment are kept; shared clear-box winding and the
retained reference loop certify their opposite indices. -/
def oppositeOfInBox {box : Box} (clearance : Region.RegionClearance polynomial box)
    (degreePositive : 0 < polynomial.natDegree) (reference : WindingOneLoop polynomial start)
    (within : firstPath.WithinAmbient)
    (first : TracedPath firstPath (source.owners sheet))
    (second : TracedPath secondPath (source.owners (BranchCutLifts.otherSheet sheet)))
    (firstInside : Polynomial.Geometry.ClearPath.InBox box firstPath) (secondInside :
      Polynomial.Geometry.ClearPath.InBox
      box secondPath)
    (frame : OwnerFrame (polynomial.eval finish)) :
    ClearBoxRootNegation.SquareRootTrace.OwnerFrame.OppositeOwners frame first.finishOwner second.finishOwner :=
  let left := frame.select first.finishOwner
  let right := frame.select second.finishOwner
  ⟨left, right, ClearBoxRootNegation.TracedPath.selections_opposite reference within first second frame left right
    (ClearBoxPathWinding.ClearPath.rawWinding_eq_of_inBox clearance degreePositive firstPath secondPath firstInside
      secondInside),
    RootOwnerNegation.negation frame left.index⟩

end Purelib.Riemann.RootContinuation.ClearBoxRootNegation.TracedPath
