module

import all Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Sources.Assembly
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Realization
import all Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Realization.Preparation
import all Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Spatial.Acquisition
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition
import all Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Spine

open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Geometry

/-! # Complete former numeric-detour computations

The import-all owners are the acquisition Spine, fine acquisition, mixed
realization Preparation and four-quarter assembly modules. Their unexposed producer bodies
are reduced only by these private quantified whole-value regressions.
-/

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint finalTarget)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)

variable {site : Fin 2} {parameter : Canonical} {unitQuarter : UnitCircuitQuarter}
variable {positive : (0 : Data.Rat.Fraction.Rational) < 2}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

namespace Steps.Acquisition

variable {actual : Transport.Quarter site parameter 2 unitQuarter positive} {regular : parameter ≠ criticalValue site}
variable {targets : List Endpoint} {current : Endpoint} {reading : ReadingAt actual current}
variable {originalOwner sourceOwner : OwnerAt site parameter unitQuarter positive current}
variable {original : Steps actual regular current reading originalOwner targets}
variable {agreement : InitialAgreement current reading sourceOwner}

open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider (AxisClearances)
open Purelib.Polynomial.Geometry
open Purelib.Polynomial.Dense.Gaussian.Bounds
open Purelib.Geometry.Rational.Box.Refinement
open Purelib.Data.List (DependentProduct)

section Detour

variable {degreeBound : Nat}
variable (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
variable (clearances : AxisClearances elimination)
variable (grid : Grid.ClearGrid (Paths.polynomial parameter)
  (RootRadius.Box.largeSquareBox (Paths.polynomial parameter)))

attribute [local irreducible] Steps.Acquisition Block Geometry
attribute [local irreducible] coordinate

/-- The complete historical spine, used only to verify the retained-Walk projection. -/
private def formerDetourSpine : (targets : List Endpoint) → (current : Endpoint) →
    (reading : ReadingAt actual current) → (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) → (lines : Lines paid elimination clearances) →
    (onGrid : ∀ value ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid value) →
    {_walk : Grid.Walks.Walk grid
      (Geometry.move elimination regular (coordinate site parameter 2 unitQuarter positive current.parameter))
      (Geometry.move elimination regular
        (coordinate site parameter 2 unitQuarter positive (finalTarget current targets).parameter)) //
      Grid.FromStates.ContainsVertex grid (Geometry.move elimination regular
        (coordinate site parameter 2 unitQuarter positive (finalTarget current targets).parameter))}
  | [], _current, _reading, _originalOwner, _original, _sourceOwner, _agreement, _paid, lines, onGrid =>
      let source := Geometry.Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      ⟨(Grid.Walks.Walk.nil source.point).castEndpoints source.point_eq source.point_eq,
        Eq.mp (congrArg (Grid.FromStates.ContainsVertex grid) source.point_eq)
          (onGrid source.point (List.Mem.head _))⟩
  | target :: targets, current, reading, _originalOwner, original, _sourceOwner, _agreement, paid,
      lines, onGrid =>
      let source := Geometry.Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      let suffix := Geometry.Lines.Bank.tail
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      let next := Geometry.Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := regular) suffix
      let moved := Geometry.detourWalk (actual := actual) (first := current.parameter) (last := target.parameter)
        (firstInside := current.inside) (lastInside := target.inside) (reading := reading)
        (targetReading := original.nextReading) (regular := regular) (payment := original.1)
        original.headGeometry elimination clearances source next grid
        (onGrid source.point (List.Mem.head _))
        (onGrid next.point (List.Mem.tail _ (List.Mem.head _)))
      let remaining : {_walk : Grid.Walks.Walk grid
          (Geometry.move elimination regular (coordinate site parameter 2 unitQuarter positive target.parameter))
          (Geometry.move elimination regular
            (coordinate site parameter 2 unitQuarter positive (finalTarget target targets).parameter)) //
          Grid.FromStates.ContainsVertex grid (Geometry.move elimination regular
            (coordinate site parameter 2 unitQuarter positive (finalTarget target targets).parameter))} :=
        formerDetourSpine targets target original.nextReading original.headCovered.finishOwner
        original.tail paid.head.finishOwner paid.head.nextAgreement paid.tail suffix
        (fun value member => onGrid value (List.Mem.tail _ member))
      ⟨moved.append remaining.val, remaining.property⟩

/-- The retained-head fold preserves the complete historical aggregate subtype. -/
private theorem detourOn_eq_former : (targets : List Endpoint) → (current : Endpoint) →
    (reading : ReadingAt actual current) → (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) → (lines : Lines paid elimination clearances) →
    (onGrid : ∀ value ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid value) →
    detourOn elimination clearances paid lines grid onGrid =
      formerDetourSpine elimination clearances grid targets current reading originalOwner original sourceOwner agreement
        paid lines onGrid
  | [], _current, _reading, _originalOwner, _original, _sourceOwner, _agreement, _paid, _lines, _onGrid => rfl
  | target :: targets, current, reading, _originalOwner, original, _sourceOwner, _agreement, paid, lines, onGrid => by
      let source := Geometry.Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      let suffix := Geometry.Lines.Bank.tail
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      let next := Geometry.Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := regular) suffix
      let moved := Geometry.detourWalk (actual := actual) (first := current.parameter) (last := target.parameter)
        (firstInside := current.inside) (lastInside := target.inside) (reading := reading)
        (targetReading := original.nextReading) (regular := regular) (payment := original.1)
        original.headGeometry elimination clearances source next grid
        (onGrid source.point (List.Mem.head _))
        (onGrid next.point (List.Mem.tail _ (List.Mem.head _)))
      have rest := detourOn_eq_former targets target original.nextReading original.headCovered.finishOwner
        original.tail paid.head.finishOwner paid.head.nextAgreement paid.tail suffix
        (fun value member => onGrid value (List.Mem.tail _ member))
      exact Subtype.ext (congrArg (fun value => moved.append (Subtype.val value)) rest)

/-- The whole historical supplied-grid result used for quantified agreement. -/
private def formerDetourOn (paid : Acquisition original sourceOwner agreement)
    (lines : Lines paid elimination clearances)
    (grid : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter)))
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid point) :
    {_walk : Grid.Walks.Walk grid
      (Geometry.move elimination regular (coordinate site parameter 2 unitQuarter positive current.parameter))
      (Geometry.move elimination regular
        (coordinate site parameter 2 unitQuarter positive (finalTarget current targets).parameter)) //
      Grid.FromStates.ContainsVertex grid (Geometry.move elimination regular
        (coordinate site parameter 2 unitQuarter positive (finalTarget current targets).parameter))} :=
  formerDetourSpine elimination clearances grid targets current reading originalOwner original sourceOwner agreement
    paid lines onGrid

/-- The public aggregate view equals the whole historical supplied-grid computation. -/
private theorem detourOn_whole_former (paid : Acquisition original sourceOwner agreement)
    (lines : Lines paid elimination clearances)
    (grid : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter)))
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid point) :
    detourOn elimination clearances paid lines grid onGrid =
      formerDetourOn elimination clearances paid lines grid onGrid :=
  detourOn_eq_former elimination clearances grid targets current reading originalOwner original
    sourceOwner agreement paid lines onGrid

end Detour

end Steps.Acquisition

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer

namespace Spatial

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Integration.Partition
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Transport.Spatial

variable {radicand : CoefficientPolynomial}
variable {site : Fin 2} {parameter : Canonical} {differential : OddPowerDifferential radicand}
variable {data : Waist.Differential.Bounds.Data site parameter differential}
variable {quarter : UnitCircuitQuarter} {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive} {accuracy : AccuracyRequest}

attribute [local irreducible] Transport.Spatial.coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

namespace Acquisition

variable {regular : parameter ≠ criticalValue site}
variable {finish : Endpoint}
variable {finishQuery : { reading : ReadingAt actual finish // QueryCache actual finish reading }}

open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider (AxisClearances)
open Purelib.Polynomial.Dense.Gaussian.Bounds
open Purelib.Polynomial.Geometry

section Detour

variable {degreeBound : Nat}
variable (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
variable (clearances : AxisClearances elimination)
variable (grid : Grid.ClearGrid (Paths.polynomial parameter)
  (RootRadius.Box.largeSquareBox (Paths.polynomial parameter)))

attribute [local irreducible] Parallel.Geometry

/-- The complete historical spine, used only to verify the retained-Walk projection. -/
private def formerDetourSpine : (remaining : List (Piece data actual accuracy)) → (first : Piece data actual accuracy) →
    (queried : ∀ piece ∈ remaining, piece.Queried) →
    (sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint) →
    (agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner) →
    (paid : Acquisition regular finishQuery remaining first queried sourceOwner agreement) →
    (lines : Lines paid elimination clearances) →
    (onGrid : ∀ point ∈ Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid point) →
    {_walk : Grid.Walks.Walk grid
      (Parallel.Geometry.move elimination regular
        (Transport.Spatial.coordinate site parameter 2 quarter positive first.span.lower))
      (Parallel.Geometry.move elimination regular
        (Transport.Spatial.coordinate site parameter 2 quarter positive finish.parameter)) //
      Grid.FromStates.ContainsVertex grid (Parallel.Geometry.move elimination regular
        (Transport.Spatial.coordinate site parameter 2 quarter positive finish.parameter))}
  | [], first, _queried, _sourceOwner, _agreement, paid, lines, onGrid =>
      let source := Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      let suffix := Lines.Bank.tail
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      let target := Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := regular) suffix
      let head := paid.head
      let walk := Parallel.Geometry.detourWalk (actual := actual)
        (first := first.span.lower) (last := finish.parameter)
        (firstInside := first.lowerEndpoint.inside) (lastInside := finish.inside)
        (reading := first.source) (targetReading := finishQuery.val)
        (regular := regular) (payment := head.payment)
        head.geometry elimination clearances source target grid
        (onGrid source.point (List.Mem.head _))
        (onGrid target.point (List.Mem.tail _ (List.Mem.head _)))
      ⟨walk, Eq.mp (congrArg (Grid.FromStates.ContainsVertex grid) target.point_eq)
        (onGrid target.point (List.Mem.tail _ (List.Mem.head _)))⟩
  | next :: remaining, first, queried, _sourceOwner, _agreement, paid, lines, onGrid =>
      let source := Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      let suffix := Lines.Bank.tail
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      let target := Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := regular) suffix
      let head := paid.head
      let walk := Parallel.Geometry.detourWalk (actual := actual)
        (first := first.span.lower) (last := next.lowerEndpoint.parameter)
        (firstInside := first.lowerEndpoint.inside) (lastInside := next.lowerEndpoint.inside)
        (reading := first.source) (targetReading := (next.sourceQuery (queried next (List.Mem.head remaining))).val)
        (regular := regular) (payment := head.payment)
        head.geometry elimination clearances source target grid
        (onGrid source.point (List.Mem.head _))
        (onGrid target.point (List.Mem.tail _ (List.Mem.head _)))
      let rest := formerDetourSpine remaining next
        (fun piece member => queried piece (List.Mem.tail next member))
        head.finishOwner head.nextAgreement paid.tail suffix
        (fun point member => onGrid point (List.Mem.tail _ member))
      ⟨walk.append rest.val, rest.property⟩

/-- The retained-head fold preserves the complete historical aggregate subtype. -/
private theorem detourOn_eq_former : (remaining : List (Piece data actual accuracy)) →
    (first : Piece data actual accuracy) →
    (queried : ∀ piece ∈ remaining, piece.Queried) →
    (sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint) →
    (agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner) →
    (paid : Acquisition regular finishQuery remaining first queried sourceOwner agreement) →
    (lines : Lines paid elimination clearances) →
    (onGrid : ∀ point ∈ Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid point) →
    detourOn elimination clearances paid lines grid onGrid =
      formerDetourSpine elimination clearances grid remaining first queried sourceOwner agreement
        paid lines onGrid
  | [], _first, _queried, _sourceOwner, _agreement, _paid, _lines, _onGrid => rfl
  | next :: remaining, first, queried, _sourceOwner, _agreement, paid, lines, onGrid => by
      let source := Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      let suffix := Lines.Bank.tail
        (elimination := elimination) (clearances := clearances) (regular := regular) lines
      let target := Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := regular) suffix
      let head := paid.head
      let walk := Parallel.Geometry.detourWalk (actual := actual)
        (first := first.span.lower) (last := next.lowerEndpoint.parameter)
        (firstInside := first.lowerEndpoint.inside) (lastInside := next.lowerEndpoint.inside)
        (reading := first.source) (targetReading := (next.sourceQuery (queried next (List.Mem.head remaining))).val)
        (regular := regular) (payment := head.payment)
        head.geometry elimination clearances source target grid
        (onGrid source.point (List.Mem.head _))
        (onGrid target.point (List.Mem.tail _ (List.Mem.head _)))
      have rest := detourOn_eq_former remaining next
        (fun piece member => queried piece (List.Mem.tail next member))
        head.finishOwner head.nextAgreement paid.tail suffix
        (fun point member => onGrid point (List.Mem.tail _ member))
      exact Subtype.ext (congrArg (fun value => walk.append (Subtype.val value)) rest)

/-- The whole historical supplied-grid result used for quantified agreement. -/
private def formerDetourOn {remaining : List (Piece data actual accuracy)} {first : Piece data actual accuracy}
    {queried : ∀ piece ∈ remaining, piece.Queried}
    {sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint}
    {agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner}
    (paid : Acquisition regular finishQuery remaining first queried sourceOwner agreement)
    (lines : Lines paid elimination clearances)
    (grid : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter)))
    (onGrid : ∀ point ∈ Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid point) :
    {_walk : Grid.Walks.Walk grid
      (Parallel.Geometry.move elimination regular
        (Transport.Spatial.coordinate site parameter 2 quarter positive first.span.lower))
      (Parallel.Geometry.move elimination regular
        (Transport.Spatial.coordinate site parameter 2 quarter positive finish.parameter)) //
      Grid.FromStates.ContainsVertex grid (Parallel.Geometry.move elimination regular
        (Transport.Spatial.coordinate site parameter 2 quarter positive finish.parameter))} :=
  formerDetourSpine elimination clearances grid remaining first queried sourceOwner agreement paid lines onGrid

/-- The public aggregate view equals the whole historical supplied-grid computation. -/
private theorem detourOn_whole_former {remaining : List (Piece data actual accuracy)}
    {first : Piece data actual accuracy}
    {queried : ∀ piece ∈ remaining, piece.Queried}
    {sourceOwner : OwnerAt site parameter quarter positive first.lowerEndpoint}
    {agreement : Steps.Acquisition.InitialAgreement first.lowerEndpoint first.source sourceOwner}
    (paid : Acquisition regular finishQuery remaining first queried sourceOwner agreement)
    (lines : Lines paid elimination clearances)
    (grid : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter)))
    (onGrid : ∀ point ∈ Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := regular) lines,
      Grid.FromStates.ContainsVertex grid point) :
    detourOn elimination clearances paid lines grid onGrid =
      formerDetourOn elimination clearances paid lines grid onGrid :=
  detourOn_eq_former elimination clearances grid remaining first queried sourceOwner agreement paid lines onGrid

end Detour

end Acquisition

end Spatial

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.Quarter

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement (Piece)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Spatial
  renaming Acquisition → LayerAcquisition
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint finalTarget)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)

variable {site : Fin 2} {parameter : Canonical} {unitQuarter : UnitCircuitQuarter}
variable {leg : Transport.Leg site parameter unitQuarter}

attribute [local irreducible] coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] ownerRootName

namespace Input.Realization

open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider (AxisClearances)
open Purelib.Polynomial.Dense.Gaussian.Bounds
open Purelib.Polynomial.Geometry

/-- The whole historical supplied-grid result used for quantified agreement. -/
private def formerDetourOn {degreeBound : Nat} {input : Input leg}
    {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint}
    {agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner}
    (retained : Realization input sourceOwner agreement)
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (clearances : AxisClearances elimination) (lines : Lines retained elimination clearances)
    (grid : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter)))
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := leg.regular) lines,
      Grid.FromStates.ContainsVertex grid point) :
    {_walk : Grid.Walks.Walk grid
      (Geometry.move elimination leg.regular
        (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint.parameter))
      (Geometry.move elimination leg.regular
        (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) retained.finishEndpoint.parameter)) //
      Grid.FromStates.ContainsVertex grid
        (Geometry.move elimination leg.regular
          (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) retained.finishEndpoint.parameter))} :=
  match input, sourceOwner, agreement, retained, lines, onGrid with
  | .inl _original, _sourceOwner, _agreement, retained, lines, onGrid =>
      Steps.Acquisition.formerDetourOn elimination clearances retained.receipt lines grid onGrid
  | .inr fine, _sourceOwner, _agreement, retained, lines, onGrid =>
      let result :=
        Refinement.Layer.Spatial.Acquisition.formerDetourOn
          elimination clearances retained.paid lines grid onGrid
      ⟨result.val.castEndpoints
          (congrArg (fun time : Fraction.Rational => Geometry.move elimination leg.regular
            (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) time))
            (fine.numerical.parts.start_time fine.numerical.layer_eq)) rfl,
        result.property⟩

/-- The public aggregate view equals the whole historical supplied-grid computation. -/
private theorem detourOn_whole_former {degreeBound : Nat} {input : Input leg}
    {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint}
    {agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner}
    (retained : Realization input sourceOwner agreement)
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (clearances : AxisClearances elimination) (lines : Lines retained elimination clearances)
    (grid : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter)))
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := leg.regular) lines,
      Grid.FromStates.ContainsVertex grid point) :
    detourOn retained elimination clearances lines grid onGrid =
      formerDetourOn retained elimination clearances lines grid onGrid := by
  cases input with
  | inl original =>
      exact Steps.Acquisition.detourOn_whole_former elimination clearances retained.receipt lines grid onGrid
  | inr fine =>
      have same :=
        Refinement.Layer.Spatial.Acquisition.detourOn_whole_former
          elimination clearances retained.paid lines grid onGrid
      apply Subtype.ext
      exact congrArg (fun value => Grid.Walks.Walk.castEndpoints value
        (congrArg (fun time : Fraction.Rational => Geometry.move elimination leg.regular
          (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) time))
          (fine.numerical.parts.start_time fine.numerical.layer_eq)) rfl) (congrArg Subtype.val same)

/-- The exact original aggregate type used by the verifier's scalar transports. -/
private abbrev DetourResult {degreeBound : Nat} {input : Input leg}
    {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint}
    {agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner}
    (retained : Realization input sourceOwner agreement)
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (grid : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter)))
    :=
    {_walk : Grid.Walks.Walk grid
      (Geometry.move elimination leg.regular
        (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint.parameter))
      (Geometry.move elimination leg.regular
        (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) retained.finishEndpoint.parameter)) //
      Grid.FromStates.ContainsVertex grid
        (Geometry.move elimination leg.regular
          (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) retained.finishEndpoint.parameter))}

end Input.Realization

end Steps.Acquisition.Quarter

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.Quarter.Circuit

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Geometry.Gaussian.UnitCircle.Basic (UnitVertex)
open Purelib.Geometry.Gaussian.UnitCircle
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint finalTarget)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider (AxisClearances)
open Purelib.Polynomial.Dense.Gaussian.Bounds
open Purelib.Polynomial.Geometry

section ActualDetours

variable {site : Fin 2} {parameter : Canonical}
variable {circuit : Transport.Circuit site parameter} {firstInput : Input circuit.first}
variable {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) firstInput.sourceEndpoint}
variable {agreement : InitialAgreement firstInput.sourceEndpoint firstInput.sourceReading sourceOwner}
variable {initial : Input.Realization firstInput sourceOwner agreement}
variable {secondInput : Input circuit.second} {thirdInput : Input circuit.third} {fourthInput : Input circuit.fourth}
variable {execution : Execution.Cache initial secondInput thirdInput fourthInput}

namespace Execution.Cache

namespace Lines

variable {degreeBound : Nat}
variable {elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound}
variable {clearances : AxisClearances elimination}

/-- The complete historical detour factory retained for whole-value verification. -/
private def formerDetour (lines : Lines execution elimination clearances)
    (base : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter))) :
    Σ grid : Grid.ClearGrid (Paths.polynomial parameter)
        (RootRadius.Box.largeSquareBox (Paths.polynomial parameter)),
      {_walk : Grid.Walks.Walk grid
        (Geometry.move elimination circuit.first.regular
          (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter))
        (Geometry.move elimination circuit.first.regular
          (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter)) //
        Grid.FromStates.ContainsVertex grid
          (Geometry.move elimination circuit.first.regular
            (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter))} :=
  let firstPairs := Geometry.Lines.Bank.pairs
    (elimination := elimination) (clearances := clearances) (regular := circuit.first.regular) lines.1
  let secondPairs := Geometry.Lines.Bank.pairs
    (elimination := elimination) (clearances := clearances) (regular := circuit.second.regular) lines.2.1
  let thirdPairs := Geometry.Lines.Bank.pairs
    (elimination := elimination) (clearances := clearances) (regular := circuit.third.regular) lines.2.2.1
  let fourthPairs := Geometry.Lines.Bank.pairs
    (elimination := elimination) (clearances := clearances) (regular := circuit.fourth.regular) lines.2.2.2
  let firstGrid := Grid.Extension.extend base (firstPairs.map Prod.fst) (firstPairs.map Prod.snd)
  let secondGrid := Grid.Extension.extend firstGrid (secondPairs.map Prod.fst) (secondPairs.map Prod.snd)
  let thirdGrid := Grid.Extension.extend secondGrid (thirdPairs.map Prod.fst) (thirdPairs.map Prod.snd)
  let finalGrid := Grid.Extension.extend thirdGrid (fourthPairs.map Prod.fst) (fourthPairs.map Prod.snd)
  let firstSecond := Grid.Extension.extend_inclusion firstGrid (secondPairs.map Prod.fst) (secondPairs.map Prod.snd)
  let secondThird := Grid.Extension.extend_inclusion secondGrid (thirdPairs.map Prod.fst) (thirdPairs.map Prod.snd)
  let thirdFourth := Grid.Extension.extend_inclusion thirdGrid (fourthPairs.map Prod.fst) (fourthPairs.map Prod.snd)
  let firstWalk := Input.Realization.formerDetourOn execution.first elimination clearances lines.1 finalGrid
    (fun point member => (firstSecond.trans (secondThird.trans thirdFourth)).vertex
      (Geometry.Lines.Bank.onExtended
        (elimination := elimination) (clearances := clearances) (regular := circuit.first.regular)
        lines.1 base point member))
  let secondWalk := Input.Realization.formerDetourOn execution.second.paid elimination clearances lines.2.1 finalGrid
    (fun point member => (secondThird.trans thirdFourth).vertex
      (Geometry.Lines.Bank.onExtended
        (elimination := elimination) (clearances := clearances) (regular := circuit.second.regular)
        lines.2.1 firstGrid point member))
  let thirdWalk := Input.Realization.formerDetourOn execution.third.paid elimination clearances lines.2.2.1 finalGrid
    (fun point member => thirdFourth.vertex
      (Geometry.Lines.Bank.onExtended
        (elimination := elimination) (clearances := clearances) (regular := circuit.third.regular)
        lines.2.2.1 secondGrid point member))
  let fourthWalk := Input.Realization.formerDetourOn execution.fourth.paid elimination clearances lines.2.2.2 finalGrid
    (Geometry.Lines.Bank.onExtended
      (elimination := elimination) (clearances := clearances) (regular := circuit.fourth.regular)
      lines.2.2.2 thirdGrid)
  let firstSeam := congrArg (Geometry.move elimination circuit.first.regular)
    (Transport.Seam.point_eq (site := site) (parameter := parameter) (leftQuarter := .first) (rightQuarter := .second)
      execution.first.finish_time secondInput.source_time Waist.directions_join.1)
  let secondSeam := congrArg (Geometry.move elimination circuit.first.regular)
    (Transport.Seam.point_eq (site := site) (parameter := parameter) (leftQuarter := .second) (rightQuarter := .third)
      execution.second.paid.finish_time thirdInput.source_time Waist.directions_join.2.1)
  let thirdSeam := congrArg (Geometry.move elimination circuit.first.regular)
    (Transport.Seam.point_eq (site := site) (parameter := parameter) (leftQuarter := .third) (rightQuarter := .fourth)
      execution.third.paid.finish_time fourthInput.source_time Waist.directions_join.2.2.1)
  let closing := congrArg (Geometry.move elimination circuit.first.regular)
    (Transport.Seam.point_eq (site := site) (parameter := parameter) (leftQuarter := .fourth) (rightQuarter := .first)
      execution.fourth.paid.finish_time firstInput.source_time Waist.directions_join.2.2.2)
  ⟨finalGrid, ⟨firstWalk.val.append ((secondWalk.val.castEndpoints firstSeam.symm rfl).append
      ((thirdWalk.val.castEndpoints secondSeam.symm rfl).append
        (fourthWalk.val.castEndpoints thirdSeam.symm closing))),
    Eq.mp (congrArg (Grid.FromStates.ContainsVertex finalGrid) closing) fourthWalk.property⟩⟩

/-- The historical assembly using the current original quarter views. -/
private def delegatedDetour (lines : Lines execution elimination clearances)
    (base : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter))) :
    Σ grid : Grid.ClearGrid (Paths.polynomial parameter)
        (RootRadius.Box.largeSquareBox (Paths.polynomial parameter)),
      {_walk : Grid.Walks.Walk grid
        (Geometry.move elimination circuit.first.regular
          (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter))
        (Geometry.move elimination circuit.first.regular
          (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter)) //
        Grid.FromStates.ContainsVertex grid
          (Geometry.move elimination circuit.first.regular
            (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter))} :=
  let firstPairs := Geometry.Lines.Bank.pairs
    (elimination := elimination) (clearances := clearances) (regular := circuit.first.regular) lines.1
  let secondPairs := Geometry.Lines.Bank.pairs
    (elimination := elimination) (clearances := clearances) (regular := circuit.second.regular) lines.2.1
  let thirdPairs := Geometry.Lines.Bank.pairs
    (elimination := elimination) (clearances := clearances) (regular := circuit.third.regular) lines.2.2.1
  let fourthPairs := Geometry.Lines.Bank.pairs
    (elimination := elimination) (clearances := clearances) (regular := circuit.fourth.regular) lines.2.2.2
  let firstGrid := Grid.Extension.extend base (firstPairs.map Prod.fst) (firstPairs.map Prod.snd)
  let secondGrid := Grid.Extension.extend firstGrid (secondPairs.map Prod.fst) (secondPairs.map Prod.snd)
  let thirdGrid := Grid.Extension.extend secondGrid (thirdPairs.map Prod.fst) (thirdPairs.map Prod.snd)
  let finalGrid := Grid.Extension.extend thirdGrid (fourthPairs.map Prod.fst) (fourthPairs.map Prod.snd)
  let firstSecond := Grid.Extension.extend_inclusion firstGrid (secondPairs.map Prod.fst) (secondPairs.map Prod.snd)
  let secondThird := Grid.Extension.extend_inclusion secondGrid (thirdPairs.map Prod.fst) (thirdPairs.map Prod.snd)
  let thirdFourth := Grid.Extension.extend_inclusion thirdGrid (fourthPairs.map Prod.fst) (fourthPairs.map Prod.snd)
  let firstWalk := Input.Realization.detourOn execution.first elimination clearances lines.1 finalGrid
    (fun point member => (firstSecond.trans (secondThird.trans thirdFourth)).vertex
      (Geometry.Lines.Bank.onExtended
        (elimination := elimination) (clearances := clearances) (regular := circuit.first.regular)
        lines.1 base point member))
  let secondWalk := Input.Realization.detourOn execution.second.paid elimination clearances lines.2.1 finalGrid
    (fun point member => (secondThird.trans thirdFourth).vertex
      (Geometry.Lines.Bank.onExtended
        (elimination := elimination) (clearances := clearances) (regular := circuit.second.regular)
        lines.2.1 firstGrid point member))
  let thirdWalk := Input.Realization.detourOn execution.third.paid elimination clearances lines.2.2.1 finalGrid
    (fun point member => thirdFourth.vertex
      (Geometry.Lines.Bank.onExtended
        (elimination := elimination) (clearances := clearances) (regular := circuit.third.regular)
        lines.2.2.1 secondGrid point member))
  let fourthWalk := Input.Realization.detourOn execution.fourth.paid elimination clearances lines.2.2.2 finalGrid
    (Geometry.Lines.Bank.onExtended
      (elimination := elimination) (clearances := clearances) (regular := circuit.fourth.regular)
      lines.2.2.2 thirdGrid)
  let firstSeam := congrArg (Geometry.move elimination circuit.first.regular)
    (Transport.Seam.point_eq (site := site) (parameter := parameter) (leftQuarter := .first) (rightQuarter := .second)
      execution.first.finish_time secondInput.source_time Waist.directions_join.1)
  let secondSeam := congrArg (Geometry.move elimination circuit.first.regular)
    (Transport.Seam.point_eq (site := site) (parameter := parameter) (leftQuarter := .second) (rightQuarter := .third)
      execution.second.paid.finish_time thirdInput.source_time Waist.directions_join.2.1)
  let thirdSeam := congrArg (Geometry.move elimination circuit.first.regular)
    (Transport.Seam.point_eq (site := site) (parameter := parameter) (leftQuarter := .third) (rightQuarter := .fourth)
      execution.third.paid.finish_time fourthInput.source_time Waist.directions_join.2.2.1)
  let closing := congrArg (Geometry.move elimination circuit.first.regular)
    (Transport.Seam.point_eq (site := site) (parameter := parameter) (leftQuarter := .fourth) (rightQuarter := .first)
      execution.fourth.paid.finish_time firstInput.source_time Waist.directions_join.2.2.2)
  ⟨finalGrid, ⟨firstWalk.val.append ((secondWalk.val.castEndpoints firstSeam.symm rfl).append
      ((thirdWalk.val.castEndpoints secondSeam.symm rfl).append
        (fourthWalk.val.castEndpoints thirdSeam.symm closing))),
    Eq.mp (congrArg (Grid.FromStates.ContainsVertex finalGrid) closing) fourthWalk.property⟩⟩

/-- The retained-head view preserves the complete historical assembly body. -/
private theorem detour_eq_delegated (lines : Lines execution elimination clearances)
    (base : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter))) :
    lines.detour base = delegatedDetour lines base := (rfl)

/-- The four original quarter agreements preserve the complete assembled result. -/
private theorem delegated_eq_former (lines : Lines execution elimination clearances)
    (base : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter))) :
    delegatedDetour lines base = formerDetour lines base := by
  let firstPairs := Geometry.Lines.Bank.pairs
    (elimination := elimination) (clearances := clearances) (regular := circuit.first.regular) lines.1
  let secondPairs := Geometry.Lines.Bank.pairs
    (elimination := elimination) (clearances := clearances) (regular := circuit.second.regular) lines.2.1
  let thirdPairs := Geometry.Lines.Bank.pairs
    (elimination := elimination) (clearances := clearances) (regular := circuit.third.regular) lines.2.2.1
  let fourthPairs := Geometry.Lines.Bank.pairs
    (elimination := elimination) (clearances := clearances) (regular := circuit.fourth.regular) lines.2.2.2
  let firstGrid := Grid.Extension.extend base (firstPairs.map Prod.fst) (firstPairs.map Prod.snd)
  let secondGrid := Grid.Extension.extend firstGrid (secondPairs.map Prod.fst) (secondPairs.map Prod.snd)
  let thirdGrid := Grid.Extension.extend secondGrid (thirdPairs.map Prod.fst) (thirdPairs.map Prod.snd)
  let finalGrid := Grid.Extension.extend thirdGrid (fourthPairs.map Prod.fst) (fourthPairs.map Prod.snd)
  let firstSecond := Grid.Extension.extend_inclusion firstGrid (secondPairs.map Prod.fst) (secondPairs.map Prod.snd)
  let secondThird := Grid.Extension.extend_inclusion secondGrid (thirdPairs.map Prod.fst) (thirdPairs.map Prod.snd)
  let thirdFourth := Grid.Extension.extend_inclusion thirdGrid (fourthPairs.map Prod.fst) (fourthPairs.map Prod.snd)
  have firstSame := Input.Realization.detourOn_whole_former execution.first elimination clearances lines.1 finalGrid
    (fun point member => (firstSecond.trans (secondThird.trans thirdFourth)).vertex
      (Geometry.Lines.Bank.onExtended
        (elimination := elimination) (clearances := clearances) (regular := circuit.first.regular)
        lines.1 base point member))
  have secondSame := Input.Realization.detourOn_whole_former execution.second.paid
    elimination clearances lines.2.1 finalGrid
    (fun point member => (secondThird.trans thirdFourth).vertex
      (Geometry.Lines.Bank.onExtended
        (elimination := elimination) (clearances := clearances) (regular := circuit.second.regular)
        lines.2.1 firstGrid point member))
  have thirdSame := Input.Realization.detourOn_whole_former execution.third.paid
    elimination clearances lines.2.2.1 finalGrid
    (fun point member => thirdFourth.vertex
      (Geometry.Lines.Bank.onExtended
        (elimination := elimination) (clearances := clearances) (regular := circuit.third.regular)
        lines.2.2.1 secondGrid point member))
  have fourthSame := Input.Realization.detourOn_whole_former execution.fourth.paid
    elimination clearances lines.2.2.2 finalGrid
    (Geometry.Lines.Bank.onExtended
      (elimination := elimination) (clearances := clearances) (regular := circuit.fourth.regular)
      lines.2.2.2 thirdGrid)

  let firstSeam := congrArg (Geometry.move elimination circuit.first.regular)
    (Transport.Seam.point_eq (site := site) (parameter := parameter) (leftQuarter := .first) (rightQuarter := .second)
      execution.first.finish_time secondInput.source_time Waist.directions_join.1)
  let secondSeam := congrArg (Geometry.move elimination circuit.first.regular)
    (Transport.Seam.point_eq (site := site) (parameter := parameter) (leftQuarter := .second) (rightQuarter := .third)
      execution.second.paid.finish_time thirdInput.source_time Waist.directions_join.2.1)
  let thirdSeam := congrArg (Geometry.move elimination circuit.first.regular)
    (Transport.Seam.point_eq (site := site) (parameter := parameter) (leftQuarter := .third) (rightQuarter := .fourth)
      execution.third.paid.finish_time fourthInput.source_time Waist.directions_join.2.2.1)
  let closing := congrArg (Geometry.move elimination circuit.first.regular)
    (Transport.Seam.point_eq (site := site) (parameter := parameter) (leftQuarter := .fourth) (rightQuarter := .first)
      execution.fourth.paid.finish_time firstInput.source_time Waist.directions_join.2.2.2)
  let Result :=
    Σ grid : Grid.ClearGrid (Paths.polynomial parameter)
        (RootRadius.Box.largeSquareBox (Paths.polynomial parameter)),
      {_walk : Grid.Walks.Walk grid
        (Geometry.move elimination circuit.first.regular
          (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter))
        (Geometry.move elimination circuit.first.regular
          (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter)) //
        Grid.FromStates.ContainsVertex grid
          (Geometry.move elimination circuit.first.regular
            (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter))}
  let combine := fun (firstWalk : Input.Realization.DetourResult execution.first elimination finalGrid)
      (secondWalk : Input.Realization.DetourResult execution.second.paid elimination finalGrid)
      (thirdWalk : Input.Realization.DetourResult execution.third.paid elimination finalGrid)
      (fourthWalk : Input.Realization.DetourResult execution.fourth.paid elimination finalGrid) =>
    (⟨finalGrid, ⟨firstWalk.val.append ((secondWalk.val.castEndpoints firstSeam.symm rfl).append
      ((thirdWalk.val.castEndpoints secondSeam.symm rfl).append
        (fourthWalk.val.castEndpoints thirdSeam.symm closing))),
    Eq.mp (congrArg (Grid.FromStates.ContainsVertex finalGrid) closing) fourthWalk.property⟩⟩ : Result)
  let firstWalk := Input.Realization.detourOn execution.first elimination clearances lines.1 finalGrid
    (fun point member => (firstSecond.trans (secondThird.trans thirdFourth)).vertex
      (Geometry.Lines.Bank.onExtended
        (elimination := elimination) (clearances := clearances) (regular := circuit.first.regular)
        lines.1 base point member))
  let oldFirstWalk := Input.Realization.formerDetourOn execution.first elimination clearances lines.1 finalGrid
    (fun point member => (firstSecond.trans (secondThird.trans thirdFourth)).vertex
      (Geometry.Lines.Bank.onExtended
        (elimination := elimination) (clearances := clearances) (regular := circuit.first.regular)
        lines.1 base point member))
  let secondWalk := Input.Realization.detourOn execution.second.paid elimination clearances lines.2.1 finalGrid
    (fun point member => (secondThird.trans thirdFourth).vertex
      (Geometry.Lines.Bank.onExtended
        (elimination := elimination) (clearances := clearances) (regular := circuit.second.regular)
        lines.2.1 firstGrid point member))
  let oldSecondWalk := Input.Realization.formerDetourOn execution.second.paid elimination clearances lines.2.1 finalGrid
    (fun point member => (secondThird.trans thirdFourth).vertex
      (Geometry.Lines.Bank.onExtended
        (elimination := elimination) (clearances := clearances) (regular := circuit.second.regular)
        lines.2.1 firstGrid point member))
  let thirdWalk := Input.Realization.detourOn execution.third.paid elimination clearances lines.2.2.1 finalGrid
    (fun point member => thirdFourth.vertex
      (Geometry.Lines.Bank.onExtended
        (elimination := elimination) (clearances := clearances) (regular := circuit.third.regular)
        lines.2.2.1 secondGrid point member))
  let oldThirdWalk := Input.Realization.formerDetourOn execution.third.paid elimination clearances lines.2.2.1 finalGrid
    (fun point member => thirdFourth.vertex
      (Geometry.Lines.Bank.onExtended
        (elimination := elimination) (clearances := clearances) (regular := circuit.third.regular)
        lines.2.2.1 secondGrid point member))
  let fourthWalk := Input.Realization.detourOn execution.fourth.paid elimination clearances lines.2.2.2 finalGrid
    (Geometry.Lines.Bank.onExtended
      (elimination := elimination) (clearances := clearances) (regular := circuit.fourth.regular)
      lines.2.2.2 thirdGrid)

  let oldFourthWalk := Input.Realization.formerDetourOn execution.fourth.paid
    elimination clearances lines.2.2.2 finalGrid
    (Geometry.Lines.Bank.onExtended
      (elimination := elimination) (clearances := clearances) (regular := circuit.fourth.regular)
      lines.2.2.2 thirdGrid)

  exact (congrArg (fun value => combine value secondWalk thirdWalk fourthWalk) firstSame).trans
    ((congrArg (fun value => combine oldFirstWalk value thirdWalk fourthWalk) secondSame).trans
      ((congrArg (fun value => combine oldFirstWalk oldSecondWalk value fourthWalk) thirdSame).trans
        (congrArg (fun value => combine oldFirstWalk oldSecondWalk oldThirdWalk value) fourthSame)))

/-- The complete factory preserves the original line, grid and closed-Walk values. -/
private theorem detour_whole_former (lines : Lines execution elimination clearances)
    (base : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter))) :
    lines.detour base = formerDetour lines base :=
  (detour_eq_delegated lines base).trans (delegated_eq_former lines base)

end Lines

/-- The complete historical detour factory retained for whole-value verification. -/
private def formerDetour {degreeBound : Nat} (execution : Execution.Cache initial secondInput thirdInput fourthInput)
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (clearances : AxisClearances elimination)
    (base : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter))) :
    Σ _lines : Lines execution elimination clearances,
      Σ grid : Grid.ClearGrid (Paths.polynomial parameter)
          (RootRadius.Box.largeSquareBox (Paths.polynomial parameter)),
        {_walk : Grid.Walks.Walk grid
          (Geometry.move elimination circuit.first.regular
            (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter))
          (Geometry.move elimination circuit.first.regular
            (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter)) //
          Grid.FromStates.ContainsVertex grid
            (Geometry.move elimination circuit.first.regular
              (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter))} :=
  let lines := Lines.build execution elimination clearances
  ⟨lines, Lines.formerDetour (execution := execution) (elimination := elimination)
    (clearances := clearances) lines base⟩

/-- The complete factory preserves the original line, grid and closed-Walk values. -/
private theorem detour_whole_former {degreeBound : Nat}
    (execution : Execution.Cache initial secondInput thirdInput fourthInput)
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (clearances : AxisClearances elimination)
    (base : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter))) :
    detour execution elimination clearances base = formerDetour execution elimination clearances base :=
  congrArg (fun value => Sigma.mk (Lines.build execution elimination clearances) value)
    (Lines.detour_whole_former (Lines.build execution elimination clearances) base)

end Execution.Cache

end ActualDetours

end Steps.Acquisition.Quarter.Circuit

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
