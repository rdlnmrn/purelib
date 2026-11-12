module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningRows
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Realization
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningValues
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.StandardIntersections
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices

open Purelib

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningRows

open Purelib.Riemann

open Purelib.Topology.Polygon

public section

/-! Cached geometric basis evidence on the very corrected bank whose programs are integrated. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates (CutBank ClosedCoordinates)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningRows (BasisCoordinates)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    BasedBranchBank.Ordered bank
    sheet} {paired : Ordered.Paired ordered}
    (prepared : Prepared paired)

/-- All retained A/A intersection numbers vanish. -/
@[expose] def AIntersectionTable (cut : CutBank prepared) : Prop := ∀ first last, cut.intersections.aa
  first last = 0
/-- All retained B/B intersection numbers vanish. -/
@[expose] def BIntersectionTable (cut : CutBank prepared) : Prop := ∀ first last, cut.intersections.bb
  first last = 0
/-- The retained A/B intersection matrix is the identity. -/
@[expose] def MixedIntersectionTable (cut : CutBank prepared) : Prop :=
  ∀ first last, cut.intersections.ab first last = if first = last then 1 else 0

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared in
/-- An executable constructor expressing every closed integral row in the same retained cut basis. -/
@[expose] def SpanningBuilder (cut : CutBank prepared) :=
  ∀ {word : List (OrientedEdge lifted.vertices.count)} (row : ClosedCoordinates word
    cut.integral), BasisCoordinates cut row

set_option genInjectivity false in
/-- The cut, its standard table, and the executable spanning constructor share one program owner. -/
structure GeometricBasis where
  /-- The actual certified cut on the retained corrected period-program owner. -/ cut : CutBank
    prepared
  /-- The retained A/A intersection table is zero. -/ aa :
    AIntersectionTable prepared cut
  /-- The retained B/B intersection table is zero. -/ bb :
    BIntersectionTable prepared cut
  /-- The retained A/B intersection table is the identity. -/ ab :
    MixedIntersectionTable prepared cut
  /-- The executable spanning constructor on this exact retained cut. -/ spanning :
    SpanningBuilder prepared cut

constructive_injectivity GeometricBasis

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared in
/-- Construct the certified cut, standard intersection table and executable spanning map on the actual retained
period-program owner. -/
@[expose] def geometricBasis : GeometricBasis
  prepared :=
  let cut := CutBank.build prepared (Meshes.LiftedPuncturedGrid.Cut.build lifted)
  ⟨cut, cut.aa_standard, cut.bb_standard, cut.ab_standard, fun row => BasisCoordinates.build cut row⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank (PairedPeriodBank)

variable {genus : Nat} {curve : HyperellipticCurve genus}

set_option genInjectivity false in
/-- Genus zero carries its finite base case; positive genus retains the actual certified cut basis. -/
inductive GeometricBasis : PairedPeriodBank curve → Type 4 where
  /-- Retain the finite genus-zero base case for the empty period bank. -/ | empty (zero : genus = 0) :
    GeometricBasis (.empty zero)
  /-- Retain the geometric basis on the exact prepared owner of the nonempty period bank. -/ | retained {branches :
    BranchIsolation.Data curve} {higher : 1 < curve.polynomial.natDegree}
      {base : FramedPuncturedGrid curve branches higher} {lifted : Meshes.LiftedPuncturedGrid base}
      {bank : BasedBranchBank lifted} {sheet : Fin 2} {ordered : BasedBranchBank.Ordered bank sheet}
        {paired : Ordered.Paired ordered}
      {prepared : Prepared paired} (basis :
        Prepared.GeometricBasis prepared) :
        GeometricBasis (.retained
        prepared)

constructive_injectivity GeometricBasis

/-- Construct geometric basis evidence for the actual period bank, preserving its empty or retained constructor. -/
@[expose] def geometricBasis : (bank : PairedPeriodBank curve) → bank.GeometricBasis
  | .empty zero => .empty zero
  | .retained prepared => .retained prepared.geometricBasis

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank
