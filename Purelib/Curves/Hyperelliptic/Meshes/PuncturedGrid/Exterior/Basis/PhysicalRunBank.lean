module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseParameters
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.PairedAreaReversal
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedChains
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseChains
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Topology.Polygon.Stokes

public section

/-! Retain one oriented, source-indexed physical run bank for an actual occurrence. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis

open Purelib.Curves
open Purelib.Integration
open Purelib
open Purelib.Riemann

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

variable (retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared)
  {index : Nat} (inputs : retained.Inputs index)
  (outer : Fin prepared.occurrences.length) {faceIndex : Nat}
  (data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer) faceIndex)
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)

variable {retained inputs outer data coefficients}

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)

namespace PhysicalRunBank

/-- Read the physical path at one retained source-parent position in the specified direction. -/
@[expose] def Physical (ordered : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns.ParentOrderedRuns
  retained inputs outer data coefficients) (forward : Bool)
    (position : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length) : List PrimitivePoint :=
  if forward then ordered.physical position else Path.PairedAreaReversal.reverseIncrements (ordered.physical position)

/-- Every retained run forms a complete source chain in the specified direction.

Forward runs traverse parameter zero to one; reverse runs traverse one to zero without changing their fragment owners.
-/
@[expose] def Chains (ordered : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns.ParentOrderedRuns
  retained inputs outer data coefficients) (forward : Bool) : Prop :=
  if forward then ∀ run ∈ ordered.runs, Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains.SourceChain
    run.fragments 0 1
  else ∀ run ∈ ordered.runs, Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains.ReverseSourceChain
    run.fragments 1 0

/-- Each retained run has source mesh width at most the requested dyadic scale in its specified direction. -/
@[expose] def Widths (ordered : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns.ParentOrderedRuns
  retained inputs outer data coefficients) (forward : Bool) (depth : Nat) : Prop :=
  if forward then ∀ run ∈ ordered.runs, Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.sourceWidth run.fragments ≤ (1 / 2 :
    Normalization.InverseRootPolynomial.Coordinate) ^ depth
  else ∀ run ∈ ordered.runs, Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.reverseSourceWidth run.fragments ≤ (1
    / 2 : Normalization.InverseRootPolynomial.Coordinate) ^ depth

/-- Each retained run contains at most the supplied number of fragments. -/
@[expose] def Capacity (ordered : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns.ParentOrderedRuns
  retained inputs outer data coefficients) (capacity : Nat) : Prop :=
  ∀ run ∈ ordered.runs, run.fragments.length ≤ capacity

/-- Each retained fragment respects the common allowance and tolerance bounds. -/
@[expose] def Budgets (ordered : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns.ParentOrderedRuns
  retained inputs outer data coefficients)
    (allowance tolerance : Normalization.InverseRootPolynomial.Coordinate) : Prop :=
  ∀ run ∈ ordered.runs, ∀ fragment ∈ run.fragments,
    fragment.allowance ≤ allowance ∧ fragment.budget.tolerance ≤ tolerance

/-- The complete source-ordered physical word reads the supplied side area with the sign determined by its direction. -/
@[expose] def Area (ordered : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns.ParentOrderedRuns
  retained inputs outer data coefficients) (forward : Bool)
    (sideArea : Normalization.InverseRootPolynomial.Gaussian) : Prop :=
  Path.PairedIncrementArea.area (List.ofFn
    (Physical ordered
    forward)).flatten =
    if forward then sideArea else -sideArea

end PhysicalRunBank

set_option genInjectivity false in
/-- The direction belongs to the retained source occurrence. The area is that
of its cached Newton side sample, with reversal and every joining term retained. -/
structure PhysicalRunBank (retained :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared) (inputs :
  retained.Inputs index)
    (outer : Fin prepared.occurrences.length) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (faceIndex depth capacity : Nat) (sideArea : Normalization.InverseRootPolynomial.Gaussian)
    (allowance tolerance : Normalization.InverseRootPolynomial.Coordinate) where
  /-- The original row data for this source occurrence and face index. -/ data :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer) faceIndex
  /-- The original physical runs indexed by their retained source-parent positions. -/ ordered :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns.ParentOrderedRuns retained inputs outer data
    coefficients
  /-- The direction used to read the retained physical runs. -/ forward : Bool
  /-- The chosen direction is exactly that of the original source occurrence. -/ direction : forward =
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer).sourceForward
  /-- Every retained run is a complete source chain in its recorded direction. -/ chains :
    PhysicalRunBank.Chains ordered forward
  /-- The retained fragment mesh widths obey the supplied dyadic depth. -/ widths :
    PhysicalRunBank.Widths ordered forward depth
  /-- The number of fragments in each retained run respects the common capacity. -/ capacity_bound :
    PhysicalRunBank.Capacity ordered capacity
  /-- The entire ordered physical word reads the original side area with its orientation sign. -/ area_eq :
    PhysicalRunBank.Area ordered forward sideArea
  /-- Every retained fragment satisfies the common allowance and tolerance bounds. -/ budgets :
    PhysicalRunBank.Budgets ordered allowance
    tolerance

constructive_injectivity PhysicalRunBank

namespace PhysicalRunBank
variable {depth capacity : Nat} {sideArea : Normalization.InverseRootPolynomial.Gaussian} {allowance tolerance :
  Normalization.InverseRootPolynomial.Coordinate}

/-- Assemble a forward physical run bank from the original source-ordered runs and their supplied certificates.

The construction retains the row data, complete source chains, dyadic width bounds, capacity, budgets and exact
side-area equality. -/
@[expose] def ofForward (ordered : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns.ParentOrderedRuns
  retained inputs outer data coefficients)
    (direction : (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).sourceForward = true)
    (chains : ∀ run ∈ ordered.runs, Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains.SourceChain
      run.fragments 0 1)
    (widths : ∀ run ∈ ordered.runs, Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.sourceWidth run.fragments ≤ (1 / 2
      : Normalization.InverseRootPolynomial.Coordinate) ^ depth)
    (capacityBound : ∀ run ∈ ordered.runs, run.fragments.length ≤ capacity)
    (budgetBounds : Budgets ordered
      allowance tolerance)
    (areaEq : Path.PairedIncrementArea.area (List.ofFn ordered.physical).flatten = sideArea) :
    PhysicalRunBank retained inputs outer coefficients
      faceIndex depth capacity sideArea allowance tolerance :=
  ⟨data, ordered, true, direction.symm, chains, widths, capacityBound, areaEq, budgetBounds⟩

/-- Assemble a reverse physical run bank from the original source-ordered runs and their supplied certificates.

The original descending chains and reverse-width bounds are retained, together with the negated side-area readback and
the same fragment budgets. -/
@[expose] def ofReverse (ordered : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns.ParentOrderedRuns
  retained inputs outer data coefficients)
    (direction : (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).sourceForward = false)
    (chains : ∀ run ∈ ordered.runs,
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains.ReverseSourceChain run.fragments 1 0)
    (widths : ∀ run ∈ ordered.runs, Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.reverseSourceWidth run.fragments ≤
      (1 / 2 : Normalization.InverseRootPolynomial.Coordinate) ^ depth)
    (capacityBound : ∀ run ∈ ordered.runs, run.fragments.length ≤ capacity)
    (budgetBounds : Budgets ordered
      allowance tolerance)
    (areaEq : Path.PairedIncrementArea.area (List.ofFn (fun position =>
      Path.PairedAreaReversal.reverseIncrements (ordered.physical position))).flatten = -sideArea) :
    PhysicalRunBank retained inputs outer coefficients
      faceIndex depth capacity sideArea allowance tolerance :=
  ⟨data, ordered, false, direction.symm, chains, widths, capacityBound, areaEq, budgetBounds⟩

/-- The component reads source-oriented paths without unpacking the cached row owner. -/
@[expose] def physical (bank : PhysicalRunBank
  retained inputs outer coefficients faceIndex depth capacity sideArea allowance tolerance) :=
  Physical bank.ordered bank.forward

/-- Reading the complete retained physical bank gives the side area with the direction of its original source
occurrence. -/
theorem area_readback (bank : PhysicalRunBank retained
  inputs outer coefficients faceIndex depth capacity sideArea allowance tolerance) :
    Path.PairedIncrementArea.area (List.ofFn bank.physical).flatten =
      if (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
        outer).sourceForward then sideArea else -sideArea :=
  bank.area_eq.trans (congrArg (fun forward => if forward then sideArea else -sideArea) bank.direction)

end PhysicalRunBank
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis
