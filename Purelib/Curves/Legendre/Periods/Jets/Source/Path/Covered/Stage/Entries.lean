module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage
import Purelib.Data.List.Append
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Admission

/-! # Original bank occurrences and their retained global source preparations

The actual requestBank keeps one source occurrence per original covered
parent, including duplicate physical points. Structural length and entry
readbacks identify the same stored preparation at its original global index.
The StageAttempt's whole bank factory equation transports those identities
without another endpoint request or local allocation.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count floor : Nat}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}

/-- The exact requested source bank retains one entry per actual original covered-parent occurrence. -/
theorem requestBank_length : {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → (prepared : PreparedParents covered floor targets) →
    (requestBank covered prepared).length = parents.length
  | [], .nil, _ => rfl
  | _ :: _, .cons _ _ remaining, prepared => congrArg Nat.succ (requestBank_length remaining prepared.2)

/-- The bank's bounded entry is the original vertex request on that SAME actual stored global preparation.

The factory occurs only in the readback claim. Lookup reads the actual
bank; no displayed vertex request is executed to recover an occurrence.
-/
theorem requestBank_getElem : {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → (prepared : PreparedParents covered floor targets) →
    (index : Fin parents.length) → (bound : index.val < (requestBank covered prepared).length) →
    (requestBank covered prepared)[index.val]'bound =
      Vertex.Entry.request (prepared.entry index).firstVertex.val targets.endpoint targets.endpoint_positive
  | [], .nil, _, index, _ => Fin.elim0 index
  | _ :: _, .cons _ _ _, _, ⟨0, _⟩, _ => rfl
  | _ :: _, .cons _ _ remaining, prepared, ⟨index + 1, bounded⟩, bound =>
      requestBank_getElem remaining prepared.2 ⟨index, Nat.lt_of_succ_lt_succ bounded⟩
        (Nat.lt_of_succ_lt_succ bound)

namespace StageAttempt

variable {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent)}
    {index rootStage : Nat} (attempt : StageAttempt covered chain index floor rootStage)

/-- The SAME actual bank of a retained global attempt has exactly its original parent count. -/
theorem bank_length : attempt.2.2.1.val.length = (parent :: parents).length :=
  (congrArg List.length attempt.2.2.1.property).trans (requestBank_length covered attempt.2.1)

/-- Every actual global bank occurrence retains the SAME source preparation and original global Targets.

The actual bank's whole factory equality and structural occurrence law
identify its complete cached entry. Neither endpoint selection nor a source
query is repeated, and no locally allocated target cache is substituted.
-/
theorem bank_getElem (sourceIndex : Fin (parent :: parents).length)
    (bound : sourceIndex.val < attempt.2.2.1.val.length) :
    attempt.2.2.1.val[sourceIndex.val]'bound =
      Vertex.Entry.request (attempt.2.1.entry sourceIndex).firstVertex.val
        attempt.1.val.endpoint attempt.1.val.endpoint_positive := by
  have bankBound : sourceIndex.val < (requestBank covered attempt.2.1).length := by
    rewrite [requestBank_length]
    exact sourceIndex.isLt
  exact (getElem_congr attempt.2.2.1.property rfl bound).trans
    (requestBank_getElem covered attempt.2.1 sourceIndex bankBound)

variable {point : LiftedPoint 2} {found : Vertex.Bank.Found attempt.2.2.1.val point}
    (position : Vertex.Bank.Position (.found found))

/-- Read the source occurrence of the SAME actual first bank match from its stored position.

Only the original bank-length equation changes the index bound. Neither a
lookup nor any displayed vertex/source request executes again.
-/
@[expose] def foundSourceIndex : Fin (parent :: parents).length :=
  ⟨position.index.val, Eq.mp (congrArg (fun length => position.index.val < length) attempt.bank_length)
    position.index.isLt⟩

/-- The selected source occurrence preserves the original actual first-match natural position exactly. -/
theorem foundSourceIndex_val : (attempt.foundSourceIndex position).val = position.index.val := rfl

/-- The exact first-match entry is the complete original source request at that SAME retained global occurrence.

This equality preserves its original Vertex, three primitive requests and
selected readings together. Coordinate equality, Distinct and root-branch
compatibility are not premises, and no source request is replayed.
-/
theorem found_entry_eq : found.entry =
    Vertex.Entry.request (attempt.2.1.entry (attempt.foundSourceIndex position)).firstVertex.val
      attempt.1.val.endpoint attempt.1.val.endpoint_positive :=
  position.entry_eq.symm.trans
    (attempt.bank_getElem (attempt.foundSourceIndex position) position.index.isLt)

/-- The original selected source occurrence has the actual requested lifted point, including its retained sheet. -/
theorem found_source_point :
    PreparedParent.startPoint ((parent :: parents)[(attempt.foundSourceIndex position).val]'
      (attempt.foundSourceIndex position).isLt) = point :=
  (congrArg (fun entry : Vertex.Entry parameter attempt.1.val.endpoint => entry.point)
    (attempt.found_entry_eq position)).symm.trans found.point_eq

/-- The selected Found's actual root channel is the SAME original source sample at its stored occurrence.

Only whole original entry equality, its point-index transport and the
original firstVertex factory law are used. No equality is inferred between
different same-key source occurrences or between independently chosen roots.
-/
theorem found_source_name : found.original.sample.certificate.value.name =
    (attempt.2.1.entry (attempt.foundSourceIndex position)).firstSample.certificate.value.name := by
  have retained := congrArg (fun entry : Vertex.Entry parameter attempt.1.val.endpoint =>
    entry.original.sample.certificate.value.name) (attempt.found_entry_eq position)
  change found.entry.original.sample.certificate.value.name =
    (attempt.2.1.entry (attempt.foundSourceIndex position)).firstVertex.val.sample.certificate.value.name at retained
  have vertexName := congrArg
    (fun vertex : Vertex parameter (PreparedParent.startPoint
        ((parent :: parents)[(attempt.foundSourceIndex position).val]'
          (attempt.foundSourceIndex position).isLt)) => vertex.sample.certificate.value.name)
    (attempt.2.1.entry (attempt.foundSourceIndex position)).firstVertex.property
  have sampleName := congrArg
    (fun sample : ContinuedNeighborhood.Point _ _ => sample.certificate.value.name)
    (Vertex.ofPoint_sample (attempt.2.1.entry (attempt.foundSourceIndex position)).firstSample)
  have transported : found.original.sample.certificate.value.name =
      found.entry.original.sample.certificate.value.name := by
    cases found with
    | mk entry present equal =>
        cases equal
        rfl
  exact transported.trans (retained.trans (vertexName.trans sampleName))

/-- The exact first selected global source query agrees with that SAME retained Found's old full-cubic sample.

The original patch supplies the child-query comparison. Whole original
entry equality identifies the actual Found sample with that child's stored
source sample; no new source request or root comparison is executed.
This does not yet compare a different repeated visiting occurrence.
-/
def foundQueryEquivalent :
    NamedEquivalent
      (((parent :: parents)[(attempt.foundSourceIndex position).val]'
        (attempt.foundSourceIndex position).isLt).edge.rootName 0
          ((parent :: parents)[(attempt.foundSourceIndex position).val]'
            (attempt.foundSourceIndex position).isLt).edge.baseInside)
      found.original.sample.certificate.value.name :=
  NamedEquivalent.transport rfl (attempt.found_source_name position).symm
    (attempt.2.1.entry (attempt.foundSourceIndex position)).firstQueryEquivalent

end StageAttempt

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

end
