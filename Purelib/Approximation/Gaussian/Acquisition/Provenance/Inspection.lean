module

public import Purelib.Approximation.Gaussian.Acquisition.Annotated.Basic
public import Purelib.Algebra.Quadratic.Pair.Gaussian.Realization.Admission
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Cached inspection of original annotated provenance

An inspection retains the entire original annotation, the actual root admission
and signed-reading work when present, and its cached exact scalar reading.
Readback and later generator admission use the same data; they do not repeat
isolation, coefficient inspection or finite sign selection.
-/

public section

namespace Purelib.Approximation.Gaussian.Acquisition.Provenance

open Purelib.Approximation.Gaussian.Acquisition (Annotated Provenance)
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Algebra.Quadratic.Pair.Gaussian (Realization)
open Purelib.Riemann.RootContinuation
open Purelib.Data.Rat.Fraction
open Purelib.Data.Gaussian

/-- Root admission and its actual signed-reading certificate at the same original root owner. -/
@[expose] def RootData {channel : Name.Coherent.CoherentNamed} (root : SquareRootSidecar.Sidecar channel) : Type 1 :=
  Sigma fun checked : Realization.AdmissionCheck channel root => checked.outcome.RationalCertificate

/-- The inspection data needed by the actual original annotation class. -/
@[expose] def Data {channel : Name.Coherent.CoherentNamed} : Option (Provenance channel) → Type 1
  | some (.squareRoot root) => RootData root
  | some (.polynomialRoot _) => ULift.{1} (Option (RationalSidecar channel))
  | some (.algebraic _) => ULift.{1} (Option (RationalSidecar channel))
  | _ => PUnit

/-- Inspect one original annotation without rebuilding its numerical channel or root producer. -/
@[expose, noinline, nospecialize] def analyze {channel : Name.Coherent.CoherentNamed}
    (source : Option (Provenance channel)) : Data source :=
  match source with
  | some (.squareRoot root) =>
      let checked := Realization.inspectRoot root
      let certificate := checked.outcome.inspectRational
      ⟨checked, certificate⟩
  | some (.rational _) => PUnit.unit
  | some (.quadratic _) => PUnit.unit
  | some (.polynomialRoot root) => ⟨root.scalar?⟩
  | some (.algebraic sidecar) => ⟨sidecar.scalar?⟩
  | none => PUnit.unit

/-- Read exact scalar evidence from the same already computed annotation inspection. -/
@[expose, noinline, nospecialize] def read {channel : Name.Coherent.CoherentNamed}
    (source : Option (Provenance channel)) (data : Data source) :
    Option (RationalSidecar channel) :=
  match source, data with
  | some (.squareRoot _), root => root.1.outcome.rationalReading? root.2
  | some (.rational reading), _ => some reading
  | some (.quadratic coordinates), _ => if zero : coordinates.evidence.value.im = 0
      then some (coordinates.scalarReading zero) else none
  | some (.polynomialRoot _), reading => reading.down
  | some (.algebraic _), reading => reading.down
  | none, _ => none

set_option genInjectivity false in
/-- A shallow cache retaining one original source, its actual dependent analysis and exact reading specification. -/
structure InspectionPayload.{u, v, w} (sourceType : Type u) (dataType : sourceType → Type v)
    (readingType : sourceType → Type w)
    (readData : (source : sourceType) → dataType source → Option (readingType source))
    (original : sourceType) where
  /-- The complete original source retained as executable data. -/
  source : sourceType
  /-- The retained source is the original nominal input. -/
  source_eq : source = original
  /-- The actual analysis computed at this same original source. -/
  data : dataType source
  /-- The cached exact reading at the same retained source. -/
  reading : Option (readingType source)
  /-- Readback consumes the actual retained analysis. -/
  reading_eq : reading = readData source data

constructive_injectivity InspectionPayload

/-- An original annotation with its cached root inspection and scalar evidence. -/
@[expose] def Inspection (original : Annotated) :=
  InspectionPayload Annotated (fun source => Data source.provenance)
    (fun source => RationalSidecar source.channel) (fun source data => read source.provenance data) original

/-- Compute the original annotation's dependent analysis and exact reading once and retain both. -/
@[expose, noinline, nospecialize] def inspect (source : Annotated) : Inspection source :=
  let data := analyze source.provenance
  let reading := read source.provenance data
  ⟨source, rfl, data, reading, rfl⟩

/-- Read the same stored analysis at its exact original annotation, using only the retained source identity. -/
@[expose, noinline, nospecialize] def Inspection.originalData {source : Annotated} (inspection : Inspection source) :
    Data source.provenance :=
  inspection.source_eq ▸ inspection.data

/-- Read the same cached scalar evidence at the original annotation without repeating inspection. -/
@[expose, noinline, nospecialize] def Inspection.scalar {source : Annotated} (inspection : Inspection source) :
    Option (RationalSidecar source.channel) := inspection.source_eq ▸ inspection.reading

/-- Inspecting an algebraic annotation retains its original scalar reading.

The same result is stored in the inspection and read without repeating the
original algebraic scalar operation.
-/
theorem inspect_algebraic_scalar {channel : Name.Coherent.CoherentNamed} (sidecar : Algebraic.Sidecar channel) :
    (inspect (Annotated.algebraic sidecar)).scalar = sidecar.scalar? := rfl

/-- Read the actual cached root admission and sign certificate selected by the original annotation. -/
@[expose, noinline, nospecialize] def Inspection.rootData {source : Annotated} (inspection : Inspection source)
    (root : SquareRootSidecar.Sidecar source.channel) (known : source.provenance = some (.squareRoot root)) :
    RootData root := by
  have data := inspection.originalData
  unfold Data at data
  rewrite [known] at data
  exact data

/-- An opaque original annotation supplies no exact scalar reading. -/
theorem inspect_opaque_scalar (channel : Name.Coherent.CoherentNamed) :
    (inspect (Annotated.opaque channel)).scalar = none := rfl

/-- A positive nonsquare original root has no scalar reading, while its admitted realization remains cached. -/
theorem inspect_root_nonsquare {channel : Name.Coherent.CoherentNamed} (root : SquareRootSidecar.Sidecar channel)
    (parameter : Rational)
    (same : root.parameter = Cast.CoordinateTaylor.ofCoordinate parameter)
    (positive : 0 < parameter) (missing : (Square.inspect parameter).root? = none) :
    (inspect ⟨channel, some (.squareRoot root)⟩).scalar = none := by
  obtain ⟨admission, selected, _⟩ := Realization.inspectRoot_positive root parameter same positive missing
  unfold inspect Inspection.scalar analyze read
  dsimp only
  rewrite [selected]
  rfl

/-- Literal identity of entire original annotations transports the same cached work without another producer call. -/
@[expose] def Inspection.transport {first second : Annotated} (inspection : Inspection first) (same : first = second) :
    Inspection second := same ▸ inspection

end Purelib.Approximation.Gaussian.Acquisition.Provenance

end
