import CCL.Riemann.ExplicitLegendreGeneratedBGeometryCertificate
import CCL.Riemann.GeneratedCycleProvenanceLemmas
import CCL.Riemann.ExplicitLegendreGeneratedBCycleProvenanceData.Chunk000
import CCL.Riemann.ExplicitLegendreGeneratedBCycleProvenanceData.Chunk001
import CCL.Riemann.ExplicitLegendreGeneratedBCycleProvenanceData.Chunk002
import CCL.Riemann.ExplicitLegendreGeneratedBCycleProvenanceData.Chunk003
import CCL.Riemann.ExplicitLegendreGeneratedBCycleProvenanceData.Chunk004
import CCL.Riemann.ExplicitLegendreGeneratedBCycleProvenanceData.Chunk005
import CCL.Riemann.ExplicitLegendreGeneratedBCycleProvenanceData.Chunk006
import CCL.Riemann.ExplicitLegendreGeneratedBCycleProvenanceData.Chunk007
import CCL.Riemann.ExplicitLegendreGeneratedBCycleProvenanceData.Chunk008
import CCL.Riemann.ExplicitLegendreGeneratedBCycleProvenanceData.Chunk009
import CCL.Riemann.ExplicitLegendreGeneratedBCycleProvenanceData.Chunk010
import CCL.Riemann.ExplicitLegendreGeneratedBCycleProvenanceData.Chunk011
import CCL.Riemann.ExplicitLegendreGeneratedBCycleProvenanceData.Chunk012
import CCL.Riemann.ExplicitLegendreGeneratedBCycleProvenanceData.Chunk013
import CCL.Riemann.ExplicitLegendreGeneratedBCycleProvenanceData.Chunk014
import CCL.Riemann.ExplicitLegendreGeneratedBCycleProvenanceData.Chunk015
import CCL.Riemann.ExplicitLegendreGeneratedBCycleProvenanceData.Chunk016
import CCL.Riemann.ExplicitLegendreGeneratedBCycleProvenanceData.Chunk017
import CCL.Riemann.ExplicitLegendreGeneratedBCycleProvenanceData.Chunk018
import CCL.Riemann.ExplicitLegendreGeneratedBCycleProvenanceData.Chunk019
import CCL.Riemann.ExplicitLegendreGeneratedBCycleProvenanceData.Chunk020
import CCL.Riemann.ExplicitLegendreGeneratedBCycleProvenanceData.Chunk021
import CCL.Riemann.ExplicitLegendreGeneratedBCycleProvenanceData.Chunk022
import CCL.Riemann.ExplicitLegendreGeneratedBCycleProvenanceData.Chunk023
import CCL.Riemann.ExplicitLegendreGeneratedBCycleProvenanceData.Chunk024
import CCL.Riemann.ExplicitLegendreGeneratedBCycleProvenanceData.Chunk025
import CCL.Riemann.ExplicitLegendreGeneratedBCycleProvenanceData.Chunk026
import CCL.Riemann.ExplicitLegendreGeneratedBCycleProvenanceData.Chunk027
import CCL.Riemann.ExplicitLegendreGeneratedBCycleProvenanceData.Chunk028
import CCL.Riemann.ExplicitLegendreGeneratedBCycleProvenanceData.Chunk029
import CCL.Riemann.ExplicitLegendreGeneratedBCycleProvenanceData.Chunk030
import CCL.Riemann.ExplicitLegendreGeneratedBCycleProvenanceData.Chunk031
import CCL.Riemann.ExplicitLegendreGeneratedBCycleProvenanceData.Chunk032
import CCL.Riemann.ExplicitLegendreGeneratedBCycleProvenanceData.Chunk033

/-!
# Provenance of the generated Legendre B-cycle rows

The generated B geometry is split into short shards.  The declarations below
compose their independently checked traces along the same two range trees used
by the retained period run.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedBCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem generatedGeometricSummaryRange016_positionTrace (token : Unit) :
    (generatedGeometricSummaryRange016 token).range.run.positionTrace =
      PositionTrace.consecutive 128 8 :=
  geometricShard016_positionTrace token

theorem generatedGeometricSummaryRange015_positionTrace (token : Unit) :
    (generatedGeometricSummaryRange015 token).range.run.positionTrace =
      PositionTrace.consecutive 120 16 := by
  change PositionTrace.append
      (geometricShard015Summary token).range.run.positionTrace
      (generatedGeometricSummaryRange016 token).range.run.positionTrace = _
  rw [geometricShard015_positionTrace,
    generatedGeometricSummaryRange016_positionTrace]
  exact PositionTrace.append_consecutive 120 8 8

theorem generatedGeometricSummaryRange014_positionTrace (token : Unit) :
    (generatedGeometricSummaryRange014 token).range.run.positionTrace =
      PositionTrace.consecutive 112 24 := by
  change PositionTrace.append
      (geometricShard014Summary token).range.run.positionTrace
      (generatedGeometricSummaryRange015 token).range.run.positionTrace = _
  rw [geometricShard014_positionTrace,
    generatedGeometricSummaryRange015_positionTrace]
  exact PositionTrace.append_consecutive 112 8 16

theorem generatedGeometricSummaryRange013_positionTrace (token : Unit) :
    (generatedGeometricSummaryRange013 token).range.run.positionTrace =
      PositionTrace.consecutive 104 32 := by
  change PositionTrace.append
      (geometricShard013Summary token).range.run.positionTrace
      (generatedGeometricSummaryRange014 token).range.run.positionTrace = _
  rw [geometricShard013_positionTrace,
    generatedGeometricSummaryRange014_positionTrace]
  exact PositionTrace.append_consecutive 104 8 24

theorem generatedGeometricSummaryRange012_positionTrace (token : Unit) :
    (generatedGeometricSummaryRange012 token).range.run.positionTrace =
      PositionTrace.consecutive 96 40 := by
  change PositionTrace.append
      (geometricShard012Summary token).range.run.positionTrace
      (generatedGeometricSummaryRange013 token).range.run.positionTrace = _
  rw [geometricShard012_positionTrace,
    generatedGeometricSummaryRange013_positionTrace]
  exact PositionTrace.append_consecutive 96 8 32

theorem generatedGeometricSummaryRange011_positionTrace (token : Unit) :
    (generatedGeometricSummaryRange011 token).range.run.positionTrace =
      PositionTrace.consecutive 88 48 := by
  change PositionTrace.append
      (geometricShard011Summary token).range.run.positionTrace
      (generatedGeometricSummaryRange012 token).range.run.positionTrace = _
  rw [geometricShard011_positionTrace,
    generatedGeometricSummaryRange012_positionTrace]
  exact PositionTrace.append_consecutive 88 8 40

theorem generatedGeometricSummaryRange010_positionTrace (token : Unit) :
    (generatedGeometricSummaryRange010 token).range.run.positionTrace =
      PositionTrace.consecutive 80 56 := by
  change PositionTrace.append
      (geometricShard010Summary token).range.run.positionTrace
      (generatedGeometricSummaryRange011 token).range.run.positionTrace = _
  rw [geometricShard010_positionTrace,
    generatedGeometricSummaryRange011_positionTrace]
  exact PositionTrace.append_consecutive 80 8 48

theorem generatedGeometricSummaryRange009_positionTrace (token : Unit) :
    (generatedGeometricSummaryRange009 token).range.run.positionTrace =
      PositionTrace.consecutive 72 64 := by
  change PositionTrace.append
      (geometricShard009Summary token).range.run.positionTrace
      (generatedGeometricSummaryRange010 token).range.run.positionTrace = _
  rw [geometricShard009_positionTrace,
    generatedGeometricSummaryRange010_positionTrace]
  exact PositionTrace.append_consecutive 72 8 56

theorem generatedGeometricSummaryRange008_positionTrace (token : Unit) :
    (generatedGeometricSummaryRange008 token).range.run.positionTrace =
      PositionTrace.consecutive 64 72 := by
  change PositionTrace.append
      (geometricShard008Summary token).range.run.positionTrace
      (generatedGeometricSummaryRange009 token).range.run.positionTrace = _
  rw [geometricShard008_positionTrace,
    generatedGeometricSummaryRange009_positionTrace]
  exact PositionTrace.append_consecutive 64 8 64

theorem generatedGeometricSummaryRange007_positionTrace (token : Unit) :
    (generatedGeometricSummaryRange007 token).range.run.positionTrace =
      PositionTrace.consecutive 56 80 := by
  change PositionTrace.append
      (geometricShard007Summary token).range.run.positionTrace
      (generatedGeometricSummaryRange008 token).range.run.positionTrace = _
  rw [geometricShard007_positionTrace,
    generatedGeometricSummaryRange008_positionTrace]
  exact PositionTrace.append_consecutive 56 8 72

theorem generatedGeometricSummaryRange006_positionTrace (token : Unit) :
    (generatedGeometricSummaryRange006 token).range.run.positionTrace =
      PositionTrace.consecutive 48 88 := by
  change PositionTrace.append
      (geometricShard006Summary token).range.run.positionTrace
      (generatedGeometricSummaryRange007 token).range.run.positionTrace = _
  rw [geometricShard006_positionTrace,
    generatedGeometricSummaryRange007_positionTrace]
  exact PositionTrace.append_consecutive 48 8 80

theorem generatedGeometricSummaryRange005_positionTrace (token : Unit) :
    (generatedGeometricSummaryRange005 token).range.run.positionTrace =
      PositionTrace.consecutive 40 96 := by
  change PositionTrace.append
      (geometricShard005Summary token).range.run.positionTrace
      (generatedGeometricSummaryRange006 token).range.run.positionTrace = _
  rw [geometricShard005_positionTrace,
    generatedGeometricSummaryRange006_positionTrace]
  exact PositionTrace.append_consecutive 40 8 88

theorem generatedGeometricSummaryRange004_positionTrace (token : Unit) :
    (generatedGeometricSummaryRange004 token).range.run.positionTrace =
      PositionTrace.consecutive 32 104 := by
  change PositionTrace.append
      (geometricShard004Summary token).range.run.positionTrace
      (generatedGeometricSummaryRange005 token).range.run.positionTrace = _
  rw [geometricShard004_positionTrace,
    generatedGeometricSummaryRange005_positionTrace]
  exact PositionTrace.append_consecutive 32 8 96

theorem generatedGeometricSummaryRange003_positionTrace (token : Unit) :
    (generatedGeometricSummaryRange003 token).range.run.positionTrace =
      PositionTrace.consecutive 24 112 := by
  change PositionTrace.append
      (geometricShard003Summary token).range.run.positionTrace
      (generatedGeometricSummaryRange004 token).range.run.positionTrace = _
  rw [geometricShard003_positionTrace,
    generatedGeometricSummaryRange004_positionTrace]
  exact PositionTrace.append_consecutive 24 8 104

theorem generatedGeometricSummaryRange002_positionTrace (token : Unit) :
    (generatedGeometricSummaryRange002 token).range.run.positionTrace =
      PositionTrace.consecutive 16 120 := by
  change PositionTrace.append
      (geometricShard002Summary token).range.run.positionTrace
      (generatedGeometricSummaryRange003 token).range.run.positionTrace = _
  rw [geometricShard002_positionTrace,
    generatedGeometricSummaryRange003_positionTrace]
  exact PositionTrace.append_consecutive 16 8 112

theorem generatedGeometricSummaryRange001_positionTrace (token : Unit) :
    (generatedGeometricSummaryRange001 token).range.run.positionTrace =
      PositionTrace.consecutive 8 128 := by
  change PositionTrace.append
      (geometricShard001Summary token).range.run.positionTrace
      (generatedGeometricSummaryRange002 token).range.run.positionTrace = _
  rw [geometricShard001_positionTrace,
    generatedGeometricSummaryRange002_positionTrace]
  exact PositionTrace.append_consecutive 8 8 120

theorem generatedGeometricSummaryRange000_positionTrace (token : Unit) :
    (generatedGeometricSummaryRange000 token).range.run.positionTrace =
      PositionTrace.consecutive 0 136 := by
  change PositionTrace.append
      (geometricShard000Summary token).range.run.positionTrace
      (generatedGeometricSummaryRange001 token).range.run.positionTrace = _
  rw [geometricShard000_positionTrace,
    generatedGeometricSummaryRange001_positionTrace]
  exact PositionTrace.append_consecutive 0 8 128

theorem generatedGeometricSummaryRange033_positionTrace (token : Unit) :
    (generatedGeometricSummaryRange033 token).range.run.positionTrace =
      PositionTrace.consecutive 264 8 :=
  geometricShard033_positionTrace token

theorem generatedGeometricSummaryRange032_positionTrace (token : Unit) :
    (generatedGeometricSummaryRange032 token).range.run.positionTrace =
      PositionTrace.consecutive 256 16 := by
  change PositionTrace.append
      (geometricShard032Summary token).range.run.positionTrace
      (generatedGeometricSummaryRange033 token).range.run.positionTrace = _
  rw [geometricShard032_positionTrace,
    generatedGeometricSummaryRange033_positionTrace]
  exact PositionTrace.append_consecutive 256 8 8

theorem generatedGeometricSummaryRange031_positionTrace (token : Unit) :
    (generatedGeometricSummaryRange031 token).range.run.positionTrace =
      PositionTrace.consecutive 248 24 := by
  change PositionTrace.append
      (geometricShard031Summary token).range.run.positionTrace
      (generatedGeometricSummaryRange032 token).range.run.positionTrace = _
  rw [geometricShard031_positionTrace,
    generatedGeometricSummaryRange032_positionTrace]
  exact PositionTrace.append_consecutive 248 8 16

theorem generatedGeometricSummaryRange030_positionTrace (token : Unit) :
    (generatedGeometricSummaryRange030 token).range.run.positionTrace =
      PositionTrace.consecutive 240 32 := by
  change PositionTrace.append
      (geometricShard030Summary token).range.run.positionTrace
      (generatedGeometricSummaryRange031 token).range.run.positionTrace = _
  rw [geometricShard030_positionTrace,
    generatedGeometricSummaryRange031_positionTrace]
  exact PositionTrace.append_consecutive 240 8 24

theorem generatedGeometricSummaryRange029_positionTrace (token : Unit) :
    (generatedGeometricSummaryRange029 token).range.run.positionTrace =
      PositionTrace.consecutive 232 40 := by
  change PositionTrace.append
      (geometricShard029Summary token).range.run.positionTrace
      (generatedGeometricSummaryRange030 token).range.run.positionTrace = _
  rw [geometricShard029_positionTrace,
    generatedGeometricSummaryRange030_positionTrace]
  exact PositionTrace.append_consecutive 232 8 32

theorem generatedGeometricSummaryRange028_positionTrace (token : Unit) :
    (generatedGeometricSummaryRange028 token).range.run.positionTrace =
      PositionTrace.consecutive 224 48 := by
  change PositionTrace.append
      (geometricShard028Summary token).range.run.positionTrace
      (generatedGeometricSummaryRange029 token).range.run.positionTrace = _
  rw [geometricShard028_positionTrace,
    generatedGeometricSummaryRange029_positionTrace]
  exact PositionTrace.append_consecutive 224 8 40

theorem generatedGeometricSummaryRange027_positionTrace (token : Unit) :
    (generatedGeometricSummaryRange027 token).range.run.positionTrace =
      PositionTrace.consecutive 216 56 := by
  change PositionTrace.append
      (geometricShard027Summary token).range.run.positionTrace
      (generatedGeometricSummaryRange028 token).range.run.positionTrace = _
  rw [geometricShard027_positionTrace,
    generatedGeometricSummaryRange028_positionTrace]
  exact PositionTrace.append_consecutive 216 8 48

theorem generatedGeometricSummaryRange026_positionTrace (token : Unit) :
    (generatedGeometricSummaryRange026 token).range.run.positionTrace =
      PositionTrace.consecutive 208 64 := by
  change PositionTrace.append
      (geometricShard026Summary token).range.run.positionTrace
      (generatedGeometricSummaryRange027 token).range.run.positionTrace = _
  rw [geometricShard026_positionTrace,
    generatedGeometricSummaryRange027_positionTrace]
  exact PositionTrace.append_consecutive 208 8 56

theorem generatedGeometricSummaryRange025_positionTrace (token : Unit) :
    (generatedGeometricSummaryRange025 token).range.run.positionTrace =
      PositionTrace.consecutive 200 72 := by
  change PositionTrace.append
      (geometricShard025Summary token).range.run.positionTrace
      (generatedGeometricSummaryRange026 token).range.run.positionTrace = _
  rw [geometricShard025_positionTrace,
    generatedGeometricSummaryRange026_positionTrace]
  exact PositionTrace.append_consecutive 200 8 64

theorem generatedGeometricSummaryRange024_positionTrace (token : Unit) :
    (generatedGeometricSummaryRange024 token).range.run.positionTrace =
      PositionTrace.consecutive 192 80 := by
  change PositionTrace.append
      (geometricShard024Summary token).range.run.positionTrace
      (generatedGeometricSummaryRange025 token).range.run.positionTrace = _
  rw [geometricShard024_positionTrace,
    generatedGeometricSummaryRange025_positionTrace]
  exact PositionTrace.append_consecutive 192 8 72

theorem generatedGeometricSummaryRange023_positionTrace (token : Unit) :
    (generatedGeometricSummaryRange023 token).range.run.positionTrace =
      PositionTrace.consecutive 184 88 := by
  change PositionTrace.append
      (geometricShard023Summary token).range.run.positionTrace
      (generatedGeometricSummaryRange024 token).range.run.positionTrace = _
  rw [geometricShard023_positionTrace,
    generatedGeometricSummaryRange024_positionTrace]
  exact PositionTrace.append_consecutive 184 8 80

theorem generatedGeometricSummaryRange022_positionTrace (token : Unit) :
    (generatedGeometricSummaryRange022 token).range.run.positionTrace =
      PositionTrace.consecutive 176 96 := by
  change PositionTrace.append
      (geometricShard022Summary token).range.run.positionTrace
      (generatedGeometricSummaryRange023 token).range.run.positionTrace = _
  rw [geometricShard022_positionTrace,
    generatedGeometricSummaryRange023_positionTrace]
  exact PositionTrace.append_consecutive 176 8 88

theorem generatedGeometricSummaryRange021_positionTrace (token : Unit) :
    (generatedGeometricSummaryRange021 token).range.run.positionTrace =
      PositionTrace.consecutive 168 104 := by
  change PositionTrace.append
      (geometricShard021Summary token).range.run.positionTrace
      (generatedGeometricSummaryRange022 token).range.run.positionTrace = _
  rw [geometricShard021_positionTrace,
    generatedGeometricSummaryRange022_positionTrace]
  exact PositionTrace.append_consecutive 168 8 96

theorem generatedGeometricSummaryRange020_positionTrace (token : Unit) :
    (generatedGeometricSummaryRange020 token).range.run.positionTrace =
      PositionTrace.consecutive 160 112 := by
  change PositionTrace.append
      (geometricShard020Summary token).range.run.positionTrace
      (generatedGeometricSummaryRange021 token).range.run.positionTrace = _
  rw [geometricShard020_positionTrace,
    generatedGeometricSummaryRange021_positionTrace]
  exact PositionTrace.append_consecutive 160 8 104

theorem generatedGeometricSummaryRange019_positionTrace (token : Unit) :
    (generatedGeometricSummaryRange019 token).range.run.positionTrace =
      PositionTrace.consecutive 152 120 := by
  change PositionTrace.append
      (geometricShard019Summary token).range.run.positionTrace
      (generatedGeometricSummaryRange020 token).range.run.positionTrace = _
  rw [geometricShard019_positionTrace,
    generatedGeometricSummaryRange020_positionTrace]
  exact PositionTrace.append_consecutive 152 8 112

theorem generatedGeometricSummaryRange018_positionTrace (token : Unit) :
    (generatedGeometricSummaryRange018 token).range.run.positionTrace =
      PositionTrace.consecutive 144 128 := by
  change PositionTrace.append
      (geometricShard018Summary token).range.run.positionTrace
      (generatedGeometricSummaryRange019 token).range.run.positionTrace = _
  rw [geometricShard018_positionTrace,
    generatedGeometricSummaryRange019_positionTrace]
  exact PositionTrace.append_consecutive 144 8 120

theorem generatedGeometricSummaryRange017_positionTrace (token : Unit) :
    (generatedGeometricSummaryRange017 token).range.run.positionTrace =
      PositionTrace.consecutive 136 136 := by
  change PositionTrace.append
      (geometricShard017Summary token).range.run.positionTrace
      (generatedGeometricSummaryRange018 token).range.run.positionTrace = _
  rw [geometricShard017_positionTrace,
    generatedGeometricSummaryRange018_positionTrace]
  exact PositionTrace.append_consecutive 136 8 128

/-- The retained first B-sheet run is exactly the first canonical mesh row
interval. -/
theorem generatedFirstSheetRange_positionTrace (token : Unit) :
    (generatedFirstSheetRange token).run.positionTrace =
      PositionTrace.consecutive 0 136 :=
  generatedGeometricSummaryRange000_positionTrace token

/-- The retained second B-sheet run is exactly the remaining canonical mesh
row interval. -/
theorem generatedSecondSheetRange_positionTrace (token : Unit) :
    (generatedSecondSheetRange token).run.positionTrace =
      PositionTrace.consecutive 136 136 :=
  generatedGeometricSummaryRange017_positionTrace token

end CCL.Riemann.ExplicitLegendreGeneratedBCertificate
