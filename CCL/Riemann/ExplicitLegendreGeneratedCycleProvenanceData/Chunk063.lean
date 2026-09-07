import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk063

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard063_positionTrace (token : Unit) :
    (geometricShard063Summary token).range.run.positionTrace =
      PositionTrace.consecutive 1008 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
