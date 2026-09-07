import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk047

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard047_positionTrace (token : Unit) :
    (geometricShard047Summary token).range.run.positionTrace =
      PositionTrace.consecutive 752 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
