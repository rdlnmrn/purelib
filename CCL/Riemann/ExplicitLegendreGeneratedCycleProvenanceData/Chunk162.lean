import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk162

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard162_positionTrace (token : Unit) :
    (geometricShard162Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2592 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
