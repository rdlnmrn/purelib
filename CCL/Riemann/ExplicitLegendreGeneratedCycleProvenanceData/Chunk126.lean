import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk126

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard126_positionTrace (token : Unit) :
    (geometricShard126Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2016 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
