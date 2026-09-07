import CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk187

/-!
Shard-local row-order provenance for generated Legendre A-period geometry.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedCycleProvenance

theorem geometricShard187_positionTrace (token : Unit) :
    (geometricShard187Summary token).range.run.positionTrace =
      PositionTrace.consecutive 2992 16 := by
  cases token
  decide +revert

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
