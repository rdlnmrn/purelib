#!/usr/bin/env bash

set -euo pipefail

lake_bin="${LAKE_BIN:-lake}"
batch_size="${LEGENDRE_SHARD_JOBS:-1}"
shopt -s nullglob
shard_files=(CCL/Riemann/ExplicitLegendreGeneratedCertificateData/Chunk*.lean)
segment_files=(CCL/Riemann/ExplicitLegendreGeneratedSegmentCertificateData/Chunk*.lean)
geometry_files=(CCL/Riemann/ExplicitLegendreGeneratedGeometryCertificateData/Chunk*.lean)
shard_count="${#shard_files[@]}"
segment_count="${#segment_files[@]}"
geometry_count="${#geometry_files[@]}"

if [[ ! "$batch_size" =~ ^[1-9][0-9]*$ ]]; then
  echo "LEGENDRE_SHARD_JOBS must be a positive integer" >&2
  exit 2
fi

if ((shard_count == 0)); then
  echo "no generated Legendre certificate shards found" >&2
  exit 2
fi

if ((geometry_count == 0)); then
  echo "no generated Legendre geometry shards found" >&2
  exit 2
fi

if ((segment_count == 0)); then
  echo "no generated Legendre segment shards found" >&2
  exit 2
fi

for ((start = 0; start < shard_count; start += batch_size)); do
  targets=()
  for ((offset = 0; offset < batch_size && start + offset < shard_count; offset++)); do
    printf -v suffix '%03d' "$((start + offset))"
    targets+=("CCL.Riemann.ExplicitLegendreGeneratedCertificateData.Chunk${suffix}")
  done
  "$lake_bin" build "${targets[@]}" --wfail
done

for ((start = 0; start < segment_count; start += batch_size)); do
  targets=()
  for ((offset = 0; offset < batch_size && start + offset < segment_count; offset++)); do
    printf -v suffix '%03d' "$((start + offset))"
    targets+=("CCL.Riemann.ExplicitLegendreGeneratedSegmentCertificateData.Chunk${suffix}")
  done
  "$lake_bin" build "${targets[@]}" --wfail
done

for ((start = 0; start < geometry_count; start += batch_size)); do
  targets=()
  for ((offset = 0; offset < batch_size && start + offset < geometry_count; offset++)); do
    printf -v suffix '%03d' "$((start + offset))"
    targets+=("CCL.Riemann.ExplicitLegendreGeneratedGeometryCertificateData.Chunk${suffix}")
  done
  "$lake_bin" build "${targets[@]}" --wfail
done
