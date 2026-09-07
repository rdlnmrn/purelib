export type Vector = [number, number]

export type SectorName =
  | "east"
  | "northEast"
  | "north"
  | "northWest"
  | "west"
  | "southWest"
  | "south"
  | "southEast"

export interface Sector {
  name: SectorName
  short: string
  code: string
  arrow: string
  rep: Vector
}

export interface Block {
  kind: "regular" | "low"
  exponent: number
  sector: SectorName
}

export interface CheckedExample {
  label: string
  target?: { point: Vector; label: string }
  blocks: Block[]
}

export const sectors: Record<SectorName, Sector> = {
  east: { name: "east", short: "E", code: "000", arrow: "→", rep: [1, 0] },
  northEast: { name: "northEast", short: "NE", code: "001", arrow: "↗", rep: [1, 1] },
  north: { name: "north", short: "N", code: "010", arrow: "↑", rep: [0, 1] },
  northWest: { name: "northWest", short: "NW", code: "011", arrow: "↖", rep: [-1, 1] },
  west: { name: "west", short: "W", code: "100", arrow: "←", rep: [-1, 0] },
  southWest: { name: "southWest", short: "SW", code: "101", arrow: "↙", rep: [-1, -1] },
  south: { name: "south", short: "S", code: "110", arrow: "↓", rep: [0, -1] },
  southEast: { name: "southEast", short: "SE", code: "111", arrow: "↘", rep: [1, -1] },
}

export const sectorOrder: SectorName[] = [
  "northWest", "north", "northEast", "west", "east", "southWest", "south", "southEast",
]

export const examples: Record<string, CheckedExample> = {
  blank: {
    label: "One north-east block",
    blocks: [{ kind: "regular", exponent: 0, sector: "northEast" }],
  },
  threeFour: {
    label: "3/5 + 4/5 i",
    target: { point: [3 / 5, 4 / 5], label: "3/5 + 4/5 i" },
    blocks: [
      { kind: "low", exponent: 0, sector: "northEast" },
      { kind: "regular", exponent: 1, sector: "northEast" },
      { kind: "regular", exponent: 0, sector: "northWest" },
    ],
  },
  thirteenFive: {
    label: "13/5",
    target: { point: [13 / 5, 0], label: "13/5" },
    blocks: [
      { kind: "regular", exponent: 2, sector: "south" },
      { kind: "regular", exponent: 2, sector: "southEast" },
      { kind: "regular", exponent: 3, sector: "northEast" },
      { kind: "regular", exponent: 1, sector: "northEast" },
    ],
  },
  piRational: {
    label: "355/113",
    target: { point: [355 / 113, 0], label: "355/113" },
    blocks: [
      { kind: "regular", exponent: 3, sector: "southWest" },
      { kind: "regular", exponent: 2, sector: "west" },
      { kind: "regular", exponent: 4, sector: "southEast" },
      { kind: "regular", exponent: 2, sector: "north" },
      { kind: "regular", exponent: 8, sector: "southWest" },
      { kind: "regular", exponent: 7, sector: "southEast" },
    ],
  },
}

function add([ax, ay]: Vector, [bx, by]: Vector): Vector {
  return [ax + bx, ay + by]
}

function multiply([ax, ay]: Vector, [bx, by]: Vector): Vector {
  return [ax * bx - ay * by, ax * by + ay * bx]
}

function inverse([x, y]: Vector): Vector | undefined {
  const denominator = x * x + y * y
  if (denominator < 1e-18) return undefined
  return [x / denominator, -y / denominator]
}

function power(exponent: number): Vector {
  if (exponent < 0) return inverse(power(-exponent)) ?? [0, 0]
  let result: Vector = [1, 0]
  let factor: Vector = [1, 1]
  let remaining = exponent
  while (remaining > 0) {
    if (remaining % 2 === 1) result = multiply(result, factor)
    factor = multiply(factor, factor)
    remaining = Math.floor(remaining / 2)
  }
  return result
}

function normSq([x, y]: Vector): number {
  return x * x + y * y
}

function sectorHolds(name: SectorName, [x, y]: Vector): boolean {
  switch (name) {
    case "east": return x >= 0.5 && y > -0.5 && y < 0.5
    case "northEast": return x >= 0.5 && y >= 0.5
    case "north": return x > -0.5 && x < 0.5 && y >= 0.5
    case "northWest": return x <= -0.5 && y >= 0.5
    case "west": return x <= -0.5 && y > -0.5 && y < 0.5
    case "southWest": return x <= -0.5 && y <= -0.5
    case "south": return x > -0.5 && x < 0.5 && y <= -0.5
    case "southEast": return x >= 0.5 && y <= -0.5
  }
}

function inBand(point: Vector): boolean {
  const length = normSq(point)
  return length >= 1 - 1e-10 && length <= 2 + 1e-10
}

function blockScale(block: Block): Vector {
  return power(block.kind === "low" ? -block.exponent : block.exponent)
}

function applyBlock(block: Block, tail: Vector): Vector | undefined {
  const reciprocal = inverse(multiply([1, 1], tail))
  if (!reciprocal) return undefined
  const normalized = add(sectors[block.sector].rep, reciprocal)
  if (!inBand(normalized) || !sectorHolds(block.sector, normalized)) return undefined
  const output = multiply(blockScale(block), normalized)
  if (!Number.isFinite(output[0]) || !Number.isFinite(output[1])) return undefined
  if (Math.abs(output[0]) >= 1e7 || Math.abs(output[1]) >= 1e7) return undefined
  return output
}

function initialSectorSamples(sector: SectorName): Vector[] {
  const points: Vector[] = []
  const divisions = 90
  const low = -Math.SQRT2
  const span = 2 * Math.SQRT2
  for (let row = 0; row <= divisions; row += 1) {
    const y = low + span * row / divisions
    for (let column = 0; column <= divisions; column += 1) {
      const x = low + span * column / divisions
      const point: Vector = [x, y]
      if (inBand(point) && sectorHolds(sector, point)) points.push(point)
    }
  }
  return points
}

export function samplePrefix(prefix: Block[]): Vector[] {
  if (prefix.length === 0) return []
  const lastIndex = prefix.length - 1
  const last = prefix[lastIndex]
  let points = initialSectorSamples(last.sector).map((point) => multiply(blockScale(last), point))
  for (let index = lastIndex - 1; index >= 0; index -= 1) {
    points = points.flatMap((tail) => {
      const output = applyBlock(prefix[index], tail)
      return output ? [output] : []
    })
  }
  return points
}

export function sampleAllPrefixes(blocks: Block[]): Vector[][] {
  return blocks.map((_, index) => samplePrefix(blocks.slice(0, index + 1)))
}

export function decimate(points: Vector[], limit = 260): Vector[] {
  if (points.length <= limit) return points
  const stride = points.length / limit
  return Array.from({ length: limit }, (_, index) => points[Math.floor(index * stride)])
}

export function viewBoxFor(sets: Vector[][], target?: Vector) {
  const points = sets.flat()
  if (target) points.push(target)
  if (points.length === 0) return { x: [-1.8, 1.8] as Vector, y: [-1.8, 1.8] as Vector }
  const xs = points.map(([x]) => x).sort((a, b) => a - b)
  const ys = points.map(([, y]) => y).sort((a, b) => a - b)
  const quantile = (values: number[], fraction: number) =>
    values[Math.min(values.length - 1, Math.floor(fraction * values.length))]
  const minX = quantile(xs, 0.006)
  const maxX = quantile(xs, 0.994)
  const minY = quantile(ys, 0.006)
  const maxY = quantile(ys, 0.994)
  const centerX = (minX + maxX) / 2
  const centerY = (minY + maxY) / 2
  const span = Math.max(maxX - minX, maxY - minY, 0.7) * 1.3
  return {
    x: [centerX - span / 2, centerX + span / 2] as Vector,
    y: [centerY - span / 2, centerY + span / 2] as Vector,
  }
}

export function rawBits(block: Block): string {
  const regular = "1".repeat(block.exponent) + "0" + sectors[block.sector].code
  return block.kind === "low" ? `0${regular}` : regular
}

export function formatBlock(block: Block): string {
  const core = `[${block.exponent}, ${sectors[block.sector].short}]`
  return block.kind === "low" ? `0${core}` : core
}
