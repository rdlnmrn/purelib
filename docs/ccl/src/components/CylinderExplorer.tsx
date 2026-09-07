import { useMemo, useState } from "react"
import { Coordinates, Mafs, Point, Text, Theme } from "mafs"
import {
  type Block,
  type SectorName,
  decimate,
  examples,
  formatBlock,
  rawBits,
  sampleAllPrefixes,
  sectorOrder,
  sectors,
  viewBoxFor,
} from "../math/ccl"

const plotColors = [Theme.orange, Theme.yellow, Theme.green, Theme.blue, Theme.indigo, Theme.violet]

function cloneBlocks(blocks: Block[]) {
  return blocks.map((block) => ({ ...block }))
}

export default function CylinderExplorer() {
  const [exampleKey, setExampleKey] = useState("threeFour")
  const [blocks, setBlocks] = useState<Block[]>(cloneBlocks(examples.threeFour.blocks))
  const [kind, setKind] = useState<Block["kind"]>("regular")
  const [exponent, setExponent] = useState(0)
  const [sector, setSector] = useState<SectorName>("northEast")
  const [showHistory, setShowHistory] = useState(true)

  const sets = useMemo(() => sampleAllPrefixes(blocks), [blocks])
  const target = exampleKey === "custom" ? undefined : examples[exampleKey]?.target
  const visibleSets = showHistory ? sets : sets.slice(-1)
  const viewBox = useMemo(
    () => viewBoxFor(visibleSets, target?.point),
    [visibleSets, target],
  )
  const currentCount = sets.at(-1)?.length ?? 0

  const chooseExample = (key: string) => {
    const example = examples[key]
    setExampleKey(key)
    setBlocks(cloneBlocks(example.blocks))
  }

  const append = () => {
    if (kind === "low" && blocks.length > 0) return
    setBlocks((current) => [...current, { kind, exponent, sector }])
    setExampleKey("custom")
    if (kind === "low") setKind("regular")
  }

  const undo = () => {
    setBlocks((current) => current.slice(0, -1))
    setExampleKey("custom")
  }

  const boundDenominator = (2n ** BigInt(blocks.length)).toString()

  return (
    <figure className="math-figure cylinder-figure" id="prefix-figure">
      <div className="figure-intro">
        <div>
          <span className="figure-number">Figure 1</span>
          <h3>A sampled CCL cylinder</h3>
        </div>
        <p>
          Each cloud is the affine image of points sampled from the exact annular-sector
          predicates. Pan or zoom the coordinate plane; the controls alter the finite word.
        </p>
      </div>

      <div className="explorer-layout">
        <div className="explorer-controls">
          <label>
            Kernel-checked example
            <select
              id="ccl-example"
              name="ccl-example"
              aria-label="Kernel-checked example"
              value={exampleKey === "custom" ? "custom" : exampleKey}
              onChange={(event) => event.target.value !== "custom" && chooseExample(event.target.value)}
            >
              {Object.entries(examples).map(([key, example]) => (
                <option key={key} value={key}>{example.label}</option>
              ))}
              {exampleKey === "custom" && <option value="custom">Edited word</option>}
            </select>
          </label>

          <div className="control-pair">
            <label>
              Block kind
              <select
                id="ccl-block-kind"
                name="ccl-block-kind"
                aria-label="Block kind"
                value={kind}
                onChange={(event) => setKind(event.target.value as Block["kind"])}
              >
                <option value="regular">regular</option>
                <option value="low" disabled={blocks.length > 0}>initial low</option>
              </select>
            </label>
            <label>
              Unary scale k
              <input
                id="ccl-exponent"
                name="ccl-exponent"
                aria-label="Unary scale k"
                type="number"
                min="0"
                max="12"
                value={exponent}
                onChange={(event) => setExponent(Math.max(0, Math.min(12, Number(event.target.value))))}
              />
            </label>
          </div>

          <fieldset>
            <legend>Sector representative s</legend>
            <div className="sector-buttons">
              {sectorOrder.map((name) => {
                const value = sectors[name]
                return (
                  <button
                    type="button"
                    key={name}
                    aria-pressed={sector === name}
                    onClick={() => setSector(name)}
                  >
                    <span>{value.arrow}</span>
                    <small>{value.short} · {value.code}</small>
                  </button>
                )
              })}
            </div>
          </fieldset>

          <div className="control-actions">
            <button type="button" className="primary-action" onClick={append}>Append block</button>
            <button type="button" onClick={undo} disabled={blocks.length === 0}>Undo</button>
            <button
              type="button"
              onClick={() => { setBlocks([]); setExampleKey("custom"); setKind("low") }}
              disabled={blocks.length === 0}
            >
              Clear
            </button>
          </div>

          <label className="check-control">
            <input
              id="ccl-show-history"
              name="ccl-show-history"
              type="checkbox"
              checked={showHistory}
              onChange={(event) => setShowHistory(event.target.checked)}
            />
            Show earlier prefixes
          </label>
        </div>

        <div className="mafs-frame cylinder-mafs" role="img" aria-label="Plot of sampled compatible CCL cylinder points">
          <Mafs
            key={`${blocks.map(rawBits).join("-")}-${showHistory}`}
            height={480}
            viewBox={{ ...viewBox, padding: 0.08 }}
            pan
            zoom={{ min: 0.35, max: 8 }}
          >
            <Coordinates.Cartesian subdivisions={false} />
            {visibleSets.map((points, visibleIndex) => {
              const actualIndex = showHistory ? visibleIndex : sets.length - 1
              const color = plotColors[actualIndex % plotColors.length]
              const opacity = actualIndex === sets.length - 1 ? 0.72 : 0.19
              return decimate(points).map(([x, y], pointIndex) => (
                <Point
                  key={`${actualIndex}-${pointIndex}`}
                  x={x}
                  y={y}
                  color={color}
                  opacity={opacity}
                  svgCircleProps={{ r: actualIndex === sets.length - 1 ? 2.2 : 1.8 }}
                />
              ))
            })}
            {target && (
              <>
                <Point x={target.point[0]} y={target.point[1]} color={Theme.red} />
                <Text x={target.point[0]} y={target.point[1]} attach="ne" color={Theme.red} size={13}>
                  {target.label}
                </Text>
              </>
            )}
          </Mafs>
        </div>
      </div>

      <div className="word-readout" aria-live="polite">
        <div>
          <span>completed blocks</span>
          <strong>{blocks.length}</strong>
        </div>
        <div className="block-sequence">
          <span>block sequence</span>
          <code>{blocks.length ? blocks.map(formatBlock).join("  ") : "empty"}</code>
        </div>
        <div className="raw-sequence">
          <span>raw binary word</span>
          <code>{blocks.length ? blocks.map(rawBits).join(" ") : "ε"}</code>
        </div>
        <div>
          <span>exact universal squared-chordal width</span>
          <strong>≤ 1 / {boundDenominator}</strong>
        </div>
        <div>
          <span>sampled compatible points</span>
          <strong>{currentCount.toLocaleString()}</strong>
        </div>
      </div>

      <figcaption>
        The dots are a floating-point illustration, not the proof and not an enumeration of
        every compatible value. The bound <code>2<sup>−n</sup></code> after <em>n</em> completed
        blocks is the exact theorem in <a href="../../CCL/Encoding/Cylinder.lean"><code>CCL.Encoding.Cylinder</code></a>.
      </figcaption>
    </figure>
  )
}
