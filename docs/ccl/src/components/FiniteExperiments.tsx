import { type FormEvent, useMemo, useState } from "react"
import { Coordinates, Line, Mafs, Point, Polygon, Text, Theme, useMovablePoint } from "mafs"

function floorDiv(numerator: bigint, denominator: bigint) {
  let quotient = numerator / denominator
  const remainder = numerator % denominator
  if (remainder !== 0n && numerator < 0n) quotient -= 1n
  return quotient
}

function continuedFraction(numerator: bigint, denominator: bigint) {
  if (denominator <= 0n) throw new Error("The denominator must be positive.")
  const digits: bigint[] = []
  let p = numerator
  let q = denominator
  for (let fuel = 0; fuel < 2048; fuel += 1) {
    const digit = floorDiv(p, q)
    digits.push(digit)
    const remainder = p - digit * q
    if (remainder === 0n) return digits
    p = q
    q = remainder
  }
  throw new Error("That input is too large for this small browser demonstration.")
}

function clEncode(numerator: bigint, denominator: bigint) {
  if (denominator <= 0n || numerator < denominator) {
    throw new Error("Use positive integers with numerator at least the denominator.")
  }
  const bits: number[] = []
  let p = numerator
  let q = denominator
  for (let fuel = 0; fuel < 2048 && p !== q; fuel += 1) {
    let exponent = 0
    let normalized = q
    while (2n * normalized <= p) {
      normalized *= 2n
      exponent += 1
    }
    for (let index = 0; index < exponent; index += 1) bits.push(1)
    if (normalized === p) return bits
    bits.push(0)
    const oldP = p
    p = normalized
    q = oldP - normalized
  }
  if (p === q) return bits
  throw new Error("That input is too large for this small browser demonstration.")
}

interface EncodingResult {
  input: string
  output: string[]
  note: string
  error?: string
}

function CFExperiment() {
  const [numerator, setNumerator] = useState("355")
  const [denominator, setDenominator] = useState("113")
  const [result, setResult] = useState<EncodingResult>({
    input: "355/113",
    output: ["3", "7", "16"],
    note: "355/113 = [3; 7, 16] — exact reconstruction",
  })

  const encode = (event: FormEvent) => {
    event.preventDefault()
    try {
      const p = BigInt(numerator)
      const q = BigInt(denominator)
      const digits = continuedFraction(p, q)
      const tail = digits.slice(1).join(", ")
      setResult({
        input: `${p}/${q}`,
        output: digits.map(String),
        note: `${p}/${q} = [${digits[0]}${tail ? `; ${tail}` : ""}] — exact reconstruction`,
      })
    } catch (error) {
      setResult({ input: "", output: [], note: "", error: error instanceof Error ? error.message : String(error) })
    }
  }

  return (
    <div className="algorithm-example">
      <h3>Ordinary continued fractions</h3>
      <p>
        Euclid's algorithm repeatedly keeps the integer part and inverts the remainder.
        On a displayed rational its denominator strictly decreases, so the word is finite
        and its finite matrix product reconstructs the input exactly.
      </p>
      <form onSubmit={encode} className="fraction-form">
        <label>numerator<input id="cf-numerator" name="cf-numerator" aria-label="Continued fraction numerator" value={numerator} onChange={(e) => setNumerator(e.target.value)} inputMode="numeric" /></label>
        <span>/</span>
        <label>denominator<input id="cf-denominator" name="cf-denominator" aria-label="Continued fraction denominator" value={denominator} onChange={(e) => setDenominator(e.target.value)} inputMode="numeric" /></label>
        <button type="submit">Encode</button>
      </form>
      {result.error ? <p className="input-error" role="alert">{result.error}</p> : (
        <div className="algorithm-result" aria-live="polite">
          <div className="digit-row">{result.output.map((digit, index) => <code key={`${digit}-${index}`}>{digit}</code>)}</div>
          <p>{result.note}</p>
        </div>
      )}
      <p className="source-note"><a href="../../CCL/Encoding/Baseline.lean">Lean: <code>cfEncode_reconstruct</code></a></p>
    </div>
  )
}

function CLExperiment() {
  const [numerator, setNumerator] = useState("13")
  const [denominator, setDenominator] = useState("5")
  const initial = clEncode(13n, 5n)
  const [result, setResult] = useState<EncodingResult>({
    input: "13/5",
    output: initial.map(String),
    note: `13/5 ↦ ${initial.join("") || "ε"} — a finite binary word`,
  })

  const encode = (event: FormEvent) => {
    event.preventDefault()
    try {
      const p = BigInt(numerator)
      const q = BigInt(denominator)
      const bits = clEncode(p, q)
      setResult({
        input: `${p}/${q}`,
        output: bits.map(String),
        note: `${p}/${q} ↦ ${bits.join("") || "ε"} — a finite binary word`,
      })
    } catch (error) {
      setResult({ input: "", output: [], note: "", error: error instanceof Error ? error.message : String(error) })
    }
  }

  return (
    <div className="algorithm-example">
      <h3>Continued logarithms</h3>
      <p>
        For positive rationals at least one, continued logarithms replace arbitrary
        integer digits by unary powers of two and a reciprocal branch. The scale scan
        and recursion are bounded by displayed natural numbers.
      </p>
      <form onSubmit={encode} className="fraction-form">
        <label>numerator<input id="cl-numerator" name="cl-numerator" aria-label="Continued logarithm numerator" value={numerator} onChange={(e) => setNumerator(e.target.value)} inputMode="numeric" /></label>
        <span>/</span>
        <label>denominator<input id="cl-denominator" name="cl-denominator" aria-label="Continued logarithm denominator" value={denominator} onChange={(e) => setDenominator(e.target.value)} inputMode="numeric" /></label>
        <button type="submit">Encode</button>
      </form>
      {result.error ? <p className="input-error" role="alert">{result.error}</p> : (
        <div className="algorithm-result" aria-live="polite">
          <div className="digit-row bits">{result.output.map((digit, index) => <code key={`${digit}-${index}`}>{digit}</code>)}</div>
          <p>{result.note}</p>
        </div>
      )}
      <p className="source-note"><a href="../../CCL/Encoding/Baseline.lean">Lean: <code>clEncode_reconstruct</code></a></p>
    </div>
  )
}

function CCFMap() {
  const movable = useMovablePoint([0.63, 0.36], {
    color: Theme.orange,
    constrain: ([x, y]) => [Math.max(0.035, Math.min(0.965, x)), Math.max(0.035, Math.min(0.965, y))],
  })
  const step = useMemo(() => {
    const [x, y] = movable.point
    const norm = x * x + y * y
    const quotient: [number, number] = [(x + y) / norm, (x - y) / norm]
    const digit: [number, number] = [Math.floor(quotient[0]), Math.floor(quotient[1])]
    const residual: [number, number] = [quotient[0] - digit[0], quotient[1] - digit[1]]
    return { quotient, digit, residual }
  }, [movable.point])

  return (
    <figure className="math-figure ccf-figure">
      <div className="figure-intro">
        <div><span className="figure-number">Figure 2</span><h3>One coordinate-floor return step</h3></div>
        <p>Drag the orange point <em>u</em>. The green point is the residual after computing γ/u and removing its coordinatewise Gaussian-integer floor.</p>
      </div>
      <div className="mafs-frame" role="img" aria-label="Interactive coordinate-floor map on the unit square">
        <Mafs height={410} viewBox={{ x: [-0.12, 1.12], y: [-0.12, 1.12] }} preserveAspectRatio="contain">
          <Coordinates.Cartesian xAxis={{ lines: 0.25 }} yAxis={{ lines: 0.25 }} />
          <Polygon points={[[0, 0], [1, 0], [1, 1], [0, 1]]} color={Theme.blue} fillOpacity={0.035} weight={1.5} />
          <Line.Segment point1={movable.point} point2={step.residual} color={Theme.green} weight={2} />
          {movable.element}
          <Point x={step.residual[0]} y={step.residual[1]} color={Theme.green} />
          <Text x={movable.x} y={movable.y} attach="sw" color={Theme.orange}>u</Text>
          <Text x={step.residual[0]} y={step.residual[1]} attach="ne" color={Theme.green}>F(u)</Text>
        </Mafs>
      </div>
      <p className="map-readout" aria-live="polite">
        <code>u = {movable.x.toFixed(3)} + {movable.y.toFixed(3)}i</code>
        <code>⌊γ/u⌋ = {step.digit[0]} {step.digit[1] < 0 ? "−" : "+"} {Math.abs(step.digit[1])}i</code>
        <code>F(u) = {step.residual[0].toFixed(3)} + {step.residual[1].toFixed(3)}i</code>
      </p>
      <div className="point-presets" aria-label="Example points for the coordinate-floor map">
        <span>Try u =</span>
        <button type="button" onClick={() => movable.setPoint([0.25, 0.75])}>¼ + ¾i</button>
        <button type="button" onClick={() => movable.setPoint([0.5, 0.5])}>½ + ½i</button>
        <button type="button" onClick={() => movable.setPoint([0.8, 0.2])}>⅘ + ⅕i</button>
      </div>
      <figcaption>
        This picture uses decimal plotting. The encoder in <a href="../../CCL/Encoding/CCF/CoordinateFloor.lean"><code>CCL.Encoding.CCF.CoordinateFloor</code></a> uses exact fractions and a finite denominator-norm descent.
      </figcaption>
    </figure>
  )
}

export function EncodingFamily() {
  return (
    <>
      <div className="algorithm-grid">
        <CFExperiment />
        <CLExperiment />
      </div>
      <CCFMap />
    </>
  )
}

export function PrecisionFigure() {
  const [decimalPlaces, setDecimalPlaces] = useState(3)
  const targetDenominator = 10 ** decimalPlaces
  let blocks = 0
  let powerOfTwo = 1
  while (powerOfTwo <= targetDenominator) {
    powerOfTwo *= 2
    blocks += 1
  }

  const rows = Array.from({ length: Math.min(blocks, 14) }, (_, index) => {
    const level = index + 1
    return { level, radius: 2 ** (-level / 2) }
  })

  return (
    <figure className="math-figure precision-figure">
      <div className="figure-intro">
        <div><span className="figure-number">Figure 3</span><h3>A finite precision request</h3></div>
        <p>The slider asks for ε = 1/10<sup>d</sup>. The calculation finds a finite n for which 2<sup>−n</sup> &lt; ε.</p>
      </div>
      <label className="range-control">
        Decimal places <output>{decimalPlaces}</output>
        <input id="precision-places" name="precision-places" aria-label="Requested decimal places" type="range" min="1" max="12" value={decimalPlaces} onChange={(event) => setDecimalPlaces(Number(event.target.value))} />
      </label>
      <div className="precision-layout">
        <div className="mafs-frame contraction-mafs" role="img" aria-label="Nested projective spread bounds">
          <Mafs height={300} viewBox={{ x: [-1.15, 1.15], y: [0, Math.min(blocks, 14) + 1] }} pan={false} zoom={false}>
            <Coordinates.Cartesian xAxis={false} yAxis={false} />
            {rows.map(({ level, radius }) => (
              <Line.Segment key={level} point1={[-radius, level]} point2={[radius, level]} color={level === rows.length ? Theme.orange : Theme.blue} weight={level === rows.length ? 5 : 2.5} opacity={0.9} />
            ))}
          </Mafs>
        </div>
        <div className="precision-result">
          <strong>{blocks}</strong>
          <span>completed blocks suffice</span>
          <code>2<sup>−{blocks}</sup> = 1 / {powerOfTwo.toLocaleString()}</code>
          <code>&lt; 1 / {targetDenominator.toLocaleString()}</code>
        </div>
      </div>
      <figcaption>
        The drawn segment has ordinary visual width proportional to √(2<sup>−n</sup>), while the formal guarantee is squared chordal separation. Converting to an affine box carries an explicit chart factor.
      </figcaption>
    </figure>
  )
}
