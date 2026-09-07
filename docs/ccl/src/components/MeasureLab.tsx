import { useState } from "react"

interface Fraction {
  numerator: bigint
  denominator: bigint
}

const abs = (value: bigint) => value < 0n ? -value : value

function gcd(left: bigint, right: bigint) {
  let a = abs(left)
  let b = abs(right)
  while (b !== 0n) [a, b] = [b, a % b]
  return a || 1n
}

function fraction(numerator: bigint, denominator = 1n): Fraction {
  let n = numerator
  let d = denominator
  if (d < 0n) { n = -n; d = -d }
  const common = gcd(n, d)
  return { numerator: n / common, denominator: d / common }
}

function add(left: Fraction, right: Fraction) {
  return fraction(
    left.numerator * right.denominator + right.numerator * left.denominator,
    left.denominator * right.denominator,
  )
}

function multiply(left: Fraction, right: Fraction) {
  return fraction(left.numerator * right.numerator, left.denominator * right.denominator)
}

function divide(left: Fraction, right: Fraction) {
  return right.numerator === 0n
    ? undefined
    : fraction(left.numerator * right.denominator, left.denominator * right.numerator)
}

function display(value: Fraction | undefined) {
  if (!value) return "undefined"
  return value.denominator === 1n
    ? value.numerator.toString()
    : `${value.numerator} / ${value.denominator}`
}

const atoms = [
  { name: "a", value: 0n, weight: fraction(1n, 8n) },
  { name: "b", value: 4n, weight: fraction(1n, 8n) },
  { name: "c", value: 2n, weight: fraction(1n, 4n) },
  { name: "d", value: 3n, weight: fraction(1n, 2n) },
]

export default function MeasureLab() {
  const [selected, setSelected] = useState([false, false, true, true])

  let probability = fraction(0n)
  let expectation = fraction(0n)
  let eventIntegral = fraction(0n)
  atoms.forEach((atom, index) => {
    const weighted = multiply(atom.weight, fraction(atom.value))
    expectation = add(expectation, weighted)
    if (selected[index]) {
      probability = add(probability, atom.weight)
      eventIntegral = add(eventIntegral, weighted)
    }
  })
  const conditional = divide(eventIntegral, probability)

  return (
    <figure className="math-figure measure-figure">
      <div className="figure-intro">
        <div><span className="figure-number">Figure 4</span><h3>A four-atom rational law</h3></div>
        <p>Select atoms to make an event. Its probability and conditional expectation are recomputed as reduced exact fractions.</p>
      </div>
      <div className="atom-grid">
        {atoms.map((atom, index) => (
          <button
            type="button"
            key={atom.name}
            className={selected[index] ? "selected" : ""}
            aria-pressed={selected[index]}
            onClick={() => setSelected((current) => current.map((value, position) => position === index ? !value : value))}
          >
            <span className="atom-bar" style={{ height: `${Number(atom.weight.numerator * 100n / atom.weight.denominator)}%` }} />
            <small>atom {atom.name}</small>
            <strong>{atom.value.toString()}</strong>
            <span>weight {display(atom.weight)}</span>
          </button>
        ))}
      </div>
      <div className="measure-results" aria-live="polite">
        <p><span>P(event)</span><strong>{display(probability)}</strong></p>
        <p><span>E[value]</span><strong>{display(expectation)}</strong></p>
        <p><span>E[value | event]</span><strong>{display(conditional)}</strong></p>
        <button type="button" onClick={() => setSelected([false, false, true, true])}>Reset event</button>
      </div>
      <figcaption>
        No approximation is involved in this laboratory: the arithmetic is over JavaScript
        <code> bigint</code>s. The formal library uses explicit finite rational tables.
      </figcaption>
    </figure>
  )
}
