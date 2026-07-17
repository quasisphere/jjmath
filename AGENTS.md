# Agent Instructions

## Proof Strategy

- Prefer the hardest next step that is likely to fail, where hidden issues will surface, over safe incremental wins.

## Lean

- When creating formalization outlines, make definitions match the standard mathematical objects as directly as possible. Use explicit Lean theorem stubs with `sorry` for unproved analytic or geometric facts instead of hiding missing work inside conditional theorem packages, underspecified assumptions, or placeholder structures.
- Do not introduce Lean `axiom` declarations for unfinished work; use theorem stubs with `by sorry` instead.

## Handwave

- In `%%handwave` docstring description fields, write mathematical prose rather than Lean-facing prose. Do not use Lean identifiers in visible description text unless the identifier is used as the URL target of a link.
- Handwave Markdown articles should likewise avoid Lean identifiers in visible prose. Lean identifiers are allowed in link URLs and `@include{lean:...}` targets.
- Keep theorem links in Handwave statements and proofs on one physical line; do not break the Markdown link text, destination, or surrounding sentence across separate source lines.
- In Handwave proof descriptions, use theorem links when they clarify dependencies. Unless the dependency is a famous named theorem, make the linked text the theorem's mathematical statement or conclusion rather than inventing labels such as "the regular-point theorem".
- Do not change existing milestone tags in the Handwave metadata of theorems unless explicitly asked. Do not add milestone tags automatically to new theorems.
- In `%%handwave` metadata for theorem declarations, make the statement precise enough to identify the quantified objects and the main formula being proved. Keep proof sketches short and make them conform to the actual formal proof: if the proof primarily applies another formal theorem, link to the mathematical conclusion of that theorem using a `lean:` URL.
- In `%%handwave` metadata statements and proofs, use mathematical notation, symbols and formulas. Make things precise and name them.
