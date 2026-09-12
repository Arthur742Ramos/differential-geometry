# Maximal forward envelope dichotomy

This is a self-contained Palomar project for the abstract gluing principle used
when constructing maximal forward evolutions.

`ForwardPiece A` consists of a positive finite horizon and an `A`-valued
evolution. If a nonempty family of pieces agrees at every common nonnegative
time, the main theorem constructs one of two envelopes:

- a finite envelope whose endpoint is the least upper bound of the horizons,
  covering every earlier nonnegative time; or
- an immortal envelope when the horizons are unbounded, covering every
  nonnegative time.

In either branch the envelope restricts to every original piece. This is the
order-theoretic core used by the surrounding arbitrary-data maximal Ricci-flow
work. The Palomar statement intentionally does **not** claim the geometric
short-time existence, uniqueness, PDE regularity, continuation, or singularity
theorems from that larger development.

## Repository map

- `Challenge.lean`: auditable statement surface with one deliberate `sorry`.
- `Solution.lean`: the matching proved declaration.
- `PalomarMaximalForward/Envelope.lean`: proof development.
- `comparator.json`: exact declaration and permitted-axiom contract.
- `formalization.yaml`: provenance, scope, automation, and review metadata.
- `scripts/verify.sh`: local package, closure, axiom, and Comparator checks.

## Verification

```bash
./scripts/verify.sh
```

On macOS the Comparator step uses an explicit unsandboxed development fallback;
Palomar's hosted Linux verifier supplies the real Landrun sandbox. A passing
local run does not itself mean the artifact is registered or editorially
approved.

Submit through <https://submit.palomar-registry.org/> using the public repository,
the exact 40-character commit, project directory `palomar/maximal-forward`, and
Comparator path `palomar/maximal-forward/comparator.json`.
