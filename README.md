# RMC constructibility of real cyclic quintics

This project presents an argument for the constructibility of real cyclic quintic extensions using **restricted marked ruler and compass (RMC)**, together with a Lean formalization and exact Python checks. Independent mathematical review is welcome.

## Main theorem

Let K be a subfield of the real numbers and let L/K be a finite Galois extension of degree 5, embedded in the real numbers. Every element of L is RMC-constructible relative to K.

In polynomial terms, this covers irreducible quintics over a real base field whose splitting field has cyclic Galois group of order 5. The permitted constructions and the meaning of constructibility relative to the base field are specified in the manuscript and Lean definitions.

## Construction model

RMC here means ordinary ruler-and-compass operations together with a restricted unit-mark verging operation: a marked ruler passes through a constructed point, with one mark on a constructed line and the other on a constructed circle.

The argument establishes a finite sequence of permitted operations. It does not claim that one verging operation suffices for every cyclic quintic.

## Verification status

- **Lean:** The formal theorem `RMCQuintic.real_galois_quintic_constructible` has been reported to compile. Its printed axiom dependencies are `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` dependency.
- **Python:** Exact rational and polynomial computations check selected identities, reconstruction formulas, interval certificates, and an explicit conductor-25 example. These scripts use Python's standard library.
- **Geometry:** The manuscript and accompanying audit give a written argument connecting the formal construction rules to geometric RMC operations. This bridge is not separately formalized in Lean.
- **External review:** Independent human mathematical review and a complete assessment of novelty remain outstanding. This repository does not claim journal acceptance or established priority.

Lean checks the theorem expressed by the definitions and hypotheses in the source. Reviewing whether those definitions faithfully express the intended geometric problem remains essential. The computational checks supplement the proof; they do not certify every claim in the manuscript.

## AI provenance and human involvement

The proposed argument, Lean code, checking scripts, and manuscript were developed with extensive generative assistance from ChatGPT 5.6 Sol and 6.1 Sol. Substantial mathematical content was AI-generated; the assistance was not limited to editing or formatting.

The project was initiated and shared to make the mathematics available for scrutiny. The uploader's role is project organization and dissemination; uploading the materials should not be interpreted as a claim to have personally devised every argument. No human author is assigned in the accompanying manuscript.

## Materials

The source package contains:

| File | Purpose |
| --- | --- |
| `cyclic-quintic-rmj.tex` | Manuscript source |
| `rmj-public.cls` | Journal formatting class used for the draft |
| `supplementary/CyclicQuinticRMC_SET_FIX_V2.lean` | Complete formal proof |
| `supplementary/geometry-audit.md` | Written geometry audit |
| `supplementary/lakefile.toml` and `supplementary/lean-toolchain` | Pinned Lean and Mathlib configuration |
| `supplementary/*.py` | Exact computational checks |
| `SHA256SUMS.txt` | Checksums for the packaged source files |

The manuscript PDF is supplied separately. The journal-specific filenames and formatting do not imply submission or acceptance.

## Reproduce the Lean check

Install Lean's Elan/Lake tooling. From the extracted source-package root, run:

```sh
cd supplementary
lake update
lake exe cache get
lake env lean CyclicQuinticRMC_SET_FIX_V2.lean
```

The package pins Lean `4.34.0` and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

Expected final dependency output:

```text
'RMCQuintic.real_galois_quintic_constructible' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Reproduce the computational checks

With Python 3, run these commands from `supplementary`:

```sh
python3 audit.py --output certificate.json --expanded expanded-residual.txt
python3 example25.py
python3 geometry_audit_checks.py
python3 recovery25_check.py
```

These commands regenerate some included computational outputs. SageMath is not required for these scripts.

## Feedback

Please open an issue with a precise claim, source location, counterexample, relevant reference, or reproducible error. Review of the construction model, geometric soundness, correspondence between manuscript and formalization, and relationship to earlier work is particularly useful.
