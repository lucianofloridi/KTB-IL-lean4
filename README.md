# KTB-IL: The Logic of Being Informed — Lean 4 Formalisation

Machine-checked proofs for the paper

> **The Logic of Being Informed: KTB as the Modal Logic of the Information Operator**
> Luciano Floridi (Yale University / University of Bologna)

## Overview

KTB-IL is the normal modal logic K extended with axioms **T** (factivity: Iφ → φ)
and **B** (Brouwersche: φ → I¬I¬φ), interpreted with the **information operator I**
("being informed that"). This formalisation covers **29 results** from the paper.

## Build

```bash
lake update
lake build
```

Requires **Lean 4** (v4.29.0-rc4) and **Mathlib**.

## Results

| # | Result | Paper ref. | Status |
|---|--------|-----------|--------|
| 1 | Frame Correspondence (T ↔ refl, B ↔ sym) | Theorem 3.1 | ✅ |
| 2 | Duality (i): p → ◇p | Prop 3.2(i) | ✅ |
| 3 | Duality (ii): ◇□φ → φ | Prop 3.2(ii) | ✅ |
| 4 | Duality (iii): ¬◇φ → ¬φ | Prop 3.2(iii) | ✅ |
| 5 | Independence of axiom 4 | Prop 3.3(a) | ✅ |
| 6 | Independence of axiom B from S4 | Prop 3.3(b) | ✅ |
| 7 | Soundness | Theorem 3.2(i) | ✅ |
| 8 | Completeness (canonical model) | Theorem 3.2(ii) | ⬜ `sorry` |
| 9 | Veridical endowment definition | Def 3.6 | ✅ |
| 10 | Mutual compatibility → refl + sym | Prop 3.4 | ✅ |
| 11 | Intended model is KTB-frame | Corollary 3.1 | ✅ |
| 12 | Characterisation theorem | Theorem 3.3 | ✅ |
| 13 | Representation theorem | Theorem 3.4 | ✅ |
| 14 | One-dir accessibility + stability → S5 | Prop 3.5(a) | ✅ |
| 15 | Non-transitivity of mutual compat | Prop 3.5(b) | ✅ |
| 16 | One-dir + monotone inclusion → S4 | Prop 3.5(c) | ✅ |
| 17 | Inverse monotonicity | Theorem 4.1 | ✅ |
| 18 | Join of endowments | Corollary 4.1 | ✅ |
| 19 | Meet of endowments | Corollary 4.2 | ✅ |
| 20 | Extremal endowments | Prop 4.1 | ✅ |
| 21 | Persistence under enrichment | Prop 4.2 | ✅ |
| 22 | Galois connection (i)–(ii) | Theorem 4.2(i–ii) | ✅ |
| 23 | No self-contradiction | Prop 4.3 | ✅ |
| 24 | Untouchable truths | Prop 4.4 | ✅ |
| 25 | No Fitch collapse (Church-Fitch) | Theorem 4.3 | ✅ |
| 26 | Iterated informability | Prop 4.5 | ✅ |
| 27 | BAM 1: (◇p → q) → (p → q) valid | Theorem 5.1 | ✅ |
| 28 | BAM 1 schema instance | Obs 5.2 | ✅ |
| 29 | Effective fragment witness | Obs 5.3 | ✅ |

**28 / 29** results machine-verified. The single `sorry` is for the completeness
theorem, which requires Lindenbaum's lemma and the deduction theorem — substantial
proof-theoretic infrastructure not yet available in Lean 4/Mathlib for this system.

## Structure

```
KTB-IL-lean4/
├── KTBIL/
│   └── Basic.lean      ← all proofs (single file)
├── Main.lean
├── lakefile.toml
├── lean-toolchain
├── LICENSE              ← MIT
└── README.md
```

## Licence

MIT — see [LICENSE](LICENSE).
