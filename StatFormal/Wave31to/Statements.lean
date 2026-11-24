import StatFormal.Wave31tl.Statements
import StatFormal.Wave30tu.Full.Statements
import StatFormal.Archive.Wave8a.Statements
import Mathlib.MeasureTheory.Measure.Support

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 31to: trimmed-mmd, **Annals of Statistics version, revision of 2026-11-21**: the general (kernel-free) results of §5.2–§5.3 and of the supplement: `lem:newtrimmean`, `prop:newapproxgen`, `prop:newapprox`, `prop:newslopegeneral`, `prop:newslope` (first two sentences), `prop:newrates` (i)–(ii), `prop:newconverse`

Scope (author decision, 2026-11-21): a light wave of the general results useful to others reusing the library. The Fourier-analytic
results of the same sections (`prop:newsobolev`, `prop:newgauss`, `prop:newrates` (iii), `prop:newgammaone`, `lem:newsobnorm`,
`thm:newsobolev`, `cor:newsobolev`, `lem:newgaussstep`, `thm:newgauss`, `prop:newupperone`, `prop:newmoments`) and the last sentence of
`prop:newslope` are not formalized in this wave (hand-checked by an independent referee and numerically).

Source: `~/projects/tmmd-aos-brief/NEW_STATEMENTS.md` at freeze: whole file sha256
`a746b3c27cbba633d6cfa9bed05078b026f5abd171dc9d55bc521d80e6df8ae9` (402 lines); the Wave31to block (from the line "# Wave31to — …",
line 207, to the end) sha256 `843849754ffc6b1c6fc8e39f8fcdda54ca5074cb8b8afba67baee11017a4c8db` (S8–S15); lines 1–205 sha256
`18f9fd214bc8366173ac9b3f41eda7e78d4fa2360f2e991728717b28b25dddac`, unchanged by this wave. Chain to Wave31tn: trimmed-mmd commit
`84e9c60`, `aos/NEW_STATEMENTS.md` (150 lines), reproduces the Wave31tn hashes `467357fe…` (whole file) and `23660a33…` (lines 1–120);
the present lines 1–205 differ from it only at line 45 (S2 header location note) and by the appended Lean-status section (lines
151–205); no frozen statement text changed. ("Lemma S4.7" in that header is the numbering of 2026-11-20; in the revision of 2026-11-21
`lem:twopointmargin` is Lemma S4.19 and Proposition S4.7 is `prop:newslopegeneral`.) A copy of the frozen file is committed with this
freeze as `certify/sources/tmmd-aos-NEW_STATEMENTS-wave31to.md`.

Printed source: local copies in `~/projects/tmmd-aos-brief/wave31to/` (read 2026-11-21), sha256: `05_rates.tex`
`03a3e25d440db4f9a0a1fbc044a4b911cf417903285caabf8aded3cf1c8d6a74`, `S4_rates.tex`
`3e78db18a288368bed986348d4fcf9eea8aee23ab4614fa72c54a38dbb6102c8`, `02_regions.tex`
`471c47e768a8038661eea91250915b984342f9d2e27de82464ab8f13bec44ee7`, `S1_regions.tex`
`d85c328a09d970eebe490abff0b087abb53f15f4d3f119d7f22dce146ae785e7`, `S5_trimming.tex`
`6235009c3762bcc1703b26f0f5c23c84f45f98ef17854bf199b881f912ca854a`, `main.pdf`
`ed07e8f42e6335ad5bba420451d9666e96531c40cdfc03022341fc45f5cc0237`, `supplement.pdf`
`7e7bdbb7214360a8efcd0f24f84dd4c19c43f12c9688fe79aacaab53d13607e6`. Printed numbers: Lemma 2.3 `lem:attainment`, Proposition 5.3
`prop:newslope`, Proposition 5.4 `prop:newapprox`, Theorem 5.7 `thm:rate`, Proposition 5.9 `prop:newrates`, Lemma S4.3 `lem:pathconvex`,
Theorem S4.6 `thm:lorate`, Proposition S4.7 `prop:newslopegeneral`, Lemma S4.9 `lem:newtrimmean`, Proposition S4.10 `prop:newapproxgen`,
Proposition S4.18 `prop:newconverse`, Lemma S5.6 `lem:contact`. The live AoS source of 10:15 differs from these copies by notation only
within the scope (`ξ_ℋ` printed `ω_ℋ`, mesh `h → Δ_𝒢`, smallest gap `h₀ → Δ_min`, slope `s → 𝔰`, `1/n+1/m → 1/n_⋆`, `Z → Γ`); no
statement of S8–S15 changed.

Printed locations (copies): `lem:newtrimmean` `S4_rates.tex:525-532`; `prop:newapproxgen` `:549-561` (notation `:539-547`);
`prop:newapprox` `05_rates.tex:94-103` (err `:88-92`, the balanced error `S4_rates.tex:589-593`); `prop:newslopegeneral`
`S4_rates.tex:453-457` (setting `:427-431`, `:449-451`); `prop:newslope` `05_rates.tex:66-77` (the limit exists: `:79`); `prop:newrates`
`05_rates.tex:200-212` (proofs `S4_rates.tex:599-634`); `prop:newconverse` `S4_rates.tex:951-961`.

Reuses (imported, not copied): `TrimmedMMD.Unconditional.Dpop`/`Demp`, `TrimmedMMD.alphaHat`, `Wave8a.trimSet`, `Distances.tvDist`,
`Wave31ti.uPath`, `Wave31ti.PolyMargin`, `Wave30tu.ValidThreshold`, `Wave30tu.LowerTool`, `Wave30tu.Full.tauFull`, `Wave30tr.tauA`,
`Wave30tp.sampleLaw`, `Wave30tq.beta`, the run objects of `Wave30tz` (`LoRun`, `IsWitnessRun`, `alphaLo`, `IsGrid`, `fitCard`) and of
`Wave31tl` (`Tfit`, `Tbet`, `tNM`, `Jeps`, `GapsGe`, `MeshBelowLe`, `gridFloor`, `rOne`), Mathlib `Measure.support`.

Encodings:
* (A1)–(A2): `H` a real complete separable inner-product space, `φ : 𝒳 → H` strongly measurable with `‖φ x‖ ≤ κ` (the canonical
  feature map is one instance). (A3) is assumed nowhere: where the printed result states Assumption 1 in full (`prop:newrates`), dropping
  it is a declared generalisation, with the one added guard `0 < κ` in `newrates_ii_a` (implied by the printed (A3) when `α⋆ > 0`: then
  `μ_P ≠ μ_Q`, so `φ ≢ 0`; without any guard the (A3)-free form fails at `φ ≡ 0`).
* `α⋆ = tvDist P Q`; `D_α = Dpop` (= the printed infimum over trimmings by the certified `Wave8a.georep_dist`); `u(α) = uPath`;
  `R = P∧Q` is Mathlib's `P ⊓ Q`; `P₀ = (P − R)/α⋆` enters only through `P − P ⊓ Q` (a positive multiple: same support, same null sets).
* "`f ∈ ℋ`": an element `g : H`, the function `wit φ g x = ⟪g, φ x⟫`, `‖f‖_ℋ := ‖g‖`, "`f ≠ 0`" is `g ≠ 0` (as in Waves 31tb/31tn);
  exact on the canonical feature map; for a general `φ` the sup/inf over `g` of `ξ_ℋ`, `𝒦`, `𝒩` are the printed ones for the RKHS of
  `k_φ(x,y) = ⟪φ x, φ y⟫` (the least `‖g‖` representing a function is attained by projection onto the closed span; `g ≠ 0` with
  `wit φ g ≡ 0` contributes `0` to `ξ_ℋ`).
* `err(f) = ∫|1_A − f| d|P−Q|` is `errFn`: `p = (dP/d(P+Q)).toReal`, `q = (dQ/d(P+Q)).toReal`, `A = {q < p}` (`setA`),
  `|P − Q| = |p − q|·(P+Q)`.
* `osc f = sup f − inf f` (`oscFn`, `iSup`/`iInf` over `𝒳` of a bounded function); `𝓕` is `Fset φ` (pointwise `[0,1]`-valued);
  `ξ_ℋ` is `xiH` (a real `sSup`, `sup ∅ = 0`); `𝒦` is `Kfun` (a real `sInf`); `𝒩` is `Nfun`, valued in `ℝ≥0∞` (`inf ∅ = ∞`; the printed
  "read as 0 when `𝒩(ε/2) = ∞`" is `ε/(2·⊤) = 0`).
* `ω^←(t) = sup{ε ∈ [0,α⋆] : ω(ε) ≤ t}` is `genInv ω α⋆ t` (`Wave30tl.omegaGen` uses `[0,1]` and is not reused). `ω : [0,α⋆] → [0,∞)`
  nondecreasing: `ω : ℝ → ℝ` with `MonotoneOn ω (Icc 0 α⋆)` and `0 ≤ ω` on `Icc 0 α⋆`; nothing is assumed off `[0,α⋆]`.
* Supports: in `newslopegeneral` the support of the Borel image law `φ_#P₀` on the separable `H` is `InSuppImg φ (P − P ⊓ Q)` (every open
  ball about the point has preimage of positive mass; no `Measure.map`); in `newslope_*` the support of `P₀` on the topological `𝒳` is
  `(P − P ⊓ Q).support` (Mathlib). "The limit" of `u(α⋆−ε)/ε` as `ε ↓ 0`: every `s` it tends to (it exists by the certified
  `Wave31ti.pathconvex_ii`).
* `prop:newrates` (i): `newrates_i` for any valid threshold `τ` at level `δ` and any lower two-sided tool `τ^A` at level `δ′` (as the
  certified `Wave30tu.rate`, `Wave31ti.rate_v3`), `t = τ(α⋆) + τ^A(α⋆)`; `newrates_i_full` at the paper's thresholds `τ_{n,m}(·,δ)`
  (`tauFull`) and `τ^A_{n,m}(·,δ′)` (`tauA`), `Δ_φ` any bound `D`. The remark `S4_rates.tex:612-613` (`τ = τ^A(·,δ)`) is `newrates_i` at a
  threshold made valid by the certified `Wave30tu.upper_valid` with `Wave30tr.thmA` (a) and `tauA_scale`; not a separate claim.
* `prop:newrates` (ii): the run hypotheses of the certified `Wave31tl.lorate_i` / `lorate_ii` verbatim (with their declared encodings and
  generalisations, and the inherited caveat that the existence of a run satisfying `IsWitnessRun` on a general `𝒳` is not certified),
  with `ω(ε)` in place of `c₀ε^γ` and `ω^←(t)` in place of `(t/c₀)^{1/γ}`; hypothesis `u(α⋆−ε) ≥ ω(ε)` on `[0,α⋆]` as printed.
* `prop:newconverse`: `α̂^A = alphaHat (Demp φ x y) (τ^A_{n,m}(·,δ))` with any bound `D` of `‖φ x − φ x′‖` (printed `Δ_φ`), `gNM` is
  `g_{n,m}`; "`α⋆ − α̂^A ≥ sup S`" is "`ε ≤ α⋆ − α̂^A` for every `ε ∈ S`" (equivalent: `S ⊆ [0,α⋆]` is nonempty, `0 ∈ S` stated).
* "With probability at least `1 − p`": a measurable event of probability `≥ 1 − p` under `P^{⊗n} ⊗ Q^{⊗m}` contained in the claimed set.
* Junk values: `toReal` of `rnDeriv` (finite a.e., only integrated); `xiH`'s set is bounded above (stated in `newapproxgen_iii_a`);
  `Kfun`'s set is nonempty (`0 ∈ Fset`) and bounded below by `0`; `Nfun > 0` on `(0,α⋆]` (`err(g) ≤ ε/2` forces `‖g‖ ≥ 1/(4κ)`), so
  `ε/(2·0) = ⊤` never occurs, and at `ε = 0` the bound is `0`; `genInv`'s set contains `0` and is bounded by `α⋆`; `Dpop` only at levels in
  `[0,1)`; `u(α⋆−ε)/ε` only near `0⁺`; `log(1/δ)` with `δ ∈ (0,1)`; `1/n`, `1/m` with `n, m ≥ 1`; `errFn` is applied to measurable
  `[0,1]`-valued functions (integrable integrand).
* `newapprox_err` (`prop:newapprox`, the identities printed with err) is kernel-free and stated for any probability measures (declared
  generalisation of the scope).

Not covered (declared): the last sentence of `prop:newslope` (`05_rates.tex:75-76`); heuristics `05_rates.tex:79-87`, `:105-113`,
`:219-229`; `S4_rates.tex:431` (`u ≤ D ≤ u/(1−α⋆)`; the first half is inside `newapproxgen_iii_a`); `S4_rates.tex:539`, `:589-595` beyond
`newapprox_err` (osc price, the Steinwart reading of `𝒦`); `:636-638`; `:963-964`, `:976-979`; every Fourier-analytic item listed above.
FROZEN 2026-11-21 after an independent critic's review (`tmmd-aos-brief/wave31to/CRITIC.md`: READY TO FREEZE after R1–R4; S8, S14
ACCEPT; S9, S11, S12, S13, S15 ACCEPT-WITH-NOTE; S10 REVISE on (c) only, applied as R1); R1–R4 and the notes N3–N5, N8, N10 applied.
Hashed in `certify/statements.lock` (with its imports); AI agents must not edit this file.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace

namespace StatFormal.Wave31to

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Unconditional StatFormal.Wave30tu StatFormal.Wave30tq
  StatFormal.Wave30tp StatFormal.Wave30tz StatFormal.Wave31tl

section Defs

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `p = dP/d(P+Q)` (real-valued version). -/
def densP (P Q : Measure 𝒳) (x : 𝒳) : ℝ := (P.rnDeriv (P + Q) x).toReal

/-- `q = dQ/d(P+Q)` (real-valued version). -/
def densQ (P Q : Measure 𝒳) (x : 𝒳) : ℝ := (Q.rnDeriv (P + Q) x).toReal

/-- `A = {p > q}`. -/
def setA (P Q : Measure 𝒳) : Set 𝒳 := {x | densQ P Q x < densP P Q x}

/-- `err(f) = ∫ |1_A − f| d|P − Q|`, `|P − Q| = |p − q|·(P+Q)` (`05_rates.tex:88-92`). -/
def errFn (P Q : Measure 𝒳) (f : 𝒳 → ℝ) : ℝ :=
  ∫ x, |(setA P Q).indicator (fun _ => (1 : ℝ)) x - f x| * |densP P Q x - densQ P Q x| ∂(P + Q)

/-- The function `f = ⟪g, φ ·⟫` of `g ∈ H`. -/
def wit (φ : 𝒳 → H) (g : H) (x : 𝒳) : ℝ := ⟪g, φ x⟫_ℝ

/-- `osc(f) = sup f − inf f`. -/
def oscFn (f : 𝒳 → ℝ) : ℝ := (⨆ x, f x) - ⨅ x, f x

/-- `𝓕 = {f ∈ ℋ : 0 ≤ f ≤ 1}`. -/
def Fset (φ : 𝒳 → H) : Set H := {g | ∀ x, 0 ≤ wit φ g x ∧ wit φ g x ≤ 1}

/-- `ξ_ℋ(ε) = sup{(ε − err(f))_+/‖f‖ : f ∈ 𝓕, f ≠ 0}`, `sup ∅ = 0`. -/
def xiH (φ : 𝒳 → H) (P Q : Measure 𝒳) (ε : ℝ) : ℝ :=
  sSup {r | ∃ g ∈ Fset φ, g ≠ 0 ∧ r = max (ε - errFn P Q (wit φ g)) 0 / ‖g‖}

/-- `𝒦(λ) = inf_{f ∈ 𝓕} {err(f) + λ‖f‖}`. -/
def Kfun (φ : 𝒳 → H) (P Q : Measure 𝒳) (lam : ℝ) : ℝ :=
  sInf {r | ∃ g ∈ Fset φ, r = errFn P Q (wit φ g) + lam * ‖g‖}

/-- `𝒩(t) = inf{‖f‖ : f ∈ 𝓕, err(f) ≤ t} ∈ [0,∞]`, `inf ∅ = ∞`. -/
def Nfun (φ : 𝒳 → H) (P Q : Measure 𝒳) (t : ℝ) : ℝ≥0∞ :=
  ⨅ (g : H) (_ : g ∈ Fset φ) (_ : errFn P Q (wit φ g) ≤ t), ENNReal.ofReal ‖g‖

/-- `ω^←(t) = sup{ε ∈ [0,α⋆] : ω(ε) ≤ t}` (`05_rates.tex:200-201`). -/
def genInv (ω : ℝ → ℝ) (αs t : ℝ) : ℝ := sSup {e | e ∈ Icc (0 : ℝ) αs ∧ ω e ≤ t}

/-- `z` lies in the support of the image law `φ_#μ`: every open ball about `z` has preimage of positive `μ`-mass. -/
def InSuppImg (φ : 𝒳 → H) (μ : Measure 𝒳) (z : H) : Prop := ∀ ρ : ℝ, 0 < ρ → 0 < μ (φ ⁻¹' Metric.ball z ρ)

/-- `g_{n,m} = Δ_φ{(1/n + 1/m)/2}^{1/2}{log^{1/2}(1/δ) − log^{1/2}(1/δ′)}` (`prop:newconverse`). -/
def gNM (D δ δ' : ℝ) (n m : ℕ) : ℝ :=
  D * √((1 / (n : ℝ) + 1 / (m : ℝ)) / 2) * (√(Real.log (1 / δ)) - √(Real.log (1 / δ')))

end Defs

namespace Claims

/-! ### S8 `lem:newtrimmean` (Lemma S4.9) -/

/-- **S8**: for `α ∈ [0,1)`, a probability `P`, a bounded measurable `f` and every `P′ ∈ R_α(P)`:
`(E_P f − α sup f)/(1−α) ≤ E_{P′} f ≤ (E_P f − α inf f)/(1−α)`. -/
def newtrimmean : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P : Measure 𝒳) [IsProbabilityMeasure P] (α : ℝ) (f : 𝒳 → ℝ),
    0 ≤ α → α < 1 → Measurable f → BddAbove (range f) → BddBelow (range f) →
      ∀ P' ∈ StatFormal.Wave8a.trimSet P α,
        ((∫ x, f x ∂P) - α * ⨆ x, f x) / (1 - α) ≤ ∫ x, f x ∂P' ∧
        ∫ x, f x ∂P' ≤ ((∫ x, f x ∂P) - α * ⨅ x, f x) / (1 - α)

/-! ### S9 `prop:newapproxgen` (Proposition S4.10) -/

/-- **S9 (i)**: under (A1)–(A2), for every `f ∈ ℋ`, `f ≠ 0`, and `α ∈ [0,1)`:
`(1−α)‖f‖ D_α(P,Q) ≥ E_P f − E_Q f − α osc(f)`. -/
def newapproxgen_i : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ : ℝ) (g : H) (α : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → g ≠ 0 → 0 ≤ α → α < 1 →
      (∫ x, wit φ g x ∂P) - (∫ x, wit φ g x ∂Q) - α * oscFn (wit φ g) ≤ (1 - α) * ‖g‖ * Dpop φ P Q α

/-- **S9 (ii)**: under (A1)–(A2) with `0 < α⋆ < 1`, for every `f ∈ 𝓕`: `E_P f − E_Q f = α⋆ − err(f)`, and if `f ≠ 0`,
`u(α⋆−ε) ≥ (ε − err(f))/‖f‖` for every `ε ∈ [0,α⋆]`. -/
def newapproxgen_ii : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ : ℝ) (g : H),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) →
    0 < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 → g ∈ Fset φ →
      (∫ x, wit φ g x ∂P) - (∫ x, wit φ g x ∂Q) = StatFormal.Distances.tvDist P Q - errFn P Q (wit φ g) ∧
      (g ≠ 0 → ∀ ε ∈ Icc (0 : ℝ) (StatFormal.Distances.tvDist P Q),
        (ε - errFn P Q (wit φ g)) / ‖g‖ ≤ StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - ε))

/-- **S9 (iii) (a)**: under (A1)–(A2) with `0 < α⋆ < 1` (the hypothesis of (ii), on which (iii) rests): `ξ_ℋ` is nondecreasing on
`[0,α⋆]`, and for every `ε ∈ [0,α⋆]` its defining set is bounded above and
`D_{α⋆−ε} ≥ u(α⋆−ε) ≥ ξ_ℋ(ε) ≥ ε/{2𝒩(ε/2)}` (the last in `ℝ≥0∞`, `0` when `𝒩(ε/2) = ∞`). -/
def newapproxgen_iii_a : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) →
    0 < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 →
      MonotoneOn (xiH φ P Q) (Icc 0 (StatFormal.Distances.tvDist P Q)) ∧
      ∀ ε ∈ Icc (0 : ℝ) (StatFormal.Distances.tvDist P Q),
        BddAbove {r | ∃ g ∈ Fset φ, g ≠ 0 ∧ r = max (ε - errFn P Q (wit φ g)) 0 / ‖g‖} ∧
        StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - ε) ≤
          Dpop φ P Q (StatFormal.Distances.tvDist P Q - ε) ∧
        xiH φ P Q ε ≤ StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - ε) ∧
        ENNReal.ofReal ε / (2 * Nfun φ P Q (ε / 2)) ≤ ENNReal.ofReal (xiH φ P Q ε)

/-- **S9 (iii) (b)**: under the same hypotheses, for every `λ ≥ 0` and `ε ∈ (0,α⋆]`: `ξ_ℋ(ε) > λ ⟺ 𝒦(λ) < ε`. -/
def newapproxgen_iii_b : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) →
    0 < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 →
      ∀ lam ε : ℝ, 0 ≤ lam → 0 < ε → ε ≤ StatFormal.Distances.tvDist P Q →
        (lam < xiH φ P Q ε ↔ Kfun φ P Q lam < ε)

/-! ### S10 `prop:newapprox` (Proposition 5.4) and the identities printed with err -/

/-- **S10 (a)**: under (A1)–(A2) with `0 < α⋆ < 1`, for every `f ∈ ℋ` with `0 ≤ f ≤ 1`, `f ≠ 0`, and every `ε ∈ [0,α⋆]`:
`D_{α⋆−ε}(P,Q) ≥ (ε − err(f))/((1 − α⋆ + ε)‖f‖)`. -/
def newapprox_a : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) →
    0 < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 →
      ∀ g ∈ Fset φ, g ≠ 0 → ∀ ε ∈ Icc (0 : ℝ) (StatFormal.Distances.tvDist P Q),
        (ε - errFn P Q (wit φ g)) / ((1 - StatFormal.Distances.tvDist P Q + ε) * ‖g‖) ≤
          Dpop φ P Q (StatFormal.Distances.tvDist P Q - ε)

/-- **S10 (b)**: under the same hypotheses, `D_{α⋆−ε}(P,Q) ≥ ε/{2𝒩(ε/2)}` for every `ε ∈ [0,α⋆]` (in `ℝ≥0∞`, `0` when
`𝒩(ε/2) = ∞`). -/
def newapprox_b : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) →
    0 < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 →
      ∀ ε ∈ Icc (0 : ℝ) (StatFormal.Distances.tvDist P Q),
        ENNReal.ofReal ε / (2 * Nfun φ P Q (ε / 2)) ≤ ENNReal.ofReal (Dpop φ P Q (StatFormal.Distances.tvDist P Q - ε))

/-- **S10 (c)** (`05_rates.tex:89-92`, `S4_rates.tex:589-593`; kernel-free, any probability measures): for every measurable
`f : 𝒳 → [0,1]`, `err(f) = α⋆ − (E_P f − E_Q f)` and `err(f) ≥ 0`; the balanced error `{E_P(1−f) + E_Q f}/2` equals
`{1 − α⋆ + err(f)}/2`, so it is at least the Bayes error `(1−α⋆)/2`, with equality at `f = 1_A` (`A` measurable, `err(1_A) = 0`), and
its excess over the Bayes error is `err(f)/2`. -/
def newapprox_err : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (f : 𝒳 → ℝ),
    Measurable f → (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
      errFn P Q f = StatFormal.Distances.tvDist P Q - ((∫ x, f x ∂P) - ∫ x, f x ∂Q) ∧
      0 ≤ errFn P Q f ∧
      ((∫ x, (1 - f x) ∂P) + ∫ x, f x ∂Q) / 2 = (1 - StatFormal.Distances.tvDist P Q + errFn P Q f) / 2 ∧
      (1 - StatFormal.Distances.tvDist P Q) / 2 ≤ ((∫ x, (1 - f x) ∂P) + ∫ x, f x ∂Q) / 2 ∧
      ((∫ x, (1 - f x) ∂P) + ∫ x, f x ∂Q) / 2 - (1 - StatFormal.Distances.tvDist P Q) / 2 = errFn P Q f / 2 ∧
      MeasurableSet (setA P Q) ∧
      errFn P Q ((setA P Q).indicator (fun _ => (1 : ℝ))) = 0 ∧
      ((∫ x, (1 - (setA P Q).indicator (fun _ => (1 : ℝ)) x) ∂P) +
          ∫ x, (setA P Q).indicator (fun _ => (1 : ℝ)) x ∂Q) / 2 = (1 - StatFormal.Distances.tvDist P Q) / 2

/-! ### S11 `prop:newslopegeneral` (Proposition S4.7) -/

/-- **S11**: under (A1)–(A2) with `0 < α⋆ < 1`, every limit `s` of `u(α⋆−ε)/ε` as `ε ↓ 0` satisfies `s ≤ ‖z − z′‖` for all
`z ∈ supp φ_#P₀`, `z′ ∈ supp φ_#Q₀` (i.e. `s ≤ dist(supp φ_#P₀, supp φ_#Q₀)`); and both supports are closed, nonempty and of full
mass (`S4_rates.tex:450-451`). -/
def newslopegeneral : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) →
    0 < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 →
      (∀ s : ℝ, Tendsto (fun e => StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - e) / e)
          (𝓝[>] 0) (𝓝 s) →
        ∀ z z' : H, InSuppImg φ (P - P ⊓ Q) z → InSuppImg φ (Q - P ⊓ Q) z' → s ≤ ‖z - z'‖) ∧
      IsClosed {z | InSuppImg φ (P - P ⊓ Q) z} ∧ IsClosed {z | InSuppImg φ (Q - P ⊓ Q) z} ∧
      (∃ z, InSuppImg φ (P - P ⊓ Q) z) ∧ (∃ z, InSuppImg φ (Q - P ⊓ Q) z) ∧
      (P - P ⊓ Q) (φ ⁻¹' {z | InSuppImg φ (P - P ⊓ Q) z}ᶜ) = 0 ∧
      (Q - P ⊓ Q) (φ ⁻¹' {z | InSuppImg φ (Q - P ⊓ Q) z}ᶜ) = 0

/-! ### S12 `prop:newslope` (Proposition 5.3), first two sentences -/

/-- **S12 (a)**: under (A1)–(A2) with `0 < α⋆ < 1`, `𝒳` a topological space with its Borel sets and `φ` continuous, every limit `s`
of `(1−α⋆+ε)D_{α⋆−ε}(P,Q)/ε` as `ε ↓ 0` satisfies `s ≤ ‖φ x − φ y‖` for all `x ∈ supp P₀`, `y ∈ supp Q₀`. -/
def newslope_a : Prop :=
  ∀ (𝒳 H : Type) [TopologicalSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ : ℝ),
    StronglyMeasurable φ → Continuous φ → (∀ x, ‖φ x‖ ≤ κ) →
    0 < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 →
      ∀ s : ℝ, Tendsto (fun e => (1 - StatFormal.Distances.tvDist P Q + e) *
          Dpop φ P Q (StatFormal.Distances.tvDist P Q - e) / e) (𝓝[>] 0) (𝓝 s) →
        ∀ x ∈ (P - P ⊓ Q).support, ∀ y ∈ (Q - P ⊓ Q).support, s ≤ ‖φ x - φ y‖

/-- **S12 (b)**: under the same hypotheses, if `supp P₀ ∩ supp Q₀ ≠ ∅` then the limit is `0` and Assumption `ass:margin` fails with
`γ = 1` (no `c₀` with `PolyMargin φ P Q c₀ 1`). -/
def newslope_b : Prop :=
  ∀ (𝒳 H : Type) [TopologicalSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ : ℝ),
    StronglyMeasurable φ → Continuous φ → (∀ x, ‖φ x‖ ≤ κ) →
    0 < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 →
    ((P - P ⊓ Q).support ∩ (Q - P ⊓ Q).support).Nonempty →
      (∀ s : ℝ, Tendsto (fun e => (1 - StatFormal.Distances.tvDist P Q + e) *
          Dpop φ P Q (StatFormal.Distances.tvDist P Q - e) / e) (𝓝[>] 0) (𝓝 s) → s = 0) ∧
      ¬ ∃ c₀ : ℝ, StatFormal.Wave31ti.PolyMargin φ P Q c₀ 1

/-! ### S13 `prop:newrates` (Proposition 5.9) (i), (ii) -/

/-- **S13 (i)**, any valid threshold `τ` at level `δ` and any lower tool `τ^A` at level `δ′`: under (A1)–(A2), `α⋆ < 1`,
`ω` nondecreasing and nonnegative on `[0,α⋆]` with `D_{α⋆−ε}(P,Q) ≥ ω(ε)` on `[0,α⋆]`, and `t = τ(α⋆) + τ^A(α⋆)`: with probability
at least `1−δ−δ′`, `α⋆ − ω^←(t) ≤ α̂ ≤ α⋆`. -/
def newrates_i : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ δ δ' : ℝ) (τ τA ω : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → StatFormal.Distances.tvDist P Q < 1 →
    MonotoneOn ω (Icc 0 (StatFormal.Distances.tvDist P Q)) →
    (∀ e ∈ Icc (0 : ℝ) (StatFormal.Distances.tvDist P Q), 0 ≤ ω e) →
    (∀ e ∈ Icc (0 : ℝ) (StatFormal.Distances.tvDist P Q), ω e ≤ Dpop φ P Q (StatFormal.Distances.tvDist P Q - e)) →
    0 < δ → δ < 1 → 0 < δ' → δ' < 1 → 1 ≤ n → 1 ≤ m →
    ValidThreshold φ n m δ τ → LowerTool φ P Q n m δ' τA →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ - δ') ≤ sampleLaw P Q n m E ∧
        E ⊆ {z | StatFormal.Distances.tvDist P Q -
              genInv ω (StatFormal.Distances.tvDist P Q)
                (τ (StatFormal.Distances.tvDist P Q) + τA (StatFormal.Distances.tvDist P Q)) ≤
                alphaHat (Demp φ z.1 z.2) τ ∧
            alphaHat (Demp φ z.1 z.2) τ ≤ StatFormal.Distances.tvDist P Q}

/-- **S13 (i)** at the paper's thresholds: `τ = τ_{n,m}(·,δ)` (`tauFull`), `τ^A = τ^A_{n,m}(·,δ′)` (`tauA`), `Δ_φ` any bound `D`,
`t_{n,m} = τ_{n,m}(α⋆,δ) + τ^A_{n,m}(α⋆,δ′)` as in `thm:rate`. -/
def newrates_i_full : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ D δ δ' : ℝ) (ω : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → StatFormal.Distances.tvDist P Q < 1 →
    MonotoneOn ω (Icc 0 (StatFormal.Distances.tvDist P Q)) →
    (∀ e ∈ Icc (0 : ℝ) (StatFormal.Distances.tvDist P Q), 0 ≤ ω e) →
    (∀ e ∈ Icc (0 : ℝ) (StatFormal.Distances.tvDist P Q), ω e ≤ Dpop φ P Q (StatFormal.Distances.tvDist P Q - e)) →
    0 < δ → δ < 1 → 0 < δ' → δ' < 1 → 1 ≤ n → 1 ≤ m →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ - δ') ≤ sampleLaw P Q n m E ∧
        E ⊆ {z | StatFormal.Distances.tvDist P Q -
              genInv ω (StatFormal.Distances.tvDist P Q)
                (StatFormal.Wave30tu.Full.tauFull κ D (StatFormal.Distances.tvDist P Q) δ n m +
                  StatFormal.Wave30tr.tauA κ D (StatFormal.Distances.tvDist P Q) δ' n m) ≤
                alphaHat (Demp φ z.1 z.2) (fun α => StatFormal.Wave30tu.Full.tauFull κ D α δ n m) ∧
            alphaHat (Demp φ z.1 z.2) (fun α => StatFormal.Wave30tu.Full.tauFull κ D α δ n m) ≤
              StatFormal.Distances.tvDist P Q}

/-- **S13 (ii-a)** (`thm:lorate` (i) with `ω(ε)` in place of `c₀ε^γ`): under (A1)–(A2), `Δ_φ ≤ 2κ`, the added guard `κ > 0`
(implied by the printed (A3)), `α⋆ < 1`, `ω` nondecreasing and nonnegative on `[0,α⋆]` with `u(α⋆−ε) ≥ ω(ε)` on `[0,α⋆]`, the run
hypotheses of `Wave31tl.lorate_i`, `h₀ > 0` below every consecutive gap and `ε ∈ (0,α⋆]`: if
`β⋆ max{T_fit(η), T_bet(η,J_ε)} ≤ ω(ε)`, then `P(α̂_lo < a_ε) ≤ η`. -/
def newrates_ii_a : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ Dφ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (ω : ℝ → ℝ) (J n m : ℕ) (α : Fin J → ℝ) (δ s2 η h0 ε : ℝ) (R : LoRun 𝒳 J n m) (B : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ Dφ) → Dφ ≤ 2 * κ → 0 < κ →
    MonotoneOn ω (Icc 0 (StatFormal.Distances.tvDist P Q)) →
    (∀ e ∈ Icc (0 : ℝ) (StatFormal.Distances.tvDist P Q), 0 ≤ ω e) →
    (∀ e ∈ Icc (0 : ℝ) (StatFormal.Distances.tvDist P Q),
      ω e ≤ StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - e)) →
    StatFormal.Distances.tvDist P Q < 1 →
    IsGrid α → 1 ≤ J → 0 < δ → δ < 1 → 0 < s2 → s2 ≤ 4 → R.IsWitnessRun φ α δ (1 / 2) s2 →
    (∀ k, R.bat k ≤ B) → 1 ≤ fitCard R.lx 1 → 1 ≤ fitCard R.ly 1 → rOne R.lx R.ly ≤ 1 → 1 ≤ R.N →
    0 < η → η < 1 → 0 < h0 → GapsGe α h0 → 0 < ε → ε ≤ StatFormal.Distances.tvDist P Q →
    beta (StatFormal.Distances.tvDist P Q) * max (Tfit κ Dφ η (rOne R.lx R.ly) B)
        (Tbet Dφ s2 (Real.log (1 / δ)) η (Jeps J ε h0) R.N) ≤ ω ε →
      sampleLaw P Q n m {z | R.alphaLo α δ z.1 z.2 < gridFloor α (StatFormal.Distances.tvDist P Q - ε)} ≤
        ENNReal.ofReal η

/-- **S13 (ii-b)** (`thm:lorate` (ii) with `ω^←(t_{n,m})` in place of `(t_{n,m}/c₀)^{1/γ}`): under the hypotheses of (ii-a) without
`κ > 0`, `ε` and `h₀`, for every upper bound `h` of the mesh of the grid below `α⋆`, with `t_{n,m} = β⋆ max{T_fit(η), T_bet(η,J)}`: with
probability at least `1 − δ − η`, `α⋆ − h − ω^←(t_{n,m}) ≤ α̂_lo ≤ α⋆`. -/
def newrates_ii_b : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ Dφ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (ω : ℝ → ℝ) (J n m : ℕ) (α : Fin J → ℝ) (δ s2 η h : ℝ) (R : LoRun 𝒳 J n m) (B : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ Dφ) → Dφ ≤ 2 * κ →
    MonotoneOn ω (Icc 0 (StatFormal.Distances.tvDist P Q)) →
    (∀ e ∈ Icc (0 : ℝ) (StatFormal.Distances.tvDist P Q), 0 ≤ ω e) →
    (∀ e ∈ Icc (0 : ℝ) (StatFormal.Distances.tvDist P Q),
      ω e ≤ StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - e)) →
    StatFormal.Distances.tvDist P Q < 1 →
    IsGrid α → 1 ≤ J → 0 < δ → δ < 1 → 0 < s2 → s2 ≤ 4 → R.IsWitnessRun φ α δ (1 / 2) s2 →
    (∀ k, R.bat k ≤ B) → 1 ≤ fitCard R.lx 1 → 1 ≤ fitCard R.ly 1 → rOne R.lx R.ly ≤ 1 → 1 ≤ R.N →
    0 < η → η < 1 → MeshBelowLe α (StatFormal.Distances.tvDist P Q) h →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ - η) ≤ sampleLaw P Q n m E ∧
        E ⊆ {z | StatFormal.Distances.tvDist P Q - h -
              genInv ω (StatFormal.Distances.tvDist P Q)
                (tNM κ Dφ (StatFormal.Distances.tvDist P Q) s2 δ η (rOne R.lx R.ly) B J R.N) ≤
                R.alphaLo α δ z.1 z.2 ∧
            R.alphaLo α δ z.1 z.2 ≤ StatFormal.Distances.tvDist P Q}

/-! ### S14 `prop:newconverse` (Proposition S4.18) -/

/-- **S14**: under (A1)–(A2), `α⋆ < 1`, `0 < δ < δ′ < 1`, `n, m ≥ 1`, any bound `D` of `‖φ x − φ x′‖`, the estimator `α̂^A` with the
threshold `τ^A_{n,m}(·,δ)` and `g_{n,m}`: `D_{α⋆} ≤ g_{n,m}` (the set contains `0`), and with probability at least `1 − δ′`,
`α⋆ − α̂^A ≥ ε` for every `ε ∈ [0,α⋆]` with `D_{α⋆−ε}(P,Q) ≤ g_{n,m}`, i.e. `α⋆ − α̂^A ≥ sup{ε ∈ [0,α⋆] : D_{α⋆−ε} ≤ g_{n,m}}`. -/
def newconverse : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ D δ δ' : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → StatFormal.Distances.tvDist P Q < 1 →
    0 < δ → δ < δ' → δ' < 1 → 1 ≤ n → 1 ≤ m →
      Dpop φ P Q (StatFormal.Distances.tvDist P Q) ≤ gNM D δ δ' n m ∧
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ') ≤ sampleLaw P Q n m E ∧
        ∀ z ∈ E, ∀ ε ∈ Icc (0 : ℝ) (StatFormal.Distances.tvDist P Q),
          Dpop φ P Q (StatFormal.Distances.tvDist P Q - ε) ≤ gNM D δ δ' n m →
            ε ≤ StatFormal.Distances.tvDist P Q -
              alphaHat (Demp φ z.1 z.2) (fun α => StatFormal.Wave30tr.tauA κ D α δ n m)

end Claims

end StatFormal.Wave31to
