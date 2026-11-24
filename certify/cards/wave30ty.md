# Fidelity card — wave 30ty: trimmed-mmd (JMLR v2), the two-sample hinge lemma `lem:hinge` (Appendix A)

Lean: `StatFormal/Wave30ty/Statements.lean` (7 claims; frozen 2026-11-08 before any proof, commit `e596fdb`, sha256
`c8316fc3f42ceeab54177cb97627a1bfe10ffa2143c8bcc37cf50596c07399de`, locked with its 7 imports: `Wave30tr`, `Wave30tp`, the frozen
`TrimmedMMD` files `Statements`, `Concentration`, `Unconditional`, `ZeroSet`, and `Lib/Distances/TV.lean`). Routes `RouteBasic`,
`RouteTwo`, `RouteOne` (untrusted); `Proofs.lean` proves all 7 claims (`theorem c : Claims.c`), and the gate checks `example : Claims.c := c`
and `#print axioms` for each (`[propext, Classical.choice, Quot.sound]`). Paper id `trimmed-mmd (jmlr)`; labels `lem:hinge (v2)` (+ a short description).
Branch `tmmd-jmlr-hinge`, based on `tmmd-jmlr-trimrate` at `10d1699` (waves 30tl, 30tn, 30tp, 30tr, 30ts, 30tu, 30tw, 30tx).
Critic (independent AI reviewer, before the freeze, 2026-11-08): 7 claims, 4 ACCEPT and 3 ACCEPT-WITH-NOTE, verdict READY TO FREEZE; it
re-derived the expectation bound (symmetrisation, contraction with constant 1 and no `ψ(0) = 0`, `E‖S_σ‖ ≤ κ√s`) and the McDiarmid
constants, confirmed the degenerate case and compiled a proof of `hinge_tail_printed_false`. Applied before hashing: two docstring
sentences (the strict form is what the three proofs *need*, the proof of `thm:twosided` writing the non-strict event; the added
hypothesis is exactly where the non-strict sentence holds) and a line reference.
Fidelity review: independent AI audit, method v1 (certify/AUDIT_METHOD.md), 2026-11-08 — PASS with notes (7 claims back-translated
blind and compared with the printed text at `3a6d388`; the declared deviations are generalisations, an integrability addition and the
positivity hypothesis forced by the certified counterexample; it re-ran the block comparison `fe74452` → `3a6d388` and confirmed every
verdict of the rename audit; notes at the end of this card).
**Author: approved (automatic on AI-audit PASS, per author decision 2026-10-21).**

## Source
Frozen from `trimmed-mmd/jmlr/` at master `3a6d388` ("JMLR v2 long version: consistency fixes (FINAL_READ_v2, 44 findings) and approved
cuts (100 -> 91 pp)"). Read-only, read 2026-11-08 (the working tree's `jmlr/` was identical to `3a6d388` for these files). sha256 at
`3a6d388`:

| file | sha256 |
|---|---|
| `appendix/A_basic.tex` (`lem:hinge` and the proofs of `thm:concentration`, `thm:twosided`) | `fab7d2677cec05a2b3ad0f7fb6eec95867404875c9ffcd3a9351c6c5b0fa94bf` |
| `appendix/C_recover.tex` (`lem:localmod` and its proof) | `07364ba6dcfdf9f28a1ed989a969ca8a01f0daf0fd9ed439243357336be89f25` |
| `sections/05_estimator.tex` (`thm:consistency`, rename audit) | `c6901dcc98acb35410a5ad3b3d55c21d597d9f3beb812e93a2e0d1ac87bdfafe` |
| `sections/08_trimming.tex` (`thm:trimrate`, `cor:trimrate`, rename audit) | `86dcfa7b1f3d2ade9734d2b1bc9d6a3bb3071f69690c09f383531e2c067da5a8` |
| `sections/04_test.tex` (context: `s`, `e_k`, `thm:twosided`) | `ab5da423f80fa0af29d4cdb8e4b5d505f055398a3b6674df03a20990c502da4d` |
| `sections/03_regions.tex` (context: `ass:regularity`) | `b9673cf0c477f8c1272c6866130075938e875cd35175716c17cb757b3a17798b` |
| `sections/06_splitting.tex` (rename audit: `thm:betting`) | `8410a6d80ee1823738b3a8351d637d9faa40b684d363d3850a5a6ee64132e5f4` |
| `appendix/B_split.tex` (rename audit: the fractions) | `ef72befd518c8cb4dc13f9f1e3f3443c3747d0b29193ae3a9255640eb790864a` |

Target passage: `A_basic.tex:126-148` (`lem:hinge`, label at `:127`), its proof `:150-185`; uses: proof of `thm:concentration`
`:187-231` (one sample, `r = 1`, `ρ₁ = κ`, `Δ₁ = 2κ`), proof of `thm:twosided` `:370-401` (`ψ = (·)₊`, `r = 1`, `ρ₁ = ρ₂ = κ`,
`Δ₁ = Δ₂ = D_φ`), proof of `lem:localmod` `C_recover.tex:458-475` (`ρ_i = κr + λ_i`, `Δ_i = 2(2κr + λ_i)`); context
`04_test.tex:101-104` (`s = 1/n + 1/m`, `e_k = E|σ_1+⋯+σ_k|/k`), `03_regions.tex:20-31`.
Compared with the previous text (`fe74452`): `lem:hinge` is the only new numbered statement; the changed numbered statements are listed
in the rename audit below (found by comparing every theorem/lemma/proposition/corollary/remark/assumption block of `jmlr/sections` and
`jmlr/appendix` between `fe74452` and `3a6d388`).

## Targets (7, all in `certify/targets.toml`, module `StatFormal.Wave30ty.Proofs`)
| label | claim / theorem `StatFormal.Wave30ty.(Claims.)…` |
|---|---|
| `lem:hinge (v2)`: measurability, integrability, `E Z, E Z⁻ ≤ 2[rκ√s + ρ₁e_n + ρ₂e_m]` | `hinge` |
| `lem:hinge (v2)`: tail as printed (`≥`), under `Δ₁²/n + Δ₂²/m > 0` | `hinge_tail` |
| `lem:hinge (v2)`: tail in the strict form (`>`), no extra hypothesis | `hinge_tail_strict` |
| `lem:hinge (v2)`, one sample: measurability, integrability, `E Z, E Z⁻ ≤ 2[rκ√(1/n) + ρ₁e_n]` | `hinge1` |
| `lem:hinge (v2)`, one sample: tail as printed, under `Δ₁²/n > 0` | `hinge1_tail` |
| `lem:hinge (v2)`, one sample: strict tail, no extra hypothesis | `hinge1_tail_strict` |
| `lem:hinge (v2)`: the printed tail with no condition on `Δ` is false (two samples and one sample) | `hinge_tail_printed_false` |

## Encodings (declared)
* **(A1)–(A2)** as in `TrimmedMMD/Concentration`, `Wave30tr.thmA`, `Wave30tx.localmod`: `𝓗` a separable real inner-product space,
  `φ : 𝒳 → 𝓗` strongly measurable, `‖φ x‖ ≤ κ` (`k(x,x) = ‖φ(x)‖² ≤ κ²`), `v(x) = ⟨v, φ(x)⟩` (reproducing property; by Pettis,
  (A1)+(A2) make the canonical feature map strongly measurable). **Generalisations**: `κ` any bound on `‖φ‖`; completeness of `𝓗`
  is not assumed (the RKHS is one instance); `𝒳` any measurable space.
* **The maps** `ψ^i : 𝒳 → ℝ → ℝ`, `IsHingeMap ψ`: `LipschitzWith 1 (ψ x)` for every `x`; `Function.uncurry ψ` measurable on `𝒳 × ℝ`
  (product σ-algebra, Borel on `ℝ`) = "`(x,z) ↦ ψ^i_x(z)` measurable"; `∃ C, ∀ x, |ψ x 0| ≤ C` = "`sup_x |ψ^i_x(0)| < ∞`".
* **Class and suprema.** `hingePar r ρ₁ ρ₂` = `𝒮`; `hOne ψ φ v a x = ψ x (a − ⟨v, φ x⟩)` = `h¹_{v,a}(x)`; `hTwo ψ φ v b y = ψ y (⟨v, φ y⟩ − b)`
  = `h²_{v,b}(y)`; `devPop P x h = ∫h dP − n⁻¹Σ h(x_i)` = `(P − P_n)h`; `devEmp P x h = n⁻¹Σ h(x_i) − ∫h dP` = `(P_n − P)h`;
  `hingeZ`, `hingeZm` = `Z`, `Z⁻` (real `⨆` over the subtype `𝒮`); one sample: `hingePar1 r ρ₁` = `{(v,a) : ‖v‖ ≤ r, |a| ≤ ρ₁}`,
  `hingeZ1`, `hingeZ1m`.
* **Samples**: `X ∼ P^{⊗n}`, `Y ∼ Q^{⊗m}` on `(Fin n → 𝒳) × (Fin m → 𝒳)` under `sampleLaw P Q n m` (one sample: `Measure.pi`), `n, m ≥ 1`
  (the empirical measures need a point; with `n = 0` the formulas would read `0⁻¹ = 0`). `s = sNM n m = 1/n + 1/m`, `e_k = ek k` (exact
  average of `|σ_1+⋯+σ_k|/k` over the `2^k` sign vectors), one sample `s = 1/n` written `√(1/n)`.
* **Tails**: "exceeds its mean by at least `ε` with probability at most `e^{−χ}`" = `TailAtLeast μ F ε χ`:
  `μ{ω : ∫F dμ + ε ≤ F ω} ≤ ofReal(e^{−χ})`; the strict form `TailMoreThan`: `μ{ω : ∫F dμ + ε < F ω} ≤ ofReal(e^{−χ})`. The oscillation
  hypotheses are literal: `∀ p ∈ 𝒮, ∀ x x', |h¹_p(x) − h¹_p(x')| ≤ Δ₁` (and `Δ₂` for `h²`).
* **Additions** (declared): `hinge`, `hinge1` also state integrability of `Z`, `Z⁻` (so the means are genuine Bochner integrals).
* **Stronger hypothesis** (declared, forced by a counterexample): `hinge_tail` / `hinge1_tail` assume `Δ₁²/n + Δ₂²/m > 0` / `Δ₁²/n > 0`.
  It is exactly the condition under which the printed non-strict sentence is true: if the sum is `0`, then `Δ₁ = Δ₂ = 0`, every
  `h^i_p` is constant in the point, `Z = Z⁻ ≡ 0` and `P(Z ≥ E Z + 0) = 1 > e^{−χ}`. `hinge_tail_strict` / `hinge1_tail_strict` need no
  extra hypothesis, and together with `hinge_tail` give everything the printed sentence can mean.

## Covered — back-translations and deviations
Common setting of the two-sample claims: `𝒳` a measurable space, `𝓗` a separable real inner-product space, `P, Q` probability
measures on `𝒳`, `φ : 𝒳 → 𝓗` strongly measurable with `‖φ‖ ≤ κ`, `ψ¹, ψ²` hinge maps, `r, ρ₁, ρ₂ ≥ 0`, `n, m ≥ 1`.

* **`hinge`** (`A_basic.tex:128-143`). `Z` and `Z⁻`, as functions of the samples, are measurable and integrable under `P^{⊗n} ⊗ Q^{⊗m}`,
  and `E Z ≤ 2[rκ√s + ρ₁e_n + ρ₂e_m]`, `E Z⁻ ≤ 2[rκ√s + ρ₁e_n + ρ₂e_m]`. As printed (integrability added).
* **`hinge_tail`** (`:144-147`). If in addition `|h¹_{v,a}(x) − h¹_{v,a}(x')| ≤ Δ₁` and `|h²_{v,b}(y) − h²_{v,b}(y')| ≤ Δ₂` for all
  points and all `(v,a,b) ∈ 𝒮`, and `Δ₁²/n + Δ₂²/m > 0`, then for every `χ > 0`,
  `P(Z ≥ E Z + √(χ(Δ₁²/n + Δ₂²/m)/2)) ≤ e^{−χ}` and the same for `Z⁻`. As printed plus the declared positivity hypothesis.
* **`hinge_tail_strict`**. Same without the positivity hypothesis, with `>` in place of `≥` (the corrected sentence).
* **`hinge1`, `hinge1_tail`, `hinge1_tail_strict`** (`:146-147`, "for one sample the same holds with the terms of the second sample
  removed: `s = 1/n`, and no `ρ₂e_m` and no `Δ₂²/m`"): `Z = sup (P − P_n)h¹`, `Z⁻ = sup (P_n − P)h¹` over `‖v‖ ≤ r`, `|a| ≤ ρ₁`, under
  `P^{⊗n}`; `E Z, E Z⁻ ≤ 2[rκ√(1/n) + ρ₁e_n]`; the tails with radius `√(χ(Δ₁²/n)/2)`, the non-strict one under `Δ₁²/n > 0`.
* **`hinge_tail_printed_false`**. The two-sample and the one-sample tail sentences, read with no condition on `Δ` beyond the
  oscillation bounds, are both false. Witness: `𝒳 = Unit`, `𝓗 = ℝ`, `φ = 0`, `ψ¹ = ψ² ≡ 0`, `P = Q = δ`, `n = m = 1`, `r = ρ = Δ = 0`,
  `χ = 1`: `Z ≡ 0`, the event `{Z ≥ E Z + 0}` is the whole space, of probability `1 > e^{−1}`.

**Proof routes** (untrusted): `Z = Zc(−1)`, `Z⁻ = Zc(1)` for the bracket `(P_n − P)(c h¹) + (Q_m − Q)(c h²)`; the bracket is Lipschitz in
`(v,a,b)` (constant `4(1+κ)`) for every sample, so the supremum is over a countable dense subset of `𝒮` (`𝓗 × ℝ × ℝ` separable);
expectation by the certified two-sample signed symmetrisation `integral_iSup_empDev2_le` (one sample: `integral_iSup_empDev_le`),
the certified coordinatewise contraction `signE_iSup_contraction` with the sample-dependent 1-Lipschitz maps `w ↦ c n⁻¹ψ¹_{X_i}(nw)`,
`w ↦ c m⁻¹ψ²_{Y_j}(mw)`, the linear bound `r‖S_σ‖ + ρ₁|σ̄| + ρ₂|σ̄'|` and `signE_norm_sum_le`, `signE_comp_inl/inr`; tails by
`Wave30tp.mcdiarmid_two_sample` with differences `Δ₁/n`, `Δ₂/m` (one sample: TauCeti's `hasSubgaussianMGF_of_bounded_differences_fin`);
the degenerate case by `Zc ≡ 0`.

## Junk-value audit
* Real `⨆` over `𝒮`: `𝒮` is nonempty (`(0,0,0) ∈ 𝒮` since `r, ρ ≥ 0`) and the bracket is bounded on `𝒮` by
  `2(C₁ + ρ₁ + κr) + 2(C₂ + ρ₂ + κr)` (`|ψ_x(w)| ≤ C + |w|`): a genuine supremum, no `iSup` junk.
* Bochner integrals: `h¹_p`, `h²_p` measurable and bounded for every `p`, `Z`, `Z⁻` measurable and bounded: no non-integrable junk
  (integrability is stated as a conclusion).
* Division: `n, m ≥ 1` everywhere (`(n : ℝ)⁻¹`, `1/n`, `Δ²/n` are genuine). `√` arguments are `≥ 0`. `ENNReal.ofReal (e^{−χ})` of a
  positive real. No `Measure.map`, `toReal`, `sInf ∅`.
* Vacuity: the hypotheses hold for the paper's instances (e.g. `ψ = (·)₊`, the Gaussian feature map, `r = 1`, `ρ = κ`, `Δ = 2κ > 0`).
* Smuggling: none; the oscillation bounds are the printed hypotheses, the positivity hypothesis is declared above.

## Defects in the printed text (`3a6d388`), with corrected wording
1. **`A_basic.tex:144-147`, `lem:hinge`, the tail sentence — false as written when `Δ₁ = Δ₂ = 0`** (one sample: `Δ₁ = 0`): then the radius
   is `0`, `Z` and `Z⁻` are constant, and `P(Z ≥ E Z) = 1 > e^{−χ}` (certified counterexample `hinge_tail_printed_false`, e.g.
   `ψ¹ = ψ² ≡ 0`). Corrected wording: "then for every `χ>0` each of `Z` and `Z^-` exceeds its mean by **more than**
   `\sqrt{\chi(\Delta_1^2/n+\Delta_2^2/m)/2}` with probability at most `e^{-\chi}`" (true with no condition, `hinge_tail_strict`; it is
   what the three proofs use), or keep "at least" and add "if `\Delta_1+\Delta_2>0`" (one sample: "if `\Delta_1>0`") (`hinge_tail`,
   `hinge1_tail`; equivalent to the frozen `\Delta_1^2/n+\Delta_2^2/m>0` because the oscillation bounds force `\Delta_i\ge0`). None of the three uses is affected:
   `thm:concentration` (`:222-225`) already says "by more than"; `thm:twosided` needs only `P(βZ > τ^A) ≤ δ`; `lem:localmod`
   (`C_recover.tex:465-474`) is a "with probability at least `1 − e^{−χ}`" statement, the complement of the strict event.
2. **`A_basic.tex:183`, proof of `lem:hinge`**: the McDiarmid display `exp(−2ε²/(Δ₁²/n + Δ₂²/m))` divides by `0` in the degenerate case.
   Add "(for `\Delta_1^2/n+\Delta_2^2/m>0`; if `\Delta_1=\Delta_2=0` every `h` is constant in the point and `Z=Z^-=0`)".
3. **`A_basic.tex:394-396`, proof of `thm:twosided`**: "`\Pp(Z\ge\E Z+D_\phi\sqrt{s\log(1/\delta)/2})\le\delta`" is false when `D_φ = 0`
   (the parenthetical "(If `D_\phi=0`, `\phi` is constant and `Z=0`.)" rescues the conclusion, not the display). Corrected:
   "`\Pp(Z>\E Z+D_\phi\sqrt{s\log(1/\delta)/2})\le\delta`", which is all `E^+ = \{\beta Z\le\tau^{\mathrm A}_{n,m}(\alpha,\delta)\}` needs;
   the parenthetical then becomes unnecessary. (The certified `Wave30tr.thmA` is unaffected.)

## Rename audit (statements changed in the same length pass, `fe74452` → `3a6d388`)
Checked against the frozen claims of the certifying waves; no new claim is needed for any of them.
* **`thm:consistency`** (`05_estimator.tex:80-93`), (ii): `η ∈ (0,1)` → `δ′ ∈ (0,1)`, `N(ε,δ,η)` → `N(ε,δ,δ′)`, `1 − δ − η` → `1 − δ − δ′`.
  Wave30tu `Claims.consistency_ii` (frozen from `0c41fb5`; the theorem block differs from `3a6d388` only in these three places)
  quantifies `∀ ε ∈ (0, α*], ∀ η, 0 < η → η < 1 → ∃ N, ∀ n m ≥ N, … ofReal (1 − δ − η) ≤ P(E)`: `η` is a bound variable, and
  `δ` is bound before it, so `N` may depend on `(ε, δ, η)`. **Pure rename** (α-conversion of a bound variable).
* **`cor:trimrate`** (`08_trimming.tex:295-307`): the symbol `c = min(c_f, c′_f)` is dropped and written inline,
  `V_α = κ(1−α)^{−1} + [(1−α)min(c_f,c′_f)]^{−1/2}`. Wave30tx `Claims.cor_trimrate` already has
  `let V := κ / (1 - α) + 1 / √((1 - α) * min cf cf')` (no symbol `c`). **Pure rename**.
* **`thm:trimrate`** (`08_trimming.tex:246-284`): "`τ^A = τ^A_{n,m}(α,δ/5)` as in `eq:tauA` (with `β` there equal to `(1−α)^{−1}`)".
  In `sec:trimrate` `β` also names the second trimming level (`β = α`); the parenthetical says that `eq:tauA` is read with its own
  `β = (1−α)^{−1}`. Wave30tx `Claims.trimrate`, `trimrate_inter` use `tauA κ Dφ α (δ/5) n m = 1/(1−α) · […]` (`Wave30tr.tauA`). **Pure
  clarification** (the frozen claim already has this reading; no content change). The theorem block differs from `c3ba305` (the
  Wave30tx source) only in this parenthetical.
* **`thm:betting`** (`06_splitting.tex:124-136`, with "the certificate" paragraph `:108-122`): the cap of the fractions renamed `c → λ_max`
  (`λ_k ∈ [0, λ_max/(1+α)]`, `λ_max ∈ (0,1]`), also `n_b, m_b → n_{[b]}, m_{[b]}` and the block letter `J → 𝒥`. The theorem block itself is
  unchanged (it refers to "every choice of fractions as above"). Wave30tv (branch `tmmd-jmlr-seqbet`) `IsBatchBetRule lx ly bat α c lam`
  with `0 < c → c ≤ 1 →` and `lam k u x y z ≤ c / (1 + α)` in `thm_betting_cond`, `thm_betting_condexp`, `thm_betting`, `cor_lower`:
  `c` is a universally quantified parameter. **Pure rename**; the batch-size and block-letter changes are notation only (the frozen
  claims quantify over any batch labelling and any disjoint blocks).
* **`rem:fixedkernel`** (`A_basic.tex:508-520`): "Unless stated otherwise, the numbers in this paper use the median heuristic". A
  statement about the paper's numerical practice; no target covers `rem:fixedkernel` (it has no formal content). **No claim affected.**
* Also changed, wording only (found by the block comparison): `rem:nearcontact` (a) "neighbourhood" → "neighborhood" (Wave30tx
  `nearcontact_a`: unaffected); `thm:split` title "Bootstrap certificate (asymptotic)" → "Asymptotic bootstrap certificate" (statement
  text unchanged). Outside the numbered blocks, the prose of the MMD obstruction (`06_splitting.tex:304-305`) and its appendix proof
  (`B_split.tex`) rename the periodic function `s → ς` (bound symbol; no claim affected).

## Certified results reused (not re-proved)
`Lib/Concentration/Symmetrization2.lean` (`integral_iSup_empDev2_le`), `Lib/Concentration/Symmetrization.lean`
(`integral_iSup_empDev_le`), `Lib/Concentration/ContractionCoord.lean` (`signE_iSup_contraction`, `signE_norm_sum_le`,
`signE_comp_inl/inr`, `signE_eq_radE`), `Lib/Concentration/EmpiricalProcess.lean` (`empDev_update_sub`, `abs_iSup_sub_iSup_le`,
`abs_empDev_le`), `Wave30tp.mcdiarmid_two_sample`, TauCeti `hasSubgaussianMGF_of_bounded_differences_fin`. The route of `Wave30tx`
`lem:localmod` (`RouteLocal`) is the template; the three uses in the paper (`thm:concentration`, `thm:twosided`, `lem:localmod`) are
already certified (`TrimmedMMD/Concentration`, `Wave30tr.thmA`, `Wave30tx.localmod`) and are not re-derived from this lemma.

## Not covered (declared)
The proof's prose (continuity of the bracket, the symmetrisation, contraction and McDiarmid steps as separate statements); the three
reductions "is the supremum of Lemma~lem:hinge with …" in the proofs of `thm:concentration`, `thm:twosided`, `lem:localmod` (proof
text; the results are certified elsewhere).

## Coverage note (COVERAGE.md row `lem:hinge`)
"certified: Z, Z^- measurable (and integrable) and both expectation bounds, two samples and one sample, as printed; the tail sentence as
printed under the added Delta_1^2/n + Delta_2^2/m > 0, and in the strict form (> instead of >=) with no extra hypothesis; the printed
tail with no condition on Delta is false (Delta = 0: Z constant, P(Z >= EZ) = 1), counterexample certified (Wave30ty)".

## AI audit notes (2026-11-08, PASS with notes; applied)
1. Wording of how the claims are checked (the gate generates the `example`/`#print axioms` lines) — fixed in the header.
2. Line references `rem:fixedkernel` `A_basic.tex:508-520` and `thm:betting` `06_splitting.tex:124-136` — fixed.
3. The alternative fix "if `Δ₁+Δ₂>0`" is equivalent to the frozen positivity hypothesis only because `Δ_i ≥ 0` is forced; one sample
   "`Δ₁>0`" — added to defect 1.
4. The prose rename `s → ς` in the MMD-obstruction sentence — added to the rename audit.
5. `𝒳`, `𝓗` are quantified over `Type` (standard in the repository).
Optional wording point (not a defect): "with `s`, `e_n` and `e_m` as in Theorem~thm:twosided" (`A_basic.tex:138`, `C_recover.tex:443`,
`08_trimming.tex:256`) refers to the paragraph before that theorem (`04_test.tex:101-104`); "as defined before Theorem~thm:twosided" is
more exact.
