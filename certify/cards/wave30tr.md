# Fidelity card — wave 30tr: trimmed-mmd (JMLR revision), one joint one-sided two-sample supremum — NOTE Theorem A (the two-sided tool), its constants `e_k`, `τ_A ≤ τ_{n,m}`

Lean: `StatFormal/Wave30tr/Statements.lean` (frozen 2026-11-08, sha256 `62061fad06ab03d2a2b1636ce5acb3b88ca60b8d2f570ead724763d9e6230efa`, locked
with its imports), routes `RouteDet`, `RouteEvents`, `RouteConst`, `RouteEk`; `Proofs.lean` checks all 8 claims.
Paper id `trimmed-mmd (jmlr)`. Imports, not copies, the frozen `TrimmedMMD` (`tau` = `τ_{n,m}`), `TrimmedMMD/Concentration` (`region`,
`empirical`), `TrimmedMMD/Unconditional` (`setDist`, `Dpop`, `Demp`), `Wave30tp` (`sNM`, `sampleLaw`) and, through `TrimmedMMD/ZeroSet`,
`StatFormal.Distances.tvDist`.
Critic (independent AI reviewer, before the freeze, 2026-11-08): 7 claims ACCEPT / ACCEPT-WITH-NOTE, none false, no counterexample (exact
arithmetic: the closed form of `e_k` for `k ≤ 399` and a brute force for `k < 12`; `e_k ≤ k^{−1/2}` for `k < 5000`; `τ_A ≤ τ_{n,m}` in 2·10⁵ random
cases). Applied before freezing: the reason given for the generalisation in `κ`, `D`; an explicit declaration of the two unprinted conjuncts of
`tauA_scale`; two "not covered" additions; and the optional `thmA_compare_half`, added as a declared strengthening.
Fidelity review: independent AI audit, method v1 (certify/AUDIT_METHOD.md), 2026-11-08 — PASS with notes
(8 claims faithful; notes: the `tvDist` supremum and the integrability of the region integrals in the junk audit, the paper now printing
`thm:twosided`/`eq:tauA`, the docstring wording of `thmA_twosided` — all applied below). After the audit, the paper text of `thm:twosided` was
re-checked by the coordinator and committed (master `0c41fb5`). Its statement differs from the audited version only in the quantifier order,
which now coincides with the frozen one (see "Printed source").
**Author: approved (automatic on AI-audit PASS, per author decision 2026-10-21).**

## Printed source (labels to be remapped)
The printed source is **`trimmed-mmd/explore/sharper_threshold/NOTE.md` §2**, a research note for the JMLR revision (read-only). It was frozen
from the version with sha256 `b6f1aab476e51d1aba9b146074cbe93bbaae7311638a485d0f9cd8511565d284`, the same version the end of wave 30tp records.
Revision plan v2, approved by the author, makes Theorem A the two-sided tool behind consistency, the rate and the confidence interval, in place
of the paper's region concentration theorem. All targets carry the provisional label `thm:twosided (NOTE Thm A …)`, with the claim's own name in
parentheses. **The labels must be remapped to the paper's labels when the JMLR text is revised.**
* Line numbers (version `b6f1aab4`):
  * §1 notation and kernel constants: `:68-84`;
  * `e_k`, `τ_A`: `:114-119`;
  * **Theorem A**: `:121-131`;
  * proof: Step 1 `:137-159`, Step 2 `:161-186`, Step 3 `:188-193` (the remark "`τ_A(α,δ) = βτ_A(0,δ)`, so `E⁺` is free of `α`" is
    `:192-193`), Comparison `:195-198`;
  * Gain: `:200-207`.
* **The paper now prints the theorem.** `trimmed-mmd/jmlr/`, master `0c41fb5` ("batch 1b: fixes from the independent re-check"):
  `sections/04_test.tex` sha256 `65b98e826426d014ca89507df5f2d4d2af9b24b905669f35eb119a1ff40cbe73`, `appendix/A_basic.tex` sha256
  `5f05deab18c50e03cce389031e5db0657c6d1e9f1a0e175e27fca93eb8db1da7`. Re-read 2026-11-08 after the coordinator's notice; the frozen statements
  needed no change. Claim by claim:
  * `thmA` ↔ **`thm:twosided`**, `04_test.tex:106-122`. Its quantifier order is now "for every pair `(P,Q)`, all `n,m ≥ 1` and `δ ∈ (0,1)`
    there are events `E⁺` and `E⁻`, not depending on `α`, … such that for every `α ∈ [0,1)`", which is exactly the Lean order. The `H_{0,α}`
    clause of `thmA` is printed as prose at `:177-180` ("`τ^A_{n,m}` … is valid by Theorem `thm:twosided` because `D_{α,k}(P,Q) = 0` under the
    null").
  * `thmA_compare` ↔ **`eq:tauA`**, `:117-121`: `τ^A_{n,m}(α,δ) ≤ r_n(α,δ/2) + r_m(α,δ/2)`. The comparator is the frozen `TrimmedMMD.tau`. The
    revised paper writes `τ_{n,m}` for the minimum of several valid thresholds, `τ^A` among them (`:176-181`); the frozen `tau` is not that
    minimum, but `r_n(α,δ/2) + r_m(α,δ/2)`, as `eq:tauA` prints it.
  * `ek_le` ↔ `:104` ("`e_k = E|σ_1+⋯+σ_k|/k ≤ k^{−1/2}`"). The paper's `D_φ` and `s`, `β` are at `:101-103`.
  * `tauA_scale` (scale identity) ↔ proof, Step 3, `A_basic.tex:380-381` ("`E⁺ = {βZ ≤ τ^A_{n,m}(α,δ)}` … does not depend on `α` because both
    sides carry the factor `β`").
  * `ek_closed`, `ek_tendsto`, `thmA_twosided` ("Hence") and `thmA_compare_half` are printed only in the NOTE; at remap they keep the NOTE as
    their printed source (the paper uses `E⁺` and `E⁻` separately, at levels it chooses: `A_basic.tex:230`, `:314`, `B_split.tex:200`).
  * Proof, `A_basic.tex:344-385`. Step 1 now says `D̂ = sup_f sep_n(f)` is attained when the distance is positive and equals `sep_n(0) = 0`
    otherwise. Step 2 replaces the van der Vaart–Wellner citation by the signed ghost-sample argument (Jensen with an independent copy, signs,
    splitting the supremum), then the coordinatewise contraction principle (Shalev-Shwartz and Ben-David, Lemma 26.9). That is exactly the
    certified route (`Symmetrization2.integral_iSup_empDev2_le`, `ContractionCoord.signE_iSup_contraction`).
* Paper context (read-only), `trimmed-mmd/jmlr/`:
  * `sections/03_regions.tex:20-31` — `ass:regularity` ((A1) boundedness and measurability, (A2) `H` separable, (A3) characteristic);
  * `sections/04_test.tex:6` — `H_{0,α}`;
  * `sections/05_estimator.tex:77-171` and `06_splitting.tex:192-205` — `thm:consistency`, `thm:rate`, `cor:confset`, `cor:upperfs` (not
    covered here; see below).

## Definitions (locked)
* `ek k = 2^{−k} Σ_{σ : Fin k → Bool} |Σ_i (σ_i ? 1 : −1)| / k`. This is the exact `E|σ_1+⋯+σ_k|/k` for i.i.d. uniform signs (the printed
  definition of `e_k`). `ek 0 = 0` is junk, but it appears only in `ek_tendsto`, where it cannot matter.
* `tauA κ D α δ n m = (1−α)⁻¹ [2κ√s + 2κ(e_n + e_m) + D√(s log(1/δ)/2)]`, with `s = sNM n m = 1/n + 1/m`. This is the printed `τ_A(α,δ)`, with
  `D` in place of `D_φ`.
* Reused (already locked): `region φ α P` (`𝒞_α(P)`), `empirical x` (`P_n`), `setDist A B = inf{‖a − b‖}`,
  `Dpop φ P Q α = setDist(𝒞_α(P), 𝒞_α(Q))` (`D_α(P,Q)`), `Demp φ x y α = setDist(𝒞_α(P_n), 𝒞_α(Q_m))` (`D̂_α`),
  `sampleLaw P Q n m = P^{⊗n} ⊗ Q^{⊗m}`, `tau κ α δ n m = r_n(α,δ/2) + r_m(α,δ/2)` (`τ_{n,m}`), `tvDist`.

## Covered (8 claims), with back-translation
In every probabilistic claim:
* `H` is a **separable** real Hilbert space (A2);
* `φ : 𝒳 → H` is strongly measurable with `‖φ‖ ≤ κ` (A1);
* `D` is any bound on `‖φ(x) − φ(x')‖`;
* `𝒳` is any measurable space, and `P, Q` are any probability measures;
* `δ ∈ (0,1)` and `n, m ≥ 1`.

The claims:
* `thmA` (**Theorem A, (a) and (b)**). For every pair there are measurable events `E⁺`, `E⁻` of `(Fin n → 𝒳) × (Fin m → 𝒳)`, each of
  `P^{⊗n}⊗Q^{⊗m}`-probability `≥ 1 − δ` and chosen before `α` (they do not depend on `α`), such that for every `α ∈ [0,1)`:
  * on `E⁺`: `D̂_α ≤ D_α(P,Q) + τ_A(α,δ)`, and `D̂_α ≤ τ_A(α,δ)` whenever `TV(P,Q) ≤ α` (`H_{0,α}`);
  * on `E⁻`: `D_α(P,Q) − τ_A(α,δ) ≤ D̂_α`.
* `thmA_twosided` (**"Hence"**). There are measurable `E⁺`, `E⁻`, each of probability `≥ 1 − δ/2`, whose intersection has probability
  `≥ 1 − δ`, and on `E⁺ ∩ E⁻`, `|D̂_α − D_α(P,Q)| ≤ τ_A(α,δ/2)` for every `α ∈ [0,1)`.
* `thmA_compare` (**"Moreover"**). For all `κ`, `D ∈ [0,2κ]`, `α ∈ [0,1)`, `δ ∈ (0,1)` and `n, m ≥ 1`: `τ_A(α,δ) ≤ τ_{n,m}(α,δ)`.
* `thmA_compare_half` (**declared strengthening**, not printed). Under the same hypotheses, `τ_A(α,δ/2) ≤ τ_{n,m}(α,δ)`. This is the comparison
  the "can replace" sentence needs, since the two-sided radius is `τ_A(α,δ/2)`. It implies `thmA_compare`.
* `tauA_scale` (**proof remark** "`τ_A(α,δ) = βτ_A(0,δ)`", plus two declared additions). For `κ, D ≥ 0`, `δ ∈ (0,1)` and `n, m ≥ 1`:
  * `τ_A(α,δ) = (1−α)⁻¹ τ_A(0,δ)` for every `α < 1`;
  * `τ_A(·,δ)` is nondecreasing on `[0,1)`;
  * `τ_A(·,δ) ≥ 0` on `[0,1)`.
* `ek_closed`: `e_k = C(k−1, ⌊(k−1)/2⌋) · 2^{1−k}` for `k ≥ 1`. In Lean, ℕ floor division is used, and `2^{1−k}` is a real `zpow`.
* `ek_le`: `e_k ≤ 1/√k` (`= k^{−1/2}`) for `k ≥ 1`.
* `ek_tendsto`: `e_k √k → √(2/π)` as `k → ∞`.

## Hypotheses used vs printed (declared)
* **(A1)–(A2)** are encoded as in the frozen `TrimmedMMD/Concentration` claims:
  * `H` is separable, which is (A2) exactly. It is used for the countable dense parameter set that makes the events measurable (the NOTE's
    "Measurability" remark);
  * `φ` is strongly measurable and bounded, which is what (A1)+(A2) give by Pettis;
  * (A3) is not assumed. This is a generalisation, since Theorem A does not use (A3).
* **`κ`, `D_φ`.** These are any bounds: `‖φ‖ ≤ κ` and `‖φ(x) − φ(x')‖ ≤ D`. The printed `κ = sup k(x,x)^{1/2}` and `D_φ = sup‖φ(x) − φ(x')‖` are
  themselves admissible, so the printed statement is the instance `κ = sup‖φ‖`, `D = D_φ`. This is a generalisation.
* **"every kernel" in the comparison** is rendered as "every `κ` and every `D ∈ [0,2κ]`". Every kernel with `k(x,x) ≤ κ²` has `D_φ ≤ 2κ`
  (`Wave30tp.kernel_consts`), and `D = 2κ` is always an admissible bound in `thmA`. This is a generalisation.
* **Quantifiers.** The NOTE reads "there are events `E⁺`, `E⁻`, not depending on `α`, … such that for every `α ∈ [0,1)` and every pair
  `(P,Q)`". The probabilities are taken under the pair, so the events must depend on it. The Lean claim reads: for every pair, `n, m`, `δ` and
  the constants, `∃ E⁺ E⁻, ∀ α`. This is the only sensible reading (see Remarks), and it is now the printed order of `thm:twosided` in the
  paper (`04_test.tex:108-110`, master `0c41fb5`).
* **"Hence … on `E⁺∩E⁻`"** refers to the events of Theorem A at level `δ/2`. The claim states those events and their probabilities
  (`≥ 1 − δ/2` each, `≥ 1 − δ` jointly) explicitly.
* **`tauA_scale`** adds two unprinted conjuncts: nonnegativity and monotonicity on `[0,1)`. Both are immediate from the scale identity. They
  are the properties of `τ_{n,m}` that the proofs of `thm:consistency` and `thm:rate` use.

## Encodings and junk-value audit
* **Division and powers.**
  * `1/n`, `1/m` and `e_n`, `e_m` have `n, m ≥ 1`.
  * `β = 1/(1−α)` has `α < 1`.
  * `ek k` (division by `k`) is used with `k ≥ 1`, except in the limit.
  * `(k − 1).choose ((k − 1)/2)` is ℕ subtraction under `k ≥ 1`, with floor division as printed.
  * `(2:ℝ) ^ ((1:ℤ) − k)` is a zpow of a nonzero base.
* **`√` and `log`.** `log(1/δ) ≥ 0`, `log(2/δ) ≥ 0` and `log(4/δ) > 0` for `δ ∈ (0,1)`. Every `√` argument is `≥ 0`.
* **`setDist` (`sInf`).** The regions are nonempty (`g ≡ 1` is admissible; `P_n`, `Q_m` are probability measures for `n, m ≥ 1`). Distances are
  `≥ 0`, so the infimum is genuine, never `sInf ∅`.
* **`ofReal`.** `ofReal(1 − δ)` and `ofReal(1 − δ/2)` are taken with `δ ∈ (0,1)`.
* **Events.** Each event is **measurable**, with probability `≥ 1 − δ` under `sampleLaw` (the convention of `TrimmedMMD/Unconditional`).
* **No `Measure.map`** occurs in any statement.
* **Bochner integrals.** The region integrals `∫ g • φ dP` are genuine: `g` is measurable with `0 ≤ g ≤ β`, `φ` is strongly measurable and
  bounded, and the measures are finite.
* **`iSup`.** The only supremum is `tvDist P Q = ⨆_A |P(A) − Q(A)|`, in the `H_{0,α}` clause of `thmA`. It is genuine: the index set of
  measurable sets is nonempty (`∅`), and the values lie in `[0,1]` for probability measures.
* **Vacuity: none.** `𝒳 = ℝ`, `H = ℝ`, `φ = tanh`, `κ = 1`, `D = 2`, `P = Q = N(0,1)`, `δ = 1/2` and `n = m = 1` satisfy every hypothesis set. For
  the comparison, any `κ ≥ 0` and `D = 2κ`.

## Not covered (declared)
* **"which can replace `τ_{n,m}(α,δ)` in the proofs of `thm:consistency`, `thm:rate`, `cor:confset`, `cor:upperfs`".** This is a statement about
  proofs of the revised paper, and should be frozen when that text exists (the form of `α̂` there, `τ_A` or `τ_new`, is not yet fixed). Its
  ingredients are covered:
  * `thmA_twosided`, whose event shape matches the hypotheses of the frozen conditional `TrimmedMMD.consistency_i`, `consistency_ii` and
    `rate`;
  * `thmA_compare_half`;
  * `tauA_scale`.

  The further properties those proofs use (`τ_A → 0` as `n, m → ∞`; `τ_A → ∞` as `α → 1` for `κ > 0`) belong to that sentence.
* **Proof-internal steps** are not frozen as claims: the reduction to the supremum `Z`, the bound `E Z ≤ 2κ√s + 2κ(e_n+e_m)`, the McDiarmid
  step, and the intermediate equality `E sup_{f,t,t'}[…] = E‖…‖ + κ(e_n + e_m)` of Step 2. They are proved below as route lemmas
  (`setDist_region_le`, `integral_iSup_jdev_le`, `prob_event`), with the `≤` that the proof uses.
* **The "Gain" paragraph** (`:200-207`) and every numerical claim (`8.47β/√n`, `9.48`, `13.92`, `10.29`, the factor `0.37`, the table values).

## Proof route (untrusted)
* **Step 1** (`RouteDet.setDist_region_le`, deterministic). Take any "source" pair `P₁, Q₁` and "target" pair `P₂, Q₂` of probability
  measures. If `(P₂−P₁)(⟨−f,φ⟩−q)₊ + (Q₂−Q₁)(⟨f,φ⟩−q')₊ ≤ S` for all `‖f‖ ≤ 1` and `|q|, |q'| ≤ κ`, then
  `dist(𝒞_α(P₁),𝒞_α(Q₁)) ≤ dist(𝒞_α(P₂),𝒞_α(Q₂)) + βS`.
  * The direction `f` comes from projecting `0` onto `closure(𝒞_α(P₁) − 𝒞_α(Q₁))`. This uses no attainment or weak compactness (the NOTE
    invokes `lem:separation`'s attainment).
  * The support functions are attained at the certified CVaR witnesses (`Concentration.exists_cvar_witness`, `q ∈ [−κ, κ]`). The target bounds
    are `Concentration.integral_mul_le_cvar`.
  * Applied with (source, target) = (empirical, population), this gives (a); with the roles exchanged, it gives (b). So one lemma serves both
    sides.
* **Measurability.** `θ = (f,t,t')` ranges over a countable dense subset of `{‖f‖ ≤ 1, |t|, |t'| ≤ κ}`, which exists because `H` is separable.
  `θ ↦` the deviation is continuous (`continuous_empDev_tm`), so the bound extends to all `θ` (`jdev_le_of_iSup`).
* **Step 2** (`RouteEvents.integral_iSup_jdev_le`, `radAvg2_le`). Two-sample symmetrisation (new library, below), then coordinatewise
  contraction over `Fin n ⊕ Fin m` with the maps `u ↦ ±u₊`, then:
  * `sup_f ⟨f,v⟩ ≤ ‖v‖` and `sup_t(−tS) ≤ κ|S|`;
  * `E_σ‖Σ σ_k u_k‖ ≤ √Σ‖u_k‖² ≤ κ√s`;
  * `E_σ|σ_1+⋯+σ_n| = n e_n`, as the marginal of the joint sign vector.
* **Step 3** (`RouteEvents.prob_event`). The certified-library two-sample McDiarmid (`Wave30tp.mcdiarmid_two_sample`) with differences `D/n` and
  `D/m`. The case `D = 0` (constant `φ`, deviation `≡ 0`) is handled separately.
* **"in particular"**: `TV ≤ α ⇒ D_α = 0`, by the certified `ZeroSet.zero_of_tv_le`. **"Hence"**: the certified union bound
  `TrimmedMMD.event_prob`.
* **Constants.**
  * `ek_le` is Jensen (`radE_abs_sum_rsign_le`).
  * `thmA_compare` and `_half` follow the NOTE's Comparison paragraph: `√s ≤ n^{−1/2} + m^{−1/2}`, `e_k ≤ k^{−1/2}`, and
    `D√(sL/2) ≤ κ√(2 log(4/δ))√s`.
  * `ek_closed` (`RouteEk`):
    * sign vectors are matched with subsets;
    * then `Σ_σ|Σσ_i| = Σ_r C(k,r)|2r−k|`;
    * then the telescoping identity `Σ_{r≤m}(k+1−2r)C(k+1,r) = (k+1)C(k,m)`.
  * `ek_tendsto`:
    * `e_{2j+1} = e_{2j} = C(2j,j)/4^j`;
    * Wallis' product in factorial form gives `(C(2j,j)/4^j)²(2j+1) = 1/W_j → 2/π`;
    * the even and odd subsequences are then combined.
* **New library lemmas** (`StatFormal/Lib/Concentration/`):
  * `ContractionCoord.lean`. Sign averages `signE` over an arbitrary finite index type, and:
    * **`signE_iSup_contraction`**, the coordinatewise contraction principle for signed Rademacher averages of an arbitrary bounded set of
      vectors, with coordinate-specific 1-Lipschitz maps (Shalev-Shwartz and Ben-David 2014, Lemma 26.9; Mohri et al. 2018, Lemma 5.7);
    * `signE_iSup_contraction_lip`, the version with Lipschitz constants `L_i`;
    * Khintchine-type second moments (`signE_rsign_mul`, `sq_signE_le`, `signE_norm_sum_le`);
    * marginals over `ι ⊕ ι'` (`signE_comp_inl`, `signE_comp_inr`);
    * `signE_eq_radE`.
  * `Symmetrization2.lean`:
    * **`integral_iSup_sumDev_le`**, symmetrisation for independent, non-identically distributed summands with coordinate-specific classes
      under `Measure.pi μ` (the ghost-sample swap is done per coordinate on `Π_i μ_i ⊗ μ_i`);
    * **`integral_iSup_empDev2_le`**, the two-sample form with one joint supremum and one sign vector on `Fin n ⊕ Fin m`, via
      `measurePreserving_sumPiEquivProdPi`.

  Both generalise the one-sample `Rademacher.lean` and `Symmetrization.lean`, which are left untouched.
* **Reused certified claims**: `TrimmedMMD.ZeroSet.zero_of_tv_le`, `TrimmedMMD.event_prob`. **Reused route lemmas**: `TrimmedMMD/Concentration`
  (`Region`, `integral_empirical`), `TrimmedClass` (`gTM`, `continuous_empDev_tm`), `Wave30tp` (`mcdiarmid_two_sample`, `sNM_pos`, `beta_mono`).

## Remarks on the printed text (NOTE §2; status in the paper at master `0c41fb5`)
No statement of §2 is false. Suggested wording fixes:
1. **Quantifier placement (NOTE `:121-123`).** "there are events … such that for every `α` and every pair `(P,Q)`" places the pair inside the
   `∃`. Suggested: "For every pair `(P,Q)`, all `n, m ≥ 1` and `δ ∈ (0,1)`, there are events `E^±` (depending on `P, Q, n, m, δ` and the
   kernel, not on `α`) … such that for every `α ∈ [0,1)`: …". **Fixed in the paper** (`04_test.tex:108-110`).
2. **"Hence … on `E⁺∩E⁻`" (NOTE `:127-128`)** reuses the names for the events at level `δ/2`. Suggested: `E⁺_{δ/2} ∩ E⁻_{δ/2}`. The paper has
   no such sentence. It uses `E⁺` and `E⁻` separately, so the remark applies only to the NOTE.
3. **"Moreover" (NOTE `:130`; paper `eq:tauA`)** compares `τ_A(α,δ)` with `r_n(α,δ/2) + r_m(α,δ/2)`. A two-sided use at one event of
   probability `≥ 1 − δ` runs both events at `δ/2` and so needs `τ_A(α,δ/2) ≤ r_n(α,δ/2) + r_m(α,δ/2)`. That inequality holds (certified as
   `thmA_compare_half`) and could be stated wherever the paper replaces the old two-sided radius.
4. **Step 3, `D_φ = 0`** (NOTE `:191`; paper `A_basic.tex:379`). McDiarmid's exponent is then `0/0`. The case is trivial (`φ` constant,
   `Z ≡ 0`), but the proof should say so. **Still open in the paper.**
5. **Step 1.** The NOTE uses attainment in `lem:separation` (weakly compact regions) for `D_α = sup_f sep(f)`. The paper's Step 1 now
   states the attained and zero cases explicitly (`A_basic.tex:348-350`). Attainment is not needed: projecting onto the closure of
   `𝒞_α(P) − 𝒞_α(Q)` gives the equality for any nonempty convex sets. This is the route certified here.
6. **Gain (NOTE `:200-201`, outside the frozen scope).** "`= 8.47β/√n`" treats the limit `e_n√n → √(2/π)` as an equality. `e_n√n` lies above
   `√(2/π)` for odd `n` and below it for even `n`. At `n = 300` the exact value is `8.465`. **Fixed in the paper**, which writes
   `τ^A ≈ 8.5 βκ/√n` (`04_test.tex:127-128`).
7. **Cosmetic, frozen file.** The docstring of `thmA_twosided` says "the events of Theorem A at level `δ/2`", whereas the Prop is a plain
   existential over events with the stated probabilities. It is harmless: the certified content is the conclusion.
