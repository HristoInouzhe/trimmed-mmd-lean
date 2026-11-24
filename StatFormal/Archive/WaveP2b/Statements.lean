import StatFormal.Archive.OTFD.Wave1.Statements
import StatFormal.Archive.OTFD.Wave8c.Statements
import StatFormal.Archive.OTFD.Wave13a.Statements
import StatFormal.Archive.Wave24d.Statements
import StatFormal.Archive.OTFD.Wave8b.Statements
import StatFormal.Archive.Wave24e.Statements
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Def
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.CovarianceBilin

/-!
# FROZEN STATEMENTS — wave P2b (PARTIAL_AUDIT group 2c, GAUSSH): Gaussian laws on `H` — otfd A `lem:app-references-Pl`
# (i), (iii); A `cor:ghs-tukey-degeneracy` (ball law); A `cor:convergent-references` examples (ii)–(iv);
# B `lem:refs-ac` (ball reference); B `lem:interior-levels` (ball reference)

Sources (CURRENT text, `otfd/papers`, commit 0d24adf1 of 2026-10-16):
* A `lem:app-references-Pl` (`A_sieves/supplement.tex:995-1015`, proof `:1017-1059`), with
  `def:app-lipschitz-hypersurface` (`:931-943`; `𝒫^ℓ(H)` with the paper's second-moment clause) and `lem:app-block-Pl`
  (`:945-955`, frozen Wave 20a).
* A `cor:ghs-tukey-degeneracy` (`A_sieves/supplement.tex:353-368`, proof `:789-843`), with `TD_H` (`:330-333`, frozen
  `OTFD/Wave13a` `tukeyDepthH`).
* A `cor:convergent-references` (`A_sieves/supplement.tex:5180-5224`), examples (ii)–(iv) of the hypothesis of (a).
* B `lem:refs-ac` (`B_bands/supplement.tex:485-490`, proof `:492-506`) and B `lem:interior-levels`
  (`B_bands/supplement.tex:935-943`), with `prop:calibrations`(b) (`B_bands/main.tex:518`; `c_K` the frozen Wave 24d
  `ballCdf`) and `τ_{K,p} = c_K⁻¹(p)`, `A_{K,p} = {g_K ≤ τ_{K,p}}` (`B_bands/main.tex:633-636`).
Imports the frozen `OTFD/Wave1` (`IsLipHyp`, `PellClass`, `truncK`), `OTFD/Wave8c` (`unifRadius`, `unifSym`, `mnorm`),
`OTFD/Wave8b` (`embed`), `OTFD/Wave13a` (`tukeyDepthH`), `Wave24d` (`ballCdf`) and `Wave24e` (`cubicLawH`) statements,
not copied; Mathlib (`HasGaussianLaw`, `covarianceBilin`, `gaussianReal`) otherwise.

Covered:
* A refs-Pl (i) `refs_Pl_gaussian`: a Gaussian random element `ζ` of `H` (any mean) with injective covariance operator
  gives mass `0` to every Lipschitz hypersurface, and `𝓛(ζ) ∈ 𝒫^ℓ(H)`. (iii) `refs_Pl_ball`: `μ^ball = 𝓛(Rζ/‖ζ‖) ∈
  𝒫^ℓ(H)`. ((ii) and the necessity claims are the certified Wave 24d `refs_Pl_*`; "consequently `μ_K ∈ 𝒫^ℓ(ℝ^K)`" is
  the certified `lem:app-pullback`.)
* A ghs-tukey, ball law: `ghs_ball_center` (`TD_H(0; μ^ball) = ½`), `ghs_ball_ae_zero` (`TD_H = 0` `μ^ball`-a.e.),
  `ghs_ball_shell` (every shell `‖u‖ = r ∈ (0,1]` has a zero-depth point).
* A convergent references: (ii) `convref_fresh_ball`, (iii) `convref_radius`, (iv) `convref_boxes` (each: `ι_K#ν_K`
  converges weakly to the stated limit).
* B refs-ac, ball: `refs_ac_ball` (`L_K⁻¹#𝓛(Ũ)` absolutely continuous and boundedly supported; `c_K` continuous).
* B interior-levels, ball: `interior_levels_ball` (`τ_{K,p}` well defined, `< 1`; `A_{K,p} ⊂ int 𝒰_K`).

Not covered (declared):
* A ghs-tukey: the breakdown consequence (it is the frozen `thm:sieve-breakdown` limit `eq:coherent-breakdown-limit`
  composed with `ghs_ball_ae_zero`; a claim would be bookkeeping); the a.e. and shell clauses are stated in
  Karhunen–Loève form only (see Encodings).
* A convergent references (iii): "which is `μ^ball` when `R' ∼ Unif(0,1)`" (the limit is stated as the image of
  `ρ ⊗ 𝓛(ζ)`; for `ρ = unifRadius` this is `μ^ball` by independence).
* B refs-ac: the naive law (already certified in OTFD Wave 8c, `B lem:naive-law`: `naive_density` gives `≪ Leb`,
  `naive_norm_law` the bounded support, `naive_calibration` `c_K(τ) = τ`) and the case `dim H = K` (here `H` carries a
  Hilbert basis indexed by `ℕ`). The cubic clauses are certified (Wave 24e `refs_ac_cubic_cK`, OTFD Wave 22b
  `cubic_density`).
* C `lem:conditional-weights` (a.s. version), listed in group 2c, is NOT attempted: its blocker is a conditional
  exponential concentration for weighted empirical measures and a `W₁` uniformity argument, not a Gaussian law on `H`.

Encodings (to be checked by the critic):
* `H` a real separable Hilbert space (`CompleteSpace`, `SecondCountableTopology`, Borel). "Gaussian random element with
  mean `m`" is Mathlib `HasGaussianLaw ζ P` (every continuous linear functional has a real Gaussian law); the mean is
  unnamed; "centred" is `∫ ζ dP = 0` (Bochner; `ζ` integrable by Fernique, no junk). The covariance operator `C` enters
  through `⟪Cx, y⟫ = covarianceBilin 𝓛(ζ) x y` (centred covariance; genuine since a Gaussian law has a second moment);
  "`C` injective" is `Function.Injective (covarianceBilin 𝓛(ζ))` (`x ↦ ⟪Cx,·⟫` injective ⇔ `C` injective, Riesz). The
  remarks "trace class, eigenvalues `ς_k > 0`, `Σ ς_k < ∞`" are consequences, not hypotheses.
* `R ∼ Unif(0,1)` is `P.map R = unifRadius` (frozen, `Leb|_(0,1]`), `R` measurable; independence `IndepFun R ζ P`;
  `μ^ball = P.map (ω ↦ (R ω/‖ζ ω‖) • ζ ω)` exactly as in the frozen Wave 24d `refs_Pl_ball_degenerate` (junk `0` only on
  the null set `{ζ = 0}`); `ζ` measurable where a `Measure.map` of `ζ`-functionals appears (genuine maps).
* Lipschitz hypersurfaces, `𝒫^ℓ(H)`: frozen `IsLipHyp`, `PellClass`; `TD_H`: frozen `tukeyDepthH` (`[0,∞]`-valued `⨅`
  over `v ≠ 0`, hence `[Nontrivial H]` in `ghs_ball_center`; a Hilbert basis indexed by `ℕ` gives it elsewhere).
* Generalisations: (iii) and `ghs_ball_center` do not assume `m = 0`, resp. independence of `R` and `ζ` (unused);
  `refs_ac_ball` allows any invertible `L_K` (paper: `L_KᵀL_K = M_K`); `convref_boxes` drops `λ_k^{(K)} ≥ 0` (the law
  of `λV` is symmetric in the sign of `λ`) and needs only `λ ∈ ℓ²` (the definition of `μ^cub`).
* `ghs_ball_ae_zero`, `ghs_ball_shell` (CONDITIONALISATION on the Karhunen–Loève form, as in the paper's proof, which
  diagonalises `C`): `ζ` in Karhunen–Loève form `KLBall` — `(f_k)` any Hilbert basis (the eigenbasis, not the sieve
  basis), `⟪f_k, ζ⟫ = √ς_k ξ_k` a.s., `ξ_k` i.i.d. `N(0,1)`, `ς_k > 0`, `Σ ς_k < ∞`. Every centred Gaussian with
  injective covariance has this form, so the premise is no mathematical restriction; it is a Lean-level conditional:
  Mathlib has the spectral theorem for compact self-adjoint operators
  (`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`, `finite_dimensional_eigenspace`), but not the
  compactness (trace class) of a Gaussian covariance operator nor the assembly of an `ℕ`-indexed eigenbasis with
  i.i.d. standardised coordinates. (An eigenbasis-free discharge also exists: Gram–Schmidt for the covariance form on a
  linearly independent sequence gives `v_k` with `⟪Cv_k, v_l⟫ = δ_kl`, so `⟪v_k, ζ⟫` are i.i.d. `N(0,1)`, which
  suffices for the strong-law + Chebyshev argument.) Conversely every `KLBall` `ζ` is a centred Gaussian with injective
  covariance. Radial shells of the ball law are `{‖u‖_H = r}`, `r ∈ (0,1]` (its radial calibration is the norm).
* Weak convergence in `H` (A convergent references) is `∫ f dι_K#ν_K → ∫ f dμ` for every bounded continuous `f`, as in
  the frozen Wave 23b `convref_coherent`; `Π_K = truncK b`, `ι_K = embed b` for the sieve Hilbert basis `b`. (ii)
  `ν_K = 𝓛(R Π_Kζ/‖Π_Kζ‖)` (junk `0` only on the null set `Π_Kζ = 0`). (iii) `R_K ∈ [0,1]` a.s., `R_K ⫫ ζ`, `𝓛(R_K) ⇀
  ρ` (against bounded continuous functions on `ℝ`), limit `(ρ ⊗ 𝓛(ζ))` pushed by `(r, z) ↦ (r/‖z‖) z`. (iv)
  `Unif(−a/2, a/2)` is `(unifSym ½).map (a · ·)` (the frozen `unifSym (1/2)` is `Unif[−½,½]`; for `a = 0` this is
  `δ₀`, not a junk `0`), `ν_K` the product on `ℝ^K` (`Measure.pi`, then `toLp`), `μ^cub` the frozen `cubicLawH`.
* B: `Ũ = R Π_Kζ/‖ζ‖` (`= RY/(‖Y‖² + W)^{1/2}` of the paper when `C` is diagonal in the sieve basis; the statement does
  not assume that), `ℝ^K = EuclideanSpace ℝ (Fin K)` with `volume`; "boundedly supported" is `∃ M, ν(B̄(0,M)ᶜ) = 0`;
  `c_K` is `ballCdf` (`= μ_K(‖·‖_{M_K} ≤ τ)` when `L_KᵀL_K = M_K`). `interior_levels_ball`: "`τ_{K,p} = c_K⁻¹(p)` well
  defined" is `∃! τ ≥ 0, c_K(τ) = p`; `𝒰_K = {‖u‖_M ≤ 1}` and `A_{K,p} = {‖u‖_M ≤ τ_{K,p}}` as in the frozen Wave 17a
  `interior_levels_naive` (any matrix `M`); `p = 1 − δ ∈ (0,1)`, `K ≥ 1`.

Critic notes:
* (i) does not follow the paper's eigenbasis + block-criterion argument (no eigenbasis is available in Lean). It conditions
  on one Gaussian coordinate: the range of `C` is dense (`ker C = 0`), so it contains a direction `u = Cv` transversal
  to the hypersurface; `Y = ⟪v, ζ⟫` and `W = ζ − (Y/⟪Cv,v⟫)u` are jointly Gaussian and uncorrelated, hence independent
  (Mathlib `HasGaussianLaw.indepFun_of_covariance_inner`), each line `W + tu` meets the hypersurface at most once, and
  `𝓛(Y)` is atomless. (iii), `refs_ac_ball` and the zero-depth clauses follow the papers' Tonelli/Chebyshev arguments;
  `refs_ac_ball` needs no diagonalisation (rays `{s y}` of a Lebesgue-null set are a.e. null, by `Leb(s⁻¹N) = 0`), and
  `𝓛(Π_Kζ) ≪ Leb` uses the untrusted Foundations `ChiSquare/Whitening`. Certified results reused in routes: Wave 24d
  `calib_ball_cont` (premise `P(Π_Kζ = 0) = 0` discharged by (i)), OTFD Wave 22b `cK_shape`, Wave 17a
  `interior_levels_naive`, Wave 24e strong-law lemma (`ae_not_summable_sq`) and cubic-law lemmas.
* Observations on the papers. (1) A `lem:app-references-Pl`(iii) "with `m = 0`" is not needed (`sζ` is Gaussian with
  mean `sm` and covariance `s²C`, and (i) holds for any mean); cosmetic. (2) A `cor:ghs-tukey-degeneracy`'s centre
  claim needs only `R > 0` a.s. (`⟪v, U⟫ ≤ 0 ⇔ ⟪v, ζ⟫ ≤ 0`), not independence; cosmetic. (3) The proof of
  `cor:ghs-tukey-degeneracy` writes the eigen-expansion in the sieve basis ("diagonalize the Gaussian covariance as in
  `subsec:pullback`", `d = Σ_k d_k e_k`, `v_m = −Σ_{k≤m}(d_k/ς_k)e_k`), but `subsec:pullback` diagonalises only "if
  the basis `(e_k)` diagonalizes `C`"; since `TD_H` is basis-free the argument holds verbatim in an eigenbasis `(f_k)`;
  minor (notation). Fix: write `f_k` for `e_k` there. (4) B `lem:refs-ac` is printed in general ("the reshaped ball
  law `L_K⁻¹#𝓛(Ũ)` of `prop:calibrations`(b) … boundedly supported and absolutely continuous on `ℝ^K`, and their CDFs
  `c_K` are continuous", with `Ũ = RΠ_Kζ/‖ζ‖_H` for any injective trace-class `C`), but its proof takes
  "`Ũ = RY/(‖Y‖² + W)^{1/2}` with `Y := (√λ_kZ_k)_{k≤K}` … `W := Σ_{j>K}λ_jZ_j²`; `R`, `Y` and `W` are independent",
  valid only when `C` is diagonal in the sieve basis, against A's "no diagonalization of `C` in the sieve basis". The
  statement is right (`refs_ac_ball`), only the proof is over-specific; minor (proof gap). Fix: `𝓛(Π_Kζ)` is a
  nondegenerate Gaussian on `ℝ^K` (`⟪C Σa_ke_k, Σa_ke_k⟫ > 0` for `a ≠ 0`), and for Lebesgue-null `N`, Tonelli in `R`
  and `r = s‖ζ‖` give `P(Ũ ∈ N) ≤ E[‖ζ‖ Leb{s > 0 : sΠ_Kζ ∈ N}] = 0`, as in A `lem:app-references-Pl`(iii); also
  `λ_k` there clashes with the cubic widths (A writes `ς_k`).

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal InnerProductSpace RealInnerProductSpace BoundedContinuousFunction Topology

namespace StatFormal.WaveP2b

/-- The ball law in Karhunen–Loève form: `(f_k)` an orthonormal (eigen)basis of `H`, `ς_k > 0`, `Σ ς_k < ∞`,
`⟪f_k, ζ⟫ = √ς_k ξ_k` a.s. with `ξ_k` i.i.d. `N(0,1)`, `R ∼ Unif(0,1]` independent of `ζ`. -/
def KLBall {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (f : HilbertBasis ℕ ℝ H) (ς : ℕ → ℝ) (ξ : ℕ → Ω → ℝ) (ζ : Ω → H)
    (R : Ω → ℝ) : Prop :=
  IsProbabilityMeasure P ∧ (∀ k, 0 < ς k) ∧ Summable ς ∧ (∀ k, Measurable (ξ k)) ∧ iIndepFun ξ P ∧
    (∀ k, P.map (ξ k) = gaussianReal 0 1) ∧ Measurable ζ ∧
    (∀ᵐ ω ∂P, ∀ k, ⟪f k, ζ ω⟫_ℝ = Real.sqrt (ς k) * ξ k ω) ∧ Measurable R ∧ P.map R = StatFormal.OTFD.Wave8c.unifRadius ∧
    IndepFun R ζ P

namespace Claims

open StatFormal.OTFD.Wave1 (IsLipHyp PellClass)
open StatFormal.OTFD.Wave8c (unifRadius)

/-- (i) A Gaussian random element `ζ` of `H` (any mean) with injective covariance operator charges no Lipschitz
hypersurface, and `𝓛(ζ) ∈ 𝒫^ℓ(H)`. -/
def refs_Pl_gaussian : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (ζ : Ω → H),
    HasGaussianLaw ζ P → Function.Injective (covarianceBilin (P.map ζ)) →
      (∀ S : Set H, IsLipHyp S → P {ω | ζ ω ∈ S} = 0) ∧ PellClass (P.map ζ)

/-- (iii) The ball law: with `ζ` as in (i) and `R ∼ Unif(0,1]` independent of `ζ`,
`μ^ball = 𝓛(Rζ/‖ζ‖) ∈ 𝒫^ℓ(H)`. -/
def refs_Pl_ball : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (ζ : Ω → H) (R : Ω → ℝ),
    HasGaussianLaw ζ P → Function.Injective (covarianceBilin (P.map ζ)) → Measurable ζ → Measurable R →
      P.map R = unifRadius → IndepFun R ζ P →
        PellClass (P.map fun ω => (R ω / ‖ζ ω‖) • ζ ω)

/-- `cor:ghs-tukey-degeneracy`, ball law, the centre: `TD_H(0; μ^ball) = 1/2` (`ζ` centred Gaussian with injective
covariance, `R ∼ Unif(0,1]`; independence of `R` and `ζ` is not needed). -/
def ghs_ball_center : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] [Nontrivial H] (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (ζ : Ω → H)
    (R : Ω → ℝ),
    HasGaussianLaw ζ P → Function.Injective (covarianceBilin (P.map ζ)) → ∫ ω, ζ ω ∂P = 0 → Measurable ζ →
      Measurable R → P.map R = unifRadius →
        StatFormal.OTFD.Wave13a.tukeyDepthH (P.map fun ω => (R ω / ‖ζ ω‖) • ζ ω) 0 = 1 / 2

/-- B `lem:interior-levels`, ball reference: with `c_K(τ) = P(R‖Π_Kζ‖/‖ζ‖ ≤ τ)` (the frozen Wave 24d `ballCdf`,
`prop:calibrations`(b)), for every level `p = 1 − δ ∈ (0,1)` and `K ≥ 1` the calibrated radius
`τ_{K,p} = c_K⁻¹(p)` is well defined (a unique `τ ≥ 0` with `c_K(τ) = p`), `τ_{K,p} < 1`, and
`A_{K,p} = {‖u‖_M ≤ τ_{K,p}}` lies in the interior of `𝒰_K = {‖u‖_M ≤ 1}`. -/
def interior_levels_ball : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (e : HilbertBasis ℕ ℝ H)
    (ζ : Ω → H) (R : Ω → ℝ) (K : ℕ) (M : Matrix (Fin K) (Fin K) ℝ) (p : ℝ),
    HasGaussianLaw ζ P → Function.Injective (covarianceBilin (P.map ζ)) → Measurable ζ → Measurable R →
      P.map R = unifRadius → IndepFun R ζ P → 1 ≤ K → 0 < p → p < 1 →
        (∃! τ : ℝ, 0 ≤ τ ∧ StatFormal.Wave24d.ballCdf P R ζ e K τ = p) ∧
          ∀ τ : ℝ, 0 ≤ τ → StatFormal.Wave24d.ballCdf P R ζ e K τ = p →
            τ < 1 ∧ {u | StatFormal.OTFD.Wave8c.mnorm M u ≤ τ} ⊆
              interior {u | StatFormal.OTFD.Wave8c.mnorm M u ≤ 1}

/-- A `cor:convergent-references`, example (ii): the fresh-denominator ball law
`ν_K = 𝓛(R Π_Kζ/‖Π_Kζ‖_{ℝ^K})` (`ζ`, `R` as in (iii)) satisfies the hypothesis of (a): `ι_K#ν_K ⇀ μ^ball` weakly in `H`
(the sieve basis a Hilbert basis `b`, `Π_K = truncK`, `ι_K = embed`; weak convergence against bounded continuous
`f`, as in the frozen Wave 23b `convref_coherent`). -/
def convref_fresh_ball : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (b : HilbertBasis ℕ ℝ H)
    (ζ : Ω → H) (R : Ω → ℝ),
    HasGaussianLaw ζ P → Function.Injective (covarianceBilin (P.map ζ)) → Measurable ζ → Measurable R →
      P.map R = unifRadius → IndepFun R ζ P →
        ∀ f : H →ᵇ ℝ, Tendsto (fun K => ∫ x, f x ∂((P.map fun ω =>
            (R ω / ‖StatFormal.OTFD.Wave1.truncK (fun k => b k) K (ζ ω)‖) •
              StatFormal.OTFD.Wave1.truncK (fun k => b k) K (ζ ω)).map
              (StatFormal.OTFD.Wave8b.embed (fun k => b k) K)))
          atTop (𝓝 (∫ x, f x ∂(P.map fun ω => (R ω / ‖ζ ω‖) • ζ ω)))

/-- A `cor:convergent-references`, example (iii): radius-perturbed truncations `ν_K = 𝓛(R_K Π_Kζ/‖ζ‖_H)`, `R_K ∈ [0,1]`
independent of `ζ` (`ζ` as in (i)), `𝓛(R_K) ⇀ ρ = 𝓛(R')`: `ι_K#ν_K ⇀ 𝓛(R'ζ/‖ζ‖)` with `R' ∼ ρ` independent of `ζ`,
i.e. the image of `ρ ⊗ 𝓛(ζ)` under `(r, z) ↦ (r/‖z‖) z`. -/
def convref_radius : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (b : HilbertBasis ℕ ℝ H)
    (ζ : Ω → H) (RK : ℕ → Ω → ℝ) (ρ : Measure ℝ) [IsProbabilityMeasure ρ],
    HasGaussianLaw ζ P → Function.Injective (covarianceBilin (P.map ζ)) → Measurable ζ →
      (∀ K, Measurable (RK K)) → (∀ K, ∀ᵐ ω ∂P, RK K ω ∈ Icc (0 : ℝ) 1) → (∀ K, IndepFun (RK K) ζ P) →
      (∀ g : ℝ →ᵇ ℝ, Tendsto (fun K => ∫ r, g r ∂(P.map (RK K))) atTop (𝓝 (∫ r, g r ∂ρ))) →
        ∀ f : H →ᵇ ℝ, Tendsto (fun K => ∫ x, f x ∂((P.map fun ω =>
            (RK K ω / ‖ζ ω‖) • StatFormal.OTFD.Wave1.truncK (fun k => b k) K (ζ ω)).map
              (StatFormal.OTFD.Wave8b.embed (fun k => b k) K)))
          atTop (𝓝 (∫ x, f x ∂((ρ.prod (P.map ζ)).map fun p : ℝ × H => (p.1 / ‖p.2‖) • p.2)))

/-- A `cor:convergent-references`, example (iv): perturbed boxes `ν_K = ⊗_{k<K} Unif(−λ_k^{(K)}/2, λ_k^{(K)}/2)` (the law of
`λ_k^{(K)} V`, `V ∼ Unif(−½, ½)` the frozen `unifSym (1/2)`; for `λ_k^{(K)} = 0` the point mass at `0`) with
`Σ_{k<K} (λ_k^{(K)} − λ_k)² → 0` and `λ ∈ ℓ²`: `ι_K#ν_K ⇀ μ^cub` (the frozen Wave 24e `cubicLawH`). -/
def convref_boxes : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (e : HilbertBasis ℕ ℝ H) (lam : ℕ → ℝ) (lamK : ∀ K : ℕ, Fin K → ℝ),
    Summable (fun k => lam k ^ 2) →
      Tendsto (fun K => ∑ k : Fin K, (lamK K k - lam k) ^ 2) atTop (𝓝 0) →
        ∀ f : H →ᵇ ℝ, Tendsto (fun K => ∫ x, f x ∂(((Measure.pi fun k : Fin K =>
            (StatFormal.OTFD.Wave8c.unifSym (1 / 2)).map (fun v => lamK K k * v)).map (WithLp.toLp 2)).map
              (StatFormal.OTFD.Wave8b.embed (fun k => e k) K)))
          atTop (𝓝 (∫ x, f x ∂(StatFormal.Wave24e.cubicLawH e lam)))

/-- B `lem:refs-ac`, ball reference: the reshaped ball law `L_K⁻¹#𝓛(Ũ)`, `Ũ = R Π_Kζ/‖ζ‖` (`ζ` centred Gaussian
with injective covariance, `R ∼ Unif(0,1]` independent of `ζ`, `K ≥ 1`, `L_K` any invertible linear map of `ℝ^K`), is
absolutely continuous and boundedly supported on `ℝ^K`, and its CDF `c_K` (the frozen Wave 24d `ballCdf`) is
continuous. -/
def refs_ac_ball : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (e : HilbertBasis ℕ ℝ H)
    (ζ : Ω → H) (R : Ω → ℝ) (K : ℕ) (L : EuclideanSpace ℝ (Fin K) ≃L[ℝ] EuclideanSpace ℝ (Fin K)),
    HasGaussianLaw ζ P → Function.Injective (covarianceBilin (P.map ζ)) → ∫ ω, ζ ω ∂P = 0 → Measurable ζ →
      Measurable R → P.map R = unifRadius → IndepFun R ζ P → 1 ≤ K →
        (P.map fun ω => L.symm ((R ω / ‖ζ ω‖) • StatFormal.OTFD.Wave1.truncK e K (ζ ω))) ≪ volume ∧
          (∃ M : ℝ, (P.map fun ω => L.symm ((R ω / ‖ζ ω‖) • StatFormal.OTFD.Wave1.truncK e K (ζ ω)))
            (Metric.closedBall 0 M)ᶜ = 0) ∧
          Continuous (StatFormal.Wave24d.ballCdf P R ζ e K)

/-- `cor:ghs-tukey-degeneracy`, ball law (Karhunen–Loève form): `TD_H(u; μ^ball) = 0` for `μ^ball`-almost every
`u`. -/
def ghs_ball_ae_zero : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (f : HilbertBasis ℕ ℝ H)
    (ς : ℕ → ℝ) (ξ : ℕ → Ω → ℝ) (ζ : Ω → H) (R : Ω → ℝ),
    KLBall P f ς ξ ζ R →
      ∀ᵐ u ∂(P.map fun ω => (R ω / ‖ζ ω‖) • ζ ω),
        StatFormal.OTFD.Wave13a.tukeyDepthH (P.map fun ω => (R ω / ‖ζ ω‖) • ζ ω) u = 0

/-- `cor:ghs-tukey-degeneracy`, ball law (Karhunen–Loève form): every noncentral radial shell `{‖u‖_H = r}`,
`r ∈ (0,1]`, contains a point of Hilbert Tukey depth `0`. -/
def ghs_ball_shell : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (f : HilbertBasis ℕ ℝ H)
    (ς : ℕ → ℝ) (ξ : ℕ → Ω → ℝ) (ζ : Ω → H) (R : Ω → ℝ),
    KLBall P f ς ξ ζ R → ∀ r ∈ Ioc (0 : ℝ) 1, ∃ u : H, ‖u‖ = r ∧
      StatFormal.OTFD.Wave13a.tukeyDepthH (P.map fun ω => (R ω / ‖ζ ω‖) • ζ ω) u = 0

end Claims

end StatFormal.WaveP2b
