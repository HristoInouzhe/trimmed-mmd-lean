import StatFormal.Archive.OTFD.Bands.Statements
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# FROZEN STATEMENTS — otfd paper B: inner band, solver sandwich, guarantee, saturation caps

Sources (verbatim in `inventory/extracted/otfd-B_bands.md`):
* `prop:band-inner-certificate` (`papers/B_bands/main.tex:766`), inner edge and exactness diagnostic;
* `cor:ext-solver-certified` (`papers/B_bands/supplement.tex:4821`), sandwich for the band of the exact potential;
* `prop:band-guarantee` (`supplement.tex:6441`) (i) containment, minimality, probability chain; (ii) trigger;
  (iii) preimage-of-image identity;
* `prop:band-saturation` (`supplement.tex:4574`), saturation caps (entropic and quadratic) and the side claims of
  its preamble (sparsemax vertex, softmax never a vertex).
Builds on the frozen kit `StatFormal/OTFD/Bands/Statements.lean` (`simplex`, `softmax`, `score`, `Qent`,
`IsSimplexProj`), imported, not copied.

Covered: everything listed above, with the generalisations noted under Encodings.
Not covered (declared): the boundary probes `u*(v)` and their feasibility (`rem:supp-probe`); the certified outer band
(knapsack) of `prop:band-certificate`(iv), and hence the sentence "(iv) holds verbatim with the caps `κ_j ∧ κ_j^sat`,
and the resulting band is no wider" (only the per-weight validity of both caps is stated); `lem:oos-potential`
(as in the kit, caps are stated for the affine scores); the convexity/compactness of `A_{K,p}` and that `μ_K` is
carried by `supp μ_K` (taken as hypotheses); the informal remarks of `prop:band-guarantee` ("the inner band is not
an outer band", "can be far from tight", the `x ∉ m + V_K` sentence); the case `F_j(0) ≥ 1` interpretation.

Encodings (see card):
* `ℝ^K = Fin K → ℝ`, `⟨·,·⟩ = dotProduct`. Band edges are suprema in `EReal` (`hsup`), so no `sSup` junk: an empty
  set gives `⊥`, an unbounded one `⊤`. Upper edge `m + h_S(v)`, lower edge `m − h_S(−v)` (the support-function form
  of `main.tex`; for the inner lower edge this equals `m + inf_F ⟨v, Q̂⟩`). The evaluation point `t` enters only
  through `v = e(t)` and the offset `m(t)`, so (inner, sandwich) claims are stated for one arbitrary `(v, m)`.
* "Outer band available" = any real numbers `ub ≥ x̂↑(t)`, `lb ≤ x̂↓(t)` (generalises `prop:band-certificate`(iv)).
* Curves are functions `𝒯 → ℝ`, `x_c(t) = m(t) + ⟨e(t), c⟩`; `ι_K` injective is the hypothesis that
  `c ↦ (t ↦ ⟨e(t), c⟩)` is injective (`eq:iota-isometry`). `X^fit = x_{Q̂(U)}`, `U` measurable with law `μ_K = P.map U`;
  "conditionally on the fit" = `Q̂` deterministic. Probability claims assert measurability of the events.
* `Â = {u ∈ 𝒰 : g(u) ≤ τ̂}` with `𝒰` compact, `μ_K(𝒰) = 1`, `g` continuous; `c_K(τ) = μ_K(g ≤ τ)` (`calCdf`),
  `τ_{K,p} = inf{τ : c_K(τ) ≥ p}` (`calInv`), stated for `p > 0` with `{τ : c_K(τ) ≥ p}` nonempty (no `sInf` junk).
* Trigger (ii) is stated for any `A' ⊆ Â` (this covers `A_{K,p} ⊆ Â` when `τ̂ ≥ τ_{K,p}`); `y = m + ι_K c` for any
  coefficient vector `c` (= `Π_K(x − m)`); raw-curve form with any `r ≥ |x(t₀) − y(t₀)|` (`r_K(x)` is one).
* Saturation caps are stated pointwise for any upper bounds `G_l ≥ s_j(u) − s_l(u)`, `l ≠ j` (covers `g_jl(p)` and
  "any upper bound"); `κ^sat` (quadratic) is `0` if `F_j(0) ≥ 1`, else `sInf {c : F_j(c) ≥ 1}`, and `sat_root`
  certifies it is the unique root in `(0,1]`. `g_jl = a_j − a_l + σ_A(b_j − b_l)` is stated with `IsGreatest`.
DRAFT: not hashed; to be frozen as `Bands2/Statements.lean` after critic review (hash-lock in
`certify/statements.lock` then; AI agents must not edit the frozen file).
Critic notes: `guarantee_prob` assumes the out-of-sample map `Q` continuous (as in the paper's proof via `lem:oos-potential`);
a discontinuous hard-map selection is outside it. Not covered: the preamble sentence "`κ_j = 1` on `J_0`, so the capped
relaxation contains `e_j`"; "inner edges on a common `F` differ by at most `T`" follows from the sandwich claims.
-/

noncomputable section
open Finset Matrix MeasureTheory

namespace StatFormal.OTFD.Bands2

open StatFormal.OTFD.Bands

variable {n K : ℕ}

/-- `h_S(v) = sup_{u∈S} ⟨v, Q(u)⟩` in `EReal`. -/
def hsup (Q : (Fin K → ℝ) → Fin K → ℝ) (S : Set (Fin K → ℝ)) (v : Fin K → ℝ) : EReal :=
  ⨆ u ∈ S, ((v ⬝ᵥ Q u : ℝ) : EReal)

/-- Upper band edge over `S` at an evaluation vector `v = e(t)` with offset `mo = 𝔪(t)`: `𝔪 + h_S(v)`. -/
def edgeUp (Q : (Fin K → ℝ) → Fin K → ℝ) (S : Set (Fin K → ℝ)) (mo : ℝ) (v : Fin K → ℝ) : EReal :=
  (mo : EReal) + hsup Q S v

/-- Lower band edge over `S`: `𝔪 − h_S(−v)`. -/
def edgeLo (Q : (Fin K → ℝ) → Fin K → ℝ) (S : Set (Fin K → ℝ)) (mo : ℝ) (v : Fin K → ℝ) : EReal :=
  (mo : EReal) - hsup Q S (-v)

/-- The curve with coefficient vector `c`: `x_c(t) = 𝔪(t) + ⟨e(t), c⟩`. -/
def curve {T : Type} (mo : T → ℝ) (e : T → Fin K → ℝ) (c : Fin K → ℝ) : T → ℝ :=
  fun t => mo t + e t ⬝ᵥ c

/-- The region seen in function space, `𝒳 = {x_u : u ∈ S}`, `x_u = curve (Q u)`. -/
def region {T : Type} (Q : (Fin K → ℝ) → Fin K → ℝ) (S : Set (Fin K → ℝ)) (mo : T → ℝ)
    (e : T → Fin K → ℝ) : Set (T → ℝ) :=
  (fun u => curve mo e (Q u)) '' S

/-- The pointwise band `[lo, up] = {y : lo(t) ≤ y(t) ≤ up(t) ∀ t}` (edges in `EReal`). -/
def band {T : Type} (lo up : T → EReal) : Set (T → ℝ) :=
  {y | ∀ t, lo t ≤ ((y t : ℝ) : EReal) ∧ ((y t : ℝ) : EReal) ≤ up t}

/-- The calibration CDF `c_K(τ) = μ_K(g ≤ τ)`. -/
def calCdf (μ : Measure (Fin K → ℝ)) (g : (Fin K → ℝ) → ℝ) (τ : ℝ) : ℝ :=
  μ.real {u | g u ≤ τ}

/-- The generalised inverse `c_K^{-1}(p) = inf{τ : c_K(τ) ≥ p}`. -/
def calInv (μ : Measure (Fin K → ℝ)) (g : (Fin K → ℝ) → ℝ) (p : ℝ) : ℝ :=
  sInf {τ | p ≤ calCdf μ g τ}

/-- `osc(d) = max_j d_j − min_j d_j`. -/
def osc (d : Fin n → ℝ) : ℝ := (⨆ j, d j) - ⨅ j, d j

/-- `T(v) = tanh(Δ/(4ε)) (max_j ⟨v, Z_j⟩ − min_j ⟨v, Z_j⟩)`. -/
def solverT (ε Δ : ℝ) (Z : Fin n → Fin K → ℝ) (v : Fin K → ℝ) : ℝ :=
  Real.tanh (Δ / (4 * ε)) * ((⨆ j, v ⬝ᵥ Z j) - ⨅ j, v ⬝ᵥ Z j)

/-- Entropic saturation cap `κ_j^sat = (1 + Σ_{l≠j} e^{−G_l/ε})⁻¹`. -/
def satCapEnt (ε : ℝ) (G : Fin n → ℝ) (j : Fin n) : ℝ :=
  (1 + ∑ l ∈ univ.erase j, Real.exp (-G l / ε))⁻¹

/-- `F_j(c) = c + Σ_{l≠j} (c − G_l/λ)_+`. -/
def satF (lam : ℝ) (G : Fin n → ℝ) (j : Fin n) (c : ℝ) : ℝ :=
  c + ∑ l ∈ univ.erase j, max 0 (c - G l / lam)

/-- Quadratic saturation cap: `0` if `F_j(0) ≥ 1`, otherwise the root of `F_j(c) = 1`
(as `inf{c : F_j(c) ≥ 1}`; see `sat_root`). -/
def satCapQuad (lam : ℝ) (G : Fin n → ℝ) (j : Fin n) : ℝ :=
  if 1 ≤ satF lam G j 0 then 0 else sInf {c | 1 ≤ satF lam G j c}

namespace Claims

/-! ### `prop:band-inner-certificate` -/

/-- Inner edges: for **any** map `Q` and any `F ⊆ A`, `x̲↑ ≤ x̂↑` and `x̲↓ ≥ x̂↓`. -/
def inner_le_exact : Prop :=
  ∀ (K : ℕ) (Q : (Fin K → ℝ) → Fin K → ℝ) (A F : Set (Fin K → ℝ)) (mo : ℝ) (v : Fin K → ℝ),
    F ⊆ A → edgeUp Q F mo v ≤ edgeUp Q A mo v ∧ edgeLo Q A mo v ≤ edgeLo Q F mo v

/-- Exactness diagnostic: with a (real) outer band `ub ≥ x̂↑`, `lb ≤ x̂↓` and nonempty `F ⊆ A`,
`gap = (ub − x̲↑) + (x̲↓ − lb)` is finite and `≥ 0`, and `gap = 0` certifies both edges exactly. -/
def inner_gap : Prop :=
  ∀ (K : ℕ) (Q : (Fin K → ℝ) → Fin K → ℝ) (A F : Set (Fin K → ℝ)) (mo : ℝ) (v : Fin K → ℝ)
    (ub lb : ℝ),
    F ⊆ A → F.Nonempty → edgeUp Q A mo v ≤ (ub : EReal) → (lb : EReal) ≤ edgeLo Q A mo v →
      0 ≤ ((ub : EReal) - edgeUp Q F mo v) + (edgeLo Q F mo v - lb) ∧
      ((ub : EReal) - edgeUp Q F mo v) + (edgeLo Q F mo v - lb) ≠ ⊤ ∧
      (((ub : EReal) - edgeUp Q F mo v) + (edgeLo Q F mo v - lb) = 0 →
        edgeUp Q F mo v = edgeUp Q A mo v ∧ edgeUp Q A mo v = ub ∧
        edgeLo Q F mo v = edgeLo Q A mo v ∧ edgeLo Q A mo v = lb)

/-! ### `cor:ext-solver-certified` -/

/-- Upper edge: `x̲↑_f − T* ≤ x̂↑_{f*} ≤ x̄↑_f + T*` whenever `Δ* ≥ osc(f − f*)`, for any outer `ub` and
inner set `F ⊆ A` computed from the returned `f`. -/
def solver_sandwich_up : Prop :=
  ∀ (n K : ℕ) (ε Δ mo ub : ℝ) (M : Matrix (Fin K) (Fin K) ℝ) (Z : Fin n → Fin K → ℝ)
    (f fstar : Fin n → ℝ) (A F : Set (Fin K → ℝ)) (v : Fin K → ℝ),
    0 < n → 0 < ε → M.PosDef → F ⊆ A → osc (f - fstar) ≤ Δ →
    edgeUp (Qent ε M Z f) A mo v ≤ (ub : EReal) →
      edgeUp (Qent ε M Z f) F mo v - (solverT ε Δ Z v : EReal) ≤ edgeUp (Qent ε M Z fstar) A mo v ∧
      edgeUp (Qent ε M Z fstar) A mo v ≤ (ub : EReal) + (solverT ε Δ Z v : EReal)

/-- Lower edge: `x̄↓_f − T* ≤ x̂↓_{f*} ≤ x̲↓_f + T*`. -/
def solver_sandwich_lo : Prop :=
  ∀ (n K : ℕ) (ε Δ mo lb : ℝ) (M : Matrix (Fin K) (Fin K) ℝ) (Z : Fin n → Fin K → ℝ)
    (f fstar : Fin n → ℝ) (A F : Set (Fin K → ℝ)) (v : Fin K → ℝ),
    0 < n → 0 < ε → M.PosDef → F ⊆ A → osc (f - fstar) ≤ Δ →
    (lb : EReal) ≤ edgeLo (Qent ε M Z f) A mo v →
      (lb : EReal) - (solverT ε Δ Z v : EReal) ≤ edgeLo (Qent ε M Z fstar) A mo v ∧
      edgeLo (Qent ε M Z fstar) A mo v ≤ edgeLo (Qent ε M Z f) F mo v + (solverT ε Δ Z v : EReal)

/-! ### `prop:band-guarantee` -/

/-- (i) `𝒳̂ ⊆ B̂` (any map, any region). -/
def guarantee_contain : Prop :=
  ∀ (K : ℕ) (T : Type) (Q : (Fin K → ℝ) → Fin K → ℝ) (A : Set (Fin K → ℝ)) (mo : T → ℝ)
    (e : T → Fin K → ℝ),
    region Q A mo e ⊆ band (fun t => edgeLo Q A (mo t) (e t)) (fun t => edgeUp Q A (mo t) (e t))

/-- (i) minimality: every pointwise band containing `𝒳̂` contains `B̂`'s edges. -/
def guarantee_minimal : Prop :=
  ∀ (K : ℕ) (T : Type) (Q : (Fin K → ℝ) → Fin K → ℝ) (A : Set (Fin K → ℝ)) (mo : T → ℝ)
    (e : T → Fin K → ℝ) (lo up : T → EReal),
    region Q A mo e ⊆ band lo up →
      ∀ t, edgeUp Q A (mo t) (e t) ≤ up t ∧ lo t ≤ edgeLo Q A (mo t) (e t)

/-- (i) probability chain (measurable events) and (iii): `μ_K(Â) ≤ P(X^fit ∈ 𝒳̂) ≤ P(X^fit ∈ B̂)`,
`μ_K(Â) = c_K(τ̂)`, `P(X^fit ∈ 𝒳̂) = μ_K(Q̂⁻¹(Q̂(Â)))`, with equality `= μ_K(Â)` when `Q̂` is injective. -/
def guarantee_prob : Prop :=
  ∀ (K : ℕ) (T Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → Fin K → ℝ) (Q : (Fin K → ℝ) → Fin K → ℝ) (g : (Fin K → ℝ) → ℝ)
    (𝒰 : Set (Fin K → ℝ)) (τhat : ℝ) (mo : T → ℝ) (e : T → Fin K → ℝ),
    Measurable U → Continuous Q → Continuous g → IsCompact 𝒰 → P.map U 𝒰 = 1 →
    Function.Injective (fun c : Fin K → ℝ => fun t => e t ⬝ᵥ c) →
      MeasurableSet {ω | curve mo e (Q (U ω)) ∈ region Q {u | u ∈ 𝒰 ∧ g u ≤ τhat} mo e} ∧
      MeasurableSet {ω | curve mo e (Q (U ω)) ∈
        band (fun t => edgeLo Q {u | u ∈ 𝒰 ∧ g u ≤ τhat} (mo t) (e t))
          (fun t => edgeUp Q {u | u ∈ 𝒰 ∧ g u ≤ τhat} (mo t) (e t))} ∧
      P.map U {u | u ∈ 𝒰 ∧ g u ≤ τhat} ≤
        P {ω | curve mo e (Q (U ω)) ∈ region Q {u | u ∈ 𝒰 ∧ g u ≤ τhat} mo e} ∧
      P {ω | curve mo e (Q (U ω)) ∈ region Q {u | u ∈ 𝒰 ∧ g u ≤ τhat} mo e} ≤
        P {ω | curve mo e (Q (U ω)) ∈
          band (fun t => edgeLo Q {u | u ∈ 𝒰 ∧ g u ≤ τhat} (mo t) (e t))
            (fun t => edgeUp Q {u | u ∈ 𝒰 ∧ g u ≤ τhat} (mo t) (e t))} ∧
      P.map U {u | u ∈ 𝒰 ∧ g u ≤ τhat} = ENNReal.ofReal (calCdf (P.map U) g τhat) ∧
      P {ω | curve mo e (Q (U ω)) ∈ region Q {u | u ∈ 𝒰 ∧ g u ≤ τhat} mo e} =
        P.map U (Q ⁻¹' (Q '' {u | u ∈ 𝒰 ∧ g u ≤ τhat})) ∧
      (Function.Injective Q →
        P {ω | curve mo e (Q (U ω)) ∈ region Q {u | u ∈ 𝒰 ∧ g u ≤ τhat} mo e} =
          P.map U {u | u ∈ 𝒰 ∧ g u ≤ τhat})

/-- (i) level: `c_K(τ̂) ≥ p` whenever `τ̂ ≥ τ_{K,p} = c_K^{-1}(p)`. -/
def guarantee_level : Prop :=
  ∀ (K : ℕ) (μ : Measure (Fin K → ℝ)) [IsProbabilityMeasure μ] (g : (Fin K → ℝ) → ℝ) (p τhat : ℝ),
    Measurable g → 0 < p → {τ | p ≤ calCdf μ g τ}.Nonempty → calInv μ g p ≤ τhat →
      p ≤ calCdf μ g τhat

/-- (ii) trigger: if `y = 𝔪 + ι_K c` leaves an outer band of `Â` at one point `t₀`, then `y ∉ 𝒳(A')` and
`c ∉ Q̂(A')` for every `A' ⊆ Â`. -/
def guarantee_trigger : Prop :=
  ∀ (K : ℕ) (T : Type) (Q : (Fin K → ℝ) → Fin K → ℝ) (A A' : Set (Fin K → ℝ)) (mo : T → ℝ)
    (e : T → Fin K → ℝ) (t0 : T) (ub lb : ℝ) (c : Fin K → ℝ),
    A' ⊆ A → edgeUp Q A (mo t0) (e t0) ≤ (ub : EReal) → (lb : EReal) ≤ edgeLo Q A (mo t0) (e t0) →
    (ub < curve mo e c t0 ∨ curve mo e c t0 < lb) →
      curve mo e c ∉ region Q A' mo e ∧ c ∉ Q '' A'

/-- (ii) raw-curve form: `x(t₀) > ub + r` or `x(t₀) < lb − r` with `|x(t₀) − y(t₀)| ≤ r`. -/
def guarantee_trigger_raw : Prop :=
  ∀ (K : ℕ) (T : Type) (Q : (Fin K → ℝ) → Fin K → ℝ) (A A' : Set (Fin K → ℝ)) (mo : T → ℝ)
    (e : T → Fin K → ℝ) (t0 : T) (ub lb r : ℝ) (c : Fin K → ℝ) (x : T → ℝ),
    A' ⊆ A → edgeUp Q A (mo t0) (e t0) ≤ (ub : EReal) → (lb : EReal) ≤ edgeLo Q A (mo t0) (e t0) →
    |x t0 - curve mo e c t0| ≤ r → (ub + r < x t0 ∨ x t0 < lb - r) →
      curve mo e c ∉ region Q A' mo e ∧ c ∉ Q '' A'

/-! ### `prop:band-saturation` -/

/-- `g_jl = max_{u∈A}[s_j(u) − s_l(u)] = a_j − a_l + σ_A(b_j − b_l)` (attained maxima). -/
def sat_gap_closed_form : Prop :=
  ∀ (n K : ℕ) (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ) (A : Set (Fin K → ℝ)) (j l : Fin n) (σ : ℝ),
    IsGreatest ((fun u => (b j - b l) ⬝ᵥ u) '' A) σ →
      IsGreatest ((fun u => score a b j u - score a b l u) '' A) (a j - a l + σ)

/-- Entropic saturation cap: `softmax_j(s(u)/ε) ≤ (1 + Σ_{l≠j} e^{−G_l/ε})⁻¹` for any
`G_l ≥ s_j(u) − s_l(u)`. -/
def sat_cap_entropic : Prop :=
  ∀ (n K : ℕ) (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ) (ε : ℝ) (G : Fin n → ℝ) (j : Fin n)
    (u : Fin K → ℝ),
    0 < ε → (∀ l, l ≠ j → score a b j u - score a b l u ≤ G l) →
      softmax (fun k => score a b k u / ε) j ≤ satCapEnt ε G j

/-- Quadratic saturation cap: with `q` the simplex projection of `s(u)/λ`, `λ = γ/m`,
`q_j ≤ κ_j^sat` for any `G_l ≥ s_j(u) − s_l(u)`. -/
def sat_cap_quadratic : Prop :=
  ∀ (n K m : ℕ) (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ) (γ : ℝ) (G : Fin n → ℝ) (j : Fin n)
    (u : Fin K → ℝ) (q : Fin n → ℝ),
    0 < γ → 0 < m → (∀ l, l ≠ j → score a b j u - score a b l u ≤ G l) →
    IsSimplexProj (fun k => score a b k u / (γ / m)) q →
      q j ≤ satCapQuad (γ / m) G j

/-- `F_j` is strictly increasing, and when `F_j(0) < 1` the cap is its unique root in `(0, 1]`. -/
def sat_root : Prop :=
  ∀ (n : ℕ) (lam : ℝ) (G : Fin n → ℝ) (j : Fin n),
    0 < lam →
      StrictMono (satF lam G j) ∧
      (satF lam G j 0 < 1 →
        0 < satCapQuad lam G j ∧ satCapQuad lam G j ≤ 1 ∧ satF lam G j (satCapQuad lam G j) = 1)

/-- Replacing `G` by larger upper bounds only enlarges both saturation caps. -/
def sat_mono : Prop :=
  ∀ (n : ℕ) (ε lam : ℝ) (G G' : Fin n → ℝ) (j : Fin n),
    0 < ε → 0 < lam → (∀ l, G l ≤ G' l) →
      satCapEnt ε G j ≤ satCapEnt ε G' j ∧ satCapQuad lam G j ≤ satCapQuad lam G' j

/-- Preamble: sparsemax weights can be a vertex: `q = e_j` whenever `x_j − x_l ≥ 1` for all `l ≠ j`
(`x = s(u)/λ`). -/
def sparsemax_vertex : Prop :=
  ∀ (n : ℕ) (x q : Fin n → ℝ) (j : Fin n),
    (∀ l, l ≠ j → 1 ≤ x j - x l) → IsSimplexProj x q → q = Pi.single j 1

/-- Preamble: no softmax weight vector is a vertex (`n ≥ 2`): every weight lies in `(0, 1)`. -/
def softmax_not_vertex : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℝ) (j : Fin n), 2 ≤ n → 0 < softmax x j ∧ softmax x j < 1

end Claims
end StatFormal.OTFD.Bands2
