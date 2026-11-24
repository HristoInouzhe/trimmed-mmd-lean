import StatFormal.Wave30tr.Statements
import StatFormal.Wave30tu.Statements
import StatFormal.Archive.Wave12c.Statements
import StatFormal.Archive.Wave8a.Statements
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Measure.CompleteLattice
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 30tx: trimmed-mmd (JMLR v2), a parametric rate for the witness and the kept set, the contact level and the data-driven level

Printed source: `trimmed-mmd/jmlr/` at trimmed-mmd master `c3ba305` ("JMLR v2: localized rate for the witness and the kept set
(author decision Q8)"; read-only, read 2026-11-08; sha256 `sections/08_trimming.tex`
`ffd387786fba48547d2272de7031d8998de54f43cee0b9bd0788a7b5a2fd0f9f`, `appendix/C_recover.tex`
`3488f8e8921ae4ef743104783e77793b6140902b8c701d59d4801558dd01f107`; context `sections/03_regions.tex` `b9673cf0…`,
`sections/04_test.tex` `bbd28b35…` (at `c339b9d` the two cited files are unchanged and `04_test.tex` changed only
in prose at `:214-218`), `sections/05_estimator.tex` `20507b94…`, full hashes on the card):
* `08_trimming.tex:232-321`, Section 7.3 `sec:trimrate`: `thm:trimrate` (with `eq:qdens` = (Q), `08_trimming.tex:196-201`, and
  `eq:qdensY` = (Q′), `:258-263`) and `cor:trimrate` (`:307-319`);
* `08_trimming.tex:321-394`, Section 7.4 `sec:nearcontact`: the lead-in (`:331-335`), `rem:nearcontact` (a), (b) (`:336-350`), the
  modulus `ω_c` (`:364-368`) and `prop:alphahat` (`:370-385`);
* `C_recover.tex:333-789`, subsection C.4 `supp:trimrate`: the notation paragraph and `eq:twotail` (`:345-366`), `lem:sepmargin`
  (`:367-380`), `lem:basicineq` (`:395-411`), `lem:localmod` (`:454-478`), the proofs (`eq:basicZ` `:569-573`), the lead-in to
  `lem:contact` (`:659-660`: `β* = (1−α*)⁻¹`, `P∧Q` "the largest measure below both `P` and `Q`, of mass `1 − TV(P,Q)`") and
  `lem:contact` (`:662-667`); Step 4 of the proof of the remark (`:729-730`) for the density form of the fractional set.
Context (read-only): `03_regions.tex:20-31` (`ass:regularity`), `:77-90` (`𝒢_α`, `eq:region`), `01_introduction.tex:12-19`
(`eq:trimset`, `R_α(P)`), `04_test.tex:107-122` (`thm:twosided`, `eq:tauA`), `:60-85` (`eq:radius`, `cor:uniform`), `05_estimator.tex`
(`eq:alphaest`, `thm:consistency`, `cor:consistency`), `08_trimming.tex:13-55` (`eq:trimset-emp`, `prop:bangbang`), `:166-230`
(`prop:witnessstab`, `eq:popdensity`, `A*`, `Â_n`, `ĝ_n`, `thm:trimconsist`), `06_splitting.tex:20-30` (`eq:sep`).

Reuses (imported, not copied): `TrimmedMMD/Concentration` (`region`, `empirical`), `TrimmedMMD/Unconditional` (`Dpop` = `D_{α,k}(P,Q)`,
`Demp` = `D̂_{α,k}`), `TrimmedMMD/BangBang` (`capped` = `Δ_α(n)`, `qp` = `eq:qp`, `ord`, `kfloor` = `n_α`), `TrimmedMMD/Projection`
(`IsMinNorm`), `TrimmedMMD/ZeroSet` (`Characteristic` = (A3)), `TrimmedMMD` (`rn` = `eq:radius`, `crossSet`, `alphaHat` = `eq:alphaest`,
`tau` = `r_n(·,δ/2) + r_m(·,δ/2)`), `Wave4b` (`witness` = `Σ w_iφ(X_i) − Σ v_jφ(Y_j)`), `Wave8a` (`trimSet` = `R_α(P)` of `eq:trimset`),
`Wave12c` (`witFn`, `quantileAt`, `QDensity` = (Q), `QDensityLower`, `etaTC`, `zetaTC`, `lamTC`, `tHat` of `thm:trimconsist`), `Wave30tp`
(`sNM` = `s`, `sampleLaw`), `Wave30tr` (`ek` = `e_k`, `tauA` = `τ^A` of `eq:tauA`), `Wave30tu` (`ValidThreshold`), `Distances.tvDist`.

Encodings (see card `certify/cards/wave30tx.md`):
* (A1)–(A2) as in the frozen `TrimmedMMD/Concentration` claims: `H` a separable real Hilbert space, `φ` strongly measurable with
  `‖φ x‖ ≤ κ`; (A3) is `Characteristic φ`, assumed only where the printed result assumes all of `ass:regularity`. `D_φ` is any bound on
  `‖φ x − φ x'‖` (as in `Wave30tr`); `D = D_{α,k}(P,Q)` is `Dpop φ P Q α` and `D̂_{α,k}` is `Demp φ x y α`.
* The population witness `d*` is any minimum-norm element of `𝒞_α(P) − 𝒞_α(Q)` (hypothesis `IsMinNorm`; it exists and is unique);
  the empirical witness `d̂` is `witness φ x y (w,v)` at any minimiser `(w,v)` of `eq:qp` over `Δ_α(n) × Δ_α(m)` (`prop:bangbang`(i)).
* `t_α` is `quantileAt` (the lower `(1−α)`-quantile, as in `thm:trimconsist`); "a `p`-quantile `t` of `f` under `R`" is
  `R(f < t) ≤ p ≤ R(f ≤ t)` (`IsQuantile`, the characterisation after `eq:twotail`); `t̂_n = d̂_{(n_α+1)}` is `tHat`; the `(m_α+1)`-th
  largest of `m` values is `ordTop`.
* Tie functions `ϑ, ϑ̂ : 𝒳 → [0, (1−α)⁻¹]` of `eq:popdensity` and `ĝ_n` (`plugDensityFn`); the normalisation `E_P[g*] = 1` is not
  needed and not assumed (generalisation).
* "On an event of probability at least `1 − δ`": a measurable event of probability `≥ 1 − δ` under `P^{⊗n} ⊗ Q^{⊗m}`, on which the
  conclusions hold for every minimiser of `eq:qp`. The `O_P` statements of `cor:trimrate` in explicit form: for every `ε ∈ (0,1)`
  there is `Λ` (depending on `ε` only) such that for every admissible `(P,Q,k,α)` there is `N` with, for `n, m ≥ N`, a measurable event
  of probability `≥ 1 − ε` on which each quantity is at most `Λ` times its rate.
* `sep_K` of `lem:sepmargin` is an `EReal` infimum (`−∞` allowed); `sep(f; A, B)` of `eq:sep` is the real `sInf − sSup`, used only for
  the (nonempty, norm-bounded) regions. `(P − P_n)h = ∫h dP − n⁻¹Σh(X_i)`. `Z(r)` is the real supremum over the parameters
  `(f,t,u)` of `𝓗(r)` (nonempty and bounded).
* `P∧Q` is Mathlib's `P ⊓ Q` (the infimum in the lattice of measures, the largest measure below both); `R* = (1−α*)⁻¹(P∧Q)`;
  `R_α(P)` is `Wave8a.trimSet`; `μ_R = ∫φ dR`; `MMD_k(Σ w_iδ_{X_i}, R*) = ‖∫φ d(Σ w_iδ_{X_i}) − μ_{R*}‖`; `dist_𝓗(a, C)` is `infDist`;
  `ω_c(ε)` is the real supremum (the set is nonempty and bounded for `ε ≥ 0`); `dR*/dP` is `rnDeriv`.
* "smallest upper bound on the density of `f(X)` on `[a,b]`" is `densUpper` = `inf{C ∈ [0,∞] : P(f ∈ B) ≤ C·Leb(B) ∀ Borel B ⊆ [a,b]}`
  (the definition in the proof of the remark, `C_recover.tex:712-714`), and the best lower bound is `densLower` =
  `sup{c ∈ [0,∞] : c·Leb(B) ≤ P(f ∈ B) ∀ Borel B ⊆ [a,b]}`. "No limit point in `L¹(P)` as `α ↑ α*`": no sequence `α_j → α*`, `α_j < α*`,
  along which the indicators converge in `L¹(P)` to an integrable `h`.
* "`k` is a Gaussian kernel on `ℝ^d`": `φ : ℝ^d → H` with `⟨φ x, φ y⟩ = exp(−‖x−y‖²/(2σ²))`, `σ > 0`, into any separable Hilbert space
  (generalisation: the RKHS is the closed span of `φ(ℝ^d)`, isometric to the printed one); "`P, Q` have continuous densities": densities
  with respect to Lebesgue measure that are continuous and nonnegative.
* `prop:alphahat`: `α̂` of `eq:alphaest` for any threshold `τ` that is valid at level `δ`, nondecreasing, continuous on `(0,1)` and whose
  crossing set is nonempty for every realisation (generalisation, as in `Wave30tu`: the paper's `τ_{n,m}` has these properties,
  `Wave30tu`/`Wave30tw`); along a schedule, thresholds also `≤ r_n(·,δ/2) + r_m(·,δ/2)` (as in `Wave30tu.cor_consistency`), and
  convergence in probability in the encoding of the frozen `Wave30tu.cor_consistency` (measurable inner events of probability `→ 1`).
* Generalisations (declared): no `[MeasurableSingletonClass 𝒳]` (unlike `Wave12c`/`Wave4b`; `Wave8a.region_empirical` needs none);
  `lem:sepmargin` without closedness of `K` or completeness of `𝓗`; `trimrate_A3` includes `α = 0`; `contact_compact` without (A3).
  Specialisation (declared): `nearcontact_densities` takes the densities with respect to a σ-finite `μ`. Additions (declared):
  `localmod` also states that `Z(r)` bounds the bracket over `𝓗(r)` and is integrable; `contact` states the lead-in (`P ⊓ Q` is the
  largest measure below both — true by definition of `⊓` — and has mass `1 − TV(P,Q)`).

Not covered (declared): `eq:twotail` as a separate display (used inside the proofs), the prose after `thm:trimrate`
(`08_trimming.tex:292-306`: orders of magnitude, the factor `√2`, numerical crossovers), the remarks after `rem:nearcontact` and
`prop:alphahat` (`:351-362`, `:386-394`), and every numerical claim.
FROZEN 2026-11-08 after an independent critic's pre-freeze review (14 claims ACCEPT / ACCEPT-WITH-NOTE, none false, no
counterexample; applied: line references, the `σ`-finite declaration, the source-drift note). Hashed in `certify/statements.lock`
(with its imports); AI agents must not edit this file.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace Pointwise

namespace StatFormal.Wave30tx

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional
  StatFormal.TrimmedMMD.BangBang StatFormal.TrimmedMMD.Projection StatFormal.TrimmedMMD.ZeroSet
  StatFormal.Wave12c StatFormal.Wave4b StatFormal.Wave30tp StatFormal.Wave30tr

section Defs

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `sep_K(f) = inf_{z ∈ K} ⟨f, z⟩` (`lem:sepmargin`), as an extended real (`−∞` if unbounded below). -/
def sepK (K : Set H) (f : H) : EReal := ⨅ z ∈ K, ((⟪f, z⟫_ℝ : ℝ) : EReal)

/-- `eq:sep`: `sep(f; A, B) = inf_{a ∈ A} ⟨f, a⟩ − sup_{b ∈ B} ⟨f, b⟩` (real; used for nonempty bounded `A`, `B`). -/
def sepAB (A B : Set H) (f : H) : ℝ :=
  sInf ((fun a => ⟪f, a⟫_ℝ) '' A) - sSup ((fun b => ⟪f, b⟫_ℝ) '' B)

/-- `(P − P_n)h = ∫ h dP − n⁻¹ Σ_i h(x_i)`. -/
def popDev (P : Measure 𝒳) {n : ℕ} (x : Fin n → 𝒳) (h : 𝒳 → ℝ) : ℝ :=
  ∫ y, h y ∂P - (n : ℝ)⁻¹ * ∑ i, h (x i)

/-- `t` is a `p`-quantile of `f` under `R`: `R(f < t) ≤ p ≤ R(f ≤ t)`. -/
def IsQuantile (R : Measure 𝒳) (f : 𝒳 → ℝ) (p t : ℝ) : Prop :=
  R.real {x | f x < t} ≤ p ∧ p ≤ R.real {x | f x ≤ t}

/-- The `(m_α+1)`-th largest of the values `v` (`m_α = ⌊m(1−α)⌋`), i.e. the `(m − m_α)`-th smallest. -/
def ordTop {m : ℕ} (v : Fin m → ℝ) (α : ℝ) : ℝ := ord v (m - kfloor m α - 1)

/-- The parameters `(f, t, u)` of the class `𝓗(r)` of `lem:localmod`: `‖f − f*‖ ≤ r`, `|t − t*| ≤ κr + λ₁`, `|u − u*| ≤ κr + λ₂`. -/
def rampPar (fstar : H) (tstar ustar κ r l1 l2 : ℝ) : Set (H × ℝ × ℝ) :=
  {p | ‖p.1 - fstar‖ ≤ r ∧ |p.2.1 - tstar| ≤ κ * r + l1 ∧ |p.2.2 - ustar| ≤ κ * r + l2}

/-- `(P − P_n)h₁ + (Q − Q_m)h₂` at `h₁ = (t − f)₊ − (t* − f*)₊`, `h₂ = (f − u)₊ − (f* − u*)₊`, `p = (f, t, u)`. -/
def rampDev (P Q : Measure 𝒳) (φ : 𝒳 → H) (fstar : H) (tstar ustar : ℝ) {n m : ℕ}
    (z : (Fin n → 𝒳) × (Fin m → 𝒳)) (p : H × ℝ × ℝ) : ℝ :=
  popDev P z.1 (fun x => max (p.2.1 - witFn p.1 φ x) 0 - max (tstar - witFn fstar φ x) 0) +
    popDev Q z.2 (fun y => max (witFn p.1 φ y - p.2.2) 0 - max (witFn fstar φ y - ustar) 0)

/-- `Z(r) = sup_{(h₁,h₂) ∈ 𝓗(r)} [(P − P_n)h₁ + (Q − Q_m)h₂]` (`lem:localmod`). -/
def Zloc (P Q : Measure 𝒳) (φ : 𝒳 → H) (fstar : H) (tstar ustar κ r l1 l2 : ℝ) {n m : ℕ}
    (z : (Fin n → 𝒳) × (Fin m → 𝒳)) : ℝ :=
  ⨆ p : rampPar fstar tstar ustar κ r l1 l2, rampDev P Q φ fstar tstar ustar z p.1

/-- `L(χ) = 2√s + 2(e_n + e_m) + 2√(2χs)` (`lem:localmod`; `L_{n,m}` of `thm:trimrate` at `χ` of the theorem). -/
def Lloc (χ : ℝ) (n m : ℕ) : ℝ := 2 * √(sNM n m) + 2 * (ek n + ek m) + 2 * √(2 * χ * sNM n m)

/-- `M(χ) = 2(λ₁e_n + λ₂e_m) + √(2χ(λ₁²/n + λ₂²/m))` (`lem:localmod`; `M_{n,m}` of `thm:trimrate` at `λ_X, λ_Y`). -/
def Mloc (l1 l2 χ : ℝ) (n m : ℕ) : ℝ :=
  2 * (l1 * ek n + l2 * ek m) + √(2 * χ * (l1 ^ 2 / n + l2 ^ 2 / m))

/-- `λ_X = c_f⁻¹(√(log(10/δ)/(2n)) + 1/n)` (and `λ_Y` with `c'_f`, `m`) of `thm:trimrate`. -/
def lamQ (c δ : ℝ) (n : ℕ) : ℝ := 1 / c * (√(Real.log (10 / δ) / (2 * n)) + 1 / n)

/-- `J = ⌈log(2√(n∧m)) / log θ⌉` of `thm:trimrate`. -/
def Jpeel (θ : ℝ) (n m : ℕ) : ℕ := ⌈Real.log (2 * √((min n m : ℕ) : ℝ)) / Real.log θ⌉₊

/-- `χ = log(5(J+1)/δ)` of `thm:trimrate`. -/
def chiPeel (θ δ : ℝ) (n m : ℕ) : ℝ := Real.log (5 * ((Jpeel θ n m : ℝ) + 1) / δ)

/-- `ζ^loc = 2θκL/(1−α) + √(2(2θ^{−J}κDL + M)/(1−α))` of `thm:trimrate`. -/
def zetaLoc (κ α D θ : ℝ) (J : ℕ) (L M : ℝ) : ℝ :=
  2 * θ * κ * L / (1 - α) + √(2 * (2 * (θ ^ J)⁻¹ * κ * D * L + M) / (1 - α))

/-- `ℓ^loc = 2κζ^loc + λ_X` of `thm:trimrate`. -/
def ellLoc (κ ζ lX : ℝ) : ℝ := 2 * κ * ζ + lX

/-- `eq:popdensity` with a tie function `ϑ`: `(1−α)⁻¹ 1{f < t} + ϑ 1{f = t}`. -/
def plugDensityFn (α : ℝ) (ϑ : 𝒳 → ℝ) (f : 𝒳 → ℝ) (t : ℝ) (x : 𝒳) : ℝ :=
  if f x < t then 1 / (1 - α) else if f x = t then ϑ x else 0

/-- The kept-set conclusions shared by `thm:trimrate`(iii) and `thm:trimconsist`, at a band half-width `ℓ`: the inclusion
`Â_n △ A* ⊆ {|d* − t_α| ≤ ℓ}` and, if `ℓ ≤ ρ`, `P(Â_n △ A*) ≤ 2C_fℓ` and `∫|ĝ_n − g*| dP ≤ 2C_fℓ/(1−α)` for all tie functions. -/
def KeptConcl (P : Measure 𝒳) (φ : 𝒳 → H) (α ρ Cf : ℝ) (dstar dh : H) (tα th ℓ : ℝ) : Prop :=
  symmDiff {x | witFn dh φ x < th} {x | witFn dstar φ x < tα} ⊆ {x | |witFn dstar φ x - tα| ≤ ℓ} ∧
    (ℓ ≤ ρ →
      P (symmDiff {x | witFn dh φ x < th} {x | witFn dstar φ x < tα}) ≤ ENNReal.ofReal (2 * Cf * ℓ) ∧
      ∀ ϑ ϑh : 𝒳 → ℝ, (∀ x, 0 ≤ ϑ x ∧ ϑ x ≤ 1 / (1 - α)) → (∀ x, 0 ≤ ϑh x ∧ ϑh x ≤ 1 / (1 - α)) →
        ∫ x, |plugDensityFn α ϑh (witFn dh φ) th x - plugDensityFn α ϑ (witFn dstar φ) tα x| ∂P ≤
          2 * Cf * ℓ / (1 - α))

/-- The conclusions (i)–(iii) of `thm:trimrate` at a realisation `z` and a minimiser `pr` of `eq:qp`. -/
def RateConcl (P Q : Measure 𝒳) (φ : 𝒳 → H) (κ Dφ α δ θ ρ cf Cf cf' : ℝ) (n m : ℕ) (dstar : H)
    (z : (Fin n → 𝒳) × (Fin m → 𝒳)) (pr : (Fin n → ℝ) × (Fin m → ℝ)) : Prop :=
  let D := Dpop φ P Q α
  let τA := tauA κ Dφ α (δ / 5) n m
  let lX := lamQ cf δ n
  let lY := lamQ cf' δ m
  let χ := chiPeel θ δ n m
  let ζ := zetaLoc κ α D θ (Jpeel θ n m) (Lloc χ n m) (Mloc lX lY χ n m)
  let tα := quantileAt P (witFn dstar φ) (1 - α)
  let dh := witness φ z.1 z.2 pr
  let Dh := Demp φ z.1 z.2 α
  let th := tHat φ dh α z.1
  (0 < Dh ∧ ‖Dh⁻¹ • dh - D⁻¹ • dstar‖ ≤ ζ / D) ∧
    ‖dh - dstar‖ ≤ τA + √(1 + τA / D) * ζ ∧
    |th / Dh - tα / D| ≤ (κ * ζ + lX) / D ∧
    KeptConcl P φ α ρ Cf dstar dh tα th (ellLoc κ ζ lX)

/-- The conclusions of `thm:trimconsist` (`eq:trimrate` and the density bound) at a realisation and a minimiser, with tie
functions. -/
def ConsistConcl (P Q : Measure 𝒳) (φ : 𝒳 → H) (κ α δ ρ cf Cf : ℝ) (n m : ℕ) (dstar : H)
    (z : (Fin n → 𝒳) × (Fin m → 𝒳)) (pr : (Fin n → ℝ) × (Fin m → ℝ)) : Prop :=
  let tα := quantileAt P (witFn dstar φ) (1 - α)
  let dh := witness φ z.1 z.2 pr
  let th := tHat φ dh α z.1
  let ℓ := lamTC κ (zetaTC (etaTC κ α δ n m) (Dpop φ P Q α)) cf δ n
  |th - tα| ≤ ℓ ∧ KeptConcl P φ α ρ Cf dstar dh tα th ℓ

/-- `R* = (P∧Q)/(1−α*)`, `α* = TV(P,Q)`, with `P∧Q = P ⊓ Q`. -/
def contactLaw (P Q : Measure 𝒳) : Measure 𝒳 :=
  ENNReal.ofReal (1 / (1 - StatFormal.Distances.tvDist P Q)) • (P ⊓ Q)

/-- `ω_c(ε) = sup{‖a − μ_{R*}‖ : a ∈ 𝒞_{α*}(P), dist(a, 𝒞_{α*}(Q)) ≤ ε}`. -/
def omegaC (φ : 𝒳 → H) (P Q : Measure 𝒳) (ε : ℝ) : ℝ :=
  sSup {r | ∃ a ∈ region φ (StatFormal.Distances.tvDist P Q) P,
    Metric.infDist a (region φ (StatFormal.Distances.tvDist P Q) Q) ≤ ε ∧
      r = ‖a - ∫ x, φ x ∂(contactLaw P Q)‖}

/-- The weighted empirical measure `Σ_i w_i δ_{x_i}`. -/
def wEmp {n : ℕ} (w : Fin n → ℝ) (x : Fin n → 𝒳) : Measure 𝒳 :=
  ∑ i, ENNReal.ofReal (w i) • Measure.dirac (x i)

/-- The smallest upper bound on the density of `f(X)`, `X ∼ P`, on `[a, b]`:
`inf{C ∈ [0,∞] : P(f ∈ B) ≤ C·Leb(B) for every Borel B ⊆ [a,b]}`. -/
def densUpper (P : Measure 𝒳) (f : 𝒳 → ℝ) (a b : ℝ) : ℝ≥0∞ :=
  sInf {C | ∀ B : Set ℝ, MeasurableSet B → B ⊆ Icc a b → P (f ⁻¹' B) ≤ C * volume B}

/-- The best lower bound on the density of `f(X)` on `[a, b]`:
`sup{c ∈ [0,∞] : c·Leb(B) ≤ P(f ∈ B) for every Borel B ⊆ [a,b]}`. -/
def densLower (P : Measure 𝒳) (f : 𝒳 → ℝ) (a b : ℝ) : ℝ≥0∞ :=
  sSup {c | ∀ B : Set ℝ, MeasurableSet B → B ⊆ Icc a b → c * volume B ≤ P (f ⁻¹' B)}

end Defs

namespace Claims

/-! ### `lem:sepmargin (v2)` -/

/-- `lem:sepmargin (v2)` (`C_recover.tex:367-380`): for `K ⊆ 𝓗` convex (and closed) with minimum-norm element `d*`, `D = ‖d*‖ > 0`,
`f* = d*/D`: `sep_K(f) ≤ ⟨f, d*⟩` for every `f`; `sep_K(f*) = D = max_{f ∈ B_𝓗} sep_K(f)`; `sep_K(f*) − sep_K(u) ≥ (D/2)‖u − f*‖²` for every
unit `u`; and `‖d' − d*‖² = (D' − D)² + D'D‖f' − f*‖²` for every `d'` with `D' = ‖d'‖ > 0`, `f' = d'/D'`. -/
def sepmargin : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (K : Set H) (dstar : H),
    Convex ℝ K → IsMinNorm K dstar → 0 < ‖dstar‖ →
      let D := ‖dstar‖
      let fstar := D⁻¹ • dstar
      (∀ f : H, sepK K f ≤ ((⟪f, dstar⟫_ℝ : ℝ) : EReal)) ∧
      sepK K fstar = (D : EReal) ∧
      IsGreatest (sepK K '' Metric.closedBall (0 : H) 1) (D : EReal) ∧
      (∀ u : H, ‖u‖ = 1 → ((D / 2 * ‖u - fstar‖ ^ 2 : ℝ) : EReal) ≤ sepK K fstar - sepK K u) ∧
      ∀ d' : H, 0 < ‖d'‖ →
        ‖d' - dstar‖ ^ 2 = (‖d'‖ - D) ^ 2 + ‖d'‖ * D * ‖‖d'‖⁻¹ • d' - fstar‖ ^ 2

/-! ### `lem:basicineq (v2)` -/

/-- `lem:basicineq (v2)` (`C_recover.tex:395-411`): under (A1)–(A2), `α ∈ (0,1)`, `β = α`, `D = D_{α,k}(P,Q) > 0` and `D̂ = D̂_{α,k} > 0`,
with `f* = d*/D`, `f̂ = d̂/D̂`, `t*` a `(1−α)`-quantile of `f*(X)`, `u*` an `α`-quantile of `f*(Y)`, `t̂` the `(n_α+1)`-th smallest of the
`f̂(X_i)` and `û` the `(m_α+1)`-th largest of the `f̂(Y_j)`: for every realisation,
`(D/2)‖f̂ − f*‖² ≤ ξ(f̂) − ξ(f*) ≤ β̄[(P − P_n){(t̂ − f̂)₊ − (t* − f*)₊} + (Q − Q_m){(f̂ − û)₊ − (f* − u*)₊}]`,
`ξ = sep_n − sep`, `β̄ = (1−α)⁻¹`. -/
def basicineq : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ α tstar ustar : ℝ) (n m : ℕ) (dstar : H),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < α → α < 1 → 1 ≤ n → 1 ≤ m →
    IsMinNorm (region φ α P - region φ α Q) dstar → 0 < Dpop φ P Q α →
    IsQuantile P (witFn ((Dpop φ P Q α)⁻¹ • dstar) φ) (1 - α) tstar →
    IsQuantile Q (witFn ((Dpop φ P Q α)⁻¹ • dstar) φ) α ustar →
      ∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳) (pr : (Fin n → ℝ) × (Fin m → ℝ)),
        pr ∈ capped n α ×ˢ capped m α →
        IsMinOn (qp (fun i => φ (x i)) (fun j => φ (y j))) (capped n α ×ˢ capped m α) pr →
        0 < Demp φ x y α →
          let D := Dpop φ P Q α
          let fstar := D⁻¹ • dstar
          let fh := (Demp φ x y α)⁻¹ • witness φ x y pr
          let th := ord (fun i => witFn fh φ (x i)) (kfloor n α)
          let uh := ordTop (fun j => witFn fh φ (y j)) α
          let ξ := fun f : H => sepAB (region φ α (empirical x)) (region φ α (empirical y)) f -
            sepAB (region φ α P) (region φ α Q) f
          D / 2 * ‖fh - fstar‖ ^ 2 ≤ ξ fh - ξ fstar ∧
          ξ fh - ξ fstar ≤ 1 / (1 - α) *
            (popDev P x (fun x' => max (th - witFn fh φ x') 0 - max (tstar - witFn fstar φ x') 0) +
              popDev Q y (fun y' => max (witFn fh φ y' - uh) 0 - max (witFn fstar φ y' - ustar) 0))

/-! ### `lem:localmod (v2)` -/

/-- `lem:localmod (v2)` (`C_recover.tex:454-478`): under (A1)–(A2), for fixed `f* ∈ 𝓗`, `t*, u* ∈ ℝ` and `r, λ₁, λ₂ ≥ 0`: `Z(r)` is
measurable, nonnegative, nondecreasing in `r` (and an upper bound of the bracket over `𝓗(r)`, integrable: declared additions),
`E Z(r) ≤ 2[κr√s + (κr + λ₁)e_n + (κr + λ₂)e_m]`, and for every `χ > 0`, with probability `≥ 1 − e^{−χ}`, `Z(r) ≤ κrL(χ) + M(χ)`. -/
def localmod : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ : ℝ) (fstar : H) (tstar ustar r l1 l2 : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ r → 0 ≤ l1 → 0 ≤ l2 → 1 ≤ n → 1 ≤ m →
      Measurable (fun z : (Fin n → 𝒳) × (Fin m → 𝒳) => Zloc P Q φ fstar tstar ustar κ r l1 l2 z) ∧
      (∀ z : (Fin n → 𝒳) × (Fin m → 𝒳), 0 ≤ Zloc P Q φ fstar tstar ustar κ r l1 l2 z) ∧
      (∀ z : (Fin n → 𝒳) × (Fin m → 𝒳), ∀ p ∈ rampPar fstar tstar ustar κ r l1 l2,
        rampDev P Q φ fstar tstar ustar z p ≤ Zloc P Q φ fstar tstar ustar κ r l1 l2 z) ∧
      (∀ z : (Fin n → 𝒳) × (Fin m → 𝒳),
        MonotoneOn (fun r' => Zloc P Q φ fstar tstar ustar κ r' l1 l2 z) (Ici 0)) ∧
      Integrable (fun z => Zloc P Q φ fstar tstar ustar κ r l1 l2 z) (sampleLaw P Q n m) ∧
      ∫ z, Zloc P Q φ fstar tstar ustar κ r l1 l2 z ∂(sampleLaw P Q n m) ≤
        2 * (κ * r * √(sNM n m) + (κ * r + l1) * ek n + (κ * r + l2) * ek m) ∧
      ∀ χ : ℝ, 0 < χ →
        ENNReal.ofReal (1 - Real.exp (-χ)) ≤ sampleLaw P Q n m
          {z | Zloc P Q φ fstar tstar ustar κ r l1 l2 z ≤ κ * r * Lloc χ n m + Mloc l1 l2 χ n m}

/-! ### `thm:trimrate (v2)` -/

/-- `thm:trimrate (v2)` (`08_trimming.tex:254-291`), (i)–(iii): under (A1)–(A2), `α ∈ (0,1)` with `D = D_{α,k}(P,Q) > 0`, `β = α`, (Q)
at `t_α` with constants `ρ, c_f, C_f` and (Q′) at an `α`-quantile `u_α` of `d*(Y)` with `c'_f`, for `δ ∈ (0,1)`, `θ > 1` and the printed
constants: if `τ^A = τ^A_{n,m}(α,δ/5) < D` and `max(λ_X, λ_Y) ≤ ρ`, then on a measurable event of probability `≥ 1 − δ`, at every
minimiser of `eq:qp`: (i) `D̂ > 0` and `‖d̂/D̂ − d*/D‖ ≤ ζ^loc/D`; (ii) `‖d̂ − d*‖ ≤ τ^A + √(1 + τ^A/D) ζ^loc`; (iii)
`|t̂_n/D̂ − t_α/D| ≤ (κζ^loc + λ_X)/D`, `Â_n △ A* ⊆ {|d* − t_α| ≤ ℓ^loc}`, and if `ℓ^loc ≤ ρ`, `P(Â_n △ A*) ≤ 2C_fℓ^loc` and
`∫|ĝ_n − g*| dP ≤ 2C_fℓ^loc/(1−α)`. -/
def trimrate : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ Dφ α δ θ ρ cf Cf cf' uα : ℝ) (n m : ℕ) (dstar : H),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ Dφ) →
    0 < α → α < 1 → 0 < Dpop φ P Q α → IsMinNorm (region φ α P - region φ α Q) dstar →
    0 < ρ → 0 < cf → 0 < cf' →
    QDensity P (witFn dstar φ) (quantileAt P (witFn dstar φ) (1 - α)) ρ cf Cf →
    IsQuantile Q (witFn dstar φ) α uα → QDensityLower Q (witFn dstar φ) uα ρ cf' →
    1 ≤ n → 1 ≤ m → 0 < δ → δ < 1 → 1 < θ →
    tauA κ Dφ α (δ / 5) n m < Dpop φ P Q α → max (lamQ cf δ n) (lamQ cf' δ m) ≤ ρ →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤ sampleLaw P Q n m E ∧
        ∀ z ∈ E, ∀ pr ∈ capped n α ×ˢ capped m α,
          IsMinOn (qp (fun i => φ (z.1 i)) (fun j => φ (z.2 j))) (capped n α ×ˢ capped m α) pr →
            RateConcl P Q φ κ Dφ α δ θ ρ cf Cf cf' n m dstar z pr

/-- `thm:trimrate (v2)`, last sentence (`08_trimming.tex:288-290`): with the event `E₁` of (i)–(iii) and an event `E₂` of
`thm:trimconsist` (probability `≥ 1 − δ`, on which its conclusions hold whenever `η < D` and `ℓ_{n,m} ≤ ρ`), `E₁ ∩ E₂` has probability
`≥ 1 − 2δ`, and on it, whenever in addition `η < D` and `ℓ_{n,m} ≤ ρ`, the inclusion and the two bounds of (iii) hold with `ℓ^loc`
replaced by `min(ℓ_{n,m}, ℓ^loc)`. -/
def trimrate_inter : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ Dφ α δ θ ρ cf Cf cf' uα : ℝ) (n m : ℕ) (dstar : H),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ Dφ) →
    0 < α → α < 1 → 0 < Dpop φ P Q α → IsMinNorm (region φ α P - region φ α Q) dstar →
    0 < ρ → 0 < cf → 0 < cf' →
    QDensity P (witFn dstar φ) (quantileAt P (witFn dstar φ) (1 - α)) ρ cf Cf →
    IsQuantile Q (witFn dstar φ) α uα → QDensityLower Q (witFn dstar φ) uα ρ cf' →
    1 ≤ n → 1 ≤ m → 0 < δ → δ < 1 → 1 < θ →
    tauA κ Dφ α (δ / 5) n m < Dpop φ P Q α → max (lamQ cf δ n) (lamQ cf' δ m) ≤ ρ →
      ∃ E₁ E₂ : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E₁ ∧ MeasurableSet E₂ ∧
        ENNReal.ofReal (1 - δ) ≤ sampleLaw P Q n m E₁ ∧ ENNReal.ofReal (1 - δ) ≤ sampleLaw P Q n m E₂ ∧
        ENNReal.ofReal (1 - 2 * δ) ≤ sampleLaw P Q n m (E₁ ∩ E₂) ∧
        (∀ z ∈ E₁, ∀ pr ∈ capped n α ×ˢ capped m α,
          IsMinOn (qp (fun i => φ (z.1 i)) (fun j => φ (z.2 j))) (capped n α ×ˢ capped m α) pr →
            RateConcl P Q φ κ Dφ α δ θ ρ cf Cf cf' n m dstar z pr) ∧
        (etaTC κ α δ n m < Dpop φ P Q α →
          lamTC κ (zetaTC (etaTC κ α δ n m) (Dpop φ P Q α)) cf δ n ≤ ρ →
          ∀ z ∈ E₂, ∀ pr ∈ capped n α ×ˢ capped m α,
            IsMinOn (qp (fun i => φ (z.1 i)) (fun j => φ (z.2 j))) (capped n α ×ˢ capped m α) pr →
              ConsistConcl P Q φ κ α δ ρ cf Cf n m dstar z pr) ∧
        (etaTC κ α δ n m < Dpop φ P Q α →
          lamTC κ (zetaTC (etaTC κ α δ n m) (Dpop φ P Q α)) cf δ n ≤ ρ →
          ∀ z ∈ E₁ ∩ E₂, ∀ pr ∈ capped n α ×ˢ capped m α,
            IsMinOn (qp (fun i => φ (z.1 i)) (fun j => φ (z.2 j))) (capped n α ×ˢ capped m α) pr →
              KeptConcl P φ α ρ Cf dstar (witness φ z.1 z.2 pr) (quantileAt P (witFn dstar φ) (1 - α))
                (tHat φ (witness φ z.1 z.2 pr) α z.1)
                (min (lamTC κ (zetaTC (etaTC κ α δ n m) (Dpop φ P Q α)) cf δ n)
                  (ellLoc κ (zetaLoc κ α (Dpop φ P Q α) θ (Jpeel θ n m) (Lloc (chiPeel θ δ n m) n m)
                    (Mloc (lamQ cf δ n) (lamQ cf' δ m) (chiPeel θ δ n m) n m)) (lamQ cf δ n))))

/-- `thm:trimrate (v2)`, the parenthetical "(under (A3), any `α < α*`)": for a characteristic kernel, `D_{α,k}(P,Q) > 0` for every
`α ∈ [0, α*)`, `α* = TV(P,Q)`. -/
def trimrate_A3 : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ α : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → Characteristic φ → 0 ≤ α →
    α < StatFormal.Distances.tvDist P Q → 0 < Dpop φ P Q α

/-! ### `cor:trimrate (v2)` -/

/-- `cor:trimrate (v2)` (`08_trimming.tex:307-319`), the four `O_P` statements in explicit form, with one factor `Λ` depending only
on the probability `ε` allowed: for `(P, Q, k, α)` satisfying the hypotheses of `thm:trimrate`, `c = min(c_f, c'_f)`,
`V_α = κ(1−α)⁻¹ + [(1−α)c]^{−1/2}` and `q = √(n∧m)`, there is `N` such that for `n, m ≥ N`, on a measurable event of probability
`≥ 1 − ε`, at every minimiser of `eq:qp`: `D̂ > 0`, `‖d̂/D̂ − d*/D‖ ≤ ΛV_α/(Dq)`, `‖d̂ − d*‖ ≤ ΛV_α/q`, and `P(Â_n △ A*)` and
`(1−α)∫|ĝ_n − g*| dP` (all tie functions) are `≤ ΛC_f(κV_α + c_f⁻¹)/q`. -/
def cor_trimrate : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ Λ : ℝ, 0 < Λ ∧
    ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
      (φ : 𝒳 → H) (κ α ρ cf Cf cf' uα : ℝ) (dstar : H),
      StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < α → α < 1 → 0 < Dpop φ P Q α →
      IsMinNorm (region φ α P - region φ α Q) dstar → 0 < ρ → 0 < cf → 0 < cf' →
      QDensity P (witFn dstar φ) (quantileAt P (witFn dstar φ) (1 - α)) ρ cf Cf →
      IsQuantile Q (witFn dstar φ) α uα → QDensityLower Q (witFn dstar φ) uα ρ cf' →
        ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
          ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
            ENNReal.ofReal (1 - ε) ≤ sampleLaw P Q n m E ∧
            ∀ z ∈ E, ∀ pr ∈ capped n α ×ˢ capped m α,
              IsMinOn (qp (fun i => φ (z.1 i)) (fun j => φ (z.2 j))) (capped n α ×ˢ capped m α) pr →
                let D := Dpop φ P Q α
                let V := κ / (1 - α) + 1 / √((1 - α) * min cf cf')
                let q := √((min n m : ℕ) : ℝ)
                let tα := quantileAt P (witFn dstar φ) (1 - α)
                let dh := witness φ z.1 z.2 pr
                let Dh := Demp φ z.1 z.2 α
                let th := tHat φ dh α z.1
                0 < Dh ∧
                ‖Dh⁻¹ • dh - D⁻¹ • dstar‖ ≤ Λ * (V / (D * q)) ∧
                ‖dh - dstar‖ ≤ Λ * (V / q) ∧
                P (symmDiff {x | witFn dh φ x < th} {x | witFn dstar φ x < tα}) ≤
                  ENNReal.ofReal (Λ * (Cf * (κ * V + 1 / cf) / q)) ∧
                ∀ ϑ ϑh : 𝒳 → ℝ, (∀ x, 0 ≤ ϑ x ∧ ϑ x ≤ 1 / (1 - α)) → (∀ x, 0 ≤ ϑh x ∧ ϑh x ≤ 1 / (1 - α)) →
                  (1 - α) * ∫ x, |plugDensityFn α ϑh (witFn dh φ) th x -
                    plugDensityFn α ϑ (witFn dstar φ) tα x| ∂P ≤ Λ * (Cf * (κ * V + 1 / cf) / q)

/-! ### `lem:contact (v2)` -/

/-- `lem:contact (v2)` (`C_recover.tex:662-667`), first sentence: under (A1)–(A2), `𝒞_{α,k}(P)` is norm-compact for every
`α ∈ [0,1)`. -/
def contact_compact : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P : Measure 𝒳) [IsProbabilityMeasure P] (φ : 𝒳 → H) (κ α : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 → IsCompact (region φ α P)

/-- `lem:contact (v2)` with its lead-in (`C_recover.tex:659-667`): `P∧Q` is the largest measure below `P` and `Q`, of mass
`1 − TV(P,Q)`; if `α* = TV(P,Q) < 1`, `R* = (P∧Q)/(1−α*)` is the only common element of `R_{α*}(P)` and `R_{α*}(Q)`, and under
(A1)–(A3) `𝒞_{α*,k}(P) ∩ 𝒞_{α*,k}(Q) = {μ_{R*}}` and `ω_c(ε) → 0` as `ε ↓ 0`. -/
def contact : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → Characteristic φ →
    StatFormal.Distances.tvDist P Q < 1 →
      IsGreatest {μ : Measure 𝒳 | μ ≤ P ∧ μ ≤ Q} (P ⊓ Q) ∧
      (P ⊓ Q) univ = ENNReal.ofReal (1 - StatFormal.Distances.tvDist P Q) ∧
      contactLaw P Q ∈ StatFormal.Wave8a.trimSet P (StatFormal.Distances.tvDist P Q) ∩
        StatFormal.Wave8a.trimSet Q (StatFormal.Distances.tvDist P Q) ∧
      (∀ R ∈ StatFormal.Wave8a.trimSet P (StatFormal.Distances.tvDist P Q) ∩
          StatFormal.Wave8a.trimSet Q (StatFormal.Distances.tvDist P Q), R = contactLaw P Q) ∧
      region φ (StatFormal.Distances.tvDist P Q) P ∩ region φ (StatFormal.Distances.tvDist P Q) Q =
        {∫ x, φ x ∂(contactLaw P Q)} ∧
      Tendsto (omegaC φ P Q) (𝓝[>] 0) (𝓝 0)

/-! ### `rem:nearcontact (v2)` -/

/-- `08_trimming.tex:338-340`, the lead-in of `rem:nearcontact (v2)` (proof: `C_recover.tex:729-730`): for laws with densities `p, q`
(with respect to a σ-finite `μ`) and `α* < 1`, `dR*/dP = β* min(p,q)/p` `P`-a.e., so `P`-a.e. the fractional set
`{0 < dR*/dP < β*}` is `{0 < q < p}`, and where `q ≥ p > 0` the contact trimming sits at its cap `β* = (1−α*)⁻¹`. -/
def nearcontact_densities : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (μ : Measure 𝒳) [SigmaFinite μ] (p q : 𝒳 → ℝ),
    Measurable p → Measurable q → (∀ x, 0 ≤ p x) → (∀ x, 0 ≤ q x) →
    IsProbabilityMeasure (μ.withDensity fun x => ENNReal.ofReal (p x)) →
    IsProbabilityMeasure (μ.withDensity fun x => ENNReal.ofReal (q x)) →
      let P := μ.withDensity fun x => ENNReal.ofReal (p x)
      let Q := μ.withDensity fun x => ENNReal.ofReal (q x)
      let βs := 1 / (1 - StatFormal.Distances.tvDist P Q)
      StatFormal.Distances.tvDist P Q < 1 →
        (∀ᵐ x ∂P, ((contactLaw P Q).rnDeriv P x).toReal = βs * min (p x) (q x) / p x) ∧
        (∀ᵐ x ∂P, (0 < ((contactLaw P Q).rnDeriv P x).toReal ∧ ((contactLaw P Q).rnDeriv P x).toReal < βs) ↔
          (0 < q x ∧ q x < p x)) ∧
        (∀ᵐ x ∂P, 0 < p x → p x ≤ q x → ((contactLaw P Q).rnDeriv P x).toReal = βs)

/-- `rem:nearcontact (v2)` (a) (`08_trimming.tex:336-345`): under (A1)–(A3) with `0 < α* < 1` and a fractional contact trimming
(`P(0 < dR*/dP < β*) > 0`), for population witnesses `d*_α` (`α ∈ [0, α*)`), `f*_α = d*_α/D_{α,k}(P,Q)`, `(1−α)`-quantiles `s_α` of
`f*_α(X)` and `A*_α = {f*_α < s_α}`: if `P(f*_α(X) = s_α) = 0` for every `α` in a left neighbourhood of `α*`, then `1_{A*_α}` has no limit
point in `L¹(P)` as `α ↑ α*`, and for every `ρ > 0` the smallest upper bound on the density of `f*_α(X)` on `[s_α − ρ, s_α + ρ]` tends to
infinity. -/
def nearcontact_a : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ : ℝ) (dstar : ℝ → H) (s : ℝ → ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → Characteristic φ →
    0 < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 →
    0 < P {x | 0 < ((contactLaw P Q).rnDeriv P x).toReal ∧
      ((contactLaw P Q).rnDeriv P x).toReal < 1 / (1 - StatFormal.Distances.tvDist P Q)} →
    (∀ α ∈ Ico 0 (StatFormal.Distances.tvDist P Q), IsMinNorm (region φ α P - region φ α Q) (dstar α)) →
    (∀ α ∈ Ico 0 (StatFormal.Distances.tvDist P Q),
      IsQuantile P (witFn ((Dpop φ P Q α)⁻¹ • dstar α) φ) (1 - α) (s α)) →
    (∀ᶠ α in 𝓝[<] (StatFormal.Distances.tvDist P Q), P {x | witFn ((Dpop φ P Q α)⁻¹ • dstar α) φ x = s α} = 0) →
      (∀ (a : ℕ → ℝ) (h : 𝒳 → ℝ), (∀ j, a j < StatFormal.Distances.tvDist P Q) →
        Tendsto a atTop (𝓝 (StatFormal.Distances.tvDist P Q)) → Integrable h P →
          ¬ Tendsto (fun j => ∫ x, |{x | witFn ((Dpop φ P Q (a j))⁻¹ • dstar (a j)) φ x < s (a j)}.indicator
              (fun _ => (1 : ℝ)) x - h x| ∂P) atTop (𝓝 0)) ∧
      ∀ ρ : ℝ, 0 < ρ →
        Tendsto (fun α => densUpper P (witFn ((Dpop φ P Q α)⁻¹ • dstar α) φ) (s α - ρ) (s α + ρ))
          (𝓝[<] (StatFormal.Distances.tvDist P Q)) (𝓝 ⊤)

/-- `rem:nearcontact (v2)` (b) (`08_trimming.tex:345-348`): under the lead-in hypotheses, if `k` is a Gaussian kernel on `ℝ^d` and
`P, Q` have continuous densities `p, q` with `{0 < q < p} ≠ ∅`, then `‖f*_α‖ = 1`, `f*_α → 0` weakly in `𝓗` as `α ↑ α*`, `f*_α(X) → 0` in
probability, `s_α → 0`, and on windows of every fixed half-width `ρ > 0` around `s_α` the best lower density bound of `f*_α(X)` tends to
`0` and the best upper bound to infinity. -/
def nearcontact_b : Prop :=
  ∀ (d : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : EuclideanSpace ℝ (Fin d) → H) (σ κ : ℝ)
    (p q : EuclideanSpace ℝ (Fin d) → ℝ) (dstar : ℝ → H) (s : ℝ → ℝ),
    0 < σ → (∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-‖x - y‖ ^ 2 / (2 * σ ^ 2))) →
    Continuous p → Continuous q → (∀ x, 0 ≤ p x) → (∀ x, 0 ≤ q x) →
    IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (p x)) →
    IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (q x)) →
      let P := volume.withDensity fun x => ENNReal.ofReal (p x)
      let Q := volume.withDensity fun x => ENNReal.ofReal (q x)
      StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → Characteristic φ →
      0 < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 →
      0 < P {x | 0 < ((contactLaw P Q).rnDeriv P x).toReal ∧
        ((contactLaw P Q).rnDeriv P x).toReal < 1 / (1 - StatFormal.Distances.tvDist P Q)} →
      {x | 0 < q x ∧ q x < p x}.Nonempty →
      (∀ α ∈ Ico 0 (StatFormal.Distances.tvDist P Q), IsMinNorm (region φ α P - region φ α Q) (dstar α)) →
      (∀ α ∈ Ico 0 (StatFormal.Distances.tvDist P Q),
        IsQuantile P (witFn ((Dpop φ P Q α)⁻¹ • dstar α) φ) (1 - α) (s α)) →
        (∀ α ∈ Ico 0 (StatFormal.Distances.tvDist P Q), ‖(Dpop φ P Q α)⁻¹ • dstar α‖ = 1) ∧
        (∀ h : H, Tendsto (fun α => ⟪(Dpop φ P Q α)⁻¹ • dstar α, h⟫_ℝ)
          (𝓝[<] (StatFormal.Distances.tvDist P Q)) (𝓝 0)) ∧
        (∀ η : ℝ, 0 < η → Tendsto (fun α => P {x | η ≤ |witFn ((Dpop φ P Q α)⁻¹ • dstar α) φ x|})
          (𝓝[<] (StatFormal.Distances.tvDist P Q)) (𝓝 0)) ∧
        Tendsto s (𝓝[<] (StatFormal.Distances.tvDist P Q)) (𝓝 0) ∧
        ∀ ρ : ℝ, 0 < ρ →
          Tendsto (fun α => densLower P (witFn ((Dpop φ P Q α)⁻¹ • dstar α) φ) (s α - ρ) (s α + ρ))
              (𝓝[<] (StatFormal.Distances.tvDist P Q)) (𝓝 0) ∧
            Tendsto (fun α => densUpper P (witFn ((Dpop φ P Q α)⁻¹ • dstar α) φ) (s α - ρ) (s α + ρ))
              (𝓝[<] (StatFormal.Distances.tvDist P Q)) (𝓝 ⊤)

/-! ### `prop:alphahat (v2)` -/

/-- `prop:alphahat (v2)` (`08_trimming.tex:370-385`), finite-sample part: under (A1)–(A3) with `0 < α* < 1`, `ω_c(ε) → 0` as `ε ↓ 0`;
for `δ' ∈ (0,1)` there is a measurable event `E` of probability `≥ 1 − 2δ'` (inside the events of `cor:uniform` for the two samples at
level `δ'`) on which, for every level `α̃ ∈ [0, α*]` and every `(w,v) ∈ 𝒯_{α̃}`,
`MMD_k(Σ w_iδ_{X_i}, R*) ≤ r_n + ω_c(D̂_{α̃,k} + r_n + r_m)` and `MMD_k(Σ v_jδ_{Y_j}, R*) ≤ r_m + ω_c^{Q,P}(D̂_{α̃,k} + r_n + r_m)`
(`r_n = r_n(α*,δ')`, `r_m = r_m(α*,δ')`); for `α̂` of `eq:alphaest` at level `δ`, `{α̂ ≤ α*}` is measurable, `E ∩ {α̂ ≤ α*}` has
probability `≥ 1 − δ − 2δ'`, and on it `D̂_{α̂,k} ≤ τ(α*)` and the two bounds hold at `α̃ = α̂`. -/
def alphahat : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ δ δ' : ℝ) (τ : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → Characteristic φ →
    0 < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 →
    0 < δ → δ < 1 → 0 < δ' → δ' < 1 → 1 ≤ n → 1 ≤ m →
    StatFormal.Wave30tu.ValidThreshold φ n m δ τ → ContinuousOn τ (Ioo 0 1) →
    (∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳), (crossSet (Demp φ x y) τ).Nonempty) →
      let αs := StatFormal.Distances.tvDist P Q
      let rN := rn κ αs δ' n
      let rM := rn κ αs δ' m
      let Bound := fun (z : (Fin n → 𝒳) × (Fin m → 𝒳)) (a : ℝ) =>
        ∀ pr ∈ capped n a ×ˢ capped m a,
          IsMinOn (qp (fun i => φ (z.1 i)) (fun j => φ (z.2 j))) (capped n a ×ˢ capped m a) pr →
            ‖∫ x, φ x ∂(wEmp pr.1 z.1) - ∫ x, φ x ∂(contactLaw P Q)‖ ≤
                rN + omegaC φ P Q (Demp φ z.1 z.2 a + rN + rM) ∧
              ‖∫ x, φ x ∂(wEmp pr.2 z.2) - ∫ x, φ x ∂(contactLaw P Q)‖ ≤
                rM + omegaC φ Q P (Demp φ z.1 z.2 a + rN + rM)
      Tendsto (omegaC φ P Q) (𝓝[>] 0) (𝓝 0) ∧
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - 2 * δ') ≤ sampleLaw P Q n m E ∧
        (∀ z ∈ E, ∀ α ∈ Ico (0 : ℝ) 1,
          Metric.hausdorffDist (region φ α (empirical z.1)) (region φ α P) ≤ rn κ α δ' n ∧
            Metric.hausdorffDist (region φ α (empirical z.2)) (region φ α Q) ≤ rn κ α δ' m) ∧
        (∀ z ∈ E, ∀ a ∈ Icc (0 : ℝ) αs, Bound z a) ∧
        MeasurableSet {z : (Fin n → 𝒳) × (Fin m → 𝒳) | alphaHat (Demp φ z.1 z.2) τ ≤ αs} ∧
        ENNReal.ofReal (1 - δ - 2 * δ') ≤
          sampleLaw P Q n m (E ∩ {z | alphaHat (Demp φ z.1 z.2) τ ≤ αs}) ∧
        ∀ z ∈ E ∩ {z | alphaHat (Demp φ z.1 z.2) τ ≤ αs},
          Demp φ z.1 z.2 (alphaHat (Demp φ z.1 z.2) τ) ≤ τ αs ∧ Bound z (alphaHat (Demp φ z.1 z.2) τ)

/-- `prop:alphahat (v2)`, the schedule sentence: under (A1)–(A3) with `0 < α* < 1`, along any schedule `δ → 0` with
`log(1/δ)/min(n,m) → 0` (thresholds `τ n m d` valid at level `d`, nondecreasing, continuous on `(0,1)`, with nonempty crossing sets, and
`≤ r_n(·,d/2) + r_m(·,d/2)`), `MMD_k(Σ w_iδ_{X_i}, R*) → 0` and `MMD_k(Σ v_jδ_{Y_j}, R*) → 0` in probability at `α̃ = α̂_{n,m}`, for every
`(w,v) ∈ 𝒯_{α̂}`. -/
def alphahat_schedule : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ : ℝ) (τ : ℕ → ℕ → ℝ → ℝ → ℝ) (ι : Type) (l : Filter ι) (n m : ι → ℕ) (δ : ι → ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → Characteristic φ →
    0 < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 →
    (∀ n m : ℕ, 1 ≤ n → 1 ≤ m → ∀ d : ℝ, 0 < d → d < 1 →
      StatFormal.Wave30tu.ValidThreshold φ n m d (τ n m d) ∧ ContinuousOn (τ n m d) (Ioo 0 1) ∧
      (∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳), (crossSet (Demp φ x y) (τ n m d)).Nonempty) ∧
      ∀ α ∈ Ico (0 : ℝ) 1, τ n m d α ≤ tau κ α d n m) →
    (∀ i, 1 ≤ n i) → (∀ i, 1 ≤ m i) → (∀ i, 0 < δ i) → Tendsto δ l (𝓝 0) →
    Tendsto (fun i => Real.log (1 / δ i) / (min (n i) (m i) : ℕ)) l (𝓝 0) →
      ∀ e : ℝ, 0 < e → ∃ E : ∀ i, Set ((Fin (n i) → 𝒳) × (Fin (m i) → 𝒳)), (∀ i, MeasurableSet (E i)) ∧
        (∀ i, E i ⊆ {z | let ah := alphaHat (Demp φ z.1 z.2) (τ (n i) (m i) (δ i))
          ∀ pr ∈ capped (n i) ah ×ˢ capped (m i) ah,
            IsMinOn (qp (fun k => φ (z.1 k)) (fun k => φ (z.2 k))) (capped (n i) ah ×ˢ capped (m i) ah) pr →
              ‖∫ x, φ x ∂(wEmp pr.1 z.1) - ∫ x, φ x ∂(contactLaw P Q)‖ ≤ e ∧
                ‖∫ x, φ x ∂(wEmp pr.2 z.2) - ∫ x, φ x ∂(contactLaw P Q)‖ ≤ e}) ∧
        Tendsto (fun i => sampleLaw P Q (n i) (m i) (E i)) l (𝓝 1)

end Claims

end StatFormal.Wave30tx
