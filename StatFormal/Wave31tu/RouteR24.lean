import StatFormal.Wave31tu.Statements
import StatFormal.Wave31tr.Proofs

/-!
# Wave 31tu route R: the paper's run is a genuine-quantile run (§4 :60-68, S3 :105-111, :181-182, §7 :20-22; untrusted proof
material)

* `genuine_ramp`: on every batch, the per-level rule of a paper run (Wave 31tr `IsPaperRun`) with genuine-quantile cut rules `qt`,
  `qu` is a genuine-quantile ramp, own-term branch of `GenuineCuts`: the selected exact minimizer, `t̂ = qt n_{<b} (own-term X
  values) (1−α)` a genuine empirical `(1−α)`-quantile and `û = qu m_{<b} (own-term Y values) α` a genuine empirical `α`-quantile
  (copy-adapted from the certified `Wave31tr.RouteRun.paperRun_witnessRamp`, with `GenuineCuts` in place of `CutsC`);
* `genuine_paperrun_route` (Y24 (a)): admissibility, the fractions and the default batches from 31tr T5 `paperRun_admissible`
  (a genuine rule is a quantile rule, 31tr T1 `genuine_rules`), the ramps from `genuine_ramp`;
* `boundaries_of_nearest`: nearest-integer boundaries are interior boundaries (`IsBoundaries 2`);
* `genuine_run_exists_route` (Y24 (c)): 31tr T4 `paperRun_exists` at the printed rule (`lowQ`, `highQ`, `w₀ = 20`, `v₀ ≡ 1`,
  `λ_max = ½`) with the given boundaries, then Y24 (a) with 31tr T1.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tu.RouteR

open StatFormal.Wave30tq StatFormal.Wave30tv StatFormal.Wave30tz StatFormal.Wave31tl StatFormal.Wave31tr

section Run

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {φ : 𝒳 → H} {J n m : ℕ} {R : LoRun 𝒳 J n m} {α : Fin J → ℝ} {δ lmax s2 w0 : ℝ}
  {v0 : Fin J → ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ} {qt qu : (k : ℕ) → (Fin k → ℝ) → ℝ → ℝ} {nb : ℕ} {cx cy : ℕ → ℕ}

/-- **The ramps of a paper run with genuine-quantile cut rules are genuine-quantile ramps** (own-term branch). -/
theorem genuine_ramp (hP : IsPaperRun R φ α δ lmax s2 w0 v0 qt qu nb cx cy) (hqt : IsGenuineQuantileRule qt)
    (hqu : IsGenuineQuantileRule qu) (hgrid : IsGrid α) (j : Fin J) (b : ℕ) (x : Fin n → 𝒳) (y : Fin m → 𝒳) :
    IsGenuineRamp φ (α j) (fitSample R.lx b x) (fitSample R.ly b y) (R.has j b x y) (R.g j b x y) := by
  obtain ⟨-, -, -, -, -, -, σ, hσ, hhg, -⟩ := hP
  have hα := hgrid.2 j
  obtain ⟨hhas, hg⟩ := hhg j b x y
  refine ⟨fun h hh => ?_, fun h1 h2 => ⟨(σ j b (fitSample R.lx b x, fitSample R.ly b y)).1,
    (σ j b (fitSample R.lx b x, fitSample R.ly b y)).2, (hσ j b h1 h2).2 _, fun h0 hh => ?_, fun hpos => ⟨_, _,
      Or.inr ⟨(hqt.2 _ _ _ h1 (by linarith) (by linarith)).1, (hqu.2 _ _ _ h2 hα.1 hα.2.le).1⟩, ?_, fun hh => ?_⟩⟩⟩
  · obtain ⟨a1, a2, -⟩ := hhas.mp hh
    omega
  · exact absurd h0 (ne_of_gt (hhas.mp hh).2.2.1)
  · rw [hhas]
    exact ⟨fun h => h.2.2.2, fun h => ⟨h1, h2, hpos, h⟩⟩
  · rw [hg, ite_eq_left hh]
    rfl

end Run

/-- **Y24 (a)**: a paper run with genuine-quantile cut rules and nearest-integer boundaries is a genuine-quantile run with the default
batches. -/
theorem genuine_paperrun_route : Claims.genuine_paperrun := by
  intro H _ _ _ φ κ J n m α δ s2 w0 v0 qt qu cxx cyy R hφ hκ hgrid _ hδ0 hδ1 hs20 _ hw0 hqt hqu hcx hcy hP
  obtain ⟨-, -, hqrule⟩ := Wave31tr.genuine_rules
  obtain ⟨hadm, hwit, hdef, -⟩ := Wave31tr.paperRun_admissible ℝ H φ κ J n m α δ (1 / 2) s2 w0 v0 qt qu 2 cxx cyy R hφ hκ
    hgrid hδ0 hδ1 (by norm_num) (by norm_num) hs20 hw0 (hqrule qt hqt) (hqrule qu hqu) hP
  exact ⟨⟨hadm, fun j k x y => genuine_ramp hP hqt hqu hgrid j (R.bat k) x y, hwit.2.2⟩, hdef rfl hcx hcy⟩

/-- Nearest-integer boundaries are interior boundaries: `c 1 ≤ c 2 ≤ n`. -/
theorem boundaries_of_nearest {n : ℕ} {c : ℕ → ℕ} (hc : NearestCuts n (c 1) (c 2)) : IsBoundaries 2 n c := by
  obtain ⟨h12, h2n⟩ := RouteRun.nearestCuts_bounds hc
  refine ⟨fun a ha b hb hab => ?_, fun b hb => ?_⟩
  · obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    interval_cases a <;> interval_cases b <;> omega
  · obtain ⟨hb1, hb2⟩ := hb
    interval_cases b <;> omega

/-- **Y24 (c)**: the printed run (cut rules `lowQ`, `highQ`, `w₀ = 20`, `v₀ ≡ 1`, `λ_max = ½`, the given nearest-integer
boundaries) exists and is a genuine-quantile run with the default batches. -/
theorem genuine_run_exists_route : Claims.genuine_run_exists := by
  intro H _ _ _ φ κ J n m α δ s2 cxx cyy hφ hκ hgrid hα0 hδ0 hδ1 hs20 hs24 hcx hcy
  obtain ⟨R, hR⟩ := Wave31tr.paperRun_exists ℝ H φ J n m α δ (1 / 2) s2 20 (fun _ _ _ _ => 1) lowQ highQ 2 cxx cyy hφ
    (fun j => hgrid.2 j) hδ0 hδ1 (by norm_num) (by norm_num) hs20 (by norm_num) (boundaries_of_nearest hcx)
    (boundaries_of_nearest hcy) (RouteRun.prior_one _ _)
  obtain ⟨hlow, hhigh, -⟩ := Wave31tr.genuine_rules
  exact ⟨R, hR, genuine_paperrun_route H φ κ J n m α δ s2 20 _ lowQ highQ cxx cyy R hφ hκ hgrid hα0 hδ0 hδ1 hs20 hs24
    (by norm_num) hlow hhigh hcx hcy hR⟩

end StatFormal.Wave31tu.RouteR
