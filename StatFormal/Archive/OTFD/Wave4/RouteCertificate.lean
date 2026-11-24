import StatFormal.Archive.OTFD.Wave4.Statements
import StatFormal.Archive.OTFD.Wave2.RouteTangent
import StatFormal.Archive.OTFD.Wave2.RouteConditional
import StatFormal.Archive.OTFD.Bands.Proofs
import StatFormal.Archive.OTFD.Bands2.RouteGuarantee
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Topology.Connected.Clopen

/-!
# Route: C `prop:conditional-certificate`

* Potentials. Entropic: `ψ(u) = ε log Σ_i exp(s_i(u|x)/ε)`; the subgradient inequality is Jensen for `exp`
  (`Σ_i q_i(u)(s_i(y) − s_i(u)) ≤ ψ(y) − ψ(u)`). Quadratic: `ψ(u) = λ(⟨q(u), s(u)/λ⟩ − ½‖q(u)‖²)`, the
  Moreau-envelope value at the maximiser `q(u)` (the projection maximises `⟨p, x⟩ − ½‖p‖²` over the simplex).
  Since `s(y) − s(u) = 2⟨Z, y − u⟩`, both give `ψ(y) ≥ ψ(u) + ⟨2T(u), y − u⟩`; convexity follows, and
  differentiability with gradient `2T` follows from continuity of `T` (`0 ≤ ψ(u+h) − ψ(u) − ⟨2T(u),h⟩ ≤
  ⟨2T(u+h) − 2T(u), h⟩`). Continuity of the quadratic map: the projection is 1-Lipschitz in `ℓ²` (`proj_VI`).
* Attainment: the certified `band_boundary_sup` (with `M = 1`) plus a maximiser of the continuous `⟨v, T⟩` on the
  nonempty compact frontier.
* Validity: `{U ∈ A} ⊆` band event (certified `guarantee_contain`), `μ_K(A_{K,p}) ≥ p` (certified
  `guarantee_level`); the band event is the preimage of a closed set under the continuous `T`.
* Witness, caps: the certified `band_dual_cert`, `tangent_caps_entropic`, `tangent_caps_quadratic`.
* Outer edges: every `q(u)`, `u ∈ A`, lies in the capped simplex, and a greedy fill is optimal there
  (certified `tangent_knapsack`).
-/

noncomputable section
open Finset Matrix MeasureTheory Filter Topology Set

namespace StatFormal.OTFD.Wave4

open StatFormal.OTFD.Bands StatFormal.OTFD.Bands2 StatFormal.OTFD.Wave2

variable {n K : ℕ}

/-! ### Generic potential lemmas -/

lemma dotCLM_apply (g h : Fin K → ℝ) : dotCLM g h = g ⬝ᵥ h := by
  simp [dotCLM, dotProduct]

lemma convexOn_of_subgrad {ψ : (Fin K → ℝ) → ℝ} {g : (Fin K → ℝ) → Fin K → ℝ}
    (hsub : ∀ u y, ψ u + g u ⬝ᵥ (y - u) ≤ ψ y) : ConvexOn ℝ Set.univ ψ := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain rfl : a = 1 - b := by linarith
  set z := (1 - b) • x + b • y with hz
  have hx : x - z = b • (x - y) := by
    rw [hz]; ext i; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hy : y - z = (1 - b) • -(x - y) := by
    rw [hz]; ext i; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    ring
  have h1 := hsub z x
  have h2 := hsub z y
  rw [hx, dotProduct_smul, smul_eq_mul] at h1
  rw [hy, dotProduct_smul, dotProduct_neg, smul_eq_mul] at h2
  simp only [smul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

lemma abs_dot_le (a h : Fin K → ℝ) : |a ⬝ᵥ h| ≤ K * (‖a‖ * ‖h‖) := by
  unfold dotProduct
  calc |∑ i, a i * h i| ≤ ∑ i, |a i * h i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin K, ‖a‖ * ‖h‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        exact mul_le_mul (norm_le_pi_norm a i) (norm_le_pi_norm h i) (abs_nonneg _) (norm_nonneg _)
    _ = K * (‖a‖ * ‖h‖) := by simp

lemma hasFDerivAt_of_subgrad {ψ : (Fin K → ℝ) → ℝ} {g : (Fin K → ℝ) → Fin K → ℝ}
    (hsub : ∀ u y, ψ u + g u ⬝ᵥ (y - u) ≤ ψ y) (hg : Continuous g) (u : Fin K → ℝ) :
    HasFDerivAt ψ (dotCLM (g u)) u := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.IsLittleO.of_bound fun c hc => ?_
  have hK : (0 : ℝ) < K + 1 := by positivity
  have hcont : Tendsto (fun h => g (u + h)) (𝓝 0) (𝓝 (g u)) := by
    have : Tendsto (fun h : Fin K → ℝ => u + h) (𝓝 0) (𝓝 u) := by
      simpa using (tendsto_const_nhds (x := u)).add (tendsto_id (x := 𝓝 (0 : Fin K → ℝ)))
    exact (hg.tendsto u).comp this
  have hev : ∀ᶠ h in 𝓝 (0 : Fin K → ℝ), ‖g (u + h) - g u‖ < c / (K + 1) := by
    have := (tendsto_iff_norm_sub_tendsto_zero.mp hcont).eventually (gt_mem_nhds (div_pos hc hK))
    simpa using this
  filter_upwards [hev] with h hh
  rw [dotCLM_apply]
  have hlo : 0 ≤ ψ (u + h) - ψ u - g u ⬝ᵥ h := by
    have := hsub u (u + h); rw [add_sub_cancel_left] at this; linarith
  have hhi : ψ (u + h) - ψ u - g u ⬝ᵥ h ≤ (g (u + h) - g u) ⬝ᵥ h := by
    have := hsub (u + h) u
    have e : u - (u + h) = -h := by abel
    rw [e, dotProduct_neg] at this
    rw [sub_dotProduct]; linarith
  rw [Real.norm_of_nonneg hlo]
  calc ψ (u + h) - ψ u - g u ⬝ᵥ h ≤ |(g (u + h) - g u) ⬝ᵥ h| := hhi.trans (le_abs_self _)
    _ ≤ K * (‖g (u + h) - g u‖ * ‖h‖) := abs_dot_le _ _
    _ ≤ (K + 1) * (c / (K + 1) * ‖h‖) := by
        apply mul_le_mul (by linarith) _ (by positivity) hK.le
        exact mul_le_mul_of_nonneg_right hh.le (norm_nonneg _)
    _ = c * ‖h‖ := by field_simp

lemma isHalfGrad_of_subgrad {ψ : (Fin K → ℝ) → ℝ} {T : (Fin K → ℝ) → Fin K → ℝ}
    (hsub : ∀ u y, ψ u + (2 • T u) ⬝ᵥ (y - u) ≤ ψ y) (hT : Continuous T) :
    IsHalfGradPotential ψ T :=
  ⟨convexOn_of_subgrad (g := fun u => 2 • T u) hsub, hsub,
    hasFDerivAt_of_subgrad (g := fun u => 2 • T u) hsub (hT.const_smul 2)⟩

/-! ### Scores -/

lemma score_cont (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ) (k : Fin n) :
    Continuous fun u => score a b k u := by
  unfold score; exact continuous_const.add (continuous_const.dotProduct continuous_id)

lemma condScore_sub (f : Fin n → ℝ) (Z : Fin n → Fin K → ℝ) (i : Fin n) (u y : Fin K → ℝ) :
    score (condA f Z) (condB Z) i y - score (condA f Z) (condB Z) i u = 2 * (Z i ⬝ᵥ (y - u)) := by
  simp only [score, condB, smul_dotProduct, dotProduct_sub, smul_eq_mul]; ring

lemma weighted_dot (w : Fin n → ℝ) (Z : Fin n → Fin K → ℝ) (d : Fin K → ℝ) :
    ∑ i, w i * (2 * (Z i ⬝ᵥ d)) = (2 • ∑ i, w i • Z i) ⬝ᵥ d := by
  rw [two_smul, add_dotProduct, sum_dotProduct, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_dotProduct, smul_eq_mul]; ring

/-! ### Entropic potential -/

lemma lse_jensen (hn : 0 < n) (x y : Fin n → ℝ) :
    ∑ i, softmax x i * (y i - x i) ≤
      Real.log (∑ i, Real.exp (y i)) - Real.log (∑ i, Real.exp (x i)) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hSx : 0 < ∑ i, Real.exp (x i) := Finset.sum_pos (fun i _ => Real.exp_pos _) univ_nonempty
  have hSy : 0 < ∑ i, Real.exp (y i) := Finset.sum_pos (fun i _ => Real.exp_pos _) univ_nonempty
  have hw := softmax_mem_simplex hn x
  have hj := convexOn_exp.map_sum_le (t := Finset.univ) (w := fun i => softmax x i)
    (p := fun i => y i - x i) (fun i _ => hw.1 i) hw.2 (fun i _ => Set.mem_univ _)
  simp only [smul_eq_mul] at hj
  have hrhs : ∑ i, softmax x i * Real.exp (y i - x i) =
      (∑ i, Real.exp (y i)) / ∑ i, Real.exp (x i) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold softmax
    rw [Real.exp_sub]; field_simp
  rw [hrhs] at hj
  rw [← Real.log_div hSy.ne' hSx.ne']
  exact (Real.le_log_iff_exp_le (div_pos hSy hSx)).2 hj

lemma entWeights_cont (ε : ℝ) (f : Fin n → ℝ) (Z : Fin n → Fin K → ℝ) (i : Fin n) :
    Continuous fun u => entWeights (condA f Z) (condB Z) ε u i := by
  unfold entWeights softmax
  refine Continuous.div ?_ ?_ fun u => ?_
  · exact Real.continuous_exp.comp ((score_cont _ _ i).div_const ε)
  · exact continuous_finsetSum _ fun k _ =>
      Real.continuous_exp.comp ((score_cont _ _ k).div_const ε)
  · have : Nonempty (Fin n) := ⟨i⟩
    exact (Finset.sum_pos (fun k _ => Real.exp_pos _) univ_nonempty).ne'

lemma condMapEnt_cont (ε : ℝ) (f : Fin n → ℝ) (Z : Fin n → Fin K → ℝ) :
    Continuous (condMapEnt ε f Z) := by
  unfold condMapEnt
  exact continuous_finsetSum _ fun i _ => (entWeights_cont ε f Z i).smul continuous_const

theorem cond_potential_ent : Claims.cond_potential_ent := by
  intro n K ε f Z hn hε
  set a := condA f Z
  set b := condB Z
  refine ⟨fun u => ε * Real.log (∑ i, Real.exp (score a b i u / ε)), ?_⟩
  refine isHalfGrad_of_subgrad (fun u y => ?_) (condMapEnt_cont ε f Z)
  have hj := lse_jensen hn (fun k => score a b k u / ε) (fun k => score a b k y / ε)
  have hsum : ∑ i, softmax (fun k => score a b k u / ε) i *
      (score a b i y / ε - score a b i u / ε) =
      (∑ i, softmax (fun k => score a b k u / ε) i * (2 * (Z i ⬝ᵥ (y - u)))) / ε := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sub_div, condScore_sub f Z i u y]; ring
  rw [hsum, weighted_dot] at hj
  have e : (2 • condMapEnt ε f Z u) ⬝ᵥ (y - u) =
      (2 • ∑ i, softmax (fun k => score a b k u / ε) i • Z i) ⬝ᵥ (y - u) := rfl
  rw [e]
  have h2 := (div_le_iff₀' hε).1 hj
  rw [mul_sub] at h2
  linarith

/-! ### Quadratic potential -/

lemma sum_sq_expand (r x : Fin n → ℝ) :
    ∑ i, (r i - x i) ^ 2 = ∑ i, r i ^ 2 - 2 * ∑ i, r i * x i + ∑ i, x i ^ 2 := by
  have : ∑ i, (r i - x i) ^ 2 = ∑ i, (r i ^ 2 - 2 * (r i * x i) + x i ^ 2) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

lemma proj_max {x q p : Fin n → ℝ} (hq : IsSimplexProj x q) (hp : p ∈ simplex n) :
    ∑ i, p i * x i - (∑ i, p i ^ 2) / 2 ≤ ∑ i, q i * x i - (∑ i, q i ^ 2) / 2 := by
  have h := hq.2 p hp
  rw [sum_sq_expand, sum_sq_expand] at h
  linarith

lemma proj_lip {x x' q q' : Fin n → ℝ} (hq : IsSimplexProj x q) (hq' : IsSimplexProj x' q') :
    ∑ i, (q i - q' i) ^ 2 ≤ ∑ i, (x i - x' i) ^ 2 := by
  have v1 := proj_VI hq hq'.1
  have v2 := proj_VI hq' hq.1
  have e : ∑ i, (x i - x' i) * (q i - q' i) - ∑ i, (q i - q' i) ^ 2 =
      ∑ i, (q i - x i) * (q' i - q i) + ∑ i, (q' i - x' i) * (q i - q' i) := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have amgm : ∑ i, (x i - x' i) * (q i - q' i) ≤
      (∑ i, (x i - x' i) ^ 2 + ∑ i, (q i - q' i) ^ 2) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (x i - x' i - (q i - q' i))]
  linarith

lemma quadWeights_cont {γ : ℝ} {m : ℕ} {f : Fin n → ℝ} {Z : Fin n → Fin K → ℝ}
    {q : (Fin K → ℝ) → Fin n → ℝ} (hq : IsQuadWeights γ m f Z q) : Continuous q := by
  set x : (Fin K → ℝ) → Fin n → ℝ :=
    fun u k => score (condA f Z) (condB Z) k u / (γ / m) with hx
  have hxc : ∀ k, Continuous fun u => x u k := fun k => (score_cont _ _ k).div_const _
  refine continuous_pi fun i => continuous_iff_continuousAt.2 fun u => ?_
  have hh : Continuous fun u' => Real.sqrt (∑ k, (x u' k - x u k) ^ 2) :=
    Real.continuous_sqrt.comp (continuous_finsetSum _ fun k _ =>
      ((hxc k).sub continuous_const).pow 2)
  have h0 : Real.sqrt (∑ k, (x u k - x u k) ^ 2) = 0 := by simp
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) (fun u' => ?_) (h0 ▸ hh.tendsto u)
  rw [Real.dist_eq]
  apply Real.abs_le_sqrt
  calc (q u' i - q u i) ^ 2 ≤ ∑ k, (q u' k - q u k) ^ 2 :=
        Finset.single_le_sum (f := fun k => (q u' k - q u k) ^ 2) (fun k _ => sq_nonneg _)
          (Finset.mem_univ i)
    _ ≤ ∑ k, (x u' k - x u k) ^ 2 := proj_lip (hq u') (hq u)

lemma condMapQuad_cont {γ : ℝ} {m : ℕ} {f : Fin n → ℝ} {Z : Fin n → Fin K → ℝ}
    {q : (Fin K → ℝ) → Fin n → ℝ} (hq : IsQuadWeights γ m f Z q) : Continuous (condMapQuad q Z) := by
  have hc := quadWeights_cont hq
  unfold condMapQuad
  exact continuous_finsetSum _ fun i _ => ((continuous_apply i).comp hc).smul continuous_const

theorem cond_potential_quad : Claims.cond_potential_quad := by
  intro n K m γ f Z q hγ hm hq
  have hlam : 0 < γ / (m : ℝ) := div_pos hγ (by exact_mod_cast hm)
  set lam := γ / (m : ℝ)
  set x : (Fin K → ℝ) → Fin n → ℝ := fun u k => score (condA f Z) (condB Z) k u / lam with hx
  refine ⟨fun u => lam * (∑ i, q u i * x u i - (∑ i, q u i ^ 2) / 2), ?_⟩
  refine isHalfGrad_of_subgrad (fun u y => ?_) (condMapQuad_cont hq)
  have hmax := proj_max (hq y) (hq u).1
  change ∑ i, q u i * x y i - _ ≤ ∑ i, q y i * x y i - _ at hmax
  have hlin : lam * (∑ i, q u i * x y i - ∑ i, q u i * x u i) =
      (2 • condMapQuad q Z u) ⬝ᵥ (y - u) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    unfold condMapQuad
    rw [← weighted_dot]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← condScore_sub f Z i u y, hx]
    field_simp
  rw [← hlin]
  have := mul_le_mul_of_nonneg_left hmax hlam.le
  nlinarith

/-! ### Attainment on the frontier -/

lemma sup_attained_of {T : (Fin K → ℝ) → Fin K → ℝ} {ψ : (Fin K → ℝ) → ℝ} (hK : 0 < K)
    (hψ : IsHalfGradPotential ψ T) (hT : Continuous T) {A : Set (Fin K → ℝ)} (hA : IsCompact A)
    (hne : A.Nonempty) (v : Fin K → ℝ) :
    ∃ u' ∈ frontier A, ∀ u ∈ A, v ⬝ᵥ T u ≤ v ⬝ᵥ T u' := by
  have : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  have hfc : IsCompact (frontier A) :=
    hA.of_isClosed_subset isClosed_frontier
      (frontier_subset_closure.trans hA.isClosed.closure_eq.le)
  have hfne : (frontier A).Nonempty := by
    rw [nonempty_frontier_iff]
    refine ⟨hne, fun h => ?_⟩
    rw [h] at hA
    exact noncompact_univ (Fin K → ℝ) hA
  obtain ⟨u', hu', hmax⟩ := hfc.exists_isMaxOn hfne
    ((continuous_const.dotProduct hT).continuousOn (s := frontier A))
  refine ⟨u', hu', fun u hu => ?_⟩
  have hsub : ∀ u y, ψ u + (2 • ((1 : Matrix (Fin K) (Fin K) ℝ) *ᵥ T u)) ⬝ᵥ (y - u) ≤ ψ y := by
    intro u y; rw [one_mulVec]; exact hψ.2.1 u y
  obtain ⟨u'', hu'', hle⟩ :=
    band_boundary_sup K 1 ψ T hK Matrix.PosDef.one hψ.1 hsub A hA v u hu
  exact hle.trans (hmax hu'')

theorem cond_sup_attained_ent : Claims.cond_sup_attained_ent := by
  intro n K ε f Z A v hn hK hε hA hne
  obtain ⟨ψ, hψ⟩ := cond_potential_ent n K ε f Z hn hε
  exact sup_attained_of hK hψ (condMapEnt_cont ε f Z) hA hne v

theorem cond_sup_attained_quad : Claims.cond_sup_attained_quad := by
  intro n K m γ f Z q A v hK hγ hm hq hA hne
  obtain ⟨ψ, hψ⟩ := cond_potential_quad n K m γ f Z q hγ hm hq
  exact sup_attained_of hK hψ (condMapQuad_cont hq) hA hne v

/-! ### Fitted-law validity -/

lemma bandEvent_closed {𝒯 : Type} (T : (Fin K → ℝ) → Fin K → ℝ) (A : Set (Fin K → ℝ))
    (mo : 𝒯 → ℝ) (e : 𝒯 → Fin K → ℝ) :
    IsClosed {c : Fin K → ℝ | curve mo e c ∈
      band (fun t => edgeLo T A (mo t) (e t)) (fun t => edgeUp T A (mo t) (e t))} := by
  have hc : ∀ t, Continuous fun c : Fin K → ℝ => ((curve mo e c t : ℝ) : EReal) := fun t =>
    continuous_coe_real_ereal.comp (continuous_const.add (continuous_const.dotProduct continuous_id))
  have : {c : Fin K → ℝ | curve mo e c ∈
      band (fun t => edgeLo T A (mo t) (e t)) (fun t => edgeUp T A (mo t) (e t))} =
      ⋂ t, ((fun c => ((curve mo e c t : ℝ) : EReal)) ⁻¹' Ici (edgeLo T A (mo t) (e t)) ∩
        (fun c => ((curve mo e c t : ℝ) : EReal)) ⁻¹' Iic (edgeUp T A (mo t) (e t))) := by
    ext c; simp [band]
  rw [this]
  exact isClosed_iInter fun t => (isClosed_Ici.preimage (hc t)).inter (isClosed_Iic.preimage (hc t))

lemma validity_of {𝒯 Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {T : (Fin K → ℝ) → Fin K → ℝ} (hT : Continuous T) {U : Ω → Fin K → ℝ} (hU : Measurable U)
    {g : (Fin K → ℝ) → ℝ} (hg : Continuous g) {𝒰 : Set (Fin K → ℝ)} (h𝒰 : IsCompact 𝒰)
    (h𝒰1 : P.map U 𝒰 = 1) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (mo : 𝒯 → ℝ) (e : 𝒯 → Fin K → ℝ) :
    MeasurableSet (bandEvent T (condRegion (P.map U) g 𝒰 p) mo e U) ∧
    ENNReal.ofReal p ≤ P (bandEvent T (condRegion (P.map U) g 𝒰 p) mo e U) := by
  set μ := P.map U with hμ
  set A := condRegion μ g 𝒰 p with hA
  have hev : bandEvent T A mo e U = U ⁻¹' (T ⁻¹' {c : Fin K → ℝ | curve mo e c ∈
      band (fun t => edgeLo T A (mo t) (e t)) (fun t => edgeUp T A (mo t) (e t))}) := rfl
  refine ⟨?_, ?_⟩
  · rw [hev]
    exact hU ((bandEvent_closed T A mo e).preimage hT).measurableSet
  -- `{U ∈ A}` is inside the band event
  have hsub : U ⁻¹' A ⊆ bandEvent T A mo e U := by
    intro ω hω
    exact guarantee_contain K 𝒯 T A mo e ⟨U ω, hω, rfl⟩
  have hAmeas : MeasurableSet A :=
    (h𝒰.isClosed.inter (isClosed_le hg continuous_const)).measurableSet
  -- level
  have hne : {τ | p ≤ calCdf μ g τ}.Nonempty := by
    obtain ⟨B, hB⟩ := h𝒰.bddAbove_image hg.continuousOn
    refine ⟨B, ?_⟩
    have hsub' : 𝒰 ⊆ {u | g u ≤ B} := fun u hu => hB ⟨u, hu, rfl⟩
    have h1 : μ {u | g u ≤ B} = 1 := le_antisymm prob_le_one (h𝒰1 ▸ measure_mono hsub')
    change p ≤ μ.real {u | g u ≤ B}
    rw [measureReal_def, h1]; simpa using hp1
  have hlev := guarantee_level K μ g p (calInv μ g p) hg.measurable hp hne le_rfl
  have hS : MeasurableSet {u | g u ≤ calInv μ g p} :=
    (isClosed_le hg continuous_const).measurableSet
  have hμA : μ A = μ {u | g u ≤ calInv μ g p} := by
    have hcompl : μ 𝒰ᶜ = 0 := by
      rw [measure_compl h𝒰.isClosed.measurableSet (measure_ne_top _ _), h𝒰1, measure_univ,
        tsub_self]
    have : A = {u | g u ≤ calInv μ g p} ∩ 𝒰 := by
      ext u; simp [hA, condRegion, and_comm]
    rw [this]
    exact measure_inter_conull hcompl
  calc ENNReal.ofReal p ≤ ENNReal.ofReal (calCdf μ g (calInv μ g p)) := ENNReal.ofReal_le_ofReal hlev
    _ = μ {u | g u ≤ calInv μ g p} := by
        unfold calCdf; rw [ofReal_measureReal (measure_ne_top _ _)]
    _ = μ A := hμA.symm
    _ = P (U ⁻¹' A) := by rw [hμ, Measure.map_apply hU hAmeas]
    _ ≤ P (bandEvent T A mo e U) := measure_mono hsub

theorem cond_validity_ent : Claims.cond_validity_ent := by
  intro n K 𝒯 Ω _ P _ ε f Z U g 𝒰 p mo e _hn _hε hU hg h𝒰 h𝒰1 hp hp1
  exact validity_of (condMapEnt_cont ε f Z) hU hg h𝒰 h𝒰1 hp hp1 mo e

theorem cond_validity_quad : Claims.cond_validity_quad := by
  intro n K m 𝒯 Ω _ P _ γ f Z q U g 𝒰 p mo e _hγ _hm hq hU hg h𝒰 h𝒰1 hp hp1
  exact validity_of (condMapQuad_cont hq) hU hg h𝒰 h𝒰1 hp hp1 mo e

/-! ### Witness and caps -/

theorem cond_gap_witness : Claims.cond_gap_witness := by
  intro n K f Z A ω i hA hne hω
  set φ := fun u : Fin K → ℝ => (condB Z i - ∑ k, ω k • condB Z k) ⬝ᵥ u
  have hφ : Continuous φ := continuous_const.dotProduct continuous_id
  have hbdd : BddAbove (φ '' A) := hA.bddAbove_image hφ.continuousOn
  have hσ : ∀ u ∈ A, φ u ≤ sSup (φ '' A) := fun u hu => le_csSup hbdd ⟨u, hu, rfl⟩
  exact band_dual_cert n K (condA f Z) (condB Z) A i ω _ hne hω hσ

theorem cond_caps_ent : Claims.cond_caps_ent := by
  intro n K ε f Z A δlow u hn hε hu hδ
  exact (tangent_caps_entropic n K ℝ (condA f Z) (condB Z) A ε δlow 0 u hn hε hu hδ).1

theorem cond_caps_quad : Claims.cond_caps_quad := by
  intro n K m γ f Z q A δlow u hγ hm hq hu hδ
  have hlam : 0 < γ / (m : ℝ) := div_pos hγ (by exact_mod_cast hm)
  exact (tangent_caps_quadratic n K ℝ (condA f Z) (condB Z) A (γ / m) δlow 0 u (q u) hlam hu hδ
    (hq u)).1

/-! ### Outer edges -/

lemma dot_barycenter (v : Fin K → ℝ) (w : Fin n → ℝ) (Z : Fin n → Fin K → ℝ) (mo : ℝ)
    (hw : w ∈ simplex n) : mo + v ⬝ᵥ ∑ i, w i • Z i = ∑ i, w i * (mo + v ⬝ᵥ Z i) := by
  rw [dotProduct_sum]
  simp only [dotProduct_smul, smul_eq_mul, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw.2,
    one_mul]

lemma outer_edges_of {T : (Fin K → ℝ) → Fin K → ℝ} {w : (Fin K → ℝ) → Fin n → ℝ}
    {Z : Fin n → Fin K → ℝ} {A : Set (Fin K → ℝ)} {κ : Fin n → ℝ}
    (hT : ∀ u, T u = ∑ i, w u i • Z i) (hw : ∀ u ∈ A, w u ∈ cappedSimplex κ)
    (mo : ℝ) (v : Fin K → ℝ) {qhi qlo : Fin n → ℝ}
    (hhi : IsGreedyFill κ (fun i => mo + v ⬝ᵥ Z i) qhi)
    (hlo : IsGreedyFill κ (fun i => -(mo + v ⬝ᵥ Z i)) qlo) :
    edgeUp T A mo v ≤ ((∑ i, qhi i * (mo + v ⬝ᵥ Z i) : ℝ) : EReal) ∧
    ((∑ i, qlo i * (mo + v ⬝ᵥ Z i) : ℝ) : EReal) ≤ edgeLo T A mo v := by
  have hk := tangent_knapsack n κ (fun i => mo + v ⬝ᵥ Z i) qhi
  have hk' := tangent_knapsack n κ (fun i => mo + v ⬝ᵥ Z i) qlo
  set c := fun i => mo + v ⬝ᵥ Z i
  have hval : ∀ u ∈ A, mo + v ⬝ᵥ T u = ∑ i, w u i * c i := fun u hu => by
    rw [hT u]; exact dot_barycenter v (w u) Z mo (hw u hu).1
  constructor
  · unfold edgeUp hsup
    have hb : ∀ u ∈ A, v ⬝ᵥ T u ≤ ∑ i, qhi i * c i - mo := by
      intro u hu
      have := (hk.1 hhi).2 ⟨w u, hw u hu, rfl⟩
      have h2 := hval u hu
      simp only at this; linarith
    have : (⨆ u ∈ A, ((v ⬝ᵥ T u : ℝ) : EReal)) ≤ ((∑ i, qhi i * c i - mo : ℝ) : EReal) :=
      iSup₂_le fun u hu => EReal.coe_le_coe_iff.2 (hb u hu)
    calc (mo : EReal) + ⨆ u ∈ A, ((v ⬝ᵥ T u : ℝ) : EReal)
        ≤ (mo : EReal) + ((∑ i, qhi i * c i - mo : ℝ) : EReal) := by gcongr
      _ = ((∑ i, qhi i * c i : ℝ) : EReal) := by rw [← EReal.coe_add]; congr 1; ring
  · unfold edgeLo hsup
    have hb : ∀ u ∈ A, (-v) ⬝ᵥ T u ≤ mo - ∑ i, qlo i * c i := by
      intro u hu
      have := (hk'.2 hlo).2 ⟨w u, hw u hu, rfl⟩
      have h2 := hval u hu
      rw [neg_dotProduct]
      simp only at this; linarith
    have : (⨆ u ∈ A, (((-v) ⬝ᵥ T u : ℝ) : EReal)) ≤ ((mo - ∑ i, qlo i * c i : ℝ) : EReal) :=
      iSup₂_le fun u hu => EReal.coe_le_coe_iff.2 (hb u hu)
    calc ((∑ i, qlo i * c i : ℝ) : EReal) = (mo : EReal) - ((mo - ∑ i, qlo i * c i : ℝ) : EReal) := by
          rw [← EReal.coe_sub]; congr 1; ring
      _ ≤ (mo : EReal) - ⨆ u ∈ A, (((-v) ⬝ᵥ T u : ℝ) : EReal) := EReal.sub_le_sub le_rfl this

theorem cond_outer_edges_ent : Claims.cond_outer_edges_ent := by
  intro n K ε f Z A δlow mo v qhi qlo hn hε hδ hhi hlo
  refine outer_edges_of (w := fun u => entWeights (condA f Z) (condB Z) ε u) (fun u => rfl)
    (fun u hu => cond_caps_ent n K ε f Z A δlow u hn hε hu hδ) mo v hhi hlo

theorem cond_outer_edges_quad : Claims.cond_outer_edges_quad := by
  intro n K m γ f Z q A δlow mo v qhi qlo hγ hm hq hδ hhi hlo
  exact outer_edges_of (w := q) (fun u => rfl)
    (fun u hu => cond_caps_quad n K m γ f Z q A δlow u hγ hm hq hu hδ) mo v hhi hlo

end StatFormal.OTFD.Wave4
