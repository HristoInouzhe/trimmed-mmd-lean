import StatFormal.Archive.OTFD.Wave6b.Statements
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Route: R `thm:region-breakdown`

* `betaPlus_eq`: `β⁺(A) ≤ inf_A d⁻` because `H_{t,D}(e) ⊆ {⟨·−u,e⟩ > 0}`; conversely, for `c < inf_A d⁻` every
  `(u,e) ∈ A × S` has an `N` with `c < ν(O_N(u,e))`, `O_N = {2/N < ⟨z−u,e⟩, ‖z−u‖ < N/2}` (continuity from
  below), and `O_N(u,e) ⊆ H_{1/N,N}(e')` centred at `u'` for `(u',e')` near `(u,e)`; a directed open cover of the
  compact `A × S` gives one `N` for all of `A × S`.
* `region_bounded`: the bound of `EntropicA` is decreasing in `δ`, and `δ_{t,D}(u) ≥ inf_A δ_{t,D}`.
* `region_unbounded`: pick `u ∈ A` with `n d⁻(u) < ℓ` and apply `EntropicB`.
* `region_bp_general`: bracket the first exploding `ℓ` between `nβ⁻` and `⌊nβ⁻⌋ + 1`.
* `region_bp`: for `ν ≪ volume`, hyperplanes are null, so `d⁻(u) = TD(u)`.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ENNReal Topology

namespace StatFormal.OTFD.Wave6b

open StatFormal.OTFDR (piCond Qhat)
open StatFormal.OTFDR.Lift (Contam Explodes BP)
open StatFormal.OTFD.Wave1 (HtD regionDepth tukeyDepth)

variable {K : ℕ}

/-! ### `Q̂` is a convex combination -/

lemma piCond_nonneg {n : ℕ} (z : Fin n → EuclideanSpace ℝ (Fin K)) (f : Fin n → ℝ) (ε : ℝ) (u) (i) :
    0 ≤ piCond z f ε u i := by
  unfold piCond
  exact div_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)

lemma piCond_le_one {n : ℕ} (z : Fin n → EuclideanSpace ℝ (Fin K)) (f : Fin n → ℝ) (ε : ℝ) (u) (i) :
    piCond z f ε u i ≤ 1 := by
  unfold piCond
  rw [div_le_one (lt_of_lt_of_le (Real.exp_pos _)
    (Finset.single_le_sum (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i)))]
  exact Finset.single_le_sum (f := fun j => Real.exp ((f j - ‖u - z j‖ ^ 2 / 2) / ε))
    (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i)

lemma norm_qhat_le {n : ℕ} (z : Fin n → EuclideanSpace ℝ (Fin K)) (f : Fin n → ℝ) (ε : ℝ) (u) :
    ‖Qhat z f ε u‖ ≤ ∑ i, ‖z i‖ := by
  unfold Qhat
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (piCond_nonneg z f ε u i)]
  exact mul_le_of_le_one_left (norm_nonneg _) (piCond_le_one z f ε u i)

/-! ### `β⁺(A) = inf_A d⁻` -/

lemma halfMass_le_dMinus (ν : Measure (EuclideanSpace ℝ (Fin K))) (u : EuclideanSpace ℝ (Fin K))
    {t D : ℝ} (ht : 0 < t) : halfMass ν u t D ≤ dMinus ν u :=
  iInf₂_mono fun _ _ => measure_mono fun _ hz => lt_of_lt_of_le ht hz.1

theorem betaPlus_le (ν : Measure (EuclideanSpace ℝ (Fin K))) (A : Set (EuclideanSpace ℝ (Fin K))) :
    betaPlus ν A ≤ ⨅ u ∈ A, dMinus ν u :=
  iSup₂_le fun _t ht => iSup_le fun _D => iInf₂_mono fun u _ => halfMass_le_dMinus ν u ht

/-- The open inner set `O_N(u,e) = {2/N < ⟨z−u,e⟩, ‖z−u‖ < N/2}`. -/
def Oset (u e : EuclideanSpace ℝ (Fin K)) (N : ℝ) : Set (EuclideanSpace ℝ (Fin K)) :=
  {z | 2 / N < ⟪z - u, e⟫_ℝ ∧ ‖z - u‖ < N / 2}

lemma Oset_subset_HtD {u e u' e' : EuclideanSpace ℝ (Fin K)} {N : ℝ} (hN : 1 ≤ N) (he : ‖e‖ = 1)
    (hu : ‖u - u'‖ < 1 / (4 * N)) (he' : ‖e' - e‖ < 1 / N ^ 2) :
    Oset u e N ⊆ HtD u' (1 / N) N e' := by
  intro z hz
  obtain ⟨h1, h2⟩ := hz
  have hN0 : 0 < N := by linarith
  set a := 1 / N with ha
  have haN : N * a = 1 := by rw [ha]; field_simp
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := by rw [ha, div_le_one hN0]; exact hN
  have hdecomp : ⟪z - u', e'⟫_ℝ = ⟪z - u, e⟫_ℝ + ⟪z - u, e' - e⟫_ℝ + ⟪u - u', e'⟫_ℝ := by
    have : z - u' = (z - u) + (u - u') := by abel
    rw [this, inner_add_left, inner_sub_right]; ring
  have hb1 : |⟪z - u, e' - e⟫_ℝ| ≤ ‖z - u‖ * ‖e' - e‖ := abs_real_inner_le_norm _ _
  have hb2 : |⟪u - u', e'⟫_ℝ| ≤ ‖u - u'‖ * ‖e'‖ := abs_real_inner_le_norm _ _
  have he'n : ‖e'‖ ≤ 2 := by
    have : ‖e'‖ ≤ ‖e‖ + ‖e' - e‖ := by
      have := norm_add_le e (e' - e); simpa using this
    have : 1 / N ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    linarith
  have hp1 : ‖z - u‖ * ‖e' - e‖ ≤ N / 2 * (1 / N ^ 2) :=
    mul_le_mul h2.le he'.le (norm_nonneg _) (by positivity)
  have hp2 : ‖u - u'‖ * ‖e'‖ ≤ 1 / (4 * N) * 2 :=
    mul_le_mul hu.le he'n (norm_nonneg _) (by positivity)
  have hq1 : N / 2 * (1 / N ^ 2) = a / 2 := by rw [ha]; field_simp
  have hq2 : 1 / (4 * N) * 2 = a / 2 := by rw [ha]; field_simp; ring
  have hq3 : 2 / N = 2 * a := by rw [ha]; ring
  refine ⟨?_, ?_⟩
  · rw [hdecomp]
    have := neg_abs_le ⟪z - u, e' - e⟫_ℝ
    have := neg_abs_le ⟪u - u', e'⟫_ℝ
    linarith
  · have : ‖z - u'‖ ≤ ‖z - u‖ + ‖u - u'‖ := by
      have := norm_add_le (z - u) (u - u'); simpa using this
    have h4 : 1 / (4 * N) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith

lemma HtD_mono {u e : EuclideanSpace ℝ (Fin K)} {N N' : ℝ} (hN : 1 ≤ N) (h : N ≤ N') :
    HtD u (1 / N) N e ⊆ HtD u (1 / N') N' e := by
  intro z hz
  refine ⟨le_trans (one_div_le_one_div_of_le (by linarith) h) hz.1, hz.2.trans h⟩

lemma Oset_mono (u e : EuclideanSpace ℝ (Fin K)) : Monotone fun m : ℕ => Oset u e ((m : ℝ) + 1) := by
  intro m m' h z hz
  have h' : (m : ℝ) + 1 ≤ (m' : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ h
  refine ⟨lt_of_le_of_lt ?_ hz.1, lt_of_lt_of_le hz.2 (by linarith)⟩
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) h'

lemma iUnion_Oset (u e : EuclideanSpace ℝ (Fin K)) :
    (⋃ m : ℕ, Oset u e ((m : ℝ) + 1)) = {z | 0 < ⟪z - u, e⟫_ℝ} := by
  ext z
  simp only [mem_iUnion, mem_ofPred_eq, Oset]
  constructor
  · rintro ⟨m, h1, _⟩
    exact lt_of_le_of_lt (by positivity) h1
  · intro hs
    obtain ⟨m, hm⟩ := exists_nat_gt (2 / ⟪z - u, e⟫_ℝ + 2 * ‖z - u‖)
    refine ⟨m, ?_, ?_⟩
    · rw [div_lt_iff₀ (by positivity)]
      have : 2 / ⟪z - u, e⟫_ℝ < m + 1 := by have := norm_nonneg (z - u); linarith
      rw [div_lt_iff₀ hs] at this
      linarith
    · have := div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hs.le
      linarith

theorem le_betaPlus (ν : Measure (EuclideanSpace ℝ (Fin K))) {A : Set (EuclideanSpace ℝ (Fin K))}
    (hA : IsCompact A) : ⨅ u ∈ A, dMinus ν u ≤ betaPlus ν A := by
  refine le_of_forall_lt_imp_le_of_dense fun c hc => ?_
  -- the open cover `U m = interior {(u,e) : c < ν(H_{1/N,N}(e) at u)}`, `N = m + 1`
  set U : ℕ → Set (EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K)) := fun m =>
    interior {p | c < ν (HtD p.1 (1 / ((m : ℝ) + 1)) ((m : ℝ) + 1) p.2)} with hU
  have hUmono : Monotone U := by
    intro m m' h
    apply interior_mono
    intro p hp
    have h' : (m : ℝ) + 1 ≤ (m' : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ h
    exact lt_of_lt_of_le hp (measure_mono (HtD_mono (by linarith [m.cast_nonneg (α := ℝ)]) h'))
  have hcover : A ×ˢ Metric.sphere (0 : EuclideanSpace ℝ (Fin K)) 1 ⊆ ⋃ m, U m := by
    rintro ⟨u, e⟩ ⟨hu, he⟩
    have he1 : ‖e‖ = 1 := by simpa using he
    have hcu : c < ν {z | 0 < ⟪z - u, e⟫_ℝ} := by
      have h1 : ⨅ u ∈ A, dMinus ν u ≤ dMinus ν u := iInf₂_le u hu
      have h2 : dMinus ν u ≤ ν {z | 0 < ⟪z - u, e⟫_ℝ} := iInf₂_le e he1
      exact lt_of_lt_of_le hc (h1.trans h2)
    rw [← iUnion_Oset u e, (Oset_mono u e).measure_iUnion, lt_iSup_iff] at hcu
    obtain ⟨m, hm⟩ := hcu
    refine mem_iUnion.mpr ⟨m, ?_⟩
    set N : ℝ := (m : ℝ) + 1 with hN
    have hN1 : 1 ≤ N := by rw [hN]; linarith [m.cast_nonneg (α := ℝ)]
    have hN0 : 0 < N := by linarith
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
    refine ⟨min (1 / (4 * N)) (1 / N ^ 2), lt_min (by positivity) (by positivity), ?_⟩
    rintro ⟨u', e'⟩ hp
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [dist_eq_norm] at hp1 hp2
    have hu' : ‖u - u'‖ < 1 / (4 * N) := by
      rw [norm_sub_rev]; exact lt_of_lt_of_le hp1 (min_le_left _ _)
    have he' : ‖e' - e‖ < 1 / N ^ 2 := lt_of_lt_of_le hp2 (min_le_right _ _)
    exact lt_of_lt_of_le hm (measure_mono (Oset_subset_HtD hN1 he1 hu' he'))
  obtain ⟨m, hm⟩ := (hA.prod (isCompact_sphere 0 1)).elim_directed_cover U
    (fun m => isOpen_interior) hcover hUmono.directed_le
  -- conclude `c ≤ inf_A δ_{1/N,N} ≤ β⁺`
  have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
  have hstep : (⨅ u ∈ A, halfMass ν u (1 / ((m : ℝ) + 1)) ((m : ℝ) + 1)) ≤ betaPlus ν A := by
    unfold betaPlus
    apply le_iSup_of_le (1 / ((m : ℝ) + 1))
    apply le_iSup_of_le hpos
    exact le_iSup (fun D : ℝ => ⨅ u ∈ A, halfMass ν u (1 / ((m : ℝ) + 1)) D) ((m : ℝ) + 1)
  refine le_trans ?_ hstep
  refine le_iInf₂ fun u hu => le_iInf₂ fun e he => ?_
  have : (u, e) ∈ U m := hm ⟨hu, by simpa using he⟩
  exact (interior_subset this : _).le

theorem betaPlus_eq : Claims.betaPlus_eq := by
  intro K ν A hA
  exact le_antisymm (betaPlus_le ν A) (le_betaPlus ν hA)

/-! ### The two clauses -/

lemma exists_unit (hK : 0 < K) : ∃ e : EuclideanSpace ℝ (Fin K), ‖e‖ = 1 :=
  ⟨EuclideanSpace.single (⟨0, hK⟩ : Fin K) (1 : ℝ), by simp⟩

lemma halfMass_le_one (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν] (hK : 0 < K)
    (u : EuclideanSpace ℝ (Fin K)) (t D : ℝ) : halfMass ν u t D ≤ 1 := by
  obtain ⟨e, he⟩ := exists_unit hK
  exact (iInf₂_le e he).trans prob_le_one

lemma dMinus_le_one (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν] (hK : 0 < K)
    (u : EuclideanSpace ℝ (Fin K)) : dMinus ν u ≤ 1 := by
  obtain ⟨e, he⟩ := exists_unit hK
  exact (iInf₂_le e he).trans prob_le_one

lemma entBound_anti {n ℓ : ℕ} {t D B ε δ δ' : ℝ} (ht : 0 < t) (hε : 0 < ε)
    (hδ : (ℓ : ℝ) < n * δ) (hδδ' : δ ≤ δ') :
    entBound n ℓ t D B ε δ' ≤ entBound n ℓ t D B ε δ := by
  unfold entBound
  have hnδ : 0 < (n : ℝ) * δ := lt_of_le_of_lt (Nat.cast_nonneg ℓ) hδ
  have hn : 0 < (n : ℝ) := by
    rcases (Nat.cast_nonneg n : (0 : ℝ) ≤ n).eq_or_lt with h | h
    · rw [← h, zero_mul] at hnδ; exact absurd hnδ (lt_irrefl 0)
    · exact h
  have hδ0 : 0 < δ := pos_of_mul_pos_right hnδ hn.le
  have hnδ' : (n : ℝ) * δ ≤ n * δ' := mul_le_mul_of_nonneg_left hδδ' hn.le
  have hκ : 0 < 1 - ℓ / (n * δ) := by rw [sub_pos, div_lt_one hnδ]; exact hδ
  have hκκ : 1 - ℓ / (n * δ) ≤ 1 - ℓ / (n * δ') := by
    have := div_le_div_of_nonneg_left (Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ) hnδ hnδ'
    linarith
  have hlog : Real.log (n / (1 - ℓ / (n * δ'))) ≤ Real.log (n / (1 - ℓ / (n * δ))) :=
    Real.log_le_log (div_pos hn (lt_of_lt_of_le hκ hκκ)) (div_le_div_of_nonneg_left hn.le hκ hκκ)
  have : (ℓ : ℝ) * (D * B + ε * Real.log (n / (1 - ℓ / (n * δ'))) + ε) ≤
      ℓ * (D * B + ε * Real.log (n / (1 - ℓ / (n * δ))) + ε) := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg ℓ)
    nlinarith
  have := div_le_div_of_nonneg_right this ht.le
  linarith

theorem region_bounded : Claims.region_bounded := by
  intro K n ν _ ε fsel Z A ℓ hK hset hA _ hℓ
  obtain ⟨hε, -, -⟩ := hset
  rcases A.eq_empty_or_nonempty with rfl | ⟨u₁, hu₁⟩
  · exact ⟨0, fun _ _ u hu => absurd hu (notMem_empty u)⟩
  simp only [betaPlus, ENNReal.mul_iSup, lt_iSup_iff] at hℓ
  obtain ⟨t, ht, D, hlt⟩ := hℓ
  set δA := ⨅ u ∈ A, halfMass ν u t D with hδA
  have hδA1 : δA ≤ 1 := (iInf₂_le u₁ hu₁).trans (halfMass_le_one ν hK u₁ t D)
  have hδAtop : δA ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hδA1
  have hreal : (ℓ : ℝ) < n * δA.toReal := by
    have := (ENNReal.toReal_lt_toReal (ENNReal.natCast_ne_top ℓ)
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) hδAtop)).mpr hlt
    simpa [ENNReal.toReal_mul] using this
  set B : ℝ := ∑ j, ‖Z j‖
  refine ⟨entBound n ℓ t D B ε δA.toReal, fun Z' hZ' u hu => ?_⟩
  have hle : δA ≤ halfMass ν u t D := iInf₂_le u hu
  have hle' : δA.toReal ≤ (halfMass ν u t D).toReal :=
    ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top (halfMass_le_one ν hK u t D)) hle
  have hu' : (ℓ : ℝ) < n * (halfMass ν u t D).toReal :=
    lt_of_lt_of_le hreal (mul_le_mul_of_nonneg_left hle' (Nat.cast_nonneg n))
  have hB : ∀ j, Z' j = Z j → ‖Z' j‖ ≤ B := fun j hj => by
    rw [hj]; exact Finset.single_le_sum (f := fun j => ‖Z j‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ j)
  calc ‖Qhat Z' (fsel Z') ε u‖ ≤ entBound n ℓ t D B ε (halfMass ν u t D).toReal :=
        ‹Wave6b.EntropicA ν ε fsel Z› ℓ u t D ht hu' Z' hZ' B hB
    _ ≤ entBound n ℓ t D B ε δA.toReal := entBound_anti ht hε hreal hle'

lemma exists_dMinus_lt {n : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin K))) {A : Set (EuclideanSpace ℝ (Fin K))}
    (hA : A.Nonempty) {ℓ : ℕ} (h : (n : ℝ≥0∞) * (⨅ u ∈ A, dMinus ν u) < ℓ) :
    ∃ u ∈ A, (n : ℝ≥0∞) * dMinus ν u < ℓ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨u, hu⟩ := hA
    simp only [Nat.cast_zero, zero_mul] at h ⊢
    exact ⟨u, hu, h⟩
  have h0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [ENNReal.mul_iInf_of_ne h0 (ENNReal.natCast_ne_top n), iInf_lt_iff] at h
  obtain ⟨u, hu, h⟩ := h
  exact ⟨u, hu, h⟩

theorem region_unbounded : Claims.region_unbounded := by
  intro K n ν _ ε fsel Z A ℓ _ _ hB _ hAne hℓ M
  obtain ⟨u, hu, hlt⟩ := exists_dMinus_lt ν hAne hℓ
  obtain ⟨Z', hZ', hM⟩ := hB ℓ u hlt M
  exact ⟨Z', hZ', u, hu, hM⟩

/-! ### The breakdown point -/

section BPsec
variable {n : ℕ} {ε : ℝ} {fsel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ}
  {A : Set (EuclideanSpace ℝ (Fin K))}

lemma bdd_region (Z' : Fin n → EuclideanSpace ℝ (Fin K)) :
    BddAbove (range fun u : A => ‖Qhat Z' (fsel Z') ε u‖) :=
  ⟨∑ i, ‖Z' i‖, by rintro _ ⟨u, rfl⟩; exact norm_qhat_le _ _ _ _⟩

lemma not_explodes_of_bdd (hAne : A.Nonempty) {Z : Fin n → EuclideanSpace ℝ (Fin K)} {ℓ : ℕ}
    (h : ∃ M : ℝ, ∀ Z' ∈ Contam Z ℓ, ∀ u ∈ A, ‖Qhat Z' (fsel Z') ε u‖ ≤ M) :
    ¬ Explodes (regionSup ε fsel A) Z ℓ := by
  obtain ⟨M, hM⟩ := h
  have : Nonempty A := hAne.to_subtype
  intro hex
  apply hex
  refine ⟨M, ?_⟩
  rintro _ ⟨Z', hZ', rfl⟩
  have h0 : 0 ≤ regionSup ε fsel A Z' := by
    obtain ⟨u, hu⟩ := hAne
    exact (norm_nonneg _).trans (le_ciSup (bdd_region (fsel := fsel) (ε := ε) (A := A) Z') ⟨u, hu⟩)
  change ‖regionSup ε fsel A Z'‖ ≤ M
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact ciSup_le fun u => hM Z' hZ' u u.2

lemma explodes_of_unbdd {Z : Fin n → EuclideanSpace ℝ (Fin K)} {ℓ : ℕ}
    (h : ∀ M : ℝ, ∃ Z' ∈ Contam Z ℓ, ∃ u ∈ A, M < ‖Qhat Z' (fsel Z') ε u‖) :
    Explodes (regionSup ε fsel A) Z ℓ := by
  rintro ⟨M, hM⟩
  obtain ⟨Z', hZ', u, hu, hlt⟩ := h M
  have h1 : ‖Qhat Z' (fsel Z') ε u‖ ≤ regionSup ε fsel A Z' :=
    le_ciSup (bdd_region (fsel := fsel) (ε := ε) (A := A) Z') ⟨u, hu⟩
  have h2 : ‖regionSup ε fsel A Z'‖ ≤ M := hM ⟨Z', hZ', rfl⟩
  have h3 := le_abs_self (regionSup ε fsel A Z')
  rw [Real.norm_eq_abs] at h2
  linarith

end BPsec

theorem region_bp_general : Claims.region_bp_general := by
  intro K n ν _ ε fsel Z A hK hn hset hEA hEB hA hAne
  set β := ⨅ u ∈ A, dMinus ν u with hβ
  obtain ⟨u₁, hu₁⟩ := hAne
  have hβ1 : β ≤ 1 := (iInf₂_le u₁ hu₁).trans (dMinus_le_one ν hK u₁)
  have hβtop : β ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hβ1
  have hβr1 : β.toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top hβ1; simpa using this
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hbp_eq : betaPlus ν A = β := betaPlus_eq K ν A hA
  -- ENNReal ↔ real for `ℓ` versus `nβ`
  have hconv : ∀ ℓ : ℕ, ((ℓ : ℝ≥0∞) < n * β ↔ (ℓ : ℝ) < n * β.toReal) := by
    intro ℓ
    have hfin : (n : ℝ≥0∞) * β ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) hβtop
    rw [← ENNReal.toReal_lt_toReal (ENNReal.natCast_ne_top ℓ) hfin]
    simp [ENNReal.toReal_mul]
  have hconv' : ∀ ℓ : ℕ, ((n : ℝ≥0∞) * β < ℓ ↔ (n : ℝ) * β.toReal < ℓ) := by
    intro ℓ
    have hfin : (n : ℝ≥0∞) * β ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) hβtop
    rw [← ENNReal.toReal_lt_toReal hfin (ENNReal.natCast_ne_top ℓ)]
    simp [ENNReal.toReal_mul]
  have hbounded : ∀ ℓ : ℕ, (ℓ : ℝ) < n * β.toReal → ¬ Explodes (regionSup ε fsel A) Z ℓ := by
    intro ℓ hℓ
    apply not_explodes_of_bdd ⟨u₁, hu₁⟩
    refine region_bounded K n ν ε fsel Z A ℓ hK hset hEA hA ?_
    rw [hbp_eq]; exact (hconv ℓ).mpr hℓ
  have hexpl : ∀ ℓ : ℕ, (n : ℝ) * β.toReal < ℓ → Explodes (regionSup ε fsel A) Z ℓ := by
    intro ℓ hℓ
    apply explodes_of_unbdd
    exact region_unbounded K n ν ε fsel Z A ℓ hK hset hEB hA ⟨u₁, hu₁⟩ ((hconv' ℓ).mpr hℓ)
  -- the explicit exploding level `ℓ₀ = ⌊nβ⌋ + 1`
  set ℓ₀ := ⌊(n : ℝ) * β.toReal⌋₊ + 1 with hℓ₀
  have hβr0 : 0 ≤ β.toReal := ENNReal.toReal_nonneg
  have hℓ₀gt : (n : ℝ) * β.toReal < ℓ₀ := by
    rw [hℓ₀]; push_cast; exact Nat.lt_floor_add_one _
  have hℓ₀le : (ℓ₀ : ℝ) ≤ n * β.toReal + 1 := by
    rw [hℓ₀]; push_cast
    linarith [Nat.floor_le (mul_nonneg hnpos.le hβr0)]
  have hex : ∃ ℓ, 1 ≤ ℓ ∧ Explodes (regionSup ε fsel A) Z ℓ := ⟨ℓ₀, by omega, hexpl ℓ₀ hℓ₀gt⟩
  classical
  have hBP : BP (regionSup ε fsel A) Z = (Nat.find hex : ℝ) / n := by
    unfold BP; simp only [hex, ↓reduceDIte]
  obtain ⟨_, hfind⟩ := Nat.find_spec hex
  have hfind_le : Nat.find hex ≤ ℓ₀ := Nat.find_min' hex ⟨by omega, hexpl ℓ₀ hℓ₀gt⟩
  refine ⟨?_, ?_⟩
  · rw [hBP, le_div_iff₀ hnpos]
    by_contra hcon
    push Not at hcon
    exact hbounded _ (by linarith) hfind
  · rw [hBP, div_le_iff₀ hnpos]
    have : (Nat.find hex : ℝ) ≤ ℓ₀ := by exact_mod_cast hfind_le
    have h1 : (β.toReal + 1 / n) * n = n * β.toReal + 1 := by field_simp
    rw [h1]; linarith

/-! ### Absolutely continuous references: `d⁻ = TD` -/

lemma hyperplane_null (ν : Measure (EuclideanSpace ℝ (Fin K))) (hac : ν ≪ volume)
    (u e : EuclideanSpace ℝ (Fin K)) (he : e ≠ 0) : ν {z | ⟪z - u, e⟫_ℝ = 0} = 0 := by
  apply hac
  have hs : (ℝ ∙ e)ᗮ ≠ ⊤ := by
    intro htop
    have : e ∈ (ℝ ∙ e)ᗮ := by rw [htop]; exact Submodule.mem_top
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_self_eq_norm_sq] at this
    exact he (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this))
  have hset : {z | ⟪z - u, e⟫_ℝ = 0} = (fun z => z + -u) ⁻¹' ((ℝ ∙ e)ᗮ : Set _) := by
    ext z
    simp only [mem_ofPred_eq, mem_preimage, SetLike.mem_coe,
      Submodule.mem_orthogonal_singleton_iff_inner_right, ← sub_eq_add_neg, real_inner_comm e]
  rw [hset, measure_preimage_add_right]
  exact Measure.addHaar_submodule volume _ hs

lemma dMinus_eq_tukey (ν : Measure (EuclideanSpace ℝ (Fin K))) (hac : ν ≪ volume)
    (u : EuclideanSpace ℝ (Fin K)) : dMinus ν u = tukeyDepth ν u := by
  apply le_antisymm
  · refine le_iInf₂ fun v hv => ?_
    set e : EuclideanSpace ℝ (Fin K) := ‖v‖⁻¹ • (-v) with he
    have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have he1 : ‖e‖ = 1 := by
      rw [he, norm_smul, norm_neg, norm_inv, norm_norm, inv_mul_cancel₀ hv0.ne']
    refine (iInf₂_le e he1).trans (measure_mono fun z hz => ?_)
    simp only [mem_ofPred_eq, he, inner_smul_right, inner_neg_right] at hz ⊢
    rw [real_inner_comm] at hz
    have : 0 < -⟪v, z - u⟫_ℝ := by
      have := (mul_pos_iff_of_pos_left (inv_pos.mpr hv0)).mp hz
      exact this
    linarith
  · refine le_iInf₂ fun e he => ?_
    have he0 : e ≠ 0 := by rintro rfl; simp at he
    refine (iInf₂_le (-e) (neg_ne_zero.mpr he0)).trans ?_
    calc ν {z | ⟪-e, z - u⟫_ℝ ≤ 0}
        ≤ ν ({z | 0 < ⟪z - u, e⟫_ℝ} ∪ {z | ⟪z - u, e⟫_ℝ = 0}) := by
          apply measure_mono
          intro z hz
          simp only [mem_ofPred_eq, inner_neg_left, neg_nonpos, mem_union] at hz ⊢
          rw [real_inner_comm] at hz
          rcases hz.lt_or_eq with h | h
          · exact Or.inl h
          · exact Or.inr h.symm
      _ ≤ ν {z | 0 < ⟪z - u, e⟫_ℝ} + ν {z | ⟪z - u, e⟫_ℝ = 0} := measure_union_le _ _
      _ = ν {z | 0 < ⟪z - u, e⟫_ℝ} := by rw [hyperplane_null ν hac u e he0, add_zero]

theorem region_bp : Claims.region_bp := by
  intro K n ν _ ε fsel Z A hK hn hac hset hEA hEB hA hAne
  have : regionDepth ν A = ⨅ u ∈ A, dMinus ν u := by
    unfold regionDepth
    exact iInf_congr fun u => iInf_congr fun _ => (dMinus_eq_tukey ν hac u).symm
  rw [this]
  exact region_bp_general K n ν ε fsel Z A hK hn hset hEA hEB hA hAne

end StatFormal.OTFD.Wave6b
