import StatFormal.Archive.Wave8a.Statements
import StatFormal.Archive.TrimmedMMD.ZeroSet.Proofs
import StatFormal.Archive.TrimmedMMD.Unconditional.Proofs

/-!
# Route: trimmed MMD `prop:georep` (geometric representation)

1. Embeddings of trimmings. `P' ∈ R_α(P)` ↦ `g = min((dP'/dP).toReal, β)`, a bounded measurable version of the
   density (`integral_rnDeriv_smul`); conversely `g ↦ P.withDensity g`, whose density is `g` a.e.
   (`rnDeriv_withDensity`). Hence `{μ_{P'}} = 𝒞_{α,k}(P)` and `D_{α,k} = dist(𝒞(P), 𝒞(Q))`.
2. Empirical laws, **with ties**. In an arbitrary measurable space "ties" are indices whose points no measurable
   set separates (`r i j`); a strongly measurable `φ` is constant on such classes (limit of simple functions), and so
   is every measurable `g`. `⊆`: `w_i = g(X_i)/n`. `⊇` (averaging): given `w ∈ Δ_α(n)`, average `w` over each class,
   realise the averages by a measurable `g = min(Σ_i c_i 1_{A_i}, β)` with `A_i` a measurable set containing exactly
   the class of `X_i` among the sample points, and double-count (`sum_avg`).
3. `eq:qp`: the capped simplices are compact and nonempty, so the squared distance is a minimum of `qp`.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace StatFormal.Wave8a

open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional
open StatFormal.TrimmedMMD.ZeroSet StatFormal.TrimmedMMD.BangBang

/-! ### Embeddings of trimmings -/

section Embed

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

theorem embed_eq (P : Measure 𝒳) [IsProbabilityMeasure P] (φ : 𝒳 → H) {α : ℝ} (hα1 : α < 1) :
    (fun P' => ∫ x, φ x ∂P') '' trimSet P α = region φ α P := by
  have hβ0 : 0 ≤ 1 / (1 - α) := div_nonneg zero_le_one (by linarith)
  ext z
  constructor
  · rintro ⟨P', ⟨hP', hac, hle⟩, rfl⟩
    set g : 𝒳 → ℝ := fun x => min ((P'.rnDeriv P x).toReal) (1 / (1 - α)) with hgdef
    have hgm : Measurable g :=
      (Measure.measurable_rnDeriv P' P).ennreal_toReal.min measurable_const
    have hgae : (fun x => (P'.rnDeriv P x).toReal) =ᵐ[P] g := by
      filter_upwards [hle] with x hx
      simp only [hgdef]
      rw [min_eq_left (ENNReal.toReal_le_of_le_ofReal hβ0 hx)]
    refine ⟨g, hgm, fun x => ⟨le_min ENNReal.toReal_nonneg hβ0, min_le_right _ _⟩, ?_, ?_⟩
    · rw [← integral_congr_ae hgae, Measure.integral_toReal_rnDeriv hac, probReal_univ]
    · change ∫ x, φ x ∂P' = ∫ x, g x • φ x ∂P
      rw [← integral_rnDeriv_smul hac]
      refine integral_congr_ae ?_
      filter_upwards [hgae] with x hx
      rw [hx]
  · rintro ⟨g, hg, hgb, hg1, rfl⟩
    have hgi : Integrable g P := IsTrimDensity.integrable ⟨hg, hgb, hg1⟩
    refine ⟨P.withDensity fun x => ENNReal.ofReal (g x), ⟨⟨?_⟩, ?_, ?_⟩, ?_⟩
    · rw [withDensity_ofReal_apply hgi (fun x => (hgb x).1) MeasurableSet.univ, setIntegral_univ,
        hg1, ENNReal.ofReal_one]
    · exact withDensity_absolutelyContinuous _ _
    · filter_upwards [Measure.rnDeriv_withDensity P hg.ennreal_ofReal] with x hx
      rw [hx]
      exact ENNReal.ofReal_le_ofReal (hgb x).2
    · exact (integral_smul_eq_withDensity P hg (fun x => (hgb x).1) φ).symm

theorem georep_embed : Claims.georep_embed := by
  intro 𝒳 H _ _ _ _ P _ φ κ α _ _ _ hα1
  exact embed_eq P φ hα1

theorem georep_dist : Claims.georep_dist := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ α _ _ _ hα1
  have hP := embed_eq P φ hα1
  have hQ := embed_eq Q φ hα1
  unfold dTrim Dpop setDist
  congr 1
  ext r
  constructor
  · rintro ⟨P', hP', Q', hQ', rfl⟩
    exact ⟨_, hP ▸ mem_image_of_mem _ hP', _, hQ ▸ mem_image_of_mem _ hQ', rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [← hP] at ha
    rw [← hQ] at hb
    obtain ⟨P', hP', rfl⟩ := ha
    obtain ⟨Q', hQ', rfl⟩ := hb
    exact ⟨P', hP', Q', hQ', rfl⟩

end Embed

/-! ### Empirical laws -/

section Empirical

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

theorem integral_empirical_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {n : ℕ} (x : Fin n → 𝒳) {h : 𝒳 → F} (hh : StronglyMeasurable h) :
    ∫ y, h y ∂(empirical x) = ∑ i, (n : ℝ)⁻¹ • h (x i) := by
  unfold empirical
  rw [integral_finsetSum_measure fun i _ =>
    (integrable_dirac' hh enorm_lt_top).smul_measure ENNReal.ofReal_ne_top]
  simp_rw [integral_smul_measure, integral_dirac' _ _ hh]
  rw [ENNReal.toReal_ofReal (by positivity)]
  simp [one_div]

/-- A strongly measurable map is constant on points that no measurable set separates. -/
theorem eq_of_insep_of_stronglyMeasurable {β : Type*} [TopologicalSpace β] [T2Space β] {f : 𝒳 → β}
    (hf : StronglyMeasurable f) {a b : 𝒳} (hab : ∀ s, MeasurableSet s → (a ∈ s ↔ b ∈ s)) :
    f a = f b := by
  have h : ∀ k, hf.approx k a = hf.approx k b := fun k => by
    have := (hab _ ((hf.approx k).measurableSet_fiber (hf.approx k a))).1 (by simp)
    simpa using this.symm
  have h1 := hf.tendsto_approx a
  simp_rw [h] at h1
  exact tendsto_nhds_unique h1 (hf.tendsto_approx b)

/-- Double counting over the classes of an equivalence relation on `Fin n`. -/
theorem sum_avg {M : Type*} [AddCommGroup M] [Module ℝ M] {n : ℕ} (r : Fin n → Fin n → Prop)
    [DecidableRel r] (hrefl : ∀ i, r i i) (hsymm : ∀ i j, r i j → r j i)
    (htrans : ∀ i j k, r i j → r j k → r i k) (v : Fin n → M) :
    ∑ j, (((Finset.univ.filter (r j)).card : ℝ))⁻¹ • ∑ i ∈ Finset.univ.filter (r j), v i =
      ∑ i, v i := by
  have hcard : ∀ i j, r i j → Finset.univ.filter (r i) = Finset.univ.filter (r j) := by
    intro i j hij
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => htrans _ _ _ (hsymm _ _ hij) h, fun h => htrans _ _ _ hij h⟩
  calc ∑ j, (((Finset.univ.filter (r j)).card : ℝ))⁻¹ • ∑ i ∈ Finset.univ.filter (r j), v i
      = ∑ j, ∑ i, if r j i then (((Finset.univ.filter (r j)).card : ℝ))⁻¹ • v i else 0 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.smul_sum, Finset.sum_filter]
    _ = ∑ i, ∑ j, if r j i then (((Finset.univ.filter (r j)).card : ℝ))⁻¹ • v i else 0 :=
        Finset.sum_comm
    _ = ∑ i, ∑ j ∈ Finset.univ.filter (r i),
          (((Finset.univ.filter (r i)).card : ℝ))⁻¹ • v i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases h : r j i
        · rw [if_pos h, if_pos (hsymm _ _ h), hcard j i h]
        · rw [if_neg h, if_neg (fun h' => h (hsymm _ _ h'))]
    _ = ∑ i, v i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀, one_smul]
        exact Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨i, by simp [hrefl]⟩)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem region_empirical {φ : 𝒳 → H} (hφ : StronglyMeasurable φ) {α : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) {n : ℕ} (hn : 0 < n) (x : Fin n → 𝒳) :
    region φ α (empirical x) = polytope φ x α := by
  classical
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have h1α : 0 < 1 - α := by linarith
  have hβ0 : 0 ≤ 1 / (1 - α) := div_nonneg zero_le_one h1α.le
  have hcap : cap n α = (n : ℝ)⁻¹ * (1 / (1 - α)) := by
    unfold cap; field_simp
  ext z
  constructor
  · rintro ⟨g, hg, hgb, hg1, rfl⟩
    refine ⟨fun i => g (x i) / n, ⟨fun i => ⟨div_nonneg (hgb _).1 hn'.le, ?_⟩, ?_⟩, ?_⟩
    · change g (x i) / n ≤ cap n α
      rw [hcap, div_eq_inv_mul (g (x i))]
      exact mul_le_mul_of_nonneg_left (hgb _).2 (inv_nonneg.2 hn'.le)
    · rw [integral_empirical_smul x hg.stronglyMeasurable] at hg1
      simpa [div_eq_inv_mul, smul_eq_mul] using hg1
    · rw [integral_empirical_smul x (h := fun y => g y • φ y) (hg.stronglyMeasurable.smul hφ)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul]
      simp only [div_eq_inv_mul]
  · rintro ⟨w, ⟨hwb, hw1⟩, rfl⟩
    -- indices whose points no measurable set separates
    set r : Fin n → Fin n → Prop := fun i j => ∀ s, MeasurableSet s → (x i ∈ s ↔ x j ∈ s)
      with hrdef
    have hrefl : ∀ i, r i i := fun i s _ => Iff.rfl
    have hsymm : ∀ i j, r i j → r j i := fun i j h s hs => (h s hs).symm
    have htrans : ∀ i j k, r i j → r j k → r i k := fun i j k h1 h2 s hs =>
      (h1 s hs).trans (h2 s hs)
    have hfilt : ∀ i j, r i j → Finset.univ.filter (r i) = Finset.univ.filter (r j) := by
      intro i j hij
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => htrans _ _ _ (hsymm _ _ hij) h, fun h => htrans _ _ _ hij h⟩
    have hsep : ∀ i j, ¬ r i j → ∃ s, MeasurableSet s ∧ x i ∈ s ∧ x j ∉ s := by
      intro i j h
      simp only [hrdef, not_forall] at h
      obtain ⟨s, hs, hiff⟩ := h
      by_cases hi : x i ∈ s
      · exact ⟨s, hs, hi, fun hj => hiff ⟨fun _ => hj, fun _ => hi⟩⟩
      · have hj : x j ∈ s := by
          by_contra hj
          exact hiff ⟨fun h => absurd h hi, fun h => absurd h hj⟩
        exact ⟨sᶜ, hs.compl, hi, fun h => h hj⟩
    choose! S hSm hSi hSj using hsep
    set A : Fin n → Set 𝒳 := fun i => ⋂ j, if r i j then univ else S i j with hAdef
    have hAm : ∀ i, MeasurableSet (A i) := fun i => MeasurableSet.iInter fun j => by
      by_cases h : r i j
      · rw [if_pos h]; exact MeasurableSet.univ
      · rw [if_neg h]; exact hSm i j h
    have hA : ∀ i j, x j ∈ A i ↔ r i j := by
      intro i j
      simp only [hAdef, mem_iInter]
      constructor
      · intro h
        by_contra hij
        have := h j
        rw [if_neg hij] at this
        exact hSj i j hij this
      · intro hij k
        by_cases hik : r i k
        · rw [if_pos hik]; trivial
        · rw [if_neg hik]; exact (hij _ (hSm i k hik)).1 (hSi i k hik)
    -- class sizes and class averages
    set N : Fin n → ℝ := fun j => ((Finset.univ.filter (r j)).card : ℝ) with hNdef
    have hNpos : ∀ j, 0 < N j := fun j =>
      Nat.cast_pos.2 (Finset.card_pos.2 ⟨j, by simp [hrefl]⟩)
    set avg : Fin n → ℝ := fun j => (N j)⁻¹ * ∑ i ∈ Finset.univ.filter (r j), w i with havgdef
    have hNeq : ∀ i j, r i j → N i = N j := fun i j h => by simp only [hNdef, hfilt i j h]
    have havgeq : ∀ i j, r i j → avg i = avg j := fun i j h => by
      simp only [havgdef, hNeq i j h, hfilt i j h]
    have havg0 : ∀ j, 0 ≤ avg j := fun j =>
      mul_nonneg (inv_nonneg.2 (hNpos j).le) (Finset.sum_nonneg fun i _ => (hwb i).1)
    have havgcap : ∀ j, avg j ≤ cap n α := by
      intro j
      have hs : ∑ i ∈ Finset.univ.filter (r j), w i ≤ N j * cap n α := by
        have := Finset.sum_le_card_nsmul (Finset.univ.filter (r j)) w (cap n α)
          (fun i _ => (hwb i).2)
        simpa [hNdef, nsmul_eq_mul] using this
      simp only [havgdef]
      rw [inv_mul_le_iff₀ (hNpos j)]
      exact hs
    -- the density
    set c : Fin n → ℝ := fun i => n * avg i / N i with hcdef
    set g0 : 𝒳 → ℝ := fun y => ∑ i, c i * (A i).indicator (fun _ => (1 : ℝ)) y with hg0def
    set g : 𝒳 → ℝ := fun y => min (g0 y) (1 / (1 - α)) with hgdef
    have hg0x : ∀ j, g0 (x j) = n * avg j := by
      intro j
      simp only [hg0def]
      have : ∀ i, c i * (A i).indicator (fun _ => (1 : ℝ)) (x j) =
          if r j i then n * avg j / N j else 0 := by
        intro i
        by_cases h : r j i
        · rw [if_pos h, indicator_of_mem ((hA i j).2 (hsymm _ _ h)), mul_one]
          simp only [hcdef, havgeq i j (hsymm _ _ h), hNeq i j (hsymm _ _ h)]
        · rw [if_neg h, indicator_of_notMem (fun hm => h (hsymm _ _ ((hA i j).1 hm))),
            mul_zero]
      simp_rw [this]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      change N j * (n * avg j / N j) = n * avg j
      field_simp [(hNpos j).ne']
    have hgx : ∀ j, g (x j) = n * avg j := by
      intro j
      simp only [hgdef]
      rw [hg0x j, min_eq_left]
      calc (n : ℝ) * avg j ≤ n * cap n α := mul_le_mul_of_nonneg_left (havgcap j) hn'.le
        _ = 1 / (1 - α) := by rw [hcap, ← mul_assoc, mul_inv_cancel₀ hn'.ne', one_mul]
    have hgm : Measurable g := by
      refine Measurable.min ?_ measurable_const
      exact Finset.measurable_sum _ fun i _ =>
        (measurable_const.indicator (hAm i)).const_mul _
    have hg0nn : ∀ y, 0 ≤ g0 y := fun y => Finset.sum_nonneg fun i _ =>
      mul_nonneg (div_nonneg (mul_nonneg hn'.le (havg0 i)) (hNpos i).le)
        (indicator_nonneg (fun _ _ => zero_le_one) _)
    have hgb : ∀ y, 0 ≤ g y ∧ g y ≤ 1 / (1 - α) := fun y =>
      ⟨le_min (hg0nn y) hβ0, min_le_right _ _⟩
    have hsumavg : ∑ j, avg j = ∑ i, w i := by
      have := sum_avg r hrefl hsymm htrans w
      simpa [havgdef, hNdef, smul_eq_mul] using this
    refine ⟨g, hgm, hgb, ?_, ?_⟩
    · rw [integral_empirical_smul x hgm.stronglyMeasurable]
      simp_rw [hgx, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hn'.ne', one_mul]
      rw [hsumavg, hw1]
    · rw [integral_empirical_smul x (h := fun y => g y • φ y) (hgm.stronglyMeasurable.smul hφ)]
      simp_rw [hgx, smul_smul, ← mul_assoc, inv_mul_cancel₀ hn'.ne', one_mul]
      have hφc : ∀ i j, r i j → φ (x i) = φ (x j) := fun i j h => eq_of_insep_of_stronglyMeasurable hφ h
      have : ∀ j, avg j • φ (x j) =
          (N j)⁻¹ • ∑ i ∈ Finset.univ.filter (r j), w i • φ (x i) := by
        intro j
        simp only [havgdef]
        rw [mul_smul, Finset.sum_smul]
        congr 1
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hφc j i (Finset.mem_filter.1 hi).2]
      simp_rw [this]
      exact (sum_avg r hrefl hsymm htrans fun i => w i • φ (x i)).symm

theorem georep_empirical : Claims.georep_empirical := by
  intro 𝒳 H _ _ _ _ φ α n x hφ hα0 hα1 hn
  exact region_empirical hφ hα0 hα1 hn x

end Empirical

/-! ### `eq:qp` -/

theorem capped_isCompact (n : ℕ) (α : ℝ) : IsCompact (capped n α) := by
  have hcl : IsClosed (capped n α) := by
    have : capped n α = (⋂ i, ({w : Fin n → ℝ | 0 ≤ w i} ∩ {w | w i ≤ cap n α})) ∩
        {w | ∑ i, w i = 1} := by
      ext w
      simp only [capped, mem_setOf_eq, mem_inter_iff, mem_iInter]
    rw [this]
    refine IsClosed.inter (isClosed_iInter fun i => ?_) ?_
    · exact (isClosed_le continuous_const (continuous_apply i)).inter
        (isClosed_le (continuous_apply i) continuous_const)
    · exact isClosed_eq (continuous_finset_sum _ fun i _ => continuous_apply i) continuous_const
  refine (isCompact_univ_pi fun _ : Fin n => isCompact_Icc (a := (0 : ℝ)) (b := cap n α)).of_isClosed_subset
    hcl fun w hw i _ => ⟨(hw.1 i).1, (hw.1 i).2⟩

theorem capped_nonempty {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    (capped n α).Nonempty := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  refine ⟨fun _ => (n : ℝ)⁻¹, fun i => ⟨inv_nonneg.2 hn'.le, ?_⟩, ?_⟩
  · unfold cap
    rw [one_div]
    exact inv_anti₀ (mul_pos hn' (by linarith)) (mul_le_of_le_one_right hn'.le (by linarith))
  · simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_inv_cancel₀ hn'.ne']

theorem georep_qp : Claims.georep_qp := by
  intro 𝒳 H _ _ _ _ φ α n m x y hφ hα0 hα1 hn hm
  have hK := (capped_isCompact n α).prod (capped_isCompact m α)
  have hne := (capped_nonempty hn hα0 hα1).prod (capped_nonempty hm hα0 hα1)
  have hcont : Continuous (qp (φ ∘ x) (φ ∘ y)) := by
    unfold qp
    fun_prop
  obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
  refine ⟨p, hp, hmin, ?_⟩
  have hD : Demp φ x y α = ‖∑ i, p.1 i • φ (x i) - ∑ j, p.2 j • φ (y j)‖ := by
    unfold Demp
    rw [region_empirical hφ hα0 hα1 hn x, region_empirical hφ hα0 hα1 hm y]
    apply le_antisymm
    · exact setDist_le_norm ⟨p.1, hp.1, rfl⟩ ⟨p.2, hp.2, rfl⟩
    · have hmem : ‖∑ i, p.1 i • φ (x i) - ∑ j, p.2 j • φ (y j)‖ ∈
          {r | ∃ a ∈ polytope φ x α, ∃ b ∈ polytope φ y α, r = ‖a - b‖} :=
        ⟨_, ⟨p.1, hp.1, rfl⟩, _, ⟨p.2, hp.2, rfl⟩, rfl⟩
      refine le_csInf ⟨_, hmem⟩ ?_
      rintro _ ⟨_, ⟨w, hw, rfl⟩, _, ⟨v, hv, rfl⟩, rfl⟩
      have := isMinOn_iff.1 hmin (w, v) ⟨hw, hv⟩
      simp only [qp, Function.comp_apply] at this
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
  rw [hD]
  rfl

/-! ### The ties trap -/

theorem georep_ties_weights : Claims.georep_ties_weights := by
  refine ⟨![1, 0], ⟨fun i => ?_, ?_⟩, fun g _ h => ?_⟩
  · have hc : cap 2 (1 / 2) = 1 := by unfold cap; norm_num
    rw [hc]
    fin_cases i <;> simp
  · simp [Fin.sum_univ_two]
  · have h0 := h 0
    have h1 := h 1
    simp at h0 h1
    linarith

end StatFormal.Wave8a
