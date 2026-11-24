import StatFormal.Wave31tj.Statements
import StatFormal.Wave30tu.Proofs

set_option linter.style.longLine false

/-!
# Route: wave 31tj, Algorithm 1 (untrusted)

The loop keeps a rejected lower end, an accepted upper end and a test point strictly between them (`loop_spec`); the bracket
then contains `α̂` by the certified `Wave30tu.crossing` (the crossing set contains `(α̂,1)`, and equals `[α̂,1)` when `α̂ > 0`).
From a midpoint, every test halves the width (`loop_width`). The event is that of the certified `Wave30tu.oneevent`.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace StatFormal.Wave31tj

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Unconditional StatFormal.Wave30tu

/-! ### The loop -/

lemma loop_spec (rej : ℝ → Prop) (ε : ℝ) : ∀ (k : ℕ) (l u a : ℝ), l < u → a ∈ Ioo l u →
    ((rej l → rej (bisectLoop rej ε k l u a).1) ∧ (¬ rej u → ¬ rej (bisectLoop rej ε k l u a).2.1) ∧
      l ≤ (bisectLoop rej ε k l u a).1 ∧ (bisectLoop rej ε k l u a).1 < (bisectLoop rej ε k l u a).2.1 ∧
      (bisectLoop rej ε k l u a).2.1 ≤ u ∧ (bisectLoop rej ε k l u a).2.2 ≤ k ∧
      ((bisectLoop rej ε k l u a).2.2 < k → (bisectLoop rej ε k l u a).2.1 - (bisectLoop rej ε k l u a).1 ≤ ε)) := by
  intro k
  induction k with
  | zero =>
    intro l u a hlu _
    simp only [bisectLoop]
    exact ⟨id, id, le_rfl, hlu, le_rfl, le_rfl, fun h => absurd h (lt_irrefl 0)⟩
  | succ k ih =>
    intro l u a hlu ha
    by_cases hw : u - l ≤ ε
    · simp only [bisectLoop, if_pos hw]
      exact ⟨id, id, le_rfl, hlu, le_rfl, Nat.zero_le _, fun _ => hw⟩
    · by_cases hr : rej a
      · simp only [bisectLoop, if_neg hw, if_pos hr]
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ih a u ((a + u) / 2) ha.2 ⟨by linarith [ha.2], by linarith [ha.2]⟩
        exact ⟨fun _ => h1 hr, h2, ha.1.le.trans h3, h4, h5, by omega, fun h => h7 (by omega)⟩
      · simp only [bisectLoop, if_neg hw, if_neg hr]
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ih l a ((l + a) / 2) ha.1 ⟨by linarith [ha.1], by linarith [ha.1]⟩
        exact ⟨h1, fun _ => h2 hr, h3, h4, h5.trans ha.2.le, by omega, fun h => h7 (by omega)⟩

/-- From a midpoint, the width after `t` tests is at most `w 2^{-t}`, and `t ≤ j` whenever `w 2^{-j} ≤ ε`. -/
lemma loop_width (rej : ℝ → Prop) (ε : ℝ) : ∀ (k : ℕ) (l u w : ℝ), u - l ≤ w →
    (bisectLoop rej ε k l u ((l + u) / 2)).2.1 - (bisectLoop rej ε k l u ((l + u) / 2)).1 ≤
        w * (1 / 2) ^ (bisectLoop rej ε k l u ((l + u) / 2)).2.2 ∧
      ∀ j : ℕ, w * (1 / 2 : ℝ) ^ j ≤ ε → (bisectLoop rej ε k l u ((l + u) / 2)).2.2 ≤ j := by
  intro k
  induction k with
  | zero =>
    intro l u w hw
    simp only [bisectLoop, pow_zero, mul_one]
    exact ⟨hw, fun _ _ => Nat.zero_le _⟩
  | succ k ih =>
    intro l u w hw
    by_cases hε : u - l ≤ ε
    · simp only [bisectLoop, if_pos hε, pow_zero, mul_one]
      exact ⟨hw, fun _ _ => Nat.zero_le _⟩
    · have hjpos : ∀ j : ℕ, w * (1 / 2 : ℝ) ^ j ≤ ε → 1 ≤ j := fun j hj => by
        by_contra h0
        have : j = 0 := by omega
        subst this; simp at hj; linarith
      by_cases hr : rej ((l + u) / 2)
      · simp only [bisectLoop, if_neg hε, if_pos hr]
        have e : ((l + u) / 2 + u) / 2 = ((l + u) / 2 + u) / 2 := rfl
        obtain ⟨h1, h2⟩ := ih ((l + u) / 2) u (w / 2) (by linarith)
        refine ⟨by rw [pow_succ]; nlinarith [h1], fun j hj => ?_⟩
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by have := hjpos j hj; omega⟩
        have := h2 j' (by rw [pow_succ] at hj; linarith)
        omega
      · simp only [bisectLoop, if_neg hε, if_neg hr]
        obtain ⟨h1, h2⟩ := ih l ((l + u) / 2) (w / 2) (by linarith)
        refine ⟨by rw [pow_succ]; nlinarith [h1], fun j hj => ?_⟩
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by have := hjpos j hj; omega⟩
        have := h2 j' (by rw [pow_succ] at hj; linarith)
        omega

lemma startPoint_mem {α₀ u₀ : ℝ} (hu : 0 < u₀) : startPoint α₀ 0 u₀ ∈ Ioo 0 u₀ := by
  unfold startPoint
  split_ifs with h
  · exact h
  · constructor <;> linarith

/-! ### The bracket contains `α̂` -/

section Bracket

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

lemma crossSet_bdd (Dh τ : ℝ → ℝ) : BddBelow (crossSet Dh τ) := ⟨0, fun _ h => h.1.1⟩

lemma bracket_alphaHat {φ : 𝒳 → H} {κ : ℝ} {τ : ℝ → ℝ} {n m : ℕ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hτ0 : ∀ α ∈ Ico (0 : ℝ) 1, 0 ≤ τ α) (hτm : MonotoneOn τ (Ico 0 1))
    (hτc : ContinuousOn τ (Ioo 0 1)) (x : Fin n → 𝒳) (y : Fin m → 𝒳) {l u : ℝ} (hl0 : 0 ≤ l) (hu1 : u < 1)
    (hlu : l ≤ u) (hl : rejected (Demp φ x y) τ l) (hu : ¬ rejected (Demp φ x y) τ u) :
    l ≤ alphaHat (Demp φ x y) τ ∧ alphaHat (Demp φ x y) τ ≤ u ∧ (0 < l → l < alphaHat (Demp φ x y) τ) := by
  have huS : u ∈ crossSet (Demp φ x y) τ := ⟨⟨hl0.trans hlu, hu1⟩, not_lt.1 hu⟩
  obtain ⟨-, hIoo, -, hIco⟩ := StatFormal.Wave30tu.crossing 𝒳 H φ κ τ n m hφ hκ hn hm hτ0 hτm hτc x y ⟨u, huS⟩
  have hlS : l ∉ crossSet (Demp φ x y) τ := fun h => hl.not_ge h.2
  have hle : l ≤ alphaHat (Demp φ x y) τ := by
    by_contra h
    push_neg at h
    exact hlS (hIoo ⟨h, by linarith⟩)
  refine ⟨hle, csInf_le (crossSet_bdd _ _) huS, fun hl0' => lt_of_le_of_ne hle fun heq => ?_⟩
  rw [← heq] at hIco
  exact hlS ((hIco hl0').symm ▸ ⟨le_rfl, by linarith⟩)

end Bracket

theorem alg_loop : Claims.alg_loop := by
  intro 𝒳 H _ _ _ _ _ φ κ τ n m hφ hκ hn hm hτ0 hτm hτc x y l₀ u₀ a₀ ε J hl0 hlu hu1 hl hu ha
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := loop_spec (rejected (Demp φ x y) τ) ε J l₀ u₀ a₀ hlu ha
  obtain ⟨b1, b2, b3⟩ := bracket_alphaHat hφ hκ hn hm hτ0 hτm hτc x y (hl0.trans h3) (h5.trans_lt hu1) h4.le (h1 hl) (h2 hu)
  exact ⟨h1 hl, h2 hu, h3, h4, h5, b1, b2, b3, h6, h7⟩

theorem alg_bracket : Claims.alg_bracket := by
  intro 𝒳 H _ _ _ _ _ φ κ τ n m hφ hκ hn hm hτ0 hτm hτc x y α₀ u₀ ε J hu₀ hacc
  refine ⟨?_, fun h0 => ?_, fun p hp => ?_⟩
  · unfold bisectAlg; split_ifs with h <;> simp [h]
  · have h0S : (0 : ℝ) ∈ crossSet (Demp φ x y) τ := ⟨⟨le_rfl, by norm_num⟩, not_lt.1 h0⟩
    exact le_antisymm (csInf_le (crossSet_bdd _ _) h0S) (le_csInf ⟨0, h0S⟩ fun _ h => h.1.1)
  · unfold bisectAlg at hp
    split_ifs at hp with h0
    cases hp
    have := alg_loop 𝒳 H φ κ τ n m hφ hκ hn hm hτ0 hτm hτc x y 0 u₀ (startPoint α₀ 0 u₀) ε J le_rfl hu₀.1 hu₀.2 h0
      hacc (startPoint_mem hu₀.1)
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := this
    exact ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, fun h => ⟨c10 h, by linarith [c10 h]⟩⟩

theorem alg_cost : Claims.alg_cost := by
  intro rej u₀ ε J p hu0 hu1 hε hp
  unfold bisectAlg at hp
  split_ifs at hp with h0
  cases hp
  -- the first test point and the first step
  have main : (bisectLoop rej ε J 0 u₀ (startPoint (1 / 2) 0 u₀)).2.1 - (bisectLoop rej ε J 0 u₀ (startPoint (1 / 2) 0 u₀)).1 ≤
        (1 / 2) ^ (bisectLoop rej ε J 0 u₀ (startPoint (1 / 2) 0 u₀)).2.2 ∧
      ∀ k : ℕ, (1 / 2 : ℝ) ^ k ≤ ε → (bisectLoop rej ε J 0 u₀ (startPoint (1 / 2) 0 u₀)).2.2 ≤ k := by
    by_cases hs : (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < u₀
    · have hsp : startPoint (1 / 2) 0 u₀ = 1 / 2 := by unfold startPoint; exact if_pos hs
      rw [hsp]
      cases J with
      | zero =>
        simp only [bisectLoop, pow_zero]
        exact ⟨by linarith, fun _ _ => Nat.zero_le _⟩
      | succ k =>
        by_cases hw : u₀ - 0 ≤ ε
        · simp only [bisectLoop, if_pos hw, pow_zero]
          exact ⟨by linarith, fun _ _ => Nat.zero_le _⟩
        · have hjpos : ∀ j : ℕ, (1 / 2 : ℝ) ^ j ≤ ε → 1 ≤ j := fun j hj => by
            by_contra h
            have : j = 0 := by omega
            subst this; simp at hj; linarith
          by_cases hr : rej (1 / 2)
          · simp only [bisectLoop, if_neg hw, if_pos hr]
            obtain ⟨h1, h2⟩ := loop_width rej ε k (1 / 2) u₀ (1 / 2) (by linarith)
            refine ⟨by rw [pow_succ]; linarith, fun j hj => ?_⟩
            obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by have := hjpos j hj; omega⟩
            have := h2 j' (by rw [pow_succ] at hj; linarith)
            omega
          · simp only [bisectLoop, if_neg hw, if_neg hr]
            obtain ⟨h1, h2⟩ := loop_width rej ε k 0 (1 / 2) (1 / 2) (by linarith)
            refine ⟨by rw [pow_succ]; linarith, fun j hj => ?_⟩
            obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by have := hjpos j hj; omega⟩
            have := h2 j' (by rw [pow_succ] at hj; linarith)
            omega
    · have hsp : startPoint (1 / 2) 0 u₀ = (0 + u₀) / 2 := by simp only [startPoint, if_neg hs]
      rw [hsp]
      obtain ⟨h1, h2⟩ := loop_width rej ε J 0 u₀ u₀ (by linarith)
      refine ⟨h1.trans ?_, fun j hj => h2 j ?_⟩
      · exact mul_le_of_le_one_left (by positivity) hu1
      · exact (mul_le_of_le_one_left (by positivity) hu1).trans hj
  refine ⟨main.1, main.2, fun he => main.2 7 (by rw [he]; norm_num)⟩

theorem alg_start : Claims.alg_start := by
  intro 𝒳 H _ _ _ _ _ φ κ D τ n m hφ hκ hD hn hm
  have hlim : Tendsto τ (𝓝[<] 1) atTop → ∃ α ∈ Ioo (0 : ℝ) 1, D ≤ τ α := fun h => by
    obtain ⟨α, hα1, hα2⟩ := ((h.eventually (eventually_ge_atTop D)).and
      (Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1))).exists
    exact ⟨α, ⟨by linarith [hα2.1], hα2.2⟩, hα1⟩
  refine ⟨fun x y α hα hDα => not_lt.2 ((StatFormal.Wave30tu.Demp_le_Dphi 𝒳 H φ κ D n m hφ hκ hD hn hm x y α hα).trans hDα),
    hlim, fun h hτ0 hτm hτc hR => ?_⟩
  set S := {α | α ∈ Ico (0 : ℝ) 1 ∧ D ≤ τ α} with hS
  obtain ⟨α₁, hα₁, hDα₁⟩ := hlim h
  have hSne : S.Nonempty := ⟨α₁, ⟨hα₁.1.le, hα₁.2⟩, hDα₁⟩
  have hbdd : BddBelow S := ⟨0, fun _ h => h.1.1⟩
  -- some `a′ ∈ (0,1)` with `τ(a′) < D`
  obtain ⟨_, ⟨a', ha', rfl⟩, ha'D⟩ := exists_lt_of_csInf_lt ((nonempty_Ioo.2 (by norm_num : (0 : ℝ) < 1)).image τ) hR
  have hlow : ∀ α ∈ S, a' < α := fun α hα => by
    by_contra hle; push_neg at hle
    have := hτm ⟨hα.1.1, hα.1.2⟩ ⟨ha'.1.le, ha'.2⟩ hle
    linarith [hα.2]
  set b := sInf S with hb
  have hab : a' ≤ b := le_csInf hSne fun α hα => (hlow α hα).le
  have hb1 : b < 1 := (csInf_le hbdd ⟨⟨hα₁.1.le, hα₁.2⟩, hDα₁⟩).trans_lt hα₁.2
  have hb0 : 0 < b := lt_of_lt_of_le ha'.1 hab
  have hbS : D ≤ τ b := by
    by_contra hlt; push_neg at hlt
    have hcont : ContinuousAt τ b := hτc.continuousAt (Ioo_mem_nhds hb0 hb1)
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 (hcont.eventually (gt_mem_nhds hlt))
    obtain ⟨α, hαS, hαlt⟩ := exists_lt_of_csInf_lt hSne (show b < b + r by linarith)
    have hbα : b ≤ α := csInf_le hbdd hαS
    have := hball (show dist α b < r by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith)
    linarith [hαS.2]
  exact ⟨b, hb0, ⟨⟨hb0.le, hb1⟩, hbS⟩, fun α hα => csInf_le hbdd hα⟩

theorem alg_event : Claims.alg_event := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ δ τ n m hφ hκ hδ hδ1 hn hm hτ h1
  obtain ⟨hmeas, hprob, hall⟩ := StatFormal.Wave30tu.oneevent 𝒳 H P Q φ κ δ τ n m hφ hκ hδ hδ1 hn hm hτ h1
  refine ⟨_, hmeas, hprob, fun z hz => ?_⟩
  have hrej : ∀ α ∈ Ico (0 : ℝ) 1, rejected (Demp φ z.1 z.2) τ α → α < StatFormal.Distances.tvDist P Q :=
    fun α hα hr => by
      by_contra hge; push_neg at hge
      exact hr.not_ge (hall z hz α ⟨hge, hα.2⟩)
  refine ⟨hrej, fun α₀ u₀ ε J p hu hp => ?_, fun l₀ u₀ a₀ ε J hl0 hu1 hl ha => ?_⟩
  · unfold bisectAlg at hp
    split_ifs at hp with h0
    cases hp
    obtain ⟨h1, -, h3, h4, h5, -⟩ := loop_spec (rejected (Demp φ z.1 z.2) τ) ε J 0 u₀ (startPoint α₀ 0 u₀) hu.1
      (startPoint_mem hu.1)
    exact hrej _ ⟨h3, by linarith [hu.2]⟩ (h1 h0)
  · obtain ⟨h1, -, h3, h4, h5, -⟩ := loop_spec (rejected (Demp φ z.1 z.2) τ) ε J l₀ u₀ a₀ (ha.1.trans ha.2) ha
    exact hrej _ ⟨hl0.trans h3, by linarith⟩ (h1 hl)

end StatFormal.Wave31tj
