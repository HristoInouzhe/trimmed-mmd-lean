import StatFormal.Archive.Wave30ah.Statements
import StatFormal.Archive.Wave30z.RouteLimit
import StatFormal.Archive.Wave11b.RouteAttain
import StatFormal.Archive.TrimmedMMD.ZeroSet.Proofs

/-!
# Route — wave 30ah: the contact level `α*_r` (untrusted)

* `region_mono`: `α ↦ 𝒞_α` is increasing (the cap `1/(1−α)` increases).
* `region_iInter`: for levels `a_j ↓ a*` (`a_j < 1`), `⋂_j 𝒞_{a_j} = 𝒞_{a*}`: a point of every `𝒞_{a_j}` has a
  density in `Kset P a_j` with the right embedding for each `j`; these sets are nested, closed, convex and bounded
  in `L²(P)`, so they meet (`nonempty_iInter_of_closed_convex`), and a common density has
  `∫_A h ≤ 1/(1 − a_j) P(A)` for all `j`, hence `≤ 1/(1 − a*) P(A)`.
* `boundary_contact_level`: every level in `(α*_r, 1)` is a meeting level (upward closedness); the nested nonempty
  compact sets `𝒞_{a_j}(P) ∩ 𝒞_{a_j}(Q)` meet; a common point lies in `𝒞_{α*}(P) ∩ 𝒞_{α*}(Q)`.
* `boundary_level_tv`: at `τ = TV(P,Q) < 1` the common trimming of `TrimmedMMD/ZeroSet` embeds into both regions.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped InnerProductSpace RealInnerProductSpace Pointwise

namespace StatFormal.Wave30ah

open StatFormal.TrimmedMMD.Concentration (region empirical)
open StatFormal.TrimmedMMD.Unconditional (setDist Dpop Demp)
open StatFormal.TrimmedMMD.ZeroSet (Kset mem_Kset isClosed_Kset convex_Kset norm_le_of_mem_Kset emb emb_add emb_smul
  continuous_emb nonempty_iInter_of_closed_convex IsTrimDensity exists_common_of_tvDist_le integral_smul_eq_withDensity)

section Level
variable {𝒳 E : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E] {φ : 𝒳 → E} {κ : ℝ}

lemma region_mono (μ : Measure 𝒳) {α α' : ℝ} (h : α ≤ α') (h1 : α' < 1) : region φ α μ ⊆ region φ α' μ := by
  rintro _ ⟨g, hg, hgb, hg1, rfl⟩
  refine ⟨g, hg, fun x => ⟨(hgb x).1, (hgb x).2.trans ?_⟩, hg1, rfl⟩
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

lemma Kset_mono (P : Measure 𝒳) [IsProbabilityMeasure P] {α α' : ℝ} (h : α ≤ α') (h1 : α' < 1) :
    Kset P α ⊆ Kset P α' := by
  intro f hf
  rw [mem_Kset] at hf ⊢
  refine ⟨fun A hA => ⟨(hf.1 A hA).1, (hf.1 A hA).2.trans ?_⟩, hf.2⟩
  exact mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le (by linarith) (by linarith)) measureReal_nonneg

lemma region_iInter (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (P : Measure 𝒳) [IsProbabilityMeasure P]
    {a : ℕ → ℝ} {as : ℝ} (ha : Antitone a) (ha1 : ∀ j, a j < 1) (hlim : Tendsto a atTop (𝓝 as)) {z : E}
    (hz : ∀ j, z ∈ region φ (a j) P) : z ∈ region φ as P := by
  have hle : ∀ j, as ≤ a j := fun j => ha.le_of_tendsto hlim j
  have has1 : as < 1 := (hle 0).trans_lt (ha1 0)
  set F : ℕ → Set (Lp ℝ 2 P) := fun j => Kset P (a j) ∩ {h | emb P φ h = z} with hF
  have hne : ∀ j, (F j).Nonempty := fun j => by
    obtain ⟨h, hK, he⟩ := (StatFormal.Wave11b.region_iff (ha1 j) z).1 (hz j)
    exact ⟨h, hK, he⟩
  have hcl : ∀ j, IsClosed (F j) := fun j =>
    (isClosed_Kset P (a j)).inter (isClosed_eq (continuous_emb hφ hκ) continuous_const)
  have hcv : ∀ j, Convex ℝ (F j) := by
    intro j h₁ hh₁ h₂ hh₂ s t hs ht hst
    refine ⟨convex_Kset P (a j) hh₁.1 hh₂.1 hs ht hst, ?_⟩
    change emb P φ (s • h₁ + t • h₂) = z
    rw [emb_add hφ hκ, emb_smul, emb_smul, hh₁.2, hh₂.2, ← add_smul, hst, one_smul]
  have hanti : Antitone F := fun i j hij h hh =>
    ⟨Kset_mono P (ha hij) (ha1 i) hh.1, hh.2⟩
  have hb : ∀ j, ∀ h ∈ F j, ‖h‖ ^ 2 ≤ (1 / (1 - a 0)) ^ 2 := by
    intro j h hh
    have h1 := norm_le_of_mem_Kset P (ha1 j) hh.1
    have h2 : 1 / (1 - a j) ≤ 1 / (1 - a 0) :=
      one_div_le_one_div_of_le (by linarith [ha1 0]) (by linarith [ha (Nat.zero_le j)])
    exact pow_le_pow_left₀ (norm_nonneg _) (h1.trans h2) 2
  obtain ⟨h, hh⟩ := nonempty_iInter_of_closed_convex F hne hcl hcv hanti _ hb
  rw [mem_iInter] at hh
  refine (StatFormal.Wave11b.region_iff has1 z).2 ⟨h, ?_, (hh 0).2⟩
  have h0 := (mem_Kset P).1 (hh 0).1
  rw [mem_Kset]
  refine ⟨fun A hA => ⟨(h0.1 A hA).1, ?_⟩, h0.2⟩
  have hlim' : Tendsto (fun j => 1 / (1 - a j) * P.real A) atTop (𝓝 (1 / (1 - as) * P.real A)) := by
    refine Tendsto.mul_const _ (Tendsto.div tendsto_const_nhds (tendsto_const_nhds.sub hlim) (by linarith))
  exact ge_of_tendsto' hlim' fun j => (((mem_Kset P).1 (hh j).1).1 A hA).2

end Level

theorem boundary_contact_level : Claims.boundary_contact_level := by
  intro 𝒳 E _ _ _ _ φ κ P Q _ _ hφ hκ ⟨α₀, hα₀0, hα₀1, hα₀⟩
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  set S := {α : ℝ | 0 ≤ α ∧ α < 1 ∧ (region φ α P ∩ region φ α Q).Nonempty} with hS
  have hSne : S.Nonempty := ⟨α₀, hα₀0, hα₀1, hα₀⟩
  have hSbdd : BddBelow S := ⟨0, fun α hα => hα.1⟩
  have hc : contactLevel φ P Q = sInf S := rfl
  set as := sInf S with has
  have has0 : 0 ≤ as := le_csInf hSne fun α hα => hα.1
  have has1 : as < 1 := (csInf_le hSbdd ⟨hα₀0, hα₀1, hα₀⟩).trans_lt hα₀1
  -- every level in `(as, 1)` is a meeting level
  have hup : ∀ a', as < a' → a' < 1 → (region φ a' P ∩ region φ a' Q).Nonempty := by
    intro a' h1 h2
    obtain ⟨s, ⟨hs0, hs1, z, hzP, hzQ⟩, hsa⟩ := exists_lt_of_csInf_lt hSne h1
    exact ⟨z, region_mono P hsa.le h2 hzP, region_mono Q hsa.le h2 hzQ⟩
  set a : ℕ → ℝ := fun j => as + (1 - as) / ((j : ℝ) + 2) with ha
  have hpos : 0 < 1 - as := by linarith
  have ha_gt : ∀ j, as < a j := fun j => by
    simp only [ha]; have : 0 < (1 - as) / ((j : ℝ) + 2) := by positivity
    linarith
  have ha_lt : ∀ j, a j < 1 := fun j => by
    simp only [ha]
    have h2 : (1 - as) / ((j : ℝ) + 2) < 1 - as := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith [(j.cast_nonneg : (0 : ℝ) ≤ j)]
    linarith
  have ha_anti : Antitone a := by
    intro i j hij
    simp only [ha]
    have : (1 - as) / ((j : ℝ) + 2) ≤ (1 - as) / ((i : ℝ) + 2) :=
      div_le_div_of_nonneg_left hpos.le (by positivity) (by exact_mod_cast (by omega : i + 2 ≤ j + 2))
    linarith
  have ha_lim : Tendsto a atTop (𝓝 as) := by
    have : Tendsto (fun j : ℕ => (1 - as) / ((j : ℝ) + 2)) atTop (𝓝 0) := by
      have h := tendsto_const_nhds (x := 1 - as) |>.div_atTop
        (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
      exact h
    simpa using (tendsto_const_nhds (x := as)).add this
  set C : ℕ → Set E := fun j => region φ (a j) P ∩ region φ (a j) Q with hC
  have hCsub : ∀ j, C (j + 1) ⊆ C j := fun j =>
    inter_subset_inter (region_mono P (ha_anti (Nat.le_succ j)) (ha_lt j))
      (region_mono Q (ha_anti (Nat.le_succ j)) (ha_lt j))
  have hCne : ∀ j, (C j).Nonempty := fun j => hup (a j) (ha_gt j) (ha_lt j)
  have hCcl : ∀ j, IsClosed (C j) := fun j =>
    (StatFormal.Wave11b.region_closed hφ hκ (ha_lt j)).inter (StatFormal.Wave11b.region_closed hφ hκ (ha_lt j))
  have hC0 : IsCompact (C 0) :=
    Metric.isCompact_of_isClosed_isBounded (hCcl 0)
      ((StatFormal.Wave30z.isBounded_region P (φ := φ) (α := a 0) hκ).subset inter_subset_left)
  obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hCsub hCne hC0 hCcl
  rw [mem_iInter] at hz
  refine ⟨has0, has1, z, ?_, ?_⟩
  · exact region_iInter hφ hκ P ha_anti ha_lt ha_lim fun j => (hz j).1
  · exact region_iInter hφ hκ Q ha_anti ha_lt ha_lim fun j => (hz j).2

theorem boundary_contact_star : Claims.boundary_contact_star := by
  intro 𝒳 E _ _ _ _ φ κ P Q _ _ Ω _ μ _ ξ η n m r cP cQ Ω' _ μ' _ 𝔾 hφ hκ hS hSc h𝔾 hmeet
  obtain ⟨h0, h1, hAB⟩ := boundary_contact_level 𝒳 E φ κ P Q hφ hκ hmeet
  exact StatFormal.Wave30z.boundary_contact 𝒳 E φ κ (contactLevel φ P Q) P Q Ω μ ξ η n m r cP cQ Ω' μ' 𝔾 hφ hκ
    h0 h1 hS hSc h𝔾 hAB

theorem boundary_level_tv : Claims.boundary_level_tv := by
  intro 𝒳 E _ _ _ _ φ κ P Q _ _ hφ hκ htv
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  set τ := StatFormal.Distances.tvDist P Q with hτ
  have hτ0 : 0 ≤ τ := StatFormal.Distances.tvDist_nonneg P Q
  obtain ⟨gP, gQ, hP, hQ, hR⟩ := exists_common_of_tvDist_le htv le_rfl
  have ha : ∫ x, gP x • φ x ∂P ∈ region φ τ P := ⟨gP, hP.1, hP.2.1, hP.2.2, rfl⟩
  have hb : ∫ x, gQ x • φ x ∂Q ∈ region φ τ Q := ⟨gQ, hQ.1, hQ.2.1, hQ.2.2, rfl⟩
  have hab : ∫ x, gP x • φ x ∂P = ∫ x, gQ x • φ x ∂Q := by
    rw [integral_smul_eq_withDensity P hP.1 (fun x => (hP.2.1 x).1),
      integral_smul_eq_withDensity Q hQ.1 (fun x => (hQ.2.1 x).1), hR]
  refine csInf_le ⟨0, fun α hα => hα.1⟩ ⟨hτ0, htv, _, ha, hab ▸ hb⟩

end StatFormal.Wave30ah
