import StatFormal.Archive.Wave30v.RouteGeom

/-!
# Route — wave 30v `boundary_value_hadamard`, `boundary_translation` (untrusted)

`valueFn = supFun ∘ L`, `L(H_A, H_B) = dualObj H_A H_B` continuous linear (2-Lipschitz); at a contact pair the
dual objective is `≤ 0` with value `0` exactly on `Ball ∩ (B − A)°` (`boundary_contact_argmax`), so the sup
functional's derivative (`boundary_sup_hadamard`) is the stated one. Translation directions: the derivative is
`sup {⟨g, x_A − x_B⟩ : g ∈ Ball ∩ (B − A)°}`, and `(B − A)° = (cl cone(B − A))°`, so Moreau
(`boundary_polar_infDist`) gives `dist(x_A − x_B, cl cone(B − A))`.
-/

set_option linter.style.longLine false

noncomputable section
open Set Filter Topology Metric
open scoped InnerProductSpace RealInnerProductSpace Pointwise

namespace StatFormal.Wave30v

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma dualObj_apply (H₁ H₂ : C(Ball E, ℝ)) (g : Ball E) : dualObj H₁ H₂ g = -H₁ (ballNeg g) - H₂ g := rfl

lemma dualObj_add_smul (x k : C(Ball E, ℝ) × C(Ball E, ℝ)) (t : ℝ) :
    dualObj (x + t • k).1 (x + t • k).2 = dualObj x.1 x.2 + t • dualObj k.1 k.2 := by
  ext g
  simp only [dualObj_apply, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, ContinuousMap.add_apply,
    ContinuousMap.smul_apply, smul_eq_mul]
  ring

lemma convex_coneHull {S : Set E} (hS : Convex ℝ S) : Convex ℝ (coneHull S) := by
  rintro _ ⟨c1, hc1, s1, hs1, rfl⟩ _ ⟨c2, hc2, s2, hs2, rfl⟩ a b ha hb hab
  have h1 : 0 ≤ a * c1 := mul_nonneg ha hc1
  have h2 : 0 ≤ b * c2 := mul_nonneg hb hc2
  by_cases h : a * c1 + b * c2 = 0
  · have e1 : a * c1 = 0 := by linarith
    have e2 : b * c2 = 0 := by linarith
    refine ⟨0, le_rfl, s1, hs1, ?_⟩
    simp only [smul_smul, e1, e2, zero_smul, add_zero]
  · have hpos : 0 < a * c1 + b * c2 := lt_of_le_of_ne (by linarith) (Ne.symm h)
    refine ⟨a * c1 + b * c2, hpos.le, (a * c1 / (a * c1 + b * c2)) • s1 + (b * c2 / (a * c1 + b * c2)) • s2,
      hS hs1 hs2 (by positivity) (by positivity) (by field_simp), ?_⟩
    have e1 : (a * c1 + b * c2) * (a * c1 / (a * c1 + b * c2)) = a * c1 := by field_simp
    have e2 : (a * c1 + b * c2) * (b * c2 / (a * c1 + b * c2)) = b * c2 := by field_simp
    simp only [smul_add, smul_smul, e1, e2]

lemma polarSet_closure_coneHull (S : Set E) : polarSet (closure (coneHull S)) = polarSet S := by
  ext g
  constructor
  · intro hg s hs
    exact hg s (subset_closure ⟨1, zero_le_one, s, hs, (one_smul ℝ s).symm⟩)
  · intro hg
    have hcl : IsClosed {v : E | ⟪g, v⟫ ≤ 0} := isClosed_le (continuous_const.inner continuous_id) continuous_const
    have hsub : coneHull S ⊆ {v : E | ⟪g, v⟫ ≤ 0} := by
      rintro _ ⟨c, hc, s, hs, rfl⟩
      show ⟪g, c • s⟫ ≤ 0
      rw [real_inner_smul_right]
      exact mul_nonpos_of_nonneg_of_nonpos hc (hg s hs)
    intro v hv
    exact closure_minimal hsub hcl hv

lemma cone_closure_coneHull (S : Set E) : ∀ c : ℝ, 0 ≤ c → ∀ v ∈ closure (coneHull S), c • v ∈ closure (coneHull S) := by
  intro c hc v hv
  refine map_mem_closure (continuous_const_smul c) hv ?_
  rintro _ ⟨c', hc', s, hs, rfl⟩
  exact ⟨c * c', mul_nonneg hc hc', s, hs, smul_smul c c' s⟩

lemma norm_dualObj_sub_le [CompactSpace (Ball E)] (H H' : C(Ball E, ℝ) × C(Ball E, ℝ)) :
    ‖dualObj H.1 H.2 - dualObj H'.1 H'.2‖ ≤ 2 * ‖H - H'‖ := by
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun g => ?_
  rw [ContinuousMap.sub_apply, dualObj_apply, dualObj_apply, Real.norm_eq_abs]
  have h1 := ContinuousMap.norm_coe_le_norm (H.1 - H'.1) (ballNeg g)
  have h2 := ContinuousMap.norm_coe_le_norm (H.2 - H'.2) g
  have h3 : ‖H.1 - H'.1‖ ≤ ‖H - H'‖ := by simpa using norm_fst_le (H - H')
  have h4 : ‖H.2 - H'.2‖ ≤ ‖H - H'‖ := by simpa using norm_snd_le (H - H')
  rw [ContinuousMap.sub_apply, Real.norm_eq_abs] at h1 h2
  have : -H.1 (ballNeg g) - H.2 g - (-H'.1 (ballNeg g) - H'.2 g) =
      -(H.1 (ballNeg g) - H'.1 (ballNeg g)) - (H.2 g - H'.2 g) := by ring
  rw [this]
  calc |-(H.1 (ballNeg g) - H'.1 (ballNeg g)) - (H.2 g - H'.2 g)|
      ≤ |H.1 (ballNeg g) - H'.1 (ballNeg g)| + |H.2 g - H'.2 g| := by
        refine (abs_sub _ _).trans ?_; rw [abs_neg]
    _ ≤ 2 * ‖H - H'‖ := by linarith

lemma lipschitz_dualObj [CompactSpace (Ball E)] :
    LipschitzWith 2 (fun H : C(Ball E, ℝ) × C(Ball E, ℝ) => dualObj H.1 H.2) := by
  refine LipschitzWith.of_dist_le_mul fun H H' => ?_
  rw [dist_eq_norm, dist_eq_norm]
  exact_mod_cast norm_dualObj_sub_le H H'

lemma continuous_dualObj [CompactSpace (Ball E)] :
    Continuous (fun H : C(Ball E, ℝ) × C(Ball E, ℝ) => dualObj H.1 H.2) := lipschitz_dualObj.continuous

end

section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

instance : Nonempty (Ball E) := ⟨⟨0, by simp⟩⟩

/-- At a contact pair, the dual objective has value `0` and maximisers `Ball ∩ (B − A)°`. -/
lemma contact_supFun_argmax {A B : Set E} {hA hB : C(Ball E, ℝ)} (hAb : Bornology.IsBounded A)
    (hBb : Bornology.IsBounded B) (hAB : (A ∩ B).Nonempty) (hAeq : ∀ g, hA g = supportFn A g)
    (hBeq : ∀ g, hB g = supportFn B g) :
    supFun (dualObj hA hB) = 0 ∧ argmaxSet (dualObj hA hB) = {g : Ball E | (g : E) ∈ polarSet (B - A)} := by
  have hval : ∀ g : Ball E, dualObj hA hB g = -supportFn A (-(g : E)) - supportFn B g := by
    intro g; simp [dualObj, hAeq, hBeq, ballNeg]
  have hc := boundary_contact_argmax E A B hAb hBb hAB
  have hsup : supFun (dualObj hA hB) = 0 := by
    refine le_antisymm (supFun_le fun g => by rw [hval]; exact (hc _).1) ?_
    have h0 : dualObj hA hB ⟨0, by simp⟩ = 0 := by
      rw [hval]
      exact ((hc 0).2).2 (fun x _ => by simp)
    rw [← h0]; exact le_supFun _ _
  refine ⟨hsup, ?_⟩
  ext g
  simp only [argmaxSet, hsup, mem_ofPred_eq, hval]
  exact (hc g).2

lemma valueDeriv_eq_supDeriv {A B : Set E} {hA hB : C(Ball E, ℝ)} (hAb : Bornology.IsBounded A)
    (hBb : Bornology.IsBounded B) (hAB : (A ∩ B).Nonempty) (hAeq : ∀ g, hA g = supportFn A g)
    (hBeq : ∀ g, hB g = supportFn B g) (H : C(Ball E, ℝ) × C(Ball E, ℝ)) :
    valueDeriv A B H = supDeriv (dualObj hA hB) (dualObj H.1 H.2) := by
  unfold valueDeriv supDeriv
  rw [(contact_supFun_argmax hAb hBb hAB hAeq hBeq).2]
  rfl

lemma continuous_valueDeriv {A B : Set E} {hA hB : C(Ball E, ℝ)} (hAb : Bornology.IsBounded A)
    (hBb : Bornology.IsBounded B) (hAB : (A ∩ B).Nonempty) (hAeq : ∀ g, hA g = supportFn A g)
    (hBeq : ∀ g, hB g = supportFn B g) : Continuous (valueDeriv A B) := by
  have : valueDeriv A B = fun H => supDeriv (dualObj hA hB) (dualObj H.1 H.2) :=
    funext (valueDeriv_eq_supDeriv hAb hBb hAB hAeq hBeq)
  rw [this]
  exact (lipschitz_supDeriv _).continuous.comp continuous_dualObj

lemma continuous_valueFn : Continuous (valueFn : C(Ball E, ℝ) × C(Ball E, ℝ) → ℝ) :=
  lipschitz_supFun.continuous.comp continuous_dualObj

end

theorem boundary_value_hadamard : Claims.boundary_value_hadamard := by
  intro E _ _ _ A B hA hB _ _ hAb hBb hAB hAeq hBeq
  obtain ⟨hsup, -⟩ := contact_supFun_argmax hAb hBb hAB hAeq hBeq
  refine ⟨hsup, ?_⟩
  intro h t k ht ht0 hk
  have hL : Tendsto (fun n => dualObj (k n).1 (k n).2) atTop (𝓝 (dualObj h.1 h.2)) :=
    (continuous_dualObj.tendsto h).comp hk
  have hmain := boundary_sup_hadamard (Ball E) (dualObj hA hB) (dualObj h.1 h.2) t
    (fun n => dualObj (k n).1 (k n).2) ht ht0 hL
  rw [valueDeriv_eq_supDeriv hAb hBb hAB hAeq hBeq]
  refine hmain.congr fun n => ?_
  simp only [valueFn]
  rw [dualObj_add_smul]

theorem boundary_translation : Claims.boundary_translation := by
  intro E _ _ _ A B hAne hBne hA hB _ xA xB
  set K := closure (coneHull (B - A)) with hK
  obtain ⟨a, ha⟩ := hAne
  obtain ⟨b, hb⟩ := hBne
  have hKne : K.Nonempty := ⟨b - a, subset_closure ⟨1, zero_le_one, b - a, ⟨b, hb, a, ha, rfl⟩, (one_smul ℝ _).symm⟩⟩
  have hKcv : Convex ℝ K := (convex_coneHull (hB.sub hA)).closure
  have hmo := boundary_polar_infDist E K hKne isClosed_closure hKcv (cone_closure_coneHull _) (xA - xB)
  rw [← hmo, polarSet_closure_coneHull]
  unfold valueDeriv
  congr 1
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨g, ⟨hg, g.2⟩, ?_⟩
    simp only [linDir, ballNeg, ContinuousMap.coe_mk, inner_neg_left, inner_sub_right]
    ring
  · rintro ⟨g, ⟨hgK, hgB⟩, rfl⟩
    refine ⟨⟨g, hgB⟩, hgK, ?_⟩
    simp only [linDir, ballNeg, ContinuousMap.coe_mk, inner_neg_left, inner_sub_right]
    ring

end StatFormal.Wave30v
