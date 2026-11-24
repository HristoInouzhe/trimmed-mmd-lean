import StatFormal.Wave31tn.Proofs
import StatFormal.Wave30tz.Proofs
import StatFormal.Wave31tr.Statements

/-!
# Wave 31tr, chunk M3: T22 (b) `same_quantile` — the two parts of Corollary 5.9 concern the same quantile (untrusted route)

* `C, N₁` are those of the certified `Wave31tn.minimax_iii` (Cor 5.9 (ii)); its second conjunct is the upper part
  `P(e > C N^{-1/2}) ≤ η` on `𝓜`.
* The lower part: the certified `Wave31tn.minimax_i` (Cor 5.9 (i)) at `Ξ = Unit`, `ρ = δ_()`, `T((x, y), ξ) = α̂_lo(x, y)`;
  `T` is measurable by the certified `Wave30tz.lo_upper` (admissibility, at any pair of laws), and valid on `𝓜` by the first
  conjunct of `minimax_iii`. It gives a pair of `𝓜` with `P(e ≥ c_lo N^{-1/2}) ≥ (1 − δ)/2 > η`, and `{e > r} ⊇ {e ≥ c_lo N^{-1/2}}`
  for `r < c_lo N^{-1/2}` (monotonicity of the measure). The product with `δ_()` is read through `Measure.prod_prod`.
* `c_lo ≤ C`: otherwise `r = C N^{-1/2} < c_lo N^{-1/2}` at that pair gives `η < P(e > C N^{-1/2}) ≤ η`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tr.RouteFW

open StatFormal.Wave30tz StatFormal.Wave30tp StatFormal.Wave31tn StatFormal.Wave31tl

/-- An event of the first coordinate has the same measure under `μ ⊗ δ_()`. -/
lemma prod_dirac_unit_real {α : Type*} [MeasurableSpace α] (μ : Measure α) (S : Set α) :
    (μ.prod (Measure.dirac ())).real {z : α × Unit | z.1 ∈ S} = μ.real S := by
  have : {z : α × Unit | z.1 ∈ S} = S ×ˢ univ := by ext z; simp
  rw [this, measureReal_def, Measure.prod_prod, measure_univ, mul_one, ← measureReal_def]

/-- **T22 (b)**: with `η < (1 − δ)/2`, the worst-case upper `η`-quantile of the error of the split-sample bound lies in
`[c_lo N^{-1/2}, C N^{-1/2}]`. -/
theorem same_quantile_route : Claims.same_quantile := by
  intro κ Dφ a₁ c₀ s2 δ η ha₁0 ha₁1 hc₀ hs20 hs24 hδ0 hδ1 hη0 hη1 hηδ
  obtain ⟨C, N₁, hC⟩ := StatFormal.Wave31tn.minimax_iii κ Dφ a₁ c₀ s2 δ η ha₁0 ha₁1 hc₀ hs20 hs24 hδ0 hδ1 hη0 hη1
  refine ⟨C, N₁, ?_⟩
  intro a₀ 𝒳 H _ _ _ _ _ φ x₁ x₂ x₃ f n m R hφ hκ hDφ hDφκ hf1 hf2 hf3 ha₀ ha₀₁ hc₀f hN hR hdef
  have hNmax : max N₁ 10 ≤ ((min n m : ℕ) : ℝ) := (le_max_left _ _).trans hN
  have hN10 : (10 : ℝ) ≤ ((min n m : ℕ) : ℝ) := (le_max_right _ _).trans hNmax
  have hNclo : clo δ a₀ ^ 2 / (a₁ - a₀) ^ 2 ≤ ((min n m : ℕ) : ℝ) := (le_max_right _ _).trans hN
  have hN1 : 1 ≤ min n m := by exact_mod_cast (show (1 : ℝ) ≤ ((min n m : ℕ) : ℝ) by linarith)
  have hsqrt : 0 < √((min n m : ℕ) : ℝ) := Real.sqrt_pos.2 (by linarith)
  -- the upper part and validity on `𝓜` (Cor 5.9 (ii))
  have hiii : ∀ P Q : Measure 𝒳, InM φ a₀ a₁ c₀ P Q → _ := fun P Q hPQ =>
    hC a₀ 𝒳 H φ n m P Q R hφ hκ hDφ hDφκ ha₀ ha₀₁ hNmax hPQ hR hdef
  have hup : ∀ P Q : Measure 𝒳, InM φ a₀ a₁ c₀ P Q →
      sampleLaw P Q n m {ω | C / √((min n m : ℕ) : ℝ) <
        StatFormal.Distances.tvDist P Q - R.alphaLo (rootGrid (min n m)) δ ω.1 ω.2} ≤ ENNReal.ofReal η :=
    fun P Q hPQ => (hiii P Q hPQ).2
  -- measurability of `α̂_lo` (admissibility; `Wave30tz.lo_upper` at any pair of laws)
  have hmeas : Measurable fun ω : (Fin n → 𝒳) × (Fin m → 𝒳) => R.alphaLo (rootGrid (min n m)) δ ω.1 ω.2 :=
    (StatFormal.Wave30tz.lo_upper 𝒳 (Measure.dirac x₁) (Measure.dirac x₁) (rootLevels (min n m)) n m
      (rootGrid (min n m)) δ (1 / 2) R (RouteS3iii.rootGrid_isGrid hN1) hδ0 hδ1 (by norm_num) (by norm_num) hR.1).1
  set T : ((Fin n → 𝒳) × (Fin m → 𝒳)) × Unit → ℝ := fun z => R.alphaLo (rootGrid (min n m)) δ z.1.1 z.1.2 with hTdef
  have hT : Measurable T := hmeas.comp measurable_fst
  -- the lower part (Cor 5.9 (i))
  have hvalid : ∀ P Q : Measure 𝒳, InM φ a₀ a₁ c₀ P Q →
      ((sampleLaw P Q n m).prod (Measure.dirac ())).real {z | StatFormal.Distances.tvDist P Q < T z} ≤ δ := by
    intro P Q hPQ
    have h := (hiii P Q hPQ).1
    have := prod_dirac_unit_real (sampleLaw P Q n m)
      {ω | StatFormal.Distances.tvDist P Q < R.alphaLo (rootGrid (min n m)) δ ω.1 ω.2}
    change ((sampleLaw P Q n m).prod (Measure.dirac ())).real
      {z | z.1 ∈ {ω : (Fin n → 𝒳) × (Fin m → 𝒳) |
        StatFormal.Distances.tvDist P Q < R.alphaLo (rootGrid (min n m)) δ ω.1 ω.2}} ≤ δ
    rw [this, measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal hδ0.le h
  obtain ⟨P, Q, hPQ, hlow⟩ := StatFormal.Wave31tn.minimax_i 𝒳 H φ κ x₁ x₂ x₃ f a₀ a₁ c₀ δ n m Unit
    (Measure.dirac ()) T hφ hκ hf1 hf2 hf3 ha₀ ha₀₁ ha₁1 hc₀ hc₀f hδ0 hδ1 hNclo hT hvalid
  haveI : IsProbabilityMeasure P := hPQ.1
  haveI : IsProbabilityMeasure Q := hPQ.2.1
  haveI := Limits.sampleLaw_isProb P Q n m
  have hlow' : ENNReal.ofReal ((1 - δ) / 2) ≤ sampleLaw P Q n m {ω | clo δ a₀ / √((min n m : ℕ) : ℝ) ≤
      StatFormal.Distances.tvDist P Q - R.alphaLo (rootGrid (min n m)) δ ω.1 ω.2} := by
    have := prod_dirac_unit_real (sampleLaw P Q n m) {ω | clo δ a₀ / √((min n m : ℕ) : ℝ) ≤
      StatFormal.Distances.tvDist P Q - R.alphaLo (rootGrid (min n m)) δ ω.1 ω.2}
    change (1 - δ) / 2 ≤ ((sampleLaw P Q n m).prod (Measure.dirac ())).real
      {z | z.1 ∈ {ω : (Fin n → 𝒳) × (Fin m → 𝒳) | clo δ a₀ / √((min n m : ℕ) : ℝ) ≤
        StatFormal.Distances.tvDist P Q - R.alphaLo (rootGrid (min n m)) δ ω.1 ω.2}} at hlow
    rw [this, measureReal_def] at hlow
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 hlow
  have hηlt : ENNReal.ofReal η < ENNReal.ofReal ((1 - δ) / 2) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hηδ
  have hpart2 : ∀ r : ℝ, r < clo δ a₀ / √((min n m : ℕ) : ℝ) →
      ENNReal.ofReal η < sampleLaw P Q n m {ω | r <
        StatFormal.Distances.tvDist P Q - R.alphaLo (rootGrid (min n m)) δ ω.1 ω.2} := by
    intro r hr
    refine hηlt.trans_le (hlow'.trans (measure_mono fun ω hω => ?_))
    simp only [mem_ofPred_eq] at hω ⊢
    linarith
  refine ⟨hup, ⟨P, Q, hPQ, hpart2⟩, ?_⟩
  by_contra hcon
  have hCl : C / √((min n m : ℕ) : ℝ) < clo δ a₀ / √((min n m : ℕ) : ℝ) :=
    div_lt_div_of_pos_right (not_le.1 hcon) hsqrt
  exact absurd ((hpart2 _ hCl).trans_le (hup P Q hPQ)) (lt_irrefl _)

end StatFormal.Wave31tr.RouteFW
