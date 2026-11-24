import StatFormal.Archive.Wave30ah.Statements
import StatFormal.Archive.Wave30v.RouteSup

/-!
# Route — wave 30ah: `lem:supdir` in its printed `ℓ^∞` form (untrusted)

Wave 30v `boundary_sup_hadamard` is the statement on `C(Θ)`. The printed lemma lets `h_k → h` in `ℓ^∞(Θ)`, with
`h_k` merely bounded: the sup functional is `1`-Lipschitz for the sup distance of bounded functions, so
`|Ψ(z₀ + t_k h_k) − Ψ(z₀ + t_k h)| ≤ t_k sup|h_k − h|`, and the quotient differs from the continuous-direction
quotient (constant sequence `h`) by at most `sup|h_k − h| → 0`.
-/

set_option linter.style.longLine false

noncomputable section
open Set Filter Topology

namespace StatFormal.Wave30ah

open StatFormal.Wave30v (supFun argmaxSet supDeriv argmaxSet_nonempty isCompact_argmaxSet exists_supDeriv
  le_supDeriv boundary_sup_hadamard)

lemma sSup_range_sub_le {Θ : Type*} [Nonempty Θ] {f g : Θ → ℝ} (hg : BddAbove (range g)) {c : ℝ}
    (h : ∀ θ, f θ ≤ g θ + c) : sSup (range f) ≤ sSup (range g) + c :=
  csSup_le (range_nonempty f) (by rintro _ ⟨θ, rfl⟩; exact (h θ).trans (by gcongr; exact le_csSup hg ⟨θ, rfl⟩))

lemma abs_sSup_range_sub_le {Θ : Type*} [Nonempty Θ] {f g : Θ → ℝ} (hf : BddAbove (range f))
    (hg : BddAbove (range g)) {c : ℝ} (h : ∀ θ, |f θ - g θ| ≤ c) : |sSup (range f) - sSup (range g)| ≤ c := by
  have h1 := sSup_range_sub_le (f := f) hg (c := c) fun θ => by linarith [(abs_le.1 (h θ)).2]
  have h2 := sSup_range_sub_le (f := g) hf (c := c) fun θ => by linarith [(abs_le.1 (h θ)).1]
  rw [abs_le]; constructor <;> linarith

theorem boundary_supdir : Claims.boundary_supdir := by
  intro Θ _ _ _ z0 h hk t hbd hunif ht ht0 Θ0
  have hΘ0 : Θ0 = argmaxSet z0 := rfl
  refine ⟨hΘ0 ▸ argmaxSet_nonempty z0, hΘ0 ▸ isCompact_argmaxSet z0, ?_, ?_⟩
  · obtain ⟨θ, hθ, he⟩ := exists_supDeriv z0 h
    refine ⟨θ, hθ, ⟨⟨θ, hθ, rfl⟩, ?_⟩⟩
    rintro _ ⟨θ', hθ', rfl⟩
    rw [he]; exact le_supDeriv hθ'
  · -- the continuous-direction quotient
    have hc := boundary_sup_hadamard Θ z0 h t (fun _ => h) ht ht0 tendsto_const_nhds
    have hcoe : ∀ k, ⇑(z0 + t k • h) = fun θ => z0 θ + t k * h θ := fun k => by
      ext θ; simp
    have hA : Tendsto (fun k => (sSup (range fun θ => z0 θ + t k * h θ) - sSup (range z0)) / t k) atTop
        (𝓝 (supDeriv z0 h)) := by
      refine hc.congr fun k => ?_
      simp only [supFun, hcoe]
    -- the error
    have hbz : BddAbove (range z0) := (isCompact_range z0.continuous).bddAbove
    have hbh : BddAbove (range h) := (isCompact_range h.continuous).bddAbove
    have hbd1 : ∀ k, BddAbove (range fun θ => z0 θ + t k * hk k θ) := fun k => by
      obtain ⟨C, hC⟩ := hbd k
      obtain ⟨M, hM⟩ := hbz
      refine ⟨M + t k * C, ?_⟩
      rintro _ ⟨θ, rfl⟩
      have := hM ⟨θ, rfl⟩
      have := mul_le_mul_of_nonneg_left (abs_le.1 (hC θ)).2 (ht k).le
      linarith
    have hbd2 : ∀ k, BddAbove (range fun θ => z0 θ + t k * h θ) := fun k => by
      obtain ⟨M, hM⟩ := hbz
      obtain ⟨M', hM'⟩ := (isCompact_range h.continuous).bddAbove
      refine ⟨M + t k * M', ?_⟩
      rintro _ ⟨θ, rfl⟩
      have := hM ⟨θ, rfl⟩
      have := mul_le_mul_of_nonneg_left (hM' ⟨θ, rfl⟩) (ht k).le
      linarith
    have hD : Tendsto (fun k => (sSup (range fun θ => z0 θ + t k * hk k θ) - sSup (range fun θ => z0 θ + t k * h θ)) / t k)
        atTop (𝓝 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := eventually_atTop.1 ((Metric.tendstoUniformly_iff.1 hunif) (ε / 2) (by linarith))
      refine ⟨N, fun k hkN => ?_⟩
      have hle := abs_sSup_range_sub_le (hbd1 k) (hbd2 k) (c := t k * (ε / 2)) fun θ => by
        have h1 := (hN k hkN θ).le
        rw [Real.dist_eq, abs_sub_comm] at h1
        have : z0 θ + t k * hk k θ - (z0 θ + t k * h θ) = t k * (hk k θ - h θ) := by ring
        rw [this, abs_mul, abs_of_pos (ht k)]
        exact mul_le_mul_of_nonneg_left h1 (ht k).le
      rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (ht k), div_lt_iff₀ (ht k)]
      nlinarith [ht k]
    have := hA.add hD
    rw [add_zero] at this
    refine this.congr fun k => ?_
    field_simp
    ring

end StatFormal.Wave30ah
