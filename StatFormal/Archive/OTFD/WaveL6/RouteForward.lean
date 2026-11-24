import StatFormal.Archive.OTFD.WaveL6.RouteGlue
import StatFormal.Archive.OTFD.WaveL3.RouteHilbert
import StatFormal.Archive.OTFD.Wave22a.RouteConvex
import StatFormal.Lib.ConvexH.HilbertCube

/-!
# Route (wave L6): A `thm:sieve-convergence`, forward limits

Untrusted route file. `sieve_conv_weak` / `sieve_conv_norm`: the certified mean-square limit
`WaveL3.sieve_strong_limit_uncond` (with `IsCMMapAE` from the a.e. subgradient selections), turned by `sieve_core`
into convergence in `P`-measure of `ι_K F_{+,K} ∘ Π_K ∈ ∂ψ_K`, then `ConvexH.eventually_abs_inner_le`
(resp. `eventually_norm_le`). `sieve_conv_norm_cube`: (⋆) with `𝒞 = C_λ`, from the certified `sieve_subgrad_cube`,
`ghs_lip`, `ghs_lip_subgrad` and `ConvexH.isCompact_cube`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.OTFD.WaveL6

open StatFormal.OTFD.WaveL1 (Euc)
open StatFormal.OTFD.Wave1 (truncK)
open StatFormal.OTFD.Wave22a (IsSubgrad supAff cubeH)

theorem lip_max {E : Type*} [NormedAddCommGroup E] {f : E → ℝ} {L : ℝ}
    (hL : ∀ x x', |f x - f x'| ≤ L * ‖x - x'‖) (x x' : E) : |f x - f x'| ≤ max L 0 * ‖x - x'‖ :=
  (hL x x').trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

theorem sieve_conv_weak : Claims.sieve_conv_weak := by
  intro H _ _ _ _ _ _ e P μ ψ F M Lψ Lφ φ FK K₀ h he htot hLN hm1 hμM hψc hψL hFm hmap hFsub hlip hFK
    hpush hsub hK hKs hd ε hε
  have hL2 := WaveL3.sieve_strong_limit_uncond H e P μ F M FK he htot hLN hm1 hμM hFm hmap
    (isCMMapAE_of_ae_subgrad hFsub) hFK hpush (fun K => isCMMapAE_of_ae_subgrad (hsub K))
  obtain ⟨hM, hG, hconv⟩ := sieve_core he (P : Measure H) hlip hFK hFm hsub hL2
  exact ConvexH.eventually_abs_inner_le (P : Measure H) hM hG hFsub (lip_max hψL) (le_max_right _ _)
    hψc hconv hK hKs hd h hε

theorem sieve_conv_norm : Claims.sieve_conv_norm := by
  intro H _ _ _ _ _ _ e P μ ψ F M Lψ Lφ φ FK K₀ C he htot hLN hm1 hμM hψc hψL hFm hmap hFsub hlip hFK
    hpush hsub hK hKs hd hC hrange hFC ε hε
  have hL2 := WaveL3.sieve_strong_limit_uncond H e P μ F M FK he htot hLN hm1 hμM hFm hmap
    (isCMMapAE_of_ae_subgrad hFsub) hFK hpush (fun K => isCMMapAE_of_ae_subgrad (hsub K))
  obtain ⟨hM, hG, hconv⟩ := sieve_core he (P : Measure H) hlip hFK hFm hsub hL2
  exact ConvexH.eventually_norm_le (P : Measure H) hM hG hFsub (lip_max hψL) (le_max_right _ _)
    hψc hconv hK hKs hd hC (fun K x y hx hy => hrange K x hx y hy) hFC hε

section Cube
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem convex_cubeH (e : ℕ → H) (lam : ℕ → ℝ) : Convex ℝ (cubeH e lam) := by
  intro y hy z hz a b ha hb hab k
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  calc |a * ⟪y, e k⟫ + b * ⟪z, e k⟫| ≤ |a * ⟪y, e k⟫| + |b * ⟪z, e k⟫| := abs_add_le _ _
    _ = a * |⟪y, e k⟫| + b * |⟪z, e k⟫| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * lam k + b * lam k := add_le_add (mul_le_mul_of_nonneg_left (hy k) ha)
        (mul_le_mul_of_nonneg_left (hz k) hb)
    _ = lam k := by rw [← add_mul, hab, one_mul]

theorem norm_le_of_mem_cubeH [CompleteSpace H] {e : ℕ → H} (he : Orthonormal ℝ e)
    (htot : ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure) {lam : ℕ → ℝ}
    (hlam : Summable fun k => lam k ^ 2) {y : H} (hy : y ∈ cubeH e lam) :
    ‖y‖ ≤ Real.sqrt (∑' k, lam k ^ 2) := by
  have hs := ConvexH.hasSum_inner_sq he htot y
  have : ‖y‖ ^ 2 ≤ ∑' k, lam k ^ 2 := by
    rw [← hs.tsum_eq]
    refine Summable.tsum_le_tsum (fun k => ?_) hs.summable hlam
    have := hy k; rw [real_inner_comm] at this
    exact sq_le_sq' (abs_le.mp this).1 (abs_le.mp this).2
  exact Real.le_sqrt_of_sq_le this

theorem norm_le_of_box {K : ℕ} {lam : ℕ → ℝ} (hlam : Summable fun k => lam k ^ 2) {z : Euc K}
    (hz : ∀ k : Fin K, |z k| ≤ lam k) : ‖z‖ ≤ Real.sqrt (∑' k, lam k ^ 2) := by
  have h1 : ‖z‖ ^ 2 ≤ ∑' k, lam k ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ k : Fin K, ‖z k‖ ^ 2 ≤ ∑ k : Fin K, lam k ^ 2 := Finset.sum_le_sum fun k _ => by
          rw [Real.norm_eq_abs, sq_abs]; exact sq_le_sq' (abs_le.mp (hz k)).1 (abs_le.mp (hz k)).2
      _ = ∑ k ∈ Finset.range K, lam k ^ 2 := Fin.sum_univ_eq_sum_range (fun k => lam k ^ 2) K
      _ ≤ ∑' k, lam k ^ 2 := hlam.sum_le_tsum _ fun k _ => sq_nonneg _
  exact Real.le_sqrt_of_sq_le h1

end Cube

theorem sieve_conv_norm_cube : Claims.sieve_conv_norm_cube := by
  intro H _ _ _ _ _ _ e lam P μ S b x₀ F M SK bK zK FK K₀ he htot hlam0 hlam hLN hm1 hμM hS hScube hbdd
    hFm hmap hFsub hSK hbox hbddK hFK hpush hsub hK hKs hd ε hε
  set R := Real.sqrt (∑' k, lam k ^ 2)
  have hSR : ∀ y ∈ S, ‖y‖ ≤ R := fun y hy => norm_le_of_mem_cubeH he htot hlam (hScube hy)
  obtain ⟨hψc, hψL⟩ := Wave22a.ghs_lip H S b R x₀ hS hSR hbdd
  have hφL : ∀ K z z', |supAff (SK K) (bK K) z - supAff (SK K) (bK K) z'| ≤ R * ‖z - z'‖ :=
    fun K => (Wave22a.ghs_lip (Euc K) (SK K) (bK K) R (zK K) (hSK K)
      (fun z hz => norm_le_of_box hlam (hbox K z hz)) (hbddK K)).2
  have hcube : IsCompact (cubeH e lam) := ConvexH.isCompact_cube he htot hlam
  have hrange : ∀ K, ∀ x ∈ K₀, ∀ y, IsSubgrad (fun x' => supAff (SK K) (bK K) (truncK e K x')) x y →
      y ∈ cubeH e lam := fun K x _ y hy =>
    Wave22a.sieve_subgrad_cube H e lam K (SK K) (bK K) (zK K) he hlam0 (hSK K) (hbox K) (hbddK K) x y hy
  have hFC : ∀ x ∈ K₀, F x ∈ cubeH e lam := by
    intro x hx
    have hsg : IsSubgrad (supAff S b) x (F x) := ConvexH.subgrad_of_hasLineDerivAt hψc (hd x hx)
    have hcl := Wave22a.ghs_lip_subgrad H S b R x₀ hS hSR hbdd x (F x) hsg
    exact closure_minimal (convexHull_min hScube (convex_cubeH e lam)) hcube.isClosed hcl
  exact sieve_conv_norm H e P μ (supAff S b) F M R R (fun K => supAff (SK K) (bK K)) FK K₀ (cubeH e lam)
    he htot hLN hm1 hμM hψc hψL hFm hmap hFsub hφL hFK hpush hsub hK hKs hd hcube hrange hFC ε hε

end StatFormal.OTFD.WaveL6
