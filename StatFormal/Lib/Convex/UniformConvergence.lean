import StatFormal.Lib.Convex.LocalLipschitz
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Pointwise convergence of convex functions is locally uniform

Library component (untrusted; no `Statements.lean` involved).

Rockafellar, *Convex Analysis*, Thm 10.8: if convex functions `Fₙ` converge pointwise to a finite
`f` on an open convex set `U` of a finite-dimensional space, the convergence is uniform on every
compact `K ⊆ U` (and the limit is convex).

## Proof outline

1. *Local equi-boundedness above.* Around `x ∈ U` take an affine basis whose convex hull lies in
   `U` and contains a ball `B(x, r)` (`exists_mem_interior_convexHull_affineBasis`). By the
   maximum principle `Fₙ ≤ maxᵢ Fₙ(bᵢ)` on the hull, and `Fₙ(bᵢ) → f(bᵢ)` at finitely many points,
   so eventually `Fₙ ≤ M` on `B(x, r)`.
2. *Local equi-Lipschitz.* `StatFormal.Convex.lipschitzOnWith_of_le_on_ball` gives, eventually, a
   common Lipschitz constant on `B(x, r/2)`; the pointwise limit `f` inherits it.
3. *Equi-Lipschitz + pointwise ⇒ uniform on compacts* (finite `δ`-net argument).
4. Locally uniform convergence on an open set is uniform convergence on compact subsets.

## Main results

* `StatFormal.Convex.tendstoUniformlyOn_of_lipschitzOnWith` — step 3 (any pseudometric space).
* `StatFormal.Convex.tendstoLocallyUniformlyOn_of_tendsto` — locally uniform convergence on `U`.
* `StatFormal.Convex.tendstoUniformlyOn_of_tendsto` — **Rockafellar Thm 10.8**: uniform
  convergence on every compact `K ⊆ U`.
-/

open Metric Set Filter
open scoped Topology NNReal

namespace StatFormal.Convex

section Metric

variable {ι X : Type*} [PseudoMetricSpace X] {l : Filter ι} {F : ι → X → ℝ} {f : X → ℝ}
  {S : Set X} {K : ℝ≥0}

/-- A pointwise limit of functions that are eventually `K`-Lipschitz on `S` is `K`-Lipschitz on
`S` (along a non-trivial filter). -/
theorem lipschitzOnWith_of_tendsto [l.NeBot] (hF : ∀ᶠ n in l, LipschitzOnWith K (F n) S)
    (hlim : ∀ x ∈ S, Tendsto (fun n => F n x) l (𝓝 (f x))) : LipschitzOnWith K f S :=
  LipschitzOnWith.of_dist_le_mul fun x hx y hy =>
    le_of_tendsto ((hlim x hx).dist (hlim y hy)) (hF.mono fun _ hn => hn.dist_le_mul x hx y hy)

/-- **Equi-Lipschitz functions converging pointwise on a compact set converge uniformly there.**
If, eventually along `l`, all `Fₙ` are `K`-Lipschitz on the compact set `S`, the limit `f` is
`K`-Lipschitz on `S`, and `Fₙ → f` pointwise on `S`, then `Fₙ → f` uniformly on `S`. -/
theorem tendstoUniformlyOn_of_lipschitzOnWith (hS : IsCompact S)
    (hF : ∀ᶠ n in l, LipschitzOnWith K (F n) S) (hf : LipschitzOnWith K f S)
    (hlim : ∀ x ∈ S, Tendsto (fun n => F n x) l (𝓝 (f x))) : TendstoUniformlyOn F f l S := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set δ : ℝ := ε / (3 * ((K : ℝ) + 1)) with hδdef
  have hK0 : (0 : ℝ) ≤ K := K.coe_nonneg
  have hδ : 0 < δ := by positivity
  obtain ⟨t, htS, htfin, hcov⟩ := finite_cover_balls_of_compact hS hδ
  have hev : ∀ᶠ n in l, ∀ c ∈ t, dist (f c) (F n c) < ε / 3 := by
    refine (Filter.eventually_all_finite htfin).2 fun c hc => ?_
    have := Metric.tendsto_nhds.1 (hlim c (htS hc)) (ε / 3) (by positivity)
    exact this.mono fun n hn => by rwa [dist_comm]
  filter_upwards [hF, hev] with n hn hn' x hx
  obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.1 (hcov hx)
  have hxc' : dist x c < δ := hxc
  have h1 : dist (f x) (f c) ≤ K * dist x c := hf.dist_le_mul x hx c (htS hc)
  have h2 : dist (F n c) (F n x) ≤ K * dist c x := hn.dist_le_mul c (htS hc) x hx
  have h3 := hn' c hc
  have hKδ : (K : ℝ) * δ ≤ ε / 3 := by
    rw [hδdef, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h4 : (K : ℝ) * dist x c ≤ ε / 3 :=
    (mul_le_mul_of_nonneg_left hxc'.le hK0).trans hKδ
  rw [dist_comm c x] at h2
  calc dist (f x) (F n x) ≤ dist (f x) (f c) + dist (f c) (F n c) + dist (F n c) (F n x) :=
        dist_triangle4 _ _ _ _
    _ < ε := by linarith

end Metric

section Convex

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {l : Filter ι} {F : ι → E → ℝ} {f : E → ℝ} {U : Set E}

/-- **Local equi-boundedness above.** If `Fₙ` are eventually convex on an open set `U` and converge
pointwise on `U`, then every `x ∈ U` has a ball `B(x, r) ⊆ U` on which, eventually, all `Fₙ` are
bounded above by one constant `M`. -/
theorem exists_eventually_le_on_ball (hU : IsOpen U) (hF : ∀ᶠ n in l, ConvexOn ℝ U (F n))
    (hlim : ∀ x ∈ U, Tendsto (fun n => F n x) l (𝓝 (f x))) {x : E} (hx : x ∈ U) :
    ∃ r > 0, ball x r ⊆ U ∧ ∃ M, ∀ᶠ n in l, ∀ y ∈ ball x r, F n y ≤ M := by
  obtain ⟨b, hxb, hbU⟩ := exists_mem_interior_convexHull_affineBasis (hU.mem_nhds hx)
  obtain ⟨r, hr, hrb⟩ := Metric.isOpen_iff.1 isOpen_interior x hxb
  have hballU : ball x r ⊆ U := hrb.trans (interior_subset.trans hbU)
  have hbiU : ∀ i, b i ∈ U := fun i => hbU (subset_convexHull ℝ _ (mem_range_self i))
  obtain ⟨M₀, hM₀⟩ := (Set.finite_range fun i => f (b i)).bddAbove
  refine ⟨r, hr, hballU, M₀ + 1, ?_⟩
  have hev : ∀ᶠ n in l, ∀ i, F n (b i) < f (b i) + 1 := by
    refine Filter.eventually_all.2 fun i => ?_
    exact (hlim _ (hbiU i)).eventually (gt_mem_nhds (lt_add_one _))
  filter_upwards [hF, hev] with n hn hn' y hy
  obtain ⟨z, ⟨i, rfl⟩, hz⟩ :=
    hn.exists_ge_of_mem_convexHull ((subset_convexHull ℝ _).trans hbU)
      (interior_subset (hrb hy))
  have := hM₀ (mem_range_self i)
  linarith [hn' i]

/-- **Local equi-Lipschitz property.** Under the hypotheses of
`exists_eventually_le_on_ball`, every `x ∈ U` has a closed ball `B̄(x, ρ) ⊆ U` and a constant `K`
such that eventually all `Fₙ`, and also the limit `f`, are `K`-Lipschitz on `B̄(x, ρ)`. -/
theorem exists_eventually_lipschitzOnWith (hU : IsOpen U) (hF : ∀ᶠ n in l, ConvexOn ℝ U (F n))
    (hlim : ∀ x ∈ U, Tendsto (fun n => F n x) l (𝓝 (f x))) [l.NeBot] {x : E} (hx : x ∈ U) :
    ∃ ρ > 0, closedBall x ρ ⊆ U ∧ ∃ K : ℝ≥0,
      (∀ᶠ n in l, LipschitzOnWith K (F n) (closedBall x ρ)) ∧
        LipschitzOnWith K f (closedBall x ρ) := by
  obtain ⟨r, hr, hrU, M, hM⟩ := exists_eventually_le_on_ball hU hF hlim hx
  have hsub : closedBall x (r / 4) ⊆ ball x (r - r / 2) :=
    closedBall_subset_ball (by linarith)
  set K : ℝ≥0 := (2 * (|M| + 2 * (|f x| + 1)) / (r / 2)).toNNReal
  have hevx : ∀ᶠ n in l, |F n x| ≤ |f x| + 1 := by
    have h := (hlim x hx).abs
    exact h.eventually (ge_mem_nhds (lt_add_one _)) |>.mono fun _ h => h
  have hFL : ∀ᶠ n in l, LipschitzOnWith K (F n) (closedBall x (r / 4)) := by
    filter_upwards [hF, hM, hevx] with n hn hn' hnx
    have h := lipschitzOnWith_of_le_on_ball (hn.subset hrU (convex_ball x r))
      (by positivity : 0 < r / 2) hn'
    refine (h.mono hsub).weaken ?_
    apply Real.toNNReal_le_toNNReal
    gcongr
  refine ⟨r / 4, by positivity, (closedBall_subset_ball (by linarith)).trans hrU, K, hFL, ?_⟩
  exact lipschitzOnWith_of_tendsto hFL fun y hy =>
    hlim y (hrU (closedBall_subset_ball (by linarith) hy))

/-- **Pointwise convergence of convex functions is locally uniform** (Rockafellar, *Convex
Analysis*, Thm 10.8). Let `E` be a finite-dimensional real normed space, `U ⊆ E` open, `Fₙ`
(eventually along a filter `l`) convex on `U`, and `Fₙ x → f x` for every `x ∈ U`, with
`f : E → ℝ` (so the limit is finite). Then `Fₙ → f` locally uniformly on `U`. -/
theorem tendstoLocallyUniformlyOn_of_tendsto (hU : IsOpen U)
    (hF : ∀ᶠ n in l, ConvexOn ℝ U (F n))
    (hlim : ∀ x ∈ U, Tendsto (fun n => F n x) l (𝓝 (f x))) :
    TendstoLocallyUniformlyOn F f l U := by
  rcases l.eq_or_neBot with rfl | hl
  · exact fun _ _ _ _ => ⟨U, self_mem_nhdsWithin, Filter.eventually_bot⟩
  refine ((tendstoLocallyUniformlyOn_TFAE F f l hU).out 1 3).2 fun x hx => ?_
  obtain ⟨ρ, hρ, hρU, K, hFK, hfK⟩ := exists_eventually_lipschitzOnWith hU hF hlim hx
  refine ⟨closedBall x ρ, mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x hρ), ?_⟩
  exact tendstoUniformlyOn_of_lipschitzOnWith (isCompact_closedBall x ρ) hFK hfK
    fun y hy => hlim y (hρU hy)

/-- **Rockafellar, *Convex Analysis*, Thm 10.8 (uniform convergence on compacts).** Let `E` be a
finite-dimensional real normed space (e.g. `EuclideanSpace ℝ (Fin d)`), `U ⊆ E` open, and let
`Fₙ` be (eventually along the filter `l`) convex on `U` with `Fₙ x → f x` for every `x ∈ U`, where
`f : E → ℝ` is finite-valued. Then `Fₙ → f` uniformly on every compact `K ⊆ U`. -/
theorem tendstoUniformlyOn_of_tendsto (hU : IsOpen U) (hF : ∀ᶠ n in l, ConvexOn ℝ U (F n))
    (hlim : ∀ x ∈ U, Tendsto (fun n => F n x) l (𝓝 (f x))) {K : Set E} (hKU : K ⊆ U)
    (hK : IsCompact K) : TendstoUniformlyOn F f l K :=
  (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1
    (tendstoLocallyUniformlyOn_of_tendsto hU hF hlim) K hKU hK

omit [FiniteDimensional ℝ E] in
/-- The pointwise limit of (eventually) convex functions on `U` is convex on `U`
(Rockafellar, *Convex Analysis*, Thm 10.8, last clause). Requires a non-trivial filter. -/
theorem convexOn_of_tendsto [l.NeBot] (hF : ∀ᶠ n in l, ConvexOn ℝ U (F n))
    (hlim : ∀ x ∈ U, Tendsto (fun n => F n x) l (𝓝 (f x))) : ConvexOn ℝ U f := by
  obtain ⟨n, hn⟩ := hF.exists
  refine ⟨hn.1, fun x hx y hy a b ha hb hab => ?_⟩
  have hxy := hn.1 hx hy ha hb hab
  refine le_of_tendsto_of_tendsto (hlim _ hxy)
    (((hlim x hx).const_smul a).add ((hlim y hy).const_smul b)) ?_
  exact hF.mono fun m hm => hm.2 hx hy ha hb hab

end Convex

end StatFormal.Convex
