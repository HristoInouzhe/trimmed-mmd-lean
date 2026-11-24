import StatFormal.Lib.Bootstrap.Basic
import StatFormal.Lib.TrimmedMean.Variance

/-!
# Bootstrap variance of an extreme trimmed mean: a deterministic bound (library)

For a sample `v : Fin n → ℝ` with `|v_i| ≤ B`, `α ∈ [0,1)`, `β = 1 − α`, `ĉ = quantLo n α v` the empirical
`β`-quantile and `L(w) = min_{capped} Σ w_i u_i` the lower extreme trimmed mean, the bootstrap replicate
`L* = L(v ∘ I)` decomposes (Rockafellar–Uryasev duality at the fixed point `ĉ`) as

  `β (L* − L̂) = D* − A*`,   `A* = (P* − P_n) g_ĉ`,  `g_c = (c − ·)_+`,  `0 ≤ D* ≤ 4B`,

and, by the deterministic asymptotic-linearity inequality `al_bound` applied to the resample with centre `ĉ`,
`D* ≤ d (|F*(ĉ) − F_n(ĉ)| + |G*(ĉ) − G_n(ĉ)|)` whenever `F*(ĉ + d) ≥ β ≥ G*(ĉ − d)`. The bootstrap second
moment (`bAvg_resample_sq`) gives `n E*[A*²] = varLo` exactly and `n E*[(F* − F_n)²] ≤ 1`; Hoeffding
(`hoeffding_resample`) bounds the bad event by `2 exp(−2nγ²)` once `F_n(ĉ + d) ≥ β + γ`, `G_n(ĉ − d) ≤ β − γ`.
Minkowski then gives (`boot_trim_bound`)

  `|√(n Var*(β L*)) − √varLo| ≤ √(4d² + 32 B² n exp(−2nγ²))`.
-/

set_option linter.style.longLine false

noncomputable section
open Finset Real

namespace StatFormal.Foundations.Bootstrap

open StatFormal.TrimmedMMD.BangBang StatFormal.Foundations.TrimmedMean

variable {n : ℕ}

/-- The lower extreme trimmed mean `min_{w ∈ capped n α} Σ w_i v_i`. -/
abbrev tLo (n : ℕ) (α : ℝ) (v : Fin n → ℝ) : ℝ := sInf ((fun w => ∑ i, w i * v i) '' capped n α)

lemma abs_tLo_le {α B : ℝ} (hn : 0 < n) (hα0 : 0 ≤ α) (hα1 : α < 1) {v : Fin n → ℝ} (hv : ∀ i, |v i| ≤ B) :
    |tLo n α v| ≤ B := by
  obtain ⟨⟨w, ⟨hb, hs⟩, hwv⟩, -⟩ := isLeast_trim hn hα0 hα1 v
  rw [tLo, trimLo_eq hn hα0 hα1, ← hwv]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |w i * v i| ≤ ∑ i, w i * B := sum_le_sum fun i _ => by
        rw [abs_mul, abs_of_nonneg (hb i).1]; exact mul_le_mul_of_nonneg_left (hv i) (hb i).1
    _ = B := by rw [← sum_mul, hs, one_mul]

lemma abs_quantLo_le {α B : ℝ} (hn : 0 < n) (hα0 : 0 ≤ α) (hα1 : α < 1) {v : Fin n → ℝ} (hv : ∀ i, |v i| ≤ B) :
    |quantLo n α v| ≤ B := by
  obtain ⟨-, -, j, hj⟩ := quantLo_spec hn hα0 hα1 v
  rw [hj]; exact hv j

lemma emean_bounds {B c : ℝ} (hn : 0 < n) {v : Fin n → ℝ} (hv : ∀ i, |v i| ≤ B) (hc : |c| ≤ B) :
    0 ≤ emean v c ∧ emean v c ≤ 2 * B := by
  unfold emean
  refine avg_bounds hn (fun i => le_max_right _ _) fun i => max_le ?_ (by linarith [(abs_nonneg c).trans hc])
  have := neg_abs_le (v i); have := hv i; have := le_abs_self c; linarith

section Fixed

variable {α B : ℝ} (v : Fin n → ℝ)

/-- The linear part `A*(I) = (P* − P_n) g_ĉ`. -/
def bootA (α : ℝ) (I : Fin n → Fin n) : ℝ := emean (v ∘ I) (quantLo n α v) - emean v (quantLo n α v)

/-- The remainder `D*(I) = β L(v ∘ I) − (β ĉ − P* g_ĉ)`. -/
def bootD (α : ℝ) (I : Fin n → Fin n) : ℝ :=
  (1 - α) * tLo n α (v ∘ I) - ((1 - α) * quantLo n α v - emean (v ∘ I) (quantLo n α v))

lemma boot_decomp (hn : 0 < n) (hα0 : 0 ≤ α) (hα1 : α < 1) (I : Fin n → Fin n) :
    (1 - α) * tLo n α (v ∘ I) = (bootD v α I - bootA v α I) + (1 - α) * tLo n α v := by
  have h := beta_trimDual hn hα1 v (quantLo n α v)
  have h2 : tLo n α v = trimDual n α v (quantLo n α v) := trimLo_eq hn hα0 hα1 v
  unfold bootD bootA
  rw [h2]
  linarith

lemma bootD_nonneg (hn : 0 < n) (hα0 : 0 ≤ α) (hα1 : α < 1) (I : Fin n → Fin n) : 0 ≤ bootD v α I := by
  have hβ : 0 < 1 - α := by linarith
  have := mul_le_mul_of_nonneg_left (trimDual_le_trimLo hn hα0 hα1 (v ∘ I) (quantLo n α v)) hβ.le
  rw [beta_trimDual hn hα1] at this
  unfold bootD
  linarith

lemma bootD_le (hn : 0 < n) (hα0 : 0 ≤ α) (hα1 : α < 1) (hv : ∀ i, |v i| ≤ B) (I : Fin n → Fin n) :
    bootD v α I ≤ 4 * B := by
  have hvI : ∀ i, |(v ∘ I) i| ≤ B := fun i => hv (I i)
  have h1 := abs_tLo_le hn hα0 hα1 hvI
  have h2 := abs_quantLo_le hn hα0 hα1 hv
  have h3 := (emean_bounds hn hvI h2).2
  have hB : 0 ≤ B := (abs_nonneg _).trans (hv ⟨0, hn⟩)
  have hβ0 : 0 ≤ 1 - α := by linarith
  have hβ1 : 1 - α ≤ 1 := by linarith
  unfold bootD
  have a1 : (1 - α) * tLo n α (v ∘ I) ≤ B := by
    have := le_abs_self (tLo n α (v ∘ I))
    nlinarith
  have a2 : -((1 - α) * quantLo n α v) ≤ B := by
    have := neg_abs_le (quantLo n α v)
    nlinarith
  linarith

lemma ecdf_quantLo_ge (hn : 0 < n) (hα0 : 0 ≤ α) (hα1 : α < 1) : 1 - α ≤ ecdf v (quantLo n α v) := by
  obtain ⟨s1, -, -⟩ := quantLo_spec hn hα0 hα1 v
  rw [card_filter_eq_ecdf _ _ hn] at s1
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  nlinarith

lemma ecdfLt_quantLo_lt (hn : 0 < n) (hα0 : 0 ≤ α) (hα1 : α < 1) : ecdfLt v (quantLo n α v) < 1 - α := by
  obtain ⟨-, s2, -⟩ := quantLo_spec hn hα0 hα1 v
  rw [card_filter_eq_ecdfLt _ _ hn] at s2
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  nlinarith

lemma bootD_le_event (hn : 0 < n) (hα0 : 0 ≤ α) (hα1 : α < 1) {d : ℝ} (hd : 0 ≤ d) (I : Fin n → Fin n)
    (hF : 1 - α ≤ ecdf (v ∘ I) (quantLo n α v + d)) (hG : ecdfLt (v ∘ I) (quantLo n α v - d) ≤ 1 - α) :
    bootD v α I ≤ d * (|ecdf (v ∘ I) (quantLo n α v) - ecdf v (quantLo n α v)| +
      |ecdfLt (v ∘ I) (quantLo n α v) - ecdfLt v (quantLo n α v)|) := by
  obtain ⟨-, b2⟩ := al_bound (q := quantLo n α v) hn hα0 hα1 hd (v ∘ I) hF hG
  have hF0 := ecdf_quantLo_ge v hn hα0 hα1
  have hG0 := ecdfLt_quantLo_lt v hn hα0 hα1
  have m1 : max (1 - α - ecdf (v ∘ I) (quantLo n α v)) 0 ≤
      |ecdf (v ∘ I) (quantLo n α v) - ecdf v (quantLo n α v)| := by
    refine max_le ?_ (abs_nonneg _)
    rw [abs_sub_comm]; exact (by linarith : 1 - α - ecdf (v ∘ I) (quantLo n α v) ≤ _).trans (le_abs_self _)
  have m2 : max (ecdfLt (v ∘ I) (quantLo n α v) - (1 - α)) 0 ≤
      |ecdfLt (v ∘ I) (quantLo n α v) - ecdfLt v (quantLo n α v)| := by
    refine max_le ?_ (abs_nonneg _)
    exact (by linarith : ecdfLt (v ∘ I) (quantLo n α v) - (1 - α) ≤ _).trans (le_abs_self _)
  unfold bootD
  exact b2.trans (mul_le_mul_of_nonneg_left (add_le_add m1 m2) hd)

/-- `n E*[(F*(x) − F_n(x))²] ≤ 1`. -/
lemma bAvg_ecdf_sq_le (hn : 0 < n) (x : ℝ) :
    bAvg (fun I : Fin n → Fin n => (ecdf (v ∘ I) x - ecdf v x) ^ 2) ≤ 1 / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := bAvg_resample_sq hn (fun j => if v j ≤ x then (1 : ℝ) else 0)
  have e : (fun I : Fin n → Fin n => (ecdf (v ∘ I) x - ecdf v x) ^ 2) =
      fun I => ((∑ i, (fun j => if v j ≤ x then (1 : ℝ) else 0) (I i)) / n -
        (∑ j, (fun j => if v j ≤ x then (1 : ℝ) else 0) j) / n) ^ 2 := rfl
  rw [e, h]
  refine div_le_div_of_nonneg_right ?_ hn'.le
  have : (∑ j, (if v j ≤ x then (1 : ℝ) else 0) ^ 2) / n ≤ 1 :=
    (avg_bounds hn (fun j => sq_nonneg _) fun j => by split_ifs <;> norm_num).2
  nlinarith [sq_nonneg ((∑ j, (if v j ≤ x then (1 : ℝ) else 0)) / n)]

lemma bAvg_ecdfLt_sq_le (hn : 0 < n) (x : ℝ) :
    bAvg (fun I : Fin n → Fin n => (ecdfLt (v ∘ I) x - ecdfLt v x) ^ 2) ≤ 1 / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := bAvg_resample_sq hn (fun j => if v j < x then (1 : ℝ) else 0)
  have e : (fun I : Fin n → Fin n => (ecdfLt (v ∘ I) x - ecdfLt v x) ^ 2) =
      fun I => ((∑ i, (fun j => if v j < x then (1 : ℝ) else 0) (I i)) / n -
        (∑ j, (fun j => if v j < x then (1 : ℝ) else 0) j) / n) ^ 2 := rfl
  rw [e, h]
  refine div_le_div_of_nonneg_right ?_ hn'.le
  have : (∑ j, (if v j < x then (1 : ℝ) else 0) ^ 2) / n ≤ 1 :=
    (avg_bounds hn (fun j => sq_nonneg _) fun j => by split_ifs <;> norm_num).2
  nlinarith [sq_nonneg ((∑ j, (if v j < x then (1 : ℝ) else 0)) / n)]

/-- Lower tail of the bootstrap cdf. -/
lemma bAvg_ecdf_lt_le (hn : 0 < n) {x β γ : ℝ} (hγ : 0 ≤ γ) (hF : β + γ ≤ ecdf v x) :
    bAvg (fun I : Fin n → Fin n => if ecdf (v ∘ I) x < β then (1 : ℝ) else 0) ≤ exp (-2 * n * γ ^ 2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set b : Fin n → ℝ := fun j => 1 - if v j ≤ x then (1 : ℝ) else 0
  have hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1 := fun j => by simp only [b]; split_ifs <;> norm_num
  refine (bAvg_mono fun I => ?_).trans (hoeffding_resample hn b hb hγ)
  have e1 : (∑ i, b (I i)) / n = 1 - ecdf (v ∘ I) x := by
    simp only [b, ecdf, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      Function.comp]
    field_simp
  have e2 : (∑ j, b j) / n = 1 - ecdf v x := by
    simp only [b, ecdf, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    field_simp
  rw [e1, e2]
  by_cases h1 : ecdf (v ∘ I) x < β
  · rw [if_pos h1, if_pos (by linarith)]
  · rw [if_neg h1]; split_ifs <;> norm_num

/-- Upper tail of the bootstrap strict cdf. -/
lemma bAvg_ecdfLt_gt_le (hn : 0 < n) {x β γ : ℝ} (hγ : 0 ≤ γ) (hG : ecdfLt v x ≤ β - γ) :
    bAvg (fun I : Fin n → Fin n => if β < ecdfLt (v ∘ I) x then (1 : ℝ) else 0) ≤ exp (-2 * n * γ ^ 2) := by
  set b : Fin n → ℝ := fun j => if v j < x then (1 : ℝ) else 0
  have hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1 := fun j => by simp only [b]; split_ifs <;> norm_num
  refine (bAvg_mono fun I => ?_).trans (hoeffding_resample hn b hb hγ)
  have e1 : (∑ i, b (I i)) / n = ecdfLt (v ∘ I) x := rfl
  have e2 : (∑ j, b j) / n = ecdfLt v x := rfl
  rw [e1, e2]
  by_cases h1 : β < ecdfLt (v ∘ I) x
  · rw [if_pos h1, if_pos (by linarith)]
  · rw [if_neg h1]; split_ifs <;> norm_num

/-- The bootstrap second moment of the remainder. -/
lemma bAvg_bootD_sq_le (hn : 0 < n) (hα0 : 0 ≤ α) (hα1 : α < 1) (hv : ∀ i, |v i| ≤ B) {d γ : ℝ} (hd : 0 ≤ d)
    (hγ : 0 ≤ γ) (hF : 1 - α + γ ≤ ecdf v (quantLo n α v + d)) (hG : ecdfLt v (quantLo n α v - d) ≤ 1 - α - γ) :
    bAvg (fun I => bootD v α I ^ 2) ≤ 4 * d ^ 2 / n + 32 * B ^ 2 * exp (-2 * n * γ ^ 2) := by
  set c := quantLo n α v
  set ΔF : (Fin n → Fin n) → ℝ := fun I => ecdf (v ∘ I) c - ecdf v c
  set ΔG : (Fin n → Fin n) → ℝ := fun I => ecdfLt (v ∘ I) c - ecdfLt v c
  set iF : (Fin n → Fin n) → ℝ := fun I => if ecdf (v ∘ I) (c + d) < 1 - α then (1 : ℝ) else 0
  set iG : (Fin n → Fin n) → ℝ := fun I => if 1 - α < ecdfLt (v ∘ I) (c - d) then (1 : ℝ) else 0
  have hB : 0 ≤ B := (abs_nonneg _).trans (hv ⟨0, hn⟩)
  have pw : ∀ I, bootD v α I ^ 2 ≤ 2 * d ^ 2 * (ΔF I ^ 2 + ΔG I ^ 2) + 16 * B ^ 2 * (iF I + iG I) := fun I => by
    have h0 := bootD_nonneg v hn hα0 hα1 I
    have h4 := bootD_le v hn hα0 hα1 hv I
    have hiF : 0 ≤ iF I := by simp only [iF]; split_ifs <;> norm_num
    have hiG : 0 ≤ iG I := by simp only [iG]; split_ifs <;> norm_num
    have hq : 0 ≤ 2 * d ^ 2 * (ΔF I ^ 2 + ΔG I ^ 2) := by positivity
    by_cases hgood : 1 - α ≤ ecdf (v ∘ I) (c + d) ∧ ecdfLt (v ∘ I) (c - d) ≤ 1 - α
    · have hD := bootD_le_event v hn hα0 hα1 hd I hgood.1 hgood.2
      have hsq : bootD v α I ^ 2 ≤ (d * (|ΔF I| + |ΔG I|)) ^ 2 := pow_le_pow_left₀ h0 hD 2
      have : (d * (|ΔF I| + |ΔG I|)) ^ 2 ≤ 2 * d ^ 2 * (ΔF I ^ 2 + ΔG I ^ 2) := by
        have k : (|ΔF I| + |ΔG I|) ^ 2 ≤ 2 * (ΔF I ^ 2 + ΔG I ^ 2) := by
          have := sq_abs (ΔF I); have := sq_abs (ΔG I)
          nlinarith [sq_nonneg (|ΔF I| - |ΔG I|)]
        calc (d * (|ΔF I| + |ΔG I|)) ^ 2 = d ^ 2 * (|ΔF I| + |ΔG I|) ^ 2 := by ring
          _ ≤ d ^ 2 * (2 * (ΔF I ^ 2 + ΔG I ^ 2)) := mul_le_mul_of_nonneg_left k (sq_nonneg d)
          _ = 2 * d ^ 2 * (ΔF I ^ 2 + ΔG I ^ 2) := by ring
      have : 0 ≤ 16 * B ^ 2 * (iF I + iG I) := by positivity
      linarith
    · have hone : 1 ≤ iF I + iG I := by
        rw [not_and_or, not_le, not_le] at hgood
        rcases hgood with h | h
        · have : iF I = 1 := by simp only [iF]; rw [if_pos h]
          linarith
        · have : iG I = 1 := by simp only [iG]; rw [if_pos h]
          linarith
      have : bootD v α I ^ 2 ≤ 16 * B ^ 2 := by nlinarith
      nlinarith
  have hFF := bAvg_ecdf_sq_le v hn c
  have hGG := bAvg_ecdfLt_sq_le v hn c
  have hiFb := bAvg_ecdf_lt_le v hn (x := c + d) (β := 1 - α) hγ hF
  have hiGb := bAvg_ecdfLt_gt_le v hn (x := c - d) (β := 1 - α) hγ (by linarith)
  calc bAvg (fun I => bootD v α I ^ 2)
      ≤ bAvg (fun I => 2 * d ^ 2 * (ΔF I ^ 2 + ΔG I ^ 2) + 16 * B ^ 2 * (iF I + iG I)) := bAvg_mono pw
    _ = 2 * d ^ 2 * (bAvg (fun I => ΔF I ^ 2) + bAvg (fun I => ΔG I ^ 2)) +
          16 * B ^ 2 * (bAvg iF + bAvg iG) := by
        rw [bAvg_add, bAvg_const_mul, bAvg_const_mul, bAvg_add, bAvg_add]
    _ ≤ 2 * d ^ 2 * (1 / n + 1 / n) + 16 * B ^ 2 * (exp (-2 * n * γ ^ 2) + exp (-2 * n * γ ^ 2)) := by
        gcongr
    _ = 4 * d ^ 2 / n + 32 * B ^ 2 * exp (-2 * n * γ ^ 2) := by ring

/-- `n Var*(A*) = varLo`. -/
lemma bVar_bootA (hn : 0 < n) : (n : ℝ) * bVar (fun I => bootA v α I) = varLo n α v := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set a : Fin n → ℝ := fun j => max (quantLo n α v - v j) 0
  have eA : (fun I : Fin n → Fin n => bootA v α I) = fun I => (∑ i, a (I i)) / n - (∑ j, a j) / n := rfl
  have hm : bAvg (fun I => bootA v α I) = 0 := by rw [eA]; exact bAvg_resample_mean hn a
  unfold bVar
  rw [hm]
  simp only [sub_zero]
  have eA2 : (fun I : Fin n → Fin n => bootA v α I ^ 2) =
      fun I => ((∑ i, a (I i)) / n - (∑ j, a j) / n) ^ 2 := rfl
  rw [eA2, bAvg_resample_sq hn a]
  unfold varLo
  field_simp
  rfl

/-- **Deterministic bootstrap bound** for the lower trimmed mean. -/
theorem boot_trim_bound (hn : 0 < n) (hα0 : 0 ≤ α) (hα1 : α < 1) (hv : ∀ i, |v i| ≤ B) {d γ : ℝ} (hd : 0 ≤ d)
    (hγ : 0 ≤ γ) (hF : 1 - α + γ ≤ ecdf v (quantLo n α v + d)) (hG : ecdfLt v (quantLo n α v - d) ≤ 1 - α - γ) :
    |√((n : ℝ) * bVar (fun I : Fin n → Fin n => (1 - α) * tLo n α (v ∘ I))) - √(varLo n α v)| ≤
      √(4 * d ^ 2 + 32 * B ^ 2 * n * exp (-2 * n * γ ^ 2)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have : Nonempty (Fin n → Fin n) := ⟨fun i => i⟩
  have e1 : bVar (fun I : Fin n → Fin n => (1 - α) * tLo n α (v ∘ I)) =
      bVar (fun I => bootD v α I + -bootA v α I) := by
    have : (fun I : Fin n → Fin n => (1 - α) * tLo n α (v ∘ I)) =
        fun I => (bootD v α I + -bootA v α I) + (1 - α) * tLo n α v := funext fun I => by
      rw [boot_decomp v hn hα0 hα1 I]; ring
    rw [this, bVar_add_const]
  have hmk := abs_sqrt_bVar_add_sub_le (fun I => bootD v α I) (fun I => -bootA v α I)
  rw [bVar_neg] at hmk
  have hA : √((n : ℝ) * bVar (fun I => bootA v α I)) = √(varLo n α v) := by rw [bVar_bootA v hn]
  rw [e1, ← hA, Real.sqrt_mul hn'.le, Real.sqrt_mul hn'.le, ← mul_sub, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc √(n : ℝ) * |√(bVar fun I => bootD v α I + -bootA v α I) - √(bVar fun I => bootA v α I)|
      ≤ √(n : ℝ) * √(bVar fun I => bootD v α I) := mul_le_mul_of_nonneg_left hmk (Real.sqrt_nonneg _)
    _ = √((n : ℝ) * bVar fun I => bootD v α I) := (Real.sqrt_mul hn'.le _).symm
    _ ≤ √(4 * d ^ 2 + 32 * B ^ 2 * n * exp (-2 * n * γ ^ 2)) := by
        refine Real.sqrt_le_sqrt ?_
        have h1 := bVar_le_bAvg_sq (fun I => bootD v α I)
        have h2 := bAvg_bootD_sq_le v hn hα0 hα1 hv hd hγ hF hG
        calc (n : ℝ) * bVar (fun I => bootD v α I) ≤ n * (4 * d ^ 2 / n + 32 * B ^ 2 * exp (-2 * n * γ ^ 2)) :=
              mul_le_mul_of_nonneg_left (h1.trans h2) hn'.le
          _ = 4 * d ^ 2 + 32 * B ^ 2 * n * exp (-2 * n * γ ^ 2) := by field_simp

end Fixed

end StatFormal.Foundations.Bootstrap
