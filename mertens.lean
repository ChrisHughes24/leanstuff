import data.nat.basic data.complex.basic data.rea l.cau_seq .exponential.series
local attribute [instance, priority 0] classical.prop_decidable
noncomputable theory
open nat is_absolute_value



lemma series_series_diag {α : Type*} [add_comm_monoid α] (f : ℕ → ℕ → α) (n : ℕ) : series (λ i, 
series (λ k, f k (i - k)) i) n = series (λ i, series (λ k, f i k) (n - i)) n := begin
  have : ∀ m : ℕ, m ≤ n → series (λ (i : ℕ), series (λ k, f k (i - k)) (min m i)) n =
      series (λ i, series (λ k, f i k) (n - i)) m,
    assume m mn, induction m with m' hi,
    simp[series_succ,series_zero,mul_add,max_eq_left (zero_le n)],
    simp only [series_succ _ m'],rw ←hi (le_of_succ_le mn),clear hi,
    induction n with n' hi,
    simp[series_succ],exact absurd mn dec_trivial,cases n' with n₂,
    simp [series_succ],rw [min_eq_left mn,series_succ,min_eq_left (le_of_succ_le mn)],
    rw eq_zero_of_le_zero (le_of_succ_le_succ mn),simp,
    cases lt_or_eq_of_le mn,
    simp [series_succ _ (succ n₂),min_eq_left mn,hi (le_of_lt_succ h)],rw [←add_assoc,←add_assoc],
    suffices : series (f (succ m')) (n₂ - m') + series (λ (k : ℕ), f k (succ (succ n₂) - k)) (succ m')
    = series (f (succ m')) (succ n₂ - m') +
        series (λ (k : ℕ), f k (succ (succ n₂) - k)) (min m' (succ (succ n₂))),
      rw this,rw[min_eq_left (le_of_succ_le mn),series_succ,succ_sub_succ,succ_sub (le_of_succ_le_succ (le_of_lt_succ h)),series_succ],
      rw [add_comm (series (λ (k : ℕ), f k (succ (succ n₂) - k)) m'),add_assoc],      
    rw ←h,simp[nat.sub_self],clear hi mn h,simp[series_succ,nat.sub_self],
    suffices : series (λ (i : ℕ), series (λ (k : ℕ), f k (i - k)) (min (succ m') i)) m' = series (λ (i : ℕ), series (λ (k : ℕ), f k (i - k)) (min m' i)) m',
      rw [this,min_eq_left (le_succ _)],clear n₂,
    have h₁ : ∀ i ≤ m', (λ (i : ℕ), series (λ (k : ℕ), f k (i - k)) (min (succ m') i)) i = (λ (i : ℕ), series (λ (k : ℕ), f k (i - k)) (min m' i)) i,
      assume i im,simp, rw [min_eq_right im,min_eq_right (le_succ_of_le im)],
    rw series_congr h₁,
  specialize this n (le_refl _),
  rw ←this,refine series_congr _,assume i ni,rw min_eq_right ni,
end

lemma series_merten {α β : Type*} [discrete_linear_ordered_field α] [ring β] {a b : ℕ → β}
{abv : β → α} [is_absolute_value abv] : is_cau_seq abs (series (λ n, abv (a n))) → is_cau_seq abv (series b) → 
∀ ε : α, 0 < ε → ∃ i : ℕ, ∀ j ≥ i, abv (series a j * series b j - series (λ n, 
series (λ m, a m * b (n - m)) n) j) < ε := begin
  assume ha hb ε ε0,
  cases seq_bounded_above_of_cau hb with Q hQ,
  cases seq_bounded_above_of_cau ha with P hP,
  have P0 : 0 < P,exact lt_of_le_of_lt (abs_nonneg _) (hP 0),
  have Pε0 := div_pos ε0 (mul_pos (show (2 : α) > 0, from by norm_num) P0),
  cases cau_seq.cauchy₂ ⟨_, hb⟩ Pε0 with N hN,simp at hN,
  have Qε0 := div_pos ε0 (mul_pos (show (4 : α) > 0, from by norm_num) (lt_of_le_of_lt (abv_nonneg _ _) (hQ 0))),
  cases cau_seq.cauchy₂ ⟨_, ha⟩ Qε0 with M hM,simp at hM,
  existsi 2 * (max N M + 1),
  assume K hK,have := diag_swap1 (λ m n, a m * b n) K,simp at this,rw this,clear this,
  have : (λ (i : ℕ), series (λ (k : ℕ), a i * b k) (K - i)) = (λ (i : ℕ), a i * series (λ (k : ℕ), b k) (K - i)),
    {apply funext,assume i,rw series_mul_left},
  rw this,clear this,simp,
  have : series (λ (i : ℕ), a i * series b (K - i)) K = series (λ (i : ℕ), a i * (series b (K - i) - series b K))
  K + series (λ i, a i * series b K) K,
    {rw ←series_add,simp[(mul_add _ _ _).symm]},
  rw this, clear this,
  rw series_mul_series,simp,
  rw abv_neg abv,
  refine lt_of_le_of_lt (abv_series_le_series_abv _) _,
  simp [abv_mul abv],
  suffices : series (λ (i : ℕ), abv (a i) * abv (series b (K - i) + -series b K)) (max N M + 1) + 
  (series (λ (i : ℕ), abv (a i) * abv (series b (K - i) + -series b K)) K -series (λ (i : ℕ), 
  abv (a i) * abv (series b (K - i) + -series b K)) (max N M + 1)) < ε / (2 * P) * P + ε / (4 * Q) * (2 * Q),
  { simp [(div_div_eq_div_mul _ _ _).symm] at this,
    rwa[div_mul_cancel _ (ne_of_lt P0).symm,(by norm_num : (4 : α) = 2 * 2),←div_div_eq_div_mul,mul_comm (2 : α),←mul_assoc,
    div_mul_cancel _ (ne_of_lt (lt_of_le_of_lt (abv_nonneg _ _) (hQ 0))).symm,div_mul_cancel,add_halves] at this,
    norm_num},
  refine add_lt_add _ _,
  {have : series (λ (i : ℕ), abv (a i) * abv (series b (K - i) + -series b K)) (max N M + 1) ≤ series
  (λ (i : ℕ), abv (a i) * (ε / (2 * P))) (max N M + 1),
    {refine series_le_series _,assume m mJ,refine mul_le_mul_of_nonneg_left _ _,
      {refine le_of_lt (hN (K - m) K _ _),{
      refine nat.le_sub_left_of_add_le (le_trans _ hK),
      rw[succ_mul,one_mul],
      exact add_le_add mJ (le_trans (le_max_left _ _) (le_of_lt (lt_add_one _)))},
      {refine le_trans _ hK,rw ←one_mul N,
      refine mul_le_mul (by norm_num) (by rw one_mul;exact le_trans (le_max_left _ _) 
      (le_of_lt (lt_add_one _))) (zero_le _) (zero_le _)}},
      exact abv_nonneg abv _},
  refine lt_of_le_of_lt this _,
  rw [series_mul_right,mul_comm],
  specialize hP (max N M + 1),rwa abs_of_nonneg at hP,
  refine (mul_lt_mul_left Pε0).mpr hP,
  refine series_nonneg _,assume x h,exact abv_nonneg abv _},
  {have hNMK : max N M + 1 < K,
    {refine lt_of_lt_of_le _ hK,
    rw [succ_mul,one_mul,←add_zero (max N M + 1)],
    refine add_lt_add_of_le_of_lt (le_refl _) _,rw add_zero,
    refine add_pos_of_nonneg_of_pos (zero_le _) (by norm_num)},
  rw series_sub_series _ hNMK,
  have : nat.sum (λ (i : ℕ), abv (a i) * abv (series b (K - i) + -series b K)) (max N M + 2) K 
  ≤ nat.sum (λ (i : ℕ), abv (a i) * (2 * Q)) (max N M + 2) K,
    {unfold nat.sum,refine series_le_series _,
    assume m hm,
    refine mul_le_mul_of_nonneg_left _ _,
    {refine le_trans (abv_add abv _ _) _,
    rw ←(by ring : Q + Q = 2 * Q),
    refine add_le_add (le_of_lt (hQ _)) _,
    rw abv_neg abv, exact le_of_lt (hQ _)},
    exact abv_nonneg abv _},
  refine lt_of_le_of_lt this _,
  rw [←series_sub_series _ hNMK,series_mul_right,series_mul_right,←sub_mul],
  refine (mul_lt_mul_right (mul_pos (by norm_num) (lt_of_le_of_lt (abv_nonneg abv _) (hQ 0)))).mpr _,
  refine lt_of_le_of_lt (le_abs_self _) _,
  refine hM _ _ _ (le_trans (le_max_right _ _) (le_of_lt (lt_add_one _))),
  refine le_trans _ hK,
  rw [succ_mul,one_mul,←add_zero M],
  exact add_le_add (le_trans (le_max_right _ _) (le_of_lt (lt_add_one _))) (zero_le _)},
end
#print series_merten