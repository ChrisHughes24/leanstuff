/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import algebra.big_operators data.real.cau_seq tactic.ring algebra.archimedean data.nat.choose analysis.limits .disjoint_finset

open nat is_absolute_value finset

variables {α : Type*} {β : Type*} (f g : ℕ → α) (n m : ℕ)

local infix `^` := monoid.pow


section sum_range
variable [add_comm_monoid α]

lemma sum_range_succ : (range (succ n)).sum f = f n + (range n).sum f :=
have h : n ∉ finset.range n := by rw finset.mem_range; exact lt_irrefl _,
by rw [finset.range_succ, finset.sum_insert h]

lemma sum_range_succ' : ∀ n : ℕ, f ∑ succ n = (λ m, f (succ m)) ∑ n + f 0
| 0        := by simp
| (succ n) := by rw [sum_range_succ (λ m, f (succ m)), add_assoc, ← sum_range_succ'];
                 exact sum_range_succ _ _


lemma sum_range_comm : f ∑ n = (λ m, f (n - (succ m))) ∑ n :=
begin
  induction n with n hi,
  { simp },
  { rw [sum_range_succ, sum_range_succ', hi, succ_sub_one, add_comm],
    simp [succ_sub_succ] }
end

lemma sum_range_diag_flip1 (f : ℕ → ℕ → α) : 
    (range n).sum (λ m, (range (m+1)).sum (λ k, f k (m - k))) = 
    (range n).sum (λ m, (range (n - m)).sum (f m)) :=
let f' : ℕ → ℕ → α := λ m k, if m + k < n then f m k else 0 in
calc (range n).sum (λ m, (range (m+1)).sum (λ k, f k (m - k))) = 
    (range n).sum (λ m, (range n).sum (λ k, f' k (m - k))) : 
    sum_congr rfl (λ x hx, begin end)
#print nat.lt_sub
lemma sum_range_diag_flip2 (f : ℕ → ℕ → α) : 
    (range n).sum (λ m, (range (m+1)).sum (λ k, f k (m - k))) = 
    (range n).sum (λ m, (range (n - m)).sum (f m)) :=
have h₁ : ((range n).sigma (range ∘ succ)).sum
    (λ (a : Σ m, ℕ), f (a.2) (a.1 - a.2)) = 
    (range n).sum (λ m, (range (m + 1)).sum
    (λ k, f k (m - k))) := sum_sigma,
have h₂ : ((range n).sigma (λ m, range (n - m))).sum (λ a : Σ (m : ℕ), ℕ, f (a.1) (a.2)) =
    (range n).sum (λ m, sum (range (n - m)) (f m)) := sum_sigma,
h₁ ▸ h₂ ▸ sum_bij 
    (λ a _, ⟨a.2, a.1 - a.2⟩) 
    (λ a ha, have h₁ : a.1 < n := mem_range.1 (mem_sigma.1 ha).1,
      have h₂ : a.2 < succ a.1 := mem_range.1 (mem_sigma.1 ha).2,
        mem_sigma.2 ⟨mem_range.2 (lt_of_lt_of_le h₂ h₁), 
        mem_range.2 ((nat.sub_lt_sub_right_iff (le_of_lt_succ h₂)).2 h₁)⟩) 
    (λ _ _, rfl) 
    (λ ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ha hb h,
      have ha : a₁ < n ∧ a₂ ≤ a₁ := 
          ⟨mem_range.1 (mem_sigma.1 ha).1, le_of_lt_succ (mem_range.1 (mem_sigma.1 ha).2)⟩,
      have hb : b₁ < n ∧ b₂ ≤ b₁ :=
          ⟨mem_range.1 (mem_sigma.1 hb).1, le_of_lt_succ (mem_range.1 (mem_sigma.1 hb).2)⟩,
      have h : a₂ = b₂ ∧ _ := sigma.mk.inj h,
      have h' : a₁ - a₂ = b₁ - b₂ := eq_of_heq h.2,
      sigma.mk.inj_iff.2 ⟨by rwa [nat.sub_eq_iff_eq_add ha.2, h.1, nat.sub_add_cancel hb.2] at h', 
        (heq_of_eq h.1)⟩)
    (λ ⟨a₁, a₂⟩ ha,
      have ha : a₁ < n ∧ a₂ < n - a₁ := 
          ⟨mem_range.1 (mem_sigma.1 ha).1, (mem_range.1 (mem_sigma.1 ha).2)⟩,
      ⟨⟨a₂ + a₁, a₁⟩, ⟨mem_sigma.2 ⟨mem_range.2 ((nat.lt_sub_right_iff_add_lt (le_of_lt ha.1)).1 ha.2),
        mem_range.2 (lt_succ_of_le (le_add_left _ _))⟩, 
      sigma.mk.inj_iff.2 ⟨rfl, heq_of_eq (nat.add_sub_cancel _ _).symm⟩⟩⟩)

lemma sum_range_diag_flip (f : ℕ → ℕ → α) : 
    (λ m, (λ k, f k (m - k)) ∑ (succ m)) ∑ n = (λ m, (λ k, f m k) ∑ (n - m)) ∑ n :=
begin
  suffices : ∀ j < n, (λ m, (λ k, f k (m - k)) ∑ succ (min j m)) ∑ n = (λ m, (λ k, f m k) ∑ (n - m)) ∑ succ j,
  { cases n with n,
    { simp },
    { rw ← this n (lt_succ_self _),
      apply finset.sum_congr rfl,
      assume m hm,
      rw finset.mem_range at hm,
      rw min_eq_right (le_of_lt_succ hm) } },
  assume j hj,
  induction j with j hi,
  { clear hj,
    induction n; simp * at * },
  { specialize hi (le_of_succ_le hj),
    rw [sum_range_succ _ (succ j), ← hi],
    clear hi,
    induction n with n hi,
    { exact absurd hj dec_trivial },
    { cases lt_or_eq_of_le (le_of_lt_succ hj) with hj' hj',
      { specialize hi hj',
        rw [sum_range_succ, sum_range_succ _ n, hi, min_eq_left (le_of_lt hj'), succ_sub (le_of_lt hj'),
            min_eq_left (le_of_lt (lt_of_succ_lt_succ hj)), sum_range_succ _ (_ - _), sum_range_succ _ (succ j)],
        simp },
      { rw [sum_range_succ, sum_range_succ _ n, ← hj', min_eq_left (le_refl _), min_eq_left (le_succ _), sum_range_succ _ (succ _), 
          succ_sub (le_refl _), nat.sub_self, sum_range_succ _ 0, finset.range_zero, finset.sum_empty, add_zero, ← add_assoc],
        refine congr_arg _ (finset.sum_congr rfl _),
        assume m hm,
        rw finset.mem_range at hm,
        rw [min_eq_right (le_of_lt hm), min_eq_right (le_of_lt_succ hm)] } } }
end

end sum_range

theorem binomial [comm_semiring α] (x y : α) : ∀ n : ℕ,
    (x + y)^n = (λ m, x^m * y^(n - m) * choose n m) ∑ succ n
| 0        := by simp
| (succ n) :=
begin
  rw [_root_.pow_succ, binomial, add_mul, finset.mul_sum, finset.mul_sum, sum_range_succ, sum_range_succ',
      sum_range_succ, sum_range_succ', add_assoc, ← add_assoc (_ ∑ n), ← finset.sum_add_distrib],
  have h₁ : x * (x^n * y^(n - n) * choose n n) = x^succ n * y^(succ n - succ n)
      * choose (succ n) (succ n) :=
    by simp [_root_.pow_succ, mul_assoc, mul_comm, mul_left_comm],
  have  h₂ : y * (x^0 * y^(n - 0) * choose n 0) = x^0 * y^(succ n - 0) * choose (succ n) 0 := 
    by simp [_root_.pow_succ, mul_assoc, mul_comm, mul_left_comm],
  have h₃ : (λ m, x * (x^m * y^(n - m) * choose n m) + y * (x^succ m * y^(n - succ m)
      * choose n (succ m))) ∑ n 
      = (λ m, x^succ m * y^(succ n - succ m) * ↑(choose (succ n) (succ m))) ∑ n := 
    finset.sum_congr rfl 
      begin 
        assume m hm,
        rw finset.mem_range at hm,
        rw [← mul_assoc y, ← mul_assoc y, mul_right_comm y, ← _root_.pow_succ, add_one, ← succ_sub hm],
        simp [succ_sub_succ, _root_.pow_succ, choose_succ_succ, mul_add, mul_comm, 
            mul_assoc, mul_left_comm]
      end,
  rw [h₁, h₂, h₃]
end

lemma zero_pow [semiring α] {n : ℕ} (hn : 0 < n) : (0 : α)^n = 0 :=
begin 
  induction n with n hi,
  { exact absurd hn dec_trivial },
  { cases n with n,
    { simp },
    { simp [hi dec_trivial, _root_.pow_succ _ (succ _), zero_mul] } }
end

lemma pow_abv (x : β) {n : ℕ} (hn : 1 ≤ n) (abv: β → α) [is_absolute_value abv] : abv (x^n) = (abv x)^n :=
begin 
  induction n with n hi,
  { exact absurd hn dec_trivial },
  { cases n with n,
    { simp },
    { simp [hi dec_trivial, _root_.pow_succ _ (succ _), abv_mul abv] } }
end


section geo_series
open cau_seq
variables [discrete_linear_ordered_field α] [ring β] {abv : β → α} [is_absolute_value abv]

private lemma lim_zero_pow_lt_one_aux [archimedean α] {x : β} (hx : abv x < 1) : ∀ ε > 0, ∃ i : ℕ, ∀ j ≥ i, abv (x^j) < ε :=
begin
  assume ε ε0,
  cases classical.em (x = 0),
  { existsi 1,
    assume j hj,
    simpa [h, _root_.zero_pow hj, abv_zero abv] },
  { have hx : (abv x)⁻¹ > 1 := one_lt_inv ((abv_pos abv).mpr h) hx,
    cases pow_unbounded_of_gt_one ε⁻¹ hx with i hi,
    have hax : 0 < abv x  := by rwa abv_pos abv,
    existsi max i 1,
    assume j hj,
    rw [pow_abv _ (le_trans (le_max_right _ _) hj), ← inv_lt_inv ε0 (pow_pos hax _),
        pow_inv _ _ (ne_of_lt hax).symm],
    exact lt_of_lt_of_le hi (pow_le_pow (le_of_lt hx) (le_trans (le_max_left _ _) hj)) }
end

lemma is_cau_pow_lt_one [archimedean α] {x : β} (hx : abv x < 1) : is_cau_seq abv (λ n, x^n) :=
of_near _ (const abv 0) $ by simp only [const_apply, sub_zero]; exact lim_zero_pow_lt_one_aux hx

lemma lim_zero_pow_lt_one [archimedean α] (x : β) (hx : abv x < 1) : lim_zero ⟨λ n, x^n, is_cau_pow_lt_one _ hx⟩ :=
lim_zero_pow_lt_one_aux abv hx


lemma sum_geo {x : β} (hx : x ≠ 1) : ∀ n, (λ m, x^m) ∑ n * (1 - x) = 1 - x^n
| 0       := by simp
| (n + 1) := by rw [sum_range_succ, add_mul, sum_geo]; simp [mul_add, _root_.pow_succ']

lemma is_cau_abv_geo_series [archimedean α] {x : β} (hx : abv x < 1) : is_cau_seq abs (λ n, (λ m, (abv x)^m) ∑ n) :=
begin
  have haa : abs (abv x) < 1 := by rwa abs_of_nonneg (abv_nonneg abv _),
  have hax1 : ¬ 1 - abv x = 0 := by rw [sub_eq_zero_iff_eq]; exact (ne_of_lt hx).symm,
  have hax1' : ¬ abv x = 1 := by rwa [eq_comm, ← sub_eq_zero_iff_eq],
  let s : cau_seq α abs := (cau_seq.const abs 1 - ⟨_, is_cau_pow_lt_one abs haa⟩) *
      cau_seq.inv (cau_seq.const abs (1 - abv x)) (by rwa const_lim_zero),
  refine (cau_seq.of_eq s _ _).2,
  assume n,
  simp [s],
  rw [← div_eq_mul_inv, div_eq_iff_mul_eq],
  exact sum_geo hax1' _, assumption,
end


end geo_series
-- -- proof that two different ways of representing a sum across a 2D plane are equal, used
-- -- in proof of exp (x + y) = exp x * exp y
-- lemma series_series_diag_flip [add_comm_monoid α] (f : ℕ → ℕ → α) (n : ℕ) : series (λ i, 
-- series (λ k, f k (i - k)) i) n = series (λ i, series (λ k, f i k) (n - i)) n := begin
--   have : ∀ m : ℕ, m ≤ n → series (λ (i : ℕ), series (λ k, f k (i - k)) (min m i)) n =
--   series (λ i, series (λ k, f i k) (n - i)) m := by
--   { assume m mn, induction m with m' hi,
--     simp[series_succ,series_zero,mul_add,max_eq_left (zero_le n)],
--     simp only [series_succ _ m'],rw ←hi (le_of_succ_le mn),clear hi,
--     induction n with n' hi,
--     simp[series_succ],exact absurd mn dec_trivial,cases n' with n₂,
--     simp [series_succ],rw [min_eq_left mn,series_succ,min_eq_left (le_of_succ_le mn)],
--     rw eq_zero_of_le_zero (le_of_succ_le_succ mn),simp,
--     cases lt_or_eq_of_le mn,
--     simp [series_succ _ (succ n₂),min_eq_left mn,hi (le_of_lt_succ h)],rw [←add_assoc,←add_assoc],
--     suffices : series (f (succ m')) (n₂ - m') + series (λ (k : ℕ), f k (succ (succ n₂) - k)) (succ m')
--     = series (f (succ m')) (succ n₂ - m') +
--         series (λ (k : ℕ), f k (succ (succ n₂) - k)) (min m' (succ (succ n₂))),
--       rw this,rw[min_eq_left (le_of_succ_le mn),series_succ,succ_sub_succ,succ_sub (le_of_succ_le_succ (le_of_lt_succ h)),series_succ],
--       rw [add_comm (series (λ (k : ℕ), f k (succ (succ n₂) - k)) m'),add_assoc],      
--     rw ←h,simp[nat.sub_self],clear hi mn h,simp[series_succ,nat.sub_self],
--     suffices : series (λ (i : ℕ), series (λ (k : ℕ), f k (i - k)) (min (succ m') i)) m' = series (λ (i : ℕ), series (λ (k : ℕ), f k (i - k)) (min m' i)) m',
--       rw [this,min_eq_left (le_succ _)],clear n₂,
--     have h₁ : ∀ i ≤ m', (λ (i : ℕ), series (λ (k : ℕ), f k (i - k)) (min (succ m') i)) i = (λ (i : ℕ), series (λ (k : ℕ), f k (i - k)) (min m' i)) i,
--       assume i im,simp, rw [min_eq_right im,min_eq_right (le_succ_of_le im)],
--     rw series_congr h₁},
--   specialize this n (le_refl _),
--   rw ←this,refine series_congr _,assume i ni,rw min_eq_right ni,
-- end

-- open monoid

-- theorem series_binomial {α : Type*} [comm_semiring α] (x y : α) (i : ℕ) : pow (x + y) i = 
-- series (λ j, choose i j * pow x j * pow y (i - j)) i := begin
--   induction i with i' hi,
--   simp!,unfold monoid.pow,rw hi,
--   rw [←series_mul_left],
--   have : ∀ j : ℕ, j ≤ i' → (λ (i : ℕ), (x + y) * (↑(choose i' i) * pow x i * pow y (i' - i))) j
--   = choose i' j * pow x (succ j) * pow y (i' - j) + choose i' j * pow x j * pow y (succ i' - j) := by
--   { assume j ji,dsimp only,rw add_mul,
--     have :  x * (↑(choose i' j) * pow x j * pow y (i' - j)) + y * (↑(choose i' j) * pow x j * pow y (i' - j))
--     = ↑(choose i' j) * (x * pow x j) * pow y (i' - j) + ↑(choose i' j) * pow x j * (y * pow y (i' - j)),
--       simp[mul_comm,_root_.mul_assoc,mul_left_comm],
--     rw [this,←_root_.pow_succ,←_root_.pow_succ,succ_sub ji]},
--   rw [series_congr this],clear this, 
--   clear hi,rw series_add,
--   have : series (λ (i : ℕ), ↑(choose i' i) * pow x i * pow y (succ i' - i)) i' = 
--       series (λ (i : ℕ), ↑(choose i' i) * pow x i * pow y (succ i' - i)) (succ i') := by
--   { simp[series_succ],},
--   rw [this,series_succ₁,series_succ₁],
--   simp[nat.sub_self],rw ←series_add,
--   refine congr_arg _ (series_congr _),
--   assume j ji,unfold choose,rw [nat.cast_add,add_mul,add_mul],
-- end

-- lemma geo_series_eq {α : Type*} [field α] (x : α) (n : ℕ) : x ≠ 1 → series (pow x) n = (1 - pow x (succ n)) / (1 - x) := begin
--   assume x1,have x1' : 1 + -x ≠ 0,assume h,rw [eq_comm, ←sub_eq_iff_eq_add] at h,simp at h,trivial,
--   induction n with n' hi,
--   {simp![div_self x1']},
--   {rw eq_div_iff_mul_eq,simpa,
--   rw [_root_.series_succ,_root_.pow_succ _ (succ n')],
--   rw hi,simp,rw [add_mul,div_mul_cancel _ x1',mul_add],ring,exact x1'},
-- end

-- lemma is_cau_geo_series {α : Type*} [discrete_linear_ordered_field α] [archimedean α] (x : α) : 
-- abs x < 1 → is_cau_seq abs (series (pow x)) := begin
--   assume x1, have : series (pow x) = λ n,(1 - pow x (succ n)) / (1 - x),
--     apply funext,assume n,refine geo_series_eq x n _ ,assume h, rw h at x1,exact absurd x1 (by norm_num),rw this,
--   have absx : 0 < abs (1 - x),refine abs_pos_of_ne_zero _,assume h,rw sub_eq_zero_iff_eq at h,rw ←h at x1,
--   have : ¬abs (1 : α) < 1,norm_num,trivial,simp at absx,
--   cases classical.em (x = 0),rw h,simp[monoid.pow],assume ε ε0,existsi 1,assume j j1,simpa!,
--   have x2: 1 < (abs x)⁻¹,rw lt_inv,simpa,{norm_num},exact abs_pos_of_ne_zero h,
--   have pos_x : 0 < abs x := abs_pos_of_ne_zero h,
--   assume ε ε0,
--   cases pow_unbounded_of_gt_one (2 / (ε * abs (1 - x))) x2 with i hi,
--   have ε2 : 0 < 2 / (ε * abs (1 - x)) := div_pos (by norm_num) (mul_pos ε0 absx),
--   rw [pow_inv,lt_inv ε2 (pow_pos pos_x _)] at hi,
--   existsi i,assume j ji,rw [inv_eq_one_div,div_div_eq_mul_div,_root_.one_mul,lt_div_iff (by norm_num : (0 : α) < 2)] at hi,
--   rw [div_sub_div_same,abs_div,div_lt_iff absx],
--   refine lt_of_le_of_lt _ hi,
--   simp,
--   refine le_trans (abs_add _ _) _,
--   have : pow (abs x) i * 2 = pow (abs x) i + pow (abs x) i,ring,
--   rw this,
--   refine add_le_add _ _,
--   {rw [←_root_.one_mul (pow (abs x) i),pow_abs,_root_.pow_succ,abs_mul],
--   exact mul_le_mul_of_nonneg_right (le_of_lt x1) (abs_nonneg _)},
--   {rw [abs_neg,←pow_abs],
--   rw [←inv_le_inv (pow_pos pos_x _) (pow_pos pos_x _),←pow_inv,←pow_inv],
--   refine pow_le_pow (le_of_lt x2) (le_succ_of_le ji),}
-- end

-- lemma is_cau_geo_series_const {α : Type*} [discrete_linear_ordered_field α] [archimedean α] (a x : α) :
-- abs x < 1 → is_cau_seq abs (series (λ n, a * pow x n)) := begin
--   assume x1 ε ε0,
--   cases classical.em (a = 0),
--   existsi 0,intros,rw [series_mul_left],induction j,simp!,assumption,rw h,simpa!,
--   cases is_cau_geo_series x x1 (ε / abs a) (div_pos ε0 (abs_pos_of_ne_zero h)) with i hi,
--   existsi i,assume j ji,rw [series_mul_left,series_mul_left,←mul_sub,abs_mul,mul_comm,←lt_div_iff],
--   exact hi j ji,exact abs_pos_of_ne_zero h,
-- end

-- lemma is_cau_series_of_abv_le_cau {α : Type*} {β : Type*} [discrete_linear_ordered_field α] [ring β] {f : ℕ → β}
-- {g : ℕ → α} {abv : β → α} [is_absolute_value abv] (n : ℕ) : (∀ m, n ≤ m → abv (f m) ≤ g m) → 
-- is_cau_seq abs (series g) → is_cau_seq abv (series f) := begin
--   assume hm hg ε ε0,cases hg (ε / 2) (div_pos ε0 (by norm_num)) with i hi,
--   existsi max n i,
--   assume j ji,
--   have hi₁ := hi j (le_trans (le_max_right n i) ji),
--   have hi₂ := hi (max n i) (le_max_right n i),
--   have sub_le := abs_sub_le (series g j) (series g i) (series g (max n i)),
--   have := add_lt_add hi₁ hi₂,rw abs_sub (series g (max n i)) at this,
--   have ε2 : ε / 2 + ε / 2 = ε,ring,
--   rw ε2 at this,
--   refine lt_of_le_of_lt _ this,
--   refine le_trans _ sub_le,
--   refine le_trans _ (le_abs_self _),
--   generalize hk : j - max n i = k,clear this ε2 hi₂ hi₁ hi ε0 ε hg sub_le,
--   rw nat.sub_eq_iff_eq_add ji at hk,rw hk, clear hk ji j,
--   induction k with k' hi,simp,rw abv_zero abv,
--   rw succ_add,unfold series,
--   rw [add_comm,add_sub_assoc],
--   refine le_trans (abv_add _ _ _) _,
--   rw [add_comm (series g (k' + max n i)),add_sub_assoc],
--   refine add_le_add _ _,
--   refine hm _ _,rw [←zero_add n,←succ_add],refine add_le_add _ _,exact zero_le _,
--   simp, exact le_max_left _ _,assumption,
-- end

-- -- The form of ratio test with  0 ≤ r < 1, and abv (f (succ m)) ≤ r * abv (f m) handled zero terms of series the best
-- lemma series_ratio_test {α : Type*} {β : Type*} [discrete_linear_ordered_field α] [ring β] 
-- [archimedean α] {abv : β → α} [is_absolute_value abv] {f : ℕ → β} (n : ℕ) (r : α) :
-- 0 ≤ r → r < 1 → (∀ m, n ≤ m → abv (f (succ m)) ≤ r * abv (f m)) → is_cau_seq abv (series f)
--   := begin
--   assume r0 r1 h,
--   refine is_cau_series_of_abv_le_cau (succ n) _ (is_cau_geo_series_const (abv (f (succ n)) * pow r⁻¹ (succ n)) r _),
--   assume m mn,
--   generalize hk : m - (succ n) = k,rw nat.sub_eq_iff_eq_add mn at hk,
--   cases classical.em (r = 0) with r_zero r_pos,have m_pos := lt_of_lt_of_le (succ_pos n) mn,
--   have := pred_le_pred mn,simp at this,
--   have := h (pred m) this,simp[r_zero,succ_pred_eq_of_pos m_pos] at this,
--   refine le_trans this _,refine mul_nonneg _ _,refine mul_nonneg (abv_nonneg _ _) (pow_nonneg (inv_nonneg.mpr r0) _),exact pow_nonneg r0 _,
--   replace r_pos : 0 < r,cases lt_or_eq_of_le r0 with h h,exact h,exact absurd h.symm r_pos,
--   revert m n,
--   induction k with k' hi,assume m n h mn hk,
--   rw [hk,zero_add,mul_right_comm,←pow_inv _ _ (ne_of_lt r_pos).symm,←div_eq_mul_inv,mul_div_cancel],
--   exact (ne_of_lt (pow_pos r_pos _)).symm,
--   assume m n h mn hk,rw [hk,succ_add],
--   have kn : k' + (succ n) ≥ (succ n), rw ←zero_add (succ n),refine add_le_add _ _,exact zero_le _,simp,
--   replace hi := hi (k' + (succ n)) n h kn rfl,
--   rw [(by simp!;ring : pow r (succ (k' + succ n)) = pow r (k' + succ n) * r),←_root_.mul_assoc],
--   replace h := h (k' + succ n) (le_of_succ_le kn),rw mul_comm at h,
--   exact le_trans h (mul_le_mul_of_nonneg_right hi r0),
--   rwa abs_of_nonneg r0,
-- end

-- lemma series_cau_of_abv_cau {α : Type*} {β : Type*} [discrete_linear_ordered_field α] [ring β] {abv : β → α} {f : ℕ → β} 
-- [is_absolute_value abv] : is_cau_seq abs (series (λ n, abv (f n))) → is_cau_seq abv (series f) := 
--    λ h, is_cau_series_of_abv_le_cau 0 (λ n h, le_refl _) h

-- -- I did not use the equivalent function on cauchy sequences as I do not have a proof 
-- -- series (λ n, series (λ m, a m * b (n - m)) n) j) is a cauchy sequence. Using this lemma
-- -- and of_near, this can be proven to be a cauchy sequence
-- lemma series_cauchy_prod {α β : Type*} [discrete_linear_ordered_field α] [ring β] {a b : ℕ → β}
-- {abv : β → α} [is_absolute_value abv] : is_cau_seq abs (series (λ n, abv (a n))) → is_cau_seq abv (series b) → 
-- ∀ ε : α, 0 < ε → ∃ i : ℕ, ∀ j ≥ i, abv (series a j * series b j - series (λ n, 
-- series (λ m, a m * b (n - m)) n) j) < ε := begin
-- -- slightly adapted version of theorem 9.4.7 from "The Real Numbers and Real Analysis", Ethan D. Bloch
--   assume ha hb ε ε0,
--   cases cau_seq.bounded ⟨_, hb⟩ with Q hQ,simp at hQ,
--   cases cau_seq.bounded ⟨_, ha⟩ with P hP,simp at hP,
--   have P0 : 0 < P,exact lt_of_le_of_lt (abs_nonneg _) (hP 0),
--   have Pε0 := div_pos ε0 (mul_pos (show (2 : α) > 0, from by norm_num) P0),
--   cases cau_seq.cauchy₂ ⟨_, hb⟩ Pε0 with N hN,simp at hN,
--   have Qε0 := div_pos ε0 (mul_pos (show (4 : α) > 0, from by norm_num) (lt_of_le_of_lt (abv_nonneg _ _) (hQ 0))),
--   cases cau_seq.cauchy₂ ⟨_, ha⟩ Qε0 with M hM,simp at hM,
--   existsi 2 * (max N M + 1),
--   assume K hK,have := series_series_diag_flip (λ m n, a m * b n) K,simp at this,rw this,clear this,
--   have : (λ (i : ℕ), series (λ (k : ℕ), a i * b k) (K - i)) = (λ (i : ℕ), a i * series (λ (k : ℕ), b k) (K - i)) := by
--     {apply funext,assume i,rw series_mul_left},
--   rw this,clear this,simp,
--   have : series (λ (i : ℕ), a i * series b (K - i)) K = series (λ (i : ℕ), a i * (series b (K - i) - series b K))
--   K + series (λ i, a i * series b K) K,
--     {rw ←series_add,simp[(mul_add _ _ _).symm]},
--   rw this, clear this,
--   rw series_mul_series,simp,
--   rw abv_neg abv,
--   refine lt_of_le_of_lt (abv_series_le_series_abv _) _,
--   simp [abv_mul abv],
--   suffices : series (λ (i : ℕ), abv (a i) * abv (series b (K - i) + -series b K)) (max N M + 1) + 
--   (series (λ (i : ℕ), abv (a i) * abv (series b (K - i) + -series b K)) K -series (λ (i : ℕ), 
--   abv (a i) * abv (series b (K - i) + -series b K)) (max N M + 1)) < ε / (2 * P) * P + ε / (4 * Q) * (2 * Q),
--   { simp [(div_div_eq_div_mul _ _ _).symm] at this,
--     rwa[div_mul_cancel _ (ne_of_lt P0).symm,(by norm_num : (4 : α) = 2 * 2),←div_div_eq_div_mul,mul_comm (2 : α),←_root_.mul_assoc,
--     div_mul_cancel _ (ne_of_lt (lt_of_le_of_lt (abv_nonneg _ _) (hQ 0))).symm,div_mul_cancel,add_halves] at this,
--     norm_num},
--   refine add_lt_add _ _,
--   {have : series (λ (i : ℕ), abv (a i) * abv (series b (K - i) + -series b K)) (max N M + 1) ≤ series
--   (λ (i : ℕ), abv (a i) * (ε / (2 * P))) (max N M + 1) := by
--     {refine series_le_series _,assume m mJ,refine mul_le_mul_of_nonneg_left _ _,
--       {refine le_of_lt (hN (K - m) K _ _),{
--       refine nat.le_sub_left_of_add_le (le_trans _ hK),
--       rw[succ_mul,_root_.one_mul],
--       exact add_le_add mJ (le_trans (le_max_left _ _) (le_of_lt (lt_add_one _)))},
--       {refine le_trans _ hK,rw ←_root_.one_mul N,
--       refine mul_le_mul (by norm_num) (by rw _root_.one_mul;exact le_trans (le_max_left _ _) 
--       (le_of_lt (lt_add_one _))) (zero_le _) (zero_le _)}},
--       exact abv_nonneg abv _},
--   refine lt_of_le_of_lt this _,
--   rw [series_mul_right,mul_comm],
--   specialize hP (max N M + 1),rwa abs_of_nonneg at hP,
--   exact (mul_lt_mul_left Pε0).mpr hP,
--   exact series_nonneg (λ x h, abv_nonneg abv _)},
--   {have hNMK : max N M + 1 < K := by
--     {refine lt_of_lt_of_le _ hK,
--     rw [succ_mul,_root_.one_mul,←add_zero (max N M + 1)],
--     refine add_lt_add_of_le_of_lt (le_refl _) _,rw add_zero,
--     refine add_pos_of_nonneg_of_pos (zero_le _) (by norm_num)},
--   rw series_sub_series _ hNMK,
--   have : series (λ (k : ℕ), abv (a (k + (max N M + 1 + 1))) * abv 
--   (series b (K - (k + (max N M + 1 + 1))) + -series b K)) (K - (max N M + 1 + 1)) ≤
--   series (λ (k : ℕ), abv (a (k + (max N M + 1 + 1))) * (2 * Q)) (K - (max N M + 1 + 1)) := by
--     {refine series_le_series _,
--     assume m hm,
--     refine mul_le_mul_of_nonneg_left _ _,
--     {refine le_trans (abv_add abv _ _) _,
--     rw (by ring : 2 * Q = Q + Q),
--     refine add_le_add (le_of_lt (hQ _)) _,
--     rw abv_neg abv, exact le_of_lt (hQ _)},
--     exact abv_nonneg abv _},
--   refine lt_of_le_of_lt this _,
--   rw [series_mul_right],
--   refine (mul_lt_mul_right (mul_pos (by norm_num) (lt_of_le_of_lt (abv_nonneg abv _) (hQ 0)))).mpr _,
--   refine lt_of_le_of_lt (le_abs_self _) _,
--   rw[←@series_sub_series _ _ (λ k, abv (a k)) (max N M + 1) K hNMK],
--   refine hM _ _ _ (le_trans (le_max_right _ _) (le_of_lt (lt_add_one _))),
--   refine le_trans _ hK,
--   rw [succ_mul,_root_.one_mul,←add_zero M],
--   exact add_le_add (le_trans (le_max_right _ _) (le_of_lt (lt_add_one _))) (zero_le _)},
-- end