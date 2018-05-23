import data.complex.basic data.real.cau_seq tactic.norm_num data.nat.basic tactic.ring algebra.archimedean
section a
open real nat is_absolute_value
noncomputable theory
local attribute [instance, priority 0] classical.prop_decidable

lemma pow_inv' {α : Type*} [discrete_field α] (a : α) (n : ℕ) : (monoid.pow a n)⁻¹ = monoid.pow a⁻¹ n := begin
  induction n with n' hi,
  simp!,
  simp!,rw [mul_inv',mul_comm,hi],
end

lemma pow_abs {α : Type*} [decidable_linear_ordered_comm_ring α] (a : α) (n : ℕ) : monoid.pow (abs a) n = abs (monoid.pow a n) := begin
  induction n with n' hi,
  simp!, simp!,rw [hi,abs_mul],
end

lemma pow_incrs_of_gt_one {α : Type*}  [linear_ordered_semiring α] {x : α} {n m : ℕ} : 1 < x → n < m → monoid.pow x n < monoid.pow x m := begin
  assume x1 nm,revert n,
  induction m with m' hi,assume n nm,
  exact absurd nm (not_lt_of_ge (zero_le n)),assume n nm,
  cases m' with m'',
  rw eq_zero_of_le_zero (le_of_lt_succ nm),simpa!,
  cases n with n',
  simp!, simp! at hi,
  rw ←one_mul (1 : α),
  exact mul_lt_mul x1 (le_of_lt (@hi 0 dec_trivial)) (by norm_num) (le_of_lt(lt_trans (by norm_num) x1)),
  have hi' := @hi n' (lt_of_succ_lt_succ nm),
  suffices : x * monoid.pow x n' < x * monoid.pow x (succ m''),
    simpa [monoid.pow],
  refine mul_lt_mul' (le_refl x) hi' _ (lt_trans (by norm_num) x1),
  clear hi hi' nm m'',
  induction n' with n'' hi,
  simp!,norm_num,
  simp!,exact mul_nonneg (le_of_lt (lt_trans (by norm_num) x1)) hi,
end

lemma pow_dcrs_of_lt_one_of_pos {α : Type*}  [discrete_linear_ordered_field α] {x : α} {n m : ℕ} : x < 1 → 0 < x → n < m → monoid.pow x m < monoid.pow x n := begin
  assume x1 x0 nm,rw [←inv_lt_inv,pow_inv',pow_inv'],
  have x11 : 1 < x⁻¹ ,rw lt_inv,simpa,{norm_num},exact x0,
  exact pow_incrs_of_gt_one x11 nm,
  exact pow_pos x0 _,exact pow_pos x0 _,
end

lemma pow_unbounded_of_gt_one {α : Type*} [discrete_linear_ordered_field α] [archimedean α] {x : α} (y : α) : 1 < x → ∃ n : ℕ, y < monoid.pow x n := begin
  assume x1,
  have : ∀ m : ℕ, (x - 1) * m < monoid.pow x m ∧ 1 ≤ monoid.pow x m,
    assume m, induction m with m' hi,
    simp,{norm_num},
    rw [←add_one,nat.cast_add,nat.cast_one], simp only [mul_add,monoid.pow],rw mul_one,
    have : x * monoid.pow x m' = monoid.pow x m' + (x - 1) * monoid.pow x m',
      rw add_comm,simp[mul_add,add_mul],
    rw this,split,
    refine add_lt_add_of_lt_of_le hi.left _,rw ←sub_pos at x1,
    have :=mul_le_mul (le_refl (x - 1)) hi.right (by norm_num) (le_of_lt x1),rwa mul_one at this,
    rw [←this, ←one_mul (1 : α)],
    exact mul_le_mul (le_of_lt x1) hi.right (by norm_num) (le_of_lt (lt_trans (by norm_num) x1)),
  cases exists_nat_gt (y / (x - 1)) with n hn,
  existsi n,rw [div_lt_iff,mul_comm] at hn,
  exact lt_trans hn (this n).left,rwa sub_pos,
end

-- defined myself rather than using finset.sum due to ease of inductive proofs. May have been better to define
-- using finset.sum and prove : series f (succ n) = series f n + f n
def series {α : Type*} [has_add α] [has_zero α] (f : ℕ → α) : ℕ → α 
| 0        := 0
| (succ n) := series n + f n

lemma series_mul {α : Type*} [semiring α] (f : ℕ → α) (a : α) (n : ℕ) : a * series f n = series (λ m, a * f m) n := begin
  induction n with n' hi,
  simp!,simp!,rw [mul_add,hi],
end
lemma series_add {α : Type*} [add_comm_monoid α] (f g : ℕ → α) (n : ℕ) : series f n + series g n = series (λ m, f m + g m) n := begin
  induction n with n' hi,simp!,simp![hi],
end

lemma series_neg {α : Type*} [ring α] (f : ℕ → α) (n : ℕ) : -series f n = series (λ m, -f m) n := begin
  induction n with n' hi, simp!,simp![hi],
end

lemma geo_series_eq {α : Type*} [field α] (x : α) (n : ℕ) : x ≠ 1 → series (monoid.pow x) n = (1 - monoid.pow x n) / (1 - x) := begin
  assume x1,have x1' : 1 + -x ≠ 0,assume h,rw [eq_comm, ←sub_eq_iff_eq_add] at h,simp at h,trivial,
  induction n with n' hi,
  simp!,rw eq_div_iff_mul_eq,simpa,
  simp!,rw hi,simp, rw [add_mul,div_mul_cancel _ x1',mul_add],ring,simp [x1'],
end

lemma geo_series_cau {α : Type*} [discrete_linear_ordered_field α] [archimedean α] (x : α) : abs x < 1 → is_cau_seq abs (series (monoid.pow x)) := begin
  assume x1, have : series (monoid.pow x) = λ n,(1 - monoid.pow x n) / (1 - x),
    apply funext,assume n,refine geo_series_eq x n _ ,assume h, rw h at x1,exact absurd x1 (by norm_num),rw this,
  have absx : 0 < abs (1 - x),refine abs_pos_of_ne_zero _,assume h,rw sub_eq_zero_iff_eq at h,rw ←h at x1,
  have : ¬abs (1 : α) < 1,norm_num,trivial,simp at absx,
  cases classical.em (x = 0),rw h,simp[monoid.pow],assume ε ε0,existsi 1,assume j j1,simpa!,
  cases j,exact absurd j1 dec_trivial,simpa!,
  have x2: 1 < (abs x)⁻¹,rw lt_inv,simpa,{norm_num},exact abs_pos_of_ne_zero h,
  assume ε ε0,cases pow_unbounded_of_gt_one (2 / (ε * abs (1 - x))) x2 with i hi,
  rw [←pow_inv',lt_inv] at hi,
  existsi i,assume j ji,rw [inv_eq_one_div,div_div_eq_mul_div,one_mul,lt_div_iff (by norm_num : (0 : α) < 2)] at hi,
  rw [div_sub_div_same,abs_div,div_lt_iff],
  refine lt_of_le_of_lt _ hi,
  simp,
  refine le_trans (abs_add _ _) _,
  have : monoid.pow (abs x) i * 2 = monoid.pow (abs x) i + monoid.pow (abs x) i,ring,
  rw this,
  refine add_le_add _ _,rw ←pow_abs,
  rw [abs_neg,←pow_abs],
  cases lt_or_eq_of_le ji,
  exact le_of_lt (pow_dcrs_of_lt_one_of_pos x1 (abs_pos_of_ne_zero h) h_1),
  rw h_1,assumption,
  refine div_pos _ _,{norm_num},
  refine mul_pos ε0 _,simpa,
  exact pow_pos (abs_pos_of_ne_zero h) _,
end

lemma geo_series_const_cau {α : Type*} [discrete_linear_ordered_field α] [archimedean α] (a x : α) : abs x < 1 → is_cau_seq abs (series (λ n, a * monoid.pow x n)) := begin
  assume x1 ε ε0,
  cases classical.em (a = 0),
  existsi 0,intros,rw [←series_mul],induction j,simp!,assumption,rw h,simpa!,
  cases geo_series_cau x x1 (ε / abs a) (div_pos ε0 (abs_pos_of_ne_zero h)) with i hi,
  existsi i,assume j ji,rw [←series_mul,←series_mul,←mul_sub,abs_mul,mul_comm,←lt_div_iff],exact hi j ji,exact abs_pos_of_ne_zero h,
end

lemma series_cau_of_abv_le_cau {α : Type*} {β : Type*} [discrete_linear_ordered_field α] [ring β] {f : ℕ → β}
    {g : ℕ → α} {abv : β → α} [is_absolute_value abv] (n : ℕ) : (∀ m, n ≤ m → abv (f m) ≤ g m) → 
    is_cau_seq abs (series g) → is_cau_seq abv (series f) := begin
  assume hm hg ε ε0,cases hg (ε / 2) (div_pos ε0 (by norm_num)) with i hi,
  existsi max n i,
  assume j ji,
  have hi₁ := hi j (le_trans (le_max_right n i) ji),
  have hi₂ := hi (max n i) (le_max_right n i),
  have sub_le := abs_sub_le (series g j) (series g i) (series g (max n i)),
  have := add_lt_add hi₁ hi₂,rw abs_sub (series g (max n i)) at this,
  have ε2 : ε / 2 + ε / 2 = ε,ring,
  rw ε2 at this,
  refine lt_of_le_of_lt _ this,
  refine le_trans _ sub_le,
  refine le_trans _ (le_abs_self _),
  generalize hk : j - max n i = k,clear this ε2 hi₂ hi₁ hi ε0 ε hg sub_le,
  rw nat.sub_eq_iff_eq_add ji at hk,rw hk, clear hk ji j,
  induction k with k' hi,simp,rw abv_zero abv,
  rw succ_add,unfold series,
  rw [add_comm,add_sub_assoc],
  refine le_trans (abv_add _ _ _) _,
  rw [add_comm (series g (k' + max n i)),add_sub_assoc],
  refine add_le_add _ _,
  refine hm _ _,rw ←zero_add n,refine add_le_add _ _,exact zero_le _,
  simp, exact le_max_left _ _,assumption,
end

-- The form of ratio test with  0 ≤ r < 1, and abv (f (succ m)) ≤ r * abv (f m) handled zero terms of series the best
lemma series_ratio_test {α : Type*} {β : Type*} [discrete_linear_ordered_field α]  [ring β] 
    [archimedean α] {abv : β → α} [is_absolute_value abv] {f : ℕ → β} (n : ℕ) (r : α) :
    0 ≤ r → r < 1 → (∀ m, n ≤ m → abv (f (succ m)) ≤ r * abv (f m)) → is_cau_seq abv (series f)
  := begin
  assume r0 r1 h,
  refine series_cau_of_abv_le_cau (succ n) _ (geo_series_const_cau (abv (f (succ n)) * monoid.pow r⁻¹ (succ n)) r _),
  assume m mn,
  generalize hk : m - (succ n) = k,rw nat.sub_eq_iff_eq_add mn at hk,
  cases classical.em (r = 0) with r_zero r_pos,have m_pos := lt_of_lt_of_le (succ_pos n) mn,
  have := pred_le_pred mn,simp at this,
  have := h (pred m) this,simp[r_zero,succ_pred_eq_of_pos m_pos] at this,
  refine le_trans this _,refine mul_nonneg _ _,refine mul_nonneg (abv_nonneg _ _) (pow_nonneg (inv_nonneg.mpr r0) _),exact pow_nonneg r0 _,
  replace r_pos : 0 < r,cases lt_or_eq_of_le r0 with h h,exact h,exact absurd h.symm r_pos,
  revert m n,
  induction k with k' hi,assume m n h mn hk,
  rw [hk,zero_add,mul_right_comm,←pow_inv',←div_eq_mul_inv,mul_div_cancel],
  exact (ne_of_lt (pow_pos r_pos _)).symm,
  assume m n h mn hk,rw [hk,succ_add],
  have kn : k' + (succ n) ≥ (succ n), rw ←zero_add (succ n),refine add_le_add _ _,exact zero_le _,simp,
  replace hi := hi (k' + (succ n)) n h kn rfl,
  rw [(by simp!;ring : monoid.pow r (succ (k' + succ n)) = monoid.pow r (k' + succ n) * r),←mul_assoc],
  replace h := h (k' + succ n) (le_of_succ_le kn),rw mul_comm at h,
  exact le_trans h (mul_le_mul_of_nonneg_right hi r0),
  rwa abs_of_nonneg r0,
end
lemma series_cau_of_abv_cau {α : Type*} {β : Type*} [discrete_linear_ordered_field α] [ring β] {abv : β → α} {f : ℕ → β} 
    [is_absolute_value abv] : is_cau_seq abs (series (λ n, abv (f n))) → is_cau_seq abv (series f) := 
   λ h, series_cau_of_abv_le_cau 0 (λ n h, le_refl _) h

lemma series_merten {α : Type*} {β : Type*} [discrete_linear_ordered_field α] [ring β] {a b : ℕ → β}
    {abv : β → α} [is_absolute_value abv] : is_cau_seq abv (series a) → is_cau_seq abs
    (series (λ n, abv (b n))) → ∀ ε > 0, ∃ i : ℕ, ∀ j ≥ i, abv (series a j * series b j -
    series (λ n, series(λ m, a m * b (n - m)) n) j) < ε := begin
  assume ε ε0,
  generalize hB : (λ k : ℕ, series b k) = B,
  generalize hA : (λ k : ℕ, series a k) = A,
  have : ∀ i : ℕ, series (λ n, series(λ m, a m * b (n - m)) n) i = series (λ n, a (i - n) * B i) i,
    assume i,
    induction i with i' hi,rw ←hB,simp!,
    unfold series,rw [hi,series_add],clear hi,
    induction i' with i₂,
    simp!,rw ←hB,simp!,




    
end
end a
open nat
lemma complex.exp_series_cau (z : ℂ) : is_cau_seq complex.abs (series (λ m, monoid.pow z m / fact m)) := begin
  cases exists_nat_gt (complex.abs z) with n hn,have n_pos : (0 : ℝ) < n := lt_of_le_of_lt (complex.abs_nonneg _) hn,
  refine series_ratio_test n (complex.abs z / n) _ _ _,exact div_nonneg_of_nonneg_of_pos (complex.abs_nonneg _) n_pos,rwa [div_lt_iff n_pos,one_mul],
  assume m mn,
  unfold monoid.pow fact,simp only [complex.abs_div,complex.abs_mul,div_eq_mul_inv,mul_inv',nat.cast_mul,complex.abs_inv],
  have : complex.abs z * complex.abs (monoid.pow z m) * ((complex.abs ↑(fact m))⁻¹ * (complex.abs ↑(succ m))⁻¹) = complex.abs z * complex.abs (monoid.pow z m) * (complex.abs ↑(fact m))⁻¹ * (complex.abs ↑(succ m))⁻¹,ring,rw this,
  have : complex.abs z * (↑n)⁻¹ * (complex.abs (monoid.pow z m) * (complex.abs ↑(fact m))⁻¹) = complex.abs z * complex.abs (monoid.pow z m) * (complex.abs ↑(fact m))⁻¹ * (↑n)⁻¹,ring,rw this,
  rw[(by simp : (succ m : ℂ) = ((succ m : ℝ) : ℂ)),complex.abs_of_nonneg],
  refine mul_le_mul_of_nonneg_left _ _,
  rw [inv_le_inv,nat.cast_le],exact le_succ_of_le mn,
  rw [←nat.cast_zero,nat.cast_lt],exact succ_pos _,exact n_pos,rw[←complex.abs_inv,←complex.abs_mul,←complex.abs_mul],
  exact complex.abs_nonneg _,rw[←nat.cast_zero,nat.cast_le],exact zero_le _,
end

def exp (z : ℂ) : ℂ := complex.lim (series (λ n, monoid.pow z n / fact n))

def sin (z : ℂ) : ℂ := (exp (⟨0, 1⟩ * z) - exp (-⟨0, 1⟩ * z)) / (2 * ⟨0, 1⟩)

def cos (z : ℂ) : ℂ := (exp (⟨0, 1⟩ * z) + exp (-⟨0, 1⟩ * z)) / 2

def tan (z : ℂ) : ℂ := sin z / cos z

def sinh (z : ℂ) : ℂ := (exp z - exp (-z)) / 2

def cosh (z : ℂ) : ℂ := (exp z + exp (-z)) / 2

def tanh (z : ℂ) : ℂ := sinh z / cosh z

lemma complex.re_const_equiv_of_const_equiv {f : ℕ → ℂ} (hf : is_cau_seq complex.abs f) (z : ℂ) :
    cau_seq.const complex.abs z ≈ ⟨f, hf⟩ → cau_seq.const _root_.abs z.re ≈  ⟨(λ (n : ℕ), (f n).re), 
    complex.is_cau_seq_re ⟨f,hf⟩⟩ := begin
  assume h,assume ε ε0,cases h ε ε0 with i hi,existsi i,assume j ji,
  replace hi := hi j ji, simp at *, rw [←complex.neg_re,←complex.add_re],
  exact lt_of_le_of_lt (complex.abs_re_le_abs _) hi,
end

lemma complex.im_const_equiv_of_const_equiv {f : ℕ → ℂ} (hf : is_cau_seq complex.abs f) (z : ℂ) :
    cau_seq.const complex.abs z ≈ ⟨f, hf⟩ → cau_seq.const _root_.abs z.im ≈  ⟨(λ (n : ℕ), (f n).im),
    complex.is_cau_seq_im ⟨f,hf⟩⟩ := begin
  assume h,assume ε ε0,cases h ε ε0 with i hi,existsi i,assume j ji,
  replace hi := hi j ji, simp at *, rw [←complex.neg_im,←complex.add_im],
  exact lt_of_le_of_lt (complex.abs_im_le_abs _) hi,
end

lemma complex.lim_const {f : ℕ → ℂ} (hf : is_cau_seq complex.abs f) (z : ℂ) : z = complex.lim f ↔ 
    cau_seq.const complex.abs z ≈ ⟨f, hf⟩ := begin
  split,have := complex.equiv_lim ⟨f, hf⟩,simp at this,
  assume h,rw h, exact setoid.symm this,assume h,
  unfold complex.lim,cases z with zre zim,simp,
  split, have := real.equiv_lim ⟨(λ (n : ℕ), (f n).re), complex.is_cau_seq_re ⟨f,hf⟩⟩,
  rw ←cau_seq.const_equiv,simp at this,
  have hf := complex.re_const_equiv_of_const_equiv hf {re := zre, im := zim} h,simp at hf,
  exact setoid.trans hf this,
  have := real.equiv_lim ⟨(λ (n : ℕ), (f n).im), complex.is_cau_seq_im ⟨f,hf⟩⟩,
  rw ←cau_seq.const_equiv,simp at this,
  have hf := complex.im_const_equiv_of_const_equiv hf {re := zre, im := zim} h,simp at hf,
  exact setoid.trans hf this,
end

lemma complex.lim_eq_lim_iff_equiv {f g : ℕ → ℂ} (hf : is_cau_seq complex.abs f) 
    (hg : is_cau_seq complex.abs g) : complex.lim f = complex.lim g ↔ @has_equiv.equiv 
    (cau_seq ℂ complex.abs) _ ⟨f, hf⟩ ⟨g, hg⟩ := begin
  have h₁:= complex.lim_const hg (complex.lim f),
  have h₂:= complex.lim_const hf (complex.lim g),
  split,assume h, simp * at *,
  exact setoid.trans (setoid.symm h₂) h₁,
  assume h,rw h₁,have := complex.equiv_lim ⟨f, hf⟩,simp at this,
  exact setoid.trans (setoid.symm this) h,
end

@[simp] lemma exp_zero : exp 0 = 1 := begin
  unfold exp,rw [eq_comm,complex.lim_const (complex.exp_series_cau 0)],
  assume ε ε0,existsi 1,assume j j1,
  induction j with j' hi,exact absurd j1 dec_trivial,
  cases j' with j₂,simpa!,replace hi := hi dec_trivial,simp! at *,assumption,
end

