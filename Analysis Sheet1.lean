import algebra.field analysis.real tactic.norm_num tactic.ring
universe u
noncomputable theory
local attribute [instance, priority 0] classical.prop_decidable

theorem real_lt_swap : ∀ a b : ℝ, a > b ↔ b < a := λ a b, ⟨λ h,h,λ h,h⟩
theorem real_le_swap : ∀ a b : ℝ, a ≥ b ↔ b ≤ a := λ a b, ⟨λ h,h,λ h,h⟩ 
lemma q_1a (x y : ℝ) : abs (x + y) ≤ abs x + abs y := abs_add_le_abs_add_abs x y
lemma q_1b (x y : ℝ) : abs (x + y) ≥ abs x - abs y := by {have := abs_sub_abs_le_abs_sub x (-y), simp at *, assumption}
lemma q_1c (x y : ℝ) : abs (x + y) ≥ abs y - abs x := by rw add_comm;exact q_1b y x
lemma q_1d (x y : ℝ) : abs (x - y) ≥ abs (abs x - abs y) := abs_abs_sub_abs_le_abs_sub x y
lemma q_1e (x y : ℝ) : abs x ≤ abs y + abs (x - y) := by rw[add_comm, ←sub_right_le_iff_le_add];exact abs_sub_abs_le_abs_sub _ _
lemma q_1f (x y : ℝ) : abs x ≥ abs y - abs (x - y) := by rw[real_le_swap,sub_right_le_iff_le_add,abs_sub];exact q_1e y x
lemma q_1g (x y z : ℝ) : abs (x - y) ≤ abs (x - z) + abs (y - z) := have h : x - y = (x - z) + (z - y) := by ring, by rw [h,abs_sub y];exact q_1a _ _

lemma q_3 (S : set ℝ) (u : ℝ) : S ≠ ∅ → u ∈ upper_bounds S → (is_lub S u ↔ (∀ ε, ε > 0 → ∃ s : ℝ, s > u - ε ∧ s ∈ S)) := begin
  assume hS hu,split,
  assume hSu ε hε,
  simp [is_lub,is_least,upper_bounds,lower_bounds] at hSu,
  apply by_contradiction,rw not_exists,assume h,
  have : ∀ s : ℝ, s ∈ S → s ≤ u - ε,
    assume s hs, have := h s,rw not_and' at this,
    have := this hs, exact le_of_not_gt this,
  have := hSu.right (u - ε) this,
  have h := (@sub_lt_sub_iff_left _ _ u ε 0).mpr hε,rw sub_zero at h,
  exact not_le_of_gt h this,
  assume h,simp[is_lub,is_least,upper_bounds,lower_bounds],simp [upper_bounds] at hu,
  split,exact hu,assume x hx,cases set.exists_mem_of_ne_empty hS with s hs,
  refine by_contradiction _,
  assume hux,have hux₁ := lt_of_not_ge hux,
  cases h (u-x) (sub_pos.mpr hux₁) with y hy,
  have : u - (u - x) = x,ring,rw this at hy,
  exact not_lt_of_ge (hx y hy.right) hy.left,
end


lemma half_gt_zero : ((1 : ℝ) / (2 : ℝ)) > 0 := by norm_num
def is_convergent {α : Type u} [has_lt α] : (α → ℝ) → Prop := λ f, ∃ l : ℝ, ∀ ε : ℝ, ε > 0 → ∃ N : α, ∀ n : α, n > N → abs (f n) ≤ ε

lemma irrational : {r : ℝ // ∀ q : ℚ, ↑q ≠ r} := sorry

lemma q_2a : ¬∀ S : set ℝ, S ≠ ∅ → upper_bounds S ≠ ∅ → (∀ s∈S, ∃ q : ℚ, s = ↑q) → ∃ (sup : ℝ) (q : ℚ), is_lub S sup ∧ sup = ↑q := begin
 rw not_forall,
 existsi {x : ℝ | (∃ q : ℚ, x = ↑q) ∧ x < ↑irrational},
 assume h,
 have h₁ : {x : ℝ | (∃ q : ℚ, x = ↑q) ∧ x < ↑irrational} ≠ ∅,
  cases exists_rat_lt ↑irrational,
  have : ↑w ∈ {x : ℝ | (∃ q : ℚ, x = ↑q) ∧ x < ↑irrational},
   simp[h_1],existsi ((↑w):ℚ),simp,
  refine set.ne_empty_of_mem this,
 have h₂ : upper_bounds {x : ℝ |  (∃ q : ℚ, x = ↑q) ∧ x < ↑irrational} ≠ ∅,
  have : ↑irrational ∈ upper_bounds {x : ℝ | (∃ q : ℚ, x = ↑q) ∧ x < ↑irrational},
   simp[upper_bounds],assume a r h h₁, exact le_of_lt h₁,
  exact set.ne_empty_of_mem this,
 have h₃ : (∀ (s : ℝ), s ∈ {x : ℝ | (∃ q : ℚ, x = ↑q) ∧ x < ↑irrational} → (∃ (q : ℚ), s = ↑q)),
  simp,assume s q hsq hs,
  exact exists.intro q hsq,
 cases h h₁ h₂ h₃ with sup hsup,clear h₁ h₂ h₃ h,
 cases hsup with q hsup,
 simp [is_lub,upper_bounds,lower_bounds,is_least] at hsup,
 cases lt_trichotomy sup ↑irrational,
 cases exists_rat_btwn h with q' hq',
 exact not_lt_of_ge (hsup.left.left q' q' (by simp) hq'.right) hq'.left,
 cases h,rw hsup.right at h,cases irrational,simp at *,have := property q,trivial,
 cases exists_rat_btwn h with q' hq',
 have : (∀ (a_1 : ℝ) (x : ℚ), a_1 = ↑x → a_1 < ↑irrational → a_1 ≤ q'),
  assume x y h h₁, exact le_of_lt (lt_trans h₁ hq'.left),
 exact not_lt_of_ge (hsup.left.right q' this) hq'.right, 
end
lemma q_6 : ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n : ℕ, n > N → abs ((1 : ℝ) - n / (n + 2)) ≤ ε := begin
 assume ε hε,
 cases exists_lt_nat (2/ε) with N hN,
 existsi N,assume n hn,
 have h2n : (2 : ℝ) + n > 0,
  rw [(by norm_num : (2:ℝ) = ↑(2:ℕ)),←nat.cast_add,←nat.cast_zero],
  rw [real_lt_swap,nat.cast_lt,add_comm],exact dec_trivial,
 have h : (0:ℝ) ≤ 1 - (↑n / (↑n + 2)),
  suffices h : (↑n : ℝ) / (↑n + 2) + 0 ≤ 1,
   exact le_sub_left_iff_add_le.mpr h,
  simp,refine div_le_of_le_mul _ _,
  norm_num,exact h2n,
 simp at h,
 rw abs_of_nonneg h,
 suffices : ((1 : ℝ) + -(↑n / (2 + ↑n))) * (2 + ↑n) ≤ ε * (2 + ↑n),
  have : (((1:ℝ) + -(↑n / (2 + ↑n))) * (2 + ↑n)) / (2 + n) ≤ (ε * (2 + n)) / (2 + n),
   exact div_le_div_of_le_of_pos this h2n,
  rwa [mul_div_cancel _ (ne_of_lt h2n).symm,mul_div_cancel _ (ne_of_lt h2n).symm] at this,
 simp[add_mul],rw div_mul_cancel _ (ne_of_lt h2n).symm,simp,
 rw [←mul_lt_mul_left hε,mul_comm,div_mul_cancel _ (ne_of_lt hε).symm] at hN,
 rw mul_add,
 suffices : ε * ↑N < ε * 2 + ε * ↑n,
  exact le_of_lt (lt_trans hN this),
 suffices : ε * ↑N < ε * ↑n,rw add_comm,
  refine lt_add_of_lt_of_nonneg this _,
  exact mul_nonneg (le_of_lt hε) (by norm_num),
 have : (↑n:ℝ) > N,rwa [real_lt_swap,nat.cast_lt],
 exact (mul_lt_mul_left hε).mpr this,
end
example : ¬∃ z : ℤ, (1:ℚ)/2 = z := begin
 rw not_exists,assume x h,have: (1:ℚ) = 2 * ↑x,rw ←h,norm_num,
 have h: (2:ℚ) = (2:ℤ),norm_num,
 rw [h,←int.cast_one,←int.cast_mul,int.cast_inj] at this,
 have h₁:= dvd_mul_right 2 x,rw ←this at h₁,exact absurd h₁ dec_trivial,
end