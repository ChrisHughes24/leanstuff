import analysis.complex analysis.polynomial

open complex polynomial finset

-- inductive lep (p : polynomial ℂ) : polynomial ℂ → Prop
-- | C_mul   : ∀ {a}, a ≠ 0 → lep (C a * p)
-- | mul     : ∀ {q}, lep q → lep (q * X)
-- | add     : ∀ {q} {a}, lep q → q ≠ -C a → lep (q + C a)

-- inductive ltp (p : polynomial ℂ) : polynomial ℂ → Prop
-- | mul_X : p ≠ 0 → ltp (p * X)
-- | mul_C : ∀ {a q}, a ≠ 0 → ltp q → ltp (C a * q)
-- | add   : ∀ {q} {a}, ltp q → q.eval 0 ≠ a → ltp (q + C a)

-- inductive ltp' : polynomial ℂ → polynomial ℂ → Prop
-- | mul_X : ∀ {p}, p ≠ 0 → ltp' p (p * X)
-- | mul_C : ∀ {p q a}, a ≠ 0 → ltp' p q → ltp' p (C a * q)
-- | add   : ∀ {p q a}, ltp' p q → q.eval 0 ≠ a → ltp' p (q + C a)

-- lemma growth_lemma_chris1 {p q : polynomial ℂ} (hpq : ltp p q) :
--   ∃ r : ℝ, ∀ z : ℂ, r < z.abs →
--    abs (p.eval z) < abs (q.eval z) :=
-- ltp.rec_on hpq
--   (λ hq g hpq, ⟨1, λ z hz, by rw [eval_mul, eval_X, complex.abs_mul];
--     exact _⟩)
--   _
--   (λ q a hqp hpa ih p, _)

-- lemma growth_lemma_chris1 {p q : polynomial ℂ} (hpq : ltp' q p) :
--   ∃ r : ℝ, ∀ z : ℂ, r < z.abs → abs (q.eval z) < abs (p.eval z) :=
-- ltp'.rec_on hpq
--   _
--   _
--   (λ p a hqp hpa _, _)

-- example : ∀ p : polynomial ℂ, ¬less_than p 0 :=
-- λ p h, less_than.rec_on h _ _ _

-- lemma polynomial_tendsto_infinity : ∀ {p : polynomial ℂ}, 0 < degree p →
--   ∀ x : ℝ, ∃ r : ℝ, ∀ z : ℂ, r < z.abs → x < (p.eval z).abs
-- | p := λ hp x, if h : degree p = 1
-- then
--   let ⟨n, hn⟩ := archimedean.arch (1 : ℝ)
--     (show 0 < abs (leading_coeff p),
--       from abs_pos.2 (λ hp0, by simp * at *; contradiction)) in
--   ⟨↑n * abs (p.eval 0) + n * (_root_.abs x), λ z hz,
--     calc x ≤ _root_.abs x : le_abs_self _
--     ... < abs (p.eval z) : lt_of_mul_lt_mul_left
--       (calc (n : ℝ) * _root_.abs x < abs z - n * abs (eval 0 p) :
--           lt_sub_iff_add_lt'.2 hz
--         ... ≤ n * abs (leading_coeff p * z) - n * abs (p.eval 0) :
--           sub_le_sub_right (by rw [complex.abs_mul, ← mul_assoc];
--           exact le_mul_of_ge_one_left (complex.abs_nonneg _)
--             (by simpa [mul_comm, add_monoid.smul_eq_mul] using hn)) _
--         ... = ↑n * (abs (leading_coeff p * z) - abs (-eval 0 p)) : by simp [mul_add]
--         ... ≤ ↑n * (abs (leading_coeff p * z - -eval 0 p)) :
--           mul_le_mul_of_nonneg_left
--             (le_trans (le_abs_self _) (complex.abs_abs_sub_le_abs_sub _ _))
--             (nat.cast_nonneg n)
--         ... = ↑n * abs (p.eval z) :
--           by conv_rhs {rw degree_eq_one h}; simp [coeff_zero_eq_eval_zero])
--       (nat.cast_nonneg n)⟩
-- else
--   have wf : degree (p /ₘ X) < degree p,
--     from degree_div_by_monic_lt _ monic_X (λ hp0, by simp * at *)
--       (by rw degree_X; exact dec_trivial),
--   have hp : 1 < degree p, from match degree p, hp, h with
--     | none    := dec_trivial
--     | (some n) := λ h0 h1, lt_of_le_of_ne (with_bot.coe_le_coe.2 (with_bot.coe_lt_coe.1 h0)) (ne.symm h1)
--     end,
--   have hXp : degree X ≤ degree p, from le_of_lt (by rw @degree_X ℂ; exact hp),
--   let ⟨r, hr⟩ := @polynomial_tendsto_infinity (p /ₘ X)
--     (@lt_of_add_lt_add_left' _ _ (1 : with_bot ℕ) _ _
--       (calc (1 : with_bot ℕ) + 0 < degree p : hp
--         ... = 1 + degree (p /ₘ X) : by rw [← @degree_X ℂ, degree_add_div_by_monic monic_X hXp]))
--   (x + (p.eval 0).abs) in
--   ⟨max 1 (r + (p.eval 0).abs), λ z hz,
--     calc x < abs (eval z (p /ₘ X)) - abs (eval 0 p) :
--       lt_sub_iff_add_lt.2 (hr z (lt_of_le_of_lt (le_add_of_nonneg_right (complex.abs_nonneg _))
--         (lt_of_le_of_lt (le_max_right _ _) hz)))
--     ... ≤ abs z * abs (eval z (p /ₘ X)) - abs (eval 0 p) :
--       sub_le_sub_right (le_mul_of_ge_one_left (complex.abs_nonneg _) (le_trans (le_max_left _ _) (le_of_lt hz))) _
--     ... ≤ _root_.abs (abs (z * eval z (p /ₘ X)) - abs (-eval 0 p)) : by rw [complex.abs_neg, ← complex.abs_mul];
--       exact le_abs_self _
--     ... ≤ abs (z * eval z (p /ₘ X) - -eval 0 p) : abs_abs_sub_le_abs_sub _ _
--     ... = abs (eval z p) : by conv_rhs {rw ← mod_by_monic_add_div p monic_X};
--       simp [coeff_zero_eq_eval_zero, mod_by_monic_X]⟩
-- using_well_founded {dec_tac := tactic.assumption}

@[elab_as_eliminator] protected lemma induction_on {M : polynomial ℂ → Prop} (p : polynomial ℂ )
  (h_C : ∀a, M (C a))
  (h_add : ∀p q, M p → M q → M (p + q))
  (h_monomial : ∀(n : ℕ) (a : ℂ), M (C a * X^n) → M (C a * X^(n+1))) :
  M p :=
have ∀{n:ℕ} {a}, M (C a * X^n),
begin
  assume n a,
  induction n with n ih,
  { simp only [pow_zero, mul_one, h_C] },
  { exact h_monomial _ _ ih }
end,
finsupp.induction p
  (suffices M (C 0), by simpa only [C, single_zero],
    h_C 0)
  (assume n a p _ _ hp, suffices M (C a * X^n + p), by rwa [single_eq_C_mul_X],
    h_add _ _ this hp)

inductive nonconstant : polynomial ℂ → Prop
| X   : ∀ {a}, a ≠ 0 → nonconstant (C a * X)
| mul : ∀ {p}, nonconstant p → nonconstant (p * X)
| add : ∀ {p} (a), nonconstant p → nonconstant (p + C a)

lemma nonconstant_of_degree_pos : ∀ {p : polynomial ℂ},
  0 < degree p → nonconstant p
| p := λ h,
have wf : degree (p /ₘ X) < degree p,
  from degree_div_by_monic_lt _ monic_X
  (λ hp0, by simp [hp0, lt_irrefl, *] at *)
  (by rw degree_X; exact dec_trivial),
by rw [← mod_by_monic_add_div p monic_X,
  add_comm, mod_by_monic_X, mul_comm] at *;
exact nonconstant.add _
  (if hpX : 0 < degree (p /ₘ X)
    then nonconstant.mul (nonconstant_of_degree_pos hpX)
    else by rw [eq_C_of_degree_le_zero (not_lt.1 hpX)] at *;
      exact if hc : coeff (p /ₘ X) 0 = 0
        then by simpa [hc, not_lt_of_ge degree_C_le] using h
        else nonconstant.X hc)
using_well_founded {dec_tac := tactic.assumption}

lemma polynomial_tendsto_infinity' {p : polynomial ℂ} (h : 0 < degree p) :
  ∀ x : ℝ, ∃ r : ℝ, ∀ z : ℂ, r < z.abs → x < (p.eval z).abs :=
nonconstant.rec_on (nonconstant_of_degree_pos h)
  (λ a ha x, ⟨x / a.abs, λ z hz,
    by simpa [(div_lt_iff' (complex.abs_pos.2 ha)).symm]⟩)
  (λ p hp ih x, let ⟨r, hr⟩ := ih x in
    ⟨max r 1, λ z hz, by rw [eval_mul, eval_X, complex.abs_mul];
        exact lt_of_lt_of_le (hr z (lt_of_le_of_lt (le_max_left _ _) hz))
          (le_mul_of_ge_one_right (complex.abs_nonneg _)
            (le_trans (le_max_right _ _) (le_of_lt hz)))⟩)
  (λ p a hp ih x, let ⟨r, hr⟩ := ih (x + a.abs) in
    ⟨r, λ z hz, by rw [eval_add, eval_C, ← sub_neg_eq_add];
      exact lt_of_lt_of_le (lt_sub_iff_add_lt.2
        (by rw complex.abs_neg; exact (hr z hz)))
        (le_trans (le_abs_self _) (complex.abs_abs_sub_le_abs_sub _ _))⟩)

axiom attains_infi (p : polynomial ℂ) :
  ∃ x, (p.eval x).abs = ⨅ y, (p.eval y).abs

axiom nth_root (n : ℕ) (z : ℂ) : ℂ

axiom nth_root_pow {n : ℕ} (hn : 0 < n) (z : ℂ) : nth_root n z ^ n = z

open euclidean_domain
local attribute [instance] classical.prop_decidable
#print roption
lemma FTA {f : polynomial ℂ} (hf : 0 < degree f) : ∃ z : ℂ, is_root f z :=
let ⟨z₀, hz₀⟩ := attains_infi f in
let n := nat.find_greatest (λ n, (X - C z₀) ^ n ∣ ((X - C z₀) * (f / (X - C z₀))))
  (nat_degree ((X - C z₀) * (f / (X - C z₀)))) in
have hgr : ∃ n, n ≤ nat_degree ((X - C z₀) * (f / (X - C z₀))) ∧
    (X - C z₀) ^ n ∣ ((X - C z₀) * (f / (X - C z₀))),
  from ⟨0, nat.zero_le _, by simp⟩,
let ⟨g, hg⟩ := nat.find_greatest_spec hgr in
have hf : f = f % (X - C z₀) + (X - C z₀) ^ n * g,
  by rw [← hg, add_comm, div_add_mod],
have hgz₀ : g.eval z₀ ≠ 0,
  from mt dvd_iff_is_root.2 (λ ⟨i, hi⟩, begin
    rw [hi, ← mul_assoc, ← pow_succ'] at hg,
    exact nat.find_greatest_is_greatest hgr (n + 1)
      ⟨nat.lt_succ_self _,
        begin
          have := congr_arg nat_degree hg,
          rw [this, nat_degree_mul_eq, nat_degree_pow_eq,
            nat_degree_X_sub_C],


        end⟩ _,
  end),
let ⟨δ, hδ⟩ := continuous_of_metric.1 (polynomial.continuous_eval g) in
begin


end