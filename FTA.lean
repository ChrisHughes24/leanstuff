import analysis.exponential analysis.polynomial
import ring_theory.prime_count

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


-- @[elab_as_eliminator] protected lemma induction_on {M : polynomial ℂ → Prop} (p : polynomial ℂ )
--   (h_C : ∀a, M (C a))
--   (h_add : ∀p q, M p → M q → M (p + q))
--   (h_monomial : ∀(n : ℕ) (a : ℂ), M (C a * X^n) → M (C a * X^(n+1))) :
--   M p :=
-- have ∀{n:ℕ} {a}, M (C a * X^n),
-- begin
--   assume n a,
--   induction n with n ih,
--   { simp only [pow_zero, mul_one, h_C] },
--   { exact h_monomial _ _ ih }
-- end,
-- finsupp.induction p
--   (suffices M (C 0), by simpa only [C, single_zero],
--     h_C 0)
--   (assume n a p _ _ hp, suffices M (C a * X^n + p), by rwa [single_eq_C_mul_X],
--     h_add _ _ this hp)

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

lemma polynomial.is_unit_iff {p : polynomial ℂ} : is_unit p ↔ degree p = 0 :=
⟨λ h, let ⟨q, hq⟩ := is_unit_iff_dvd_one.1 h in
    have hp0 : p ≠ 0, from λ hp0, by simpa [hp0] using hq,
    have hq0 : q ≠ 0, from λ hp0, by simpa [hp0] using hq,
    have nat_degree (1 : polynomial ℂ) = nat_degree (p * q),
      from congr_arg _ hq,
    by rw [nat_degree_one, nat_degree_mul_eq hp0 hq0, eq_comm,
        add_eq_zero_iff, ← with_bot.coe_eq_coe,
        ← degree_eq_nat_degree hp0] at this;
      exact this.1,
  λ h, have degree p ≤ 0, by simp [*, le_refl],
    have hc : coeff p 0 ≠ 0, from λ hc,
        by rw [eq_C_of_degree_le_zero this, hc] at h;
        simpa using h,
    is_unit_iff_dvd_one.2 ⟨C (coeff p 0)⁻¹, begin
      conv in p { rw eq_C_of_degree_le_zero this },
      rw [← C_mul, _root_.mul_inv_cancel hc, C_1]
    end⟩⟩

instance decidable_dvd {α : Type*} [comm_ring α] [decidable_eq α] :
  decidable_rel ((∣) : polynomial α → polynomial α → Prop) :=
sorry

lemma polynomial.finite_of_degree_pos {α : Type*} [integral_domain α] [decidable_eq α]
  {p q : polynomial α} (hp : (0 : with_bot ℕ) < degree p) (hq : q ≠ 0) :
  prime_count.finite p q :=
⟨nat_degree q, λ ⟨r, hr⟩,
  have hp0 : p ≠ 0, from λ hp0, by simp [hp0] at hp; contradiction,
  have hr0 : r ≠ 0, from λ hr0, by simp * at *,
  have hpn0 : p ^ (nat_degree q + 1) ≠ 0,
    from pow_ne_zero _ hp0,
  have hnp : 0 < nat_degree p,
    by rw [← with_bot.coe_lt_coe, ← degree_eq_nat_degree hp0];
    exact hp,
  begin
    have := congr_arg nat_degree hr,
    rw [nat_degree_mul_eq hpn0 hr0, nat_degree_pow_eq, add_mul, add_assoc] at this,
    exact ne_of_lt (lt_add_of_le_of_pos (le_mul_of_ge_one_right' (nat.zero_le _) hnp)
      (add_pos_of_pos_of_nonneg (by rwa one_mul) (nat.zero_le _))) this
  end⟩

def polynomial.multiplicity {α : Type*} [integral_domain α] [decidable_eq α]
  (p : polynomial α) (a :  α) : ℕ :=
if h0 : p = 0 then 0 else
(prime_count (X - C a) p).get (polynomial.finite_of_degree_pos
  (by rw degree_X_sub_C; exact dec_trivial) h0)

lemma pow_multiplicity_dvd {α : Type*} [integral_domain α] [decidable_eq α]
  (p : polynomial α) (a : α) :
  (X - C a) ^ polynomial.multiplicity p a ∣ p :=
if h : p = 0 then by simp [h]
else by rw [polynomial.multiplicity, dif_neg h];
  exact prime_count.spec _

lemma div_by_monic_mul_pow_multiplicity_eq
  {α : Type*} [integral_domain α] [decidable_eq α]
  (p : polynomial α) (a : α) :
  p /ₘ ((X - C a) ^ polynomial.multiplicity p a) *
  (X - C a) ^ polynomial.multiplicity p a = p :=
have monic ((X - C a) ^ polynomial.multiplicity p a),
  from by rw [monic.def, leading_coeff_pow,
    (show _ = _, from monic_X_sub_C _), one_pow],
by conv_rhs { rw [← mod_by_monic_add_div p this,
    (dvd_iff_mod_by_monic_eq_zero this).2 (pow_multiplicity_dvd _ _)] };
  simp [mul_comm]

lemma eval_div_by_monic_pow_multiplicity_ne_zero
  {α : Type*} [integral_domain α] [decidable_eq α]
  {p : polynomial α} (a : α) (hp : p ≠ 0) :
  (p /ₘ ((X - C a) ^ polynomial.multiplicity p a)).eval a ≠ 0 :=
mt dvd_iff_is_root.2 $ λ ⟨q, hq⟩,
begin
  have := div_by_monic_mul_pow_multiplicity_eq p a,
  rw [mul_comm, hq, ← mul_assoc, ← pow_succ',
    polynomial.multiplicity, dif_neg hp] at this,
  refine prime_count.is_greatest'
    (polynomial.finite_of_degree_pos
    (show (0 : with_bot ℕ) < degree (X - C a),
      by rw degree_X_sub_C; exact dec_trivial) hp)
    (nat.lt_succ_self _) (dvd_of_mul_right_eq _ this)
end

axiom attains_infi (p : polynomial ℂ) :
  ∃ x, (p.eval x).abs = ⨅ y, (p.eval y).abs

axiom nth_root (n : ℕ) (z : ℂ) : ℂ

axiom nth_root_pow (n : ℕ) (z : ℂ) : nth_root n z ^ n = z

axiom abs_nth_root (n : ℕ) (z : ℂ) : abs (nth_root n z) =
  real.nth_root (abs z) n

#print real.nth_root

open euclidean_domain
local attribute [instance, priority 0] classical.prop_decidable
set_option trace.simplify.rewrite true
lemma FTA {f : polynomial ℂ} (hf : 0 < degree f) : ∃ z : ℂ, is_root f z :=
let ⟨z₀, hz₀⟩ := attains_infi f in
exists.intro z₀ $ by_contradiction $ λ hf0,
have hfX : f - C (f.eval z₀) ≠ 0,
  from mt sub_eq_zero.1 (λ h, not_le_of_gt hf
    (h.symm ▸ degree_C_le)),
let n := polynomial.multiplicity (f - C (f.eval z₀)) z₀ in
let g := (f - C (f.eval z₀)) /ₘ ((X - C z₀) ^ n) in
have hg0 : g.eval z₀ ≠ 0, from eval_div_by_monic_pow_multiplicity_ne_zero _ hfX,
have hg : g * (X - C z₀) ^ n = f - C (f.eval z₀),
  from div_by_monic_mul_pow_multiplicity_eq _ _,
have hn0 : 0 < n, from nat.pos_of_ne_zero $ λ hn0,
  by simpa [g, hn0] using hg0,
let ⟨δ', hδ'₁, hδ'₂⟩ := continuous_of_metric.1 (polynomial.continuous_eval g) z₀
  ((g.eval z₀).abs) (complex.abs_pos.2 hg0) in
let δ := min (min (δ' / 2) 1) (((f.eval z₀).abs / (g.eval z₀).abs) / 2) in
have hf0' : 0 < (f.eval z₀).abs, from complex.abs_pos.2 hf0,
have hfg0 : 0 < abs (eval z₀ f) * (abs (eval z₀ g))⁻¹,
  from div_pos hf0' (complex.abs_pos.2 hg0),
have hδ0 : 0 < δ, from lt_min
  (lt_min (half_pos hδ'₁) (by norm_num)) (half_pos hfg0),
have hδ : ∀ z : ℂ, abs (z - z₀) = δ → abs (g.eval z - g.eval z₀) <
  (g.eval z₀).abs,
  from λ z hz, hδ'₂ z (by rw [complex.dist_eq, hz];
    exact lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _))
      (half_lt_self hδ'₁)),
have hδ1 : δ ≤ 1, from le_trans (min_le_left _ _) (min_le_right _ _),
let F : polynomial ℂ := C (f.eval z₀) + C (g.eval z₀) * (X - C z₀) ^ n in
let z' := nth_root n (-f.eval z₀ * (g.eval z₀).abs * δ ^ n /
  ((f.eval z₀).abs * g.eval z₀)) + z₀ in
have hF₁ : F.eval z' = f.eval z₀ - f.eval z₀ * (g.eval z₀).abs
    * δ ^ n / (f.eval z₀).abs,
  by simp [F, nth_root_pow, div_eq_mul_inv, eval_pow, mul_assoc,
      mul_comm (g.eval z₀),
      mul_left_comm (g.eval z₀), mul_left_comm (g.eval z₀)⁻¹,
      mul_inv', inv_mul_cancel hg0];
    simp [mul_comm, mul_left_comm, mul_assoc],
have hδs : (g.eval z₀).abs * δ ^ n / (f.eval z₀).abs < 1,
  begin
    rw [div_eq_mul_inv, mul_right_comm, mul_comm,
      ← @inv_inv' _ _ (complex.abs _ * _), mul_inv',
      inv_inv', ← div_eq_mul_inv, div_lt_iff hfg0, one_mul],
    calc δ ^ n ≤ δ ^ 1 : pow_le_pow_of_le_one
        (le_of_lt hδ0) hδ1 hn0
      ... = δ : _root_.pow_one _
      ... ≤ ((f.eval z₀).abs / (g.eval z₀).abs) / 2 : min_le_right _ _
      ... < _ : half_lt_self hfg0
  end,
have hF₂ : (F.eval z').abs = (f.eval z₀).abs - (g.eval z₀).abs * δ ^ n,
  from calc (F.eval z').abs = (f.eval z₀ - f.eval z₀ * (g.eval z₀).abs
    * δ ^ n / (f.eval z₀).abs).abs : congr_arg abs hF₁
  ... = abs (f.eval z₀) * complex.abs (1 - (g.eval z₀).abs * δ ^ n /
      (f.eval z₀).abs : ℝ) : by rw [← complex.abs_mul];
        exact congr_arg complex.abs
          (by simp [mul_add, add_mul, mul_assoc, div_eq_mul_inv])
  ... = _ : by rw [complex.abs_of_nonneg (sub_nonneg.2 (le_of_lt hδs)),
      mul_sub, mul_div_cancel' _ (ne.symm (ne_of_lt hf0')), mul_one],
have hef0 : abs (eval z₀ g) * (eval z₀ f).abs ≠ 0,
  from mul_ne_zero (mt complex.abs_eq_zero.1 hg0)
    (mt complex.abs_eq_zero.1 hf0),
have hz'z₀ : abs (z' - z₀) = δ :=
  begin
     simp [z', mul_assoc, mul_left_comm _ (_ ^ n),
      mul_comm _ (_ ^ n), mul_comm (eval z₀ f).abs,
      _root_.mul_div_cancel _ hef0, of_real_mul,
      neg_mul_eq_neg_mul_symm, neg_div, abs_nth_root,
      is_absolute_value.abv_pow complex.abs],
  end,
have hF₃ : (f.eval z' - F.eval z').abs < (g.eval z₀).abs * δ ^ n,
  from calc (f.eval z' - F.eval z').abs
      = (g.eval z' - g.eval z₀).abs * (z' - z₀).abs ^ n :
        by rw [← eq_sub_iff_add_eq.1 hg, ← is_absolute_value.abv_pow complex.abs,
            ← complex.abs_mul, sub_mul];
          simp [F, eval_pow, eval_add, eval_mul,
            eval_sub, eval_C, eval_X, eval_neg, add_sub_cancel]
  ... = (g.eval z' - g.eval z₀).abs * δ ^ n : by rw hz'z₀
  ... < _ : (mul_lt_mul_right (pow_pos hδ0 _)).2 (hδ _ hz'z₀),
lt_irrefl (f.eval z₀).abs $
calc (f.eval z₀).abs = ⨅ y, (f.eval y).abs : hz₀
... ≤ (f.eval z').abs : lattice.cinfi_le
  ⟨0, λ _ ⟨z, hz⟩, by simp [hz.symm, complex.abs_nonneg]⟩
... = (F.eval z' + (f.eval z' - F.eval z')).abs : by simp
... ≤ (F.eval z').abs + (f.eval z' - F.eval z').abs : complex.abs_add _ _
... < (f.eval z₀).abs - (g.eval z₀).abs * δ ^ n + (g.eval z₀).abs * δ ^ n :
  add_lt_add_of_le_of_lt (by rw hF₂) hF₃
... = _ : by simp
