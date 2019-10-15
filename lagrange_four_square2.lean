import data.zmod.basic tactic.ring data.polynomial group_theory.perm.sign

open finset polynomial

lemma add_even_of_add_square_even {m x y : ℤ} (h : 2 * m = x^2 + y^2) : (x + y) % 2 = 0 :=
have hzmod : ∀ x y : zmod 2, x ^ 2 + y ^ 2 = 0 → x + y = 0, from dec_trivial,
have (x : zmod 2)^2 + (y : zmod 2)^2 = 0,
  by simpa [show (2 : zmod 2) = 0, from rfl, eq_comm] using congr_arg (coe : ℤ → zmod 2) h,
show x + y ≡ 0 [ZMOD 2], from (zmod.eq_iff_modeq_int' (show 2 > 0, from dec_trivial)).1 $
by simpa using hzmod _ _ this

lemma sub_even_of_add_square_even {m x y : ℤ} (h : 2 * m = x^2 + y^2) : (x - y) % 2 = 0 :=
add_even_of_add_square_even (show 2 * m = x^2 + (-y)^2, by simpa)

private lemma sum_two_squares_of_two_mul_sum_two_squares {m x y : ℤ} (h : 2 * m = x^2 + y^2) :
  m = ((x - y) / 2) ^ 2 + ((x + y) / 2) ^ 2 :=
(domain.mul_left_inj (show (2*2 : ℤ) ≠ 0, from dec_trivial)).1 $
calc 2 * 2 * m = (x - y)^2 + (x + y)^2 : by rw [mul_assoc, h]; ring
... = (2 * ((x - y) / 2))^2 + (2 * ((x + y) / 2))^2 :
  by rw [int.mul_div_cancel' ((int.dvd_iff_mod_eq_zero _ _).2 (sub_even_of_add_square_even h)),
    int.mul_div_cancel' ((int.dvd_iff_mod_eq_zero _ _).2 (add_even_of_add_square_even h))]
... = 2 * 2 * (((x - y) / 2) ^ 2 + ((x + y) / 2) ^ 2) :
  by simp [mul_add, pow_succ, mul_comm, mul_assoc, mul_left_comm]

private lemma sum_four_squares_of_two_mul_sum_four_squares {m a b c d : ℤ}
  (h : a^2 + b^2 + c^2 + d^2 = 2 * m) :
  ∃ w x y z, w^2 + x^2 + y^2 + z^2 = m :=
let dec : decidable (∀ f : fin 4 → zmod 2, (f 0)^2 + (f 1)^2 + (f 2)^2 + (f 3)^2 = 0 →
    ∃ σ : equiv.perm (fin 4), f (σ 0) ^ 2 + f (σ 1) ^ 2 = 0 ∧ f (σ 2) ^ 2 + f (σ 3) ^ 2 = 0) :=
  @fintype.decidable_forall_fintype (fin 4 → zmod 2) _ _
    (λ f : fin 4 → zmod 2, @forall_prop_decidable ((f 0)^2 + (f 1)^2 + (f 2)^2 + (f 3)^2 = 0)
      _ (zmod.decidable_eq 2 _ 0)
      (λ h, @fintype.decidable_exists_fintype (equiv.perm (fin 4)) _
        (λ σ, f (σ 0) ^ 2 + f (σ 1) ^ 2 = 0 ∧ f (σ 2) ^ 2 + f (σ 3) ^ 2 = 0)
        _)) in
have ∀ f : fin 4 → zmod 2, (f 0)^2 + (f 1)^2 + (f 2)^2 + (f 3)^2 = 0 →
    ∃ σ : equiv.perm (fin 4), f (σ 0) ^ 2 + f (σ 1) ^ 2 = 0 ∧ f (σ 2) ^ 2 + f (σ 3) ^ 2 = 0,
  from @of_as_true _ dec trivial,
let f : fin 4 → ℤ := vector.nth ⟨[a,b,c,d], rfl⟩ in
let ⟨σ, hσ⟩ := this (coe ∘ f) (by rw [← @zero_mul (zmod 2) _ m, ← show ((2 : ℤ) : zmod 2) = 0, from rfl,
  ← int.cast_mul, ← h]; simp only [int.cast_add, int.cast_pow]; refl) in
have h01 : 2 ∣ f (σ 0) ^ 2 + f (σ 1) ^ 2,
  from (@zmod.eq_zero_iff_dvd_int 2 _).1 $ by simpa using hσ.1,
have h23 : 2 ∣ f (σ 2) ^ 2 + f (σ 3) ^ 2,
  from (@zmod.eq_zero_iff_dvd_int 2 _).1 $ by simpa using hσ.2,
let ⟨x, hx⟩ := h01 in let ⟨y, hy⟩ := h23 in
⟨(f (σ 0) - f (σ 1)) / 2, (f (σ 0) + f (σ 1)) / 2, (f (σ 2) - f (σ 3)) / 2, (f (σ 2) + f (σ 3)) / 2,
  begin
    rw [← sum_two_squares_of_two_mul_sum_two_squares hx.symm, add_assoc,
      ← sum_two_squares_of_two_mul_sum_two_squares hy.symm,
      ← domain.mul_left_inj (show (2 : ℤ) ≠ 0, from dec_trivial), ← h, mul_add, ← hx, ← hy],
    suffices : f (σ 0)^2 + (f (σ 1)^2 + (f (σ 2)^2 + (f (σ 3)^2 + 0))) =
      f 0^2 + (f 1^2 + (f 2^2 + (f 3^2 + 0))),
    { by simpa [f] },
    have : univ.sum (λ x, f (σ x)^2) = univ.sum (λ x, f x^2),
    { conv_rhs { rw finset.sum_univ_perm σ } },
    exact this,
  end⟩

lemma card_roots' {α : Type*} [integral_domain α] {p : polynomial α} (hp0 : p ≠ 0) :
  p.roots.card ≤ nat_degree p :=
with_bot.coe_le_coe.1 (le_trans (card_roots hp0) (le_of_eq $ degree_eq_nat_degree hp0))

lemma card_image_polynomial_eval {α : Type*} [integral_domain α] [fintype α] [decidable_eq α]
  {p : polynomial α} (hp : 0 < p.degree) :
  fintype.card α ≤ nat_degree p * (univ.image (λ x, eval x p)).card :=
have hdp : ∀ {a : α}, degree p = degree (p - C a),
  from λ a, eq.symm $ by rw [sub_eq_add_neg, add_comm]; exact
    degree_add_eq_of_degree_lt
      (show degree (-C a) < degree p, by rw degree_neg;
        exact lt_of_le_of_lt (degree_C_le) hp),
have hp0 : ∀ {a : α}, p - C a ≠ 0, from λ a h, by rw [@hdp a, h] at hp; simp * at *,
have hroots : ∀ {x a : α}, x ∈ (p - C a).roots ↔ p.eval x = a,
  from λ _ _, by rw [mem_roots hp0, is_root, eval_sub, eval_C, sub_eq_zero],
calc fintype.card α = fintype.card (Σ a : set.range (λ x, eval x p), {x // p.eval x = a}) :
  fintype.card_congr (equiv.sigma_subtype_preimage_equiv _
    (set.range (λ x, eval x p)) (set.mem_range_self : _)).symm
... = univ.sum (λ a : set.range (λ x, eval x p), fintype.card {x // p.eval x = a}) :
  fintype.card_sigma _
... = (univ.image (λ x, eval x p)).sum (λ a, (p - C a).roots.card) :
  finset.sum_bij (λ a _, a)
    (λ ⟨a, x, hx⟩ _, mem_image.2 ⟨x, mem_univ _, hx⟩)
    (λ ⟨a, ha⟩ _, finset.card_congr (λ a _, a.val) (λ ⟨x, hx⟩ _, by rwa hroots)
      (λ _ _ _ _, subtype.ext.2)
      (λ x hx, ⟨⟨x, by rwa ← hroots⟩, mem_univ _, rfl⟩))
    (λ _ _ _ _, subtype.ext.2)
    (λ x, by rw [mem_image]; exact λ ⟨a, _, ha⟩, ⟨⟨x, ⟨a, ha⟩⟩, mem_univ _, rfl⟩)
... ≤ (univ.image (λ x, eval x p)).sum (λ _, p.nat_degree) :
  sum_le_sum (λ a _, by rw [nat_degree_eq_of_degree_eq (@hdp a)]; exact card_roots' (@hp0 a))
... = _ : by rw [sum_const, add_monoid.smul_eq_mul', nat.cast_id]

lemma exists_root_sum_quadratic {α : Type*} [fintype α] [integral_domain α]
  (f g : polynomial α) (hf2 : degree f = 2) (hg2 : degree g = 2) (hα : fintype.card α % 2 = 1) :
  ∃ a b, f.eval a + g.eval b = 0 :=
by letI := classical.dec_eq α; exact
have ∀ f : polynomial α, degree f = 2 →
    fintype.card α ≤ 2 * (univ.image (λ x : α, eval x f)).card,
  from λ f hf, have hf0 : f ≠ 0, from λ h, by simp * at *; contradiction,
    calc fintype.card α ≤ nat_degree f * (univ.image (λ x, eval x f)).card :
      card_image_polynomial_eval (hf.symm ▸ dec_trivial)
    ... = _ : by rw [degree_eq_nat_degree hf0, show (2 : with_bot ℕ) = (2 : ℕ), from rfl,
      with_bot.coe_eq_coe] at hf; rw hf,
have ∀ f : polynomial α, degree f = 2 →
    fintype.card α < 2 * (univ.image (λ x : α, eval x f)).card,
  from λ f hf, lt_of_le_of_ne (this _ hf) (mt (congr_arg (% 2)) (by simp *)),
have h : fintype.card α < (univ.image (λ x : α, eval x f)).card +
    (univ.image (λ x : α, eval x (-g))).card,
  from (mul_lt_mul_left (show 2 > 0, by norm_num)).1 $
    by rw [two_mul, mul_add]; exact add_lt_add (this _ hf2) (this _ (by simpa)),
have hd : ¬ disjoint (univ.image (λ x : α, eval x f)) (univ.image (λ x : α, eval x (-g))),
  from λ hd, by rw [← card_disjoint_union hd, ← not_le] at h;
    exact h (card_le_of_subset $ subset_univ _),
begin
  simp only [disjoint_left, mem_image] at hd,
  push_neg at hd,
  rcases hd with ⟨x, ⟨a, _, ha⟩, ⟨b, _, hb⟩⟩,
  use [a, b],
  rw [ha, ← hb, eval_neg, neg_add_self]
end

lemma neg_one_sum_two_squares_mod_p {p : ℕ} (hp : p.prime) : ∃ a b : zmodp p hp, a^2 + b^2 + 1 = 0 :=
hp.eq_two_or_odd.elim (λ hp2, by subst hp2; exact dec_trivial) $ λ hp2,
let ⟨a, b, hab⟩ := exists_root_sum_quadratic (-X^2 : polynomial (zmodp p hp)) (X^2 - C (-1)) (by simp)
  (degree_X_pow_sub_C dec_trivial _) (by simp *) in
⟨a, b, by simpa using hab⟩

def zmod.val_min_abs {n : ℕ+} (x : zmod n) : ℤ :=
if x.val ≤ n / 2 then x.val else x.val - n

@[simp] lemma zmod.coe_val_min_abs {n : ℕ+} (x : zmod n) :
  (x.val_min_abs : zmod n) = x :=
by simp [zmod.val_min_abs]; split_ifs; simp

lemma zmod.nat_abs_val_min_abs_le {n : ℕ+} (x : zmod n) :
  x.val_min_abs.nat_abs ≤ n / 2 :=
have (x.val - n : ℤ) ≤ 0, from sub_nonpos.2 $ int.coe_nat_le.2 $ le_of_lt x.2,
begin
  rw zmod.val_min_abs,
  split_ifs with h,
  { exact h },
  { rw [← int.coe_nat_le, int.of_nat_nat_abs_of_nonpos this, neg_sub],
    conv_lhs { congr, rw [coe_coe, ← nat.mod_add_div n 2, int.coe_nat_add, int.coe_nat_mul,
      int.coe_nat_bit0, int.coe_nat_one] },
    rw ← sub_nonneg,
    suffices : (0 : ℤ) ≤ x.val - ((n % 2 : ℕ) + (n / 2 : ℕ)),
    { exact le_trans this (le_of_eq $ by ring) },
    exact sub_nonneg.2 (by rw [← int.coe_nat_add, int.coe_nat_le];
      exact calc (n : ℕ) % 2 + n / 2 ≤ 1 + n / 2 :
        add_le_add (nat.le_of_lt_succ (nat.mod_lt _ dec_trivial)) (le_refl _)
        ... ≤ x.val : by rw add_comm; exact nat.succ_le_of_lt (lt_of_not_ge h)) }
end

@[simp] lemma zmod.val_min_abs_zero {n : ℕ+} : (0 : zmod n).val_min_abs = 0 :=
by simp [zmod.val_min_abs]

@[simp] lemma zmod.val_min_abs_eq_zero {n : ℕ+} (x : zmod n) :
  x.val_min_abs = 0 ↔ x = 0 :=
⟨λ h, begin
  dsimp [zmod.val_min_abs] at h,
  split_ifs at h,
  { exact fin.eq_of_veq (by simp * at *) },
  { exact absurd h (mt sub_eq_zero.1 (ne_of_lt $ int.coe_nat_lt.2 x.2)) }
end, λ hx0, hx0.symm ▸ zmod.val_min_abs_zero⟩

def zmodp.val_min_abs {p : ℕ} {hp : p.prime} : zmodp p hp → ℤ := zmod.val_min_abs

@[simp] lemma zmodp.coe_val_min_abs {p : ℕ} (hp : p.prime) (x : zmodp p hp) :
  (x.val_min_abs : zmodp p hp) = x := @zmod.coe_val_min_abs ⟨p, hp.pos⟩ x

lemma zmodp.nat_abs_val_min_abs_le {p : ℕ} {hp : p.prime} (x : zmodp p hp) :
  x.val_min_abs.nat_abs ≤ p / 2 :=
zmod.nat_abs_val_min_abs_le _

lemma exists_sum_two_squares_add_one_eq_k {p : ℕ} (hp : p.prime) (hp1 : p % 2 = 1) :
  ∃ (a b : ℤ) (k : ℕ), a^2 + b^2 + 1 = k * p ∧ k < p :=
let ⟨a, b, hab⟩ := neg_one_sum_two_squares_mod_p hp in
have hab' : (p : ℤ) ∣ a.val_min_abs ^ 2 + b.val_min_abs ^ 2 + 1,
  from (zmodp.eq_zero_iff_dvd_int hp _).1 $ by simpa using hab,
let ⟨k, hk⟩ := hab' in
have hk0 : 0 ≤ k, from nonneg_of_mul_nonneg_left
  (by rw ← hk; exact (add_nonneg (add_nonneg (pow_two_nonneg _) (pow_two_nonneg _)) zero_le_one))
  (int.coe_nat_pos.2 hp.pos),
⟨a.val_min_abs, b.val_min_abs, k.nat_abs,
    by rw [hk, int.nat_abs_of_nonneg hk0, mul_comm],
  lt_of_mul_lt_mul_left
    (calc p * k.nat_abs = a.val_min_abs.nat_abs ^ 2 + b.val_min_abs.nat_abs ^ 2 + 1 :
        by rw [← int.coe_nat_inj', int.coe_nat_add, int.coe_nat_add, nat.pow_two, nat.pow_two,
          int.nat_abs_mul_self, int.nat_abs_mul_self,← pow_two, ← pow_two,
          int.coe_nat_one, hk, int.coe_nat_mul, int.nat_abs_of_nonneg hk0]
      ... ≤ (p / 2) ^ 2 + (p / 2)^2 + 1 :
        add_le_add
          (add_le_add
            (nat.pow_le_pow_of_le_left (zmodp.nat_abs_val_min_abs_le _) _)
            (nat.pow_le_pow_of_le_left (zmodp.nat_abs_val_min_abs_le _) _))
          (le_refl _)
      ... < (p / 2) ^ 2 + (p / 2)^ 2 + (p % 2)^2 + ((2 * (p / 2)^2 + (4 * (p / 2) * (p % 2)))) :
        by rw [hp1, nat.one_pow, mul_one];
          exact (lt_add_iff_pos_right _).2
            (add_pos_of_nonneg_of_pos (nat.zero_le _) (mul_pos dec_trivial
              (nat.div_pos hp.two_le dec_trivial)))
      ... = _ : begin
        conv_rhs { rw [← nat.mod_add_div p 2] },
        simp only [nat.pow_two],
        rw [← int.coe_nat_inj'],
        simp only [nat.pow_two, int.coe_nat_add, int.coe_nat_mul, int.coe_nat_bit0, int.coe_nat_one,
          two_mul, mul_add, add_mul],
        ring,
      end)
    (show 0 ≤ p, from nat.zero_le _)⟩

open_locale classical

lemma odd_prime_sum_four_squares {p : ℕ} (hp : p.prime) (hp2 : p%2 = 1) :
  ∃ a b c d : ℤ, a^2 + b^2 + c^2 + d^2 = p :=
have hm : ∃ m < p, 0 < m ∧ ∃ a b c d : ℤ, a^2 + b^2 + c^2 + d^2 = m * p,
  from let ⟨a, b, k, hk⟩ := exists_sum_two_squares_add_one_eq_k hp hp2 in
  ⟨k, hk.2, nat.pos_of_ne_zero $
    (λ hk0, by rw [hk0, int.coe_nat_zero, zero_mul] at hk;
      exact ne_of_gt (show a^2 + b^2 + 1 > 0, from add_pos_of_nonneg_of_pos
        (add_nonneg (pow_two_nonneg _) (pow_two_nonneg _)) zero_lt_one) hk.1),
    a, b, 1, 0, by simpa [pow_two] using hk.1⟩,
let m := nat.find hm in
let ⟨a, b, c, d, (habcd : a^2 + b^2 + c^2 + d^2 = m * p)⟩ := (nat.find_spec hm).snd.2 in
have hm0 : 0 < m, from (nat.find_spec hm).snd.1,
have hmp : m < p, from (nat.find_spec hm).fst,
m.mod_two_eq_zero_or_one.elim
  (λ hm2 : m % 2 = 0,
    let ⟨k, hk⟩ := (nat.dvd_iff_mod_eq_zero _ _).2 hm2 in
    have hk0 : 0 < k, from nat.pos_of_ne_zero $ λ _, by simp [*, lt_irrefl] at *,
    have hkm : k < m, by rw [hk, two_mul]; exact (lt_add_iff_pos_left _).2 hk0,
    false.elim $ nat.find_min hm hkm ⟨lt_trans hkm hmp, hk0,
      sum_four_squares_of_two_mul_sum_four_squares
        (show a^2 + b^2 + c^2 + d^2 = 2 * (k * p),
          by rw [habcd, hk, int.coe_nat_mul, mul_assoc]; simp)⟩)
  (λ hm2 : m % 2 = 1,
    if hm1 : m = 1 then ⟨a, b, c, d, by simp only [hm1, habcd, int.coe_nat_one, one_mul]⟩
    else --have hm1 : 1 < m, from lt_of_le_of_ne hm0 (ne.symm hm1),
      let mp : ℕ+ := ⟨m, hm0⟩ in
      let w := (a : zmod mp).val_min_abs, x := (b : zmod mp).val_min_abs,
          y := (c : zmod mp).val_min_abs, z := (d : zmod mp).val_min_abs in
      have hnat_abs : w^2 + x^2 + y^2 + z^2 =
          (w.nat_abs^2 + x.nat_abs^2 + y.nat_abs ^2 + z.nat_abs ^ 2 : ℕ),
        by simp [pow_two],
      have hwxyzlt : w^2 + x^2 + y^2 + z^2 < m^2,
        from calc w^2 + x^2 + y^2 + z^2
            = (w.nat_abs^2 + x.nat_abs^2 + y.nat_abs ^2 + z.nat_abs ^ 2 : ℕ) : hnat_abs
        ... ≤ ((m / 2) ^ 2 + (m / 2) ^ 2 + (m / 2) ^ 2 + (m / 2) ^ 2 : ℕ) :
          int.coe_nat_le.2 $ add_le_add (add_le_add (add_le_add
            (nat.pow_le_pow_of_le_left (zmod.nat_abs_val_min_abs_le _) _)
            (nat.pow_le_pow_of_le_left (zmod.nat_abs_val_min_abs_le _) _))
            (nat.pow_le_pow_of_le_left (zmod.nat_abs_val_min_abs_le _) _))
            (nat.pow_le_pow_of_le_left (zmod.nat_abs_val_min_abs_le _) _)
        ... = 4 * (m / 2 : ℕ) ^ 2 : by simp [pow_two, bit0, bit1, mul_add, add_mul]
        ... < 4 * (m / 2 : ℕ) ^ 2 + ((4 * (m / 2) : ℕ) * (m % 2 : ℕ) + (m % 2 : ℕ)^2) :
          (lt_add_iff_pos_right _).2 (by rw [hm2, int.coe_nat_one, one_pow, mul_one];
            exact add_pos_of_nonneg_of_pos (int.coe_nat_nonneg _) zero_lt_one)
        ... = m ^ 2 : by conv_rhs {rw [← nat.mod_add_div m 2]};
          simp [-nat.mod_add_div, mul_add, add_mul, bit0, bit1, mul_comm, mul_assoc, mul_left_comm,
            pow_add],
      have hwxyzabcd : ((w^2 + x^2 + y^2 + z^2 : ℤ) : zmod mp) =
          ((a^2 + b^2 + c^2 + d^2 : ℤ) : zmod mp),
        by simp [w, x, y, z, pow_two],
      have hwxyz0 : ((w^2 + x^2 + y^2 + z^2 : ℤ) : zmod mp) = 0,
        by rw [hwxyzabcd, habcd, int.cast_mul, show ((m : ℤ) : zmod mp) = (mp : zmod mp), from rfl,
          int.cast_coe_nat, coe_coe, zmod.cast_self_eq_zero]; simp,
      let ⟨n, hn⟩ := (zmod.eq_zero_iff_dvd_int.1 hwxyz0) in
      have hn0 : 0 < n.nat_abs, from int.nat_abs_pos_of_ne_zero (λ hn0,
        have hwxyz0 : (w.nat_abs^2 + x.nat_abs^2 + y.nat_abs^2 + z.nat_abs^2 : ℕ) = 0,
          by rw [← int.coe_nat_eq_zero, ← hnat_abs]; rwa [hn0, mul_zero] at hn,
        have habcd0 : (m : ℤ) ∣ a ∧ (m : ℤ) ∣ b ∧ (m : ℤ) ∣ c ∧ (m : ℤ) ∣ d,
          by simpa [add_eq_zero_iff_eq_zero_of_nonneg (pow_two_nonneg _) (pow_two_nonneg _),
            nat.pow_two, w, x, y, z, zmod.eq_zero_iff_dvd_int] using hwxyz0,
        let ⟨ma, hma⟩ := habcd0.1,     ⟨mb, hmb⟩ := habcd0.2.1,
            ⟨mc, hmc⟩ := habcd0.2.2.1, ⟨md, hmd⟩ := habcd0.2.2.2 in
        have hmdvdp : m ∣ p,
          from int.coe_nat_dvd.1 ⟨ma^2 + mb^2 + mc^2 + md^2,
            (domain.mul_left_inj (show (m : ℤ) ≠ 0, from int.coe_nat_ne_zero_iff_pos.2 hm0)).1 $
              by rw [← habcd, hma, hmb, hmc, hmd]; ring⟩,
        (hp.2 _ hmdvdp).elim hm1 (λ hmeqp, by simpa [lt_irrefl, hmeqp] using hmp)),
      have hawbxcydz : ((mp : ℕ) : ℤ) ∣ a * w + b * x + c * y + d * z,
        from zmod.eq_zero_iff_dvd_int.1 $ by rw [← hwxyz0]; simp; ring,
      have haxbwczdy : ((mp : ℕ) : ℤ) ∣ a * x - b * w - c * z + d * y,
        from zmod.eq_zero_iff_dvd_int.1 $ by simp; ring,
      have haybzcwdx : ((mp : ℕ) : ℤ) ∣ a * y + b * z - c * w - d * x,
        from zmod.eq_zero_iff_dvd_int.1 $ by simp; ring,
      have hazbycxdw : ((mp : ℕ) : ℤ) ∣ a * z - b * y + c * x - d * w,
        from zmod.eq_zero_iff_dvd_int.1 $ by simp; ring,
      let ⟨s, hs⟩ := hawbxcydz, ⟨t, ht⟩ := haxbwczdy, ⟨u, hu⟩ := haybzcwdx, ⟨v, hv⟩ := hazbycxdw in
      have hn_nonneg : 0 ≤ n,
        from nonneg_of_mul_nonneg_left
          (by erw [← hn]; repeat {try {refine add_nonneg _ _}, try {exact pow_two_nonneg _}})
          (int.coe_nat_pos.2 hm0),
      have hnm : n.nat_abs < mp,
        from int.coe_nat_lt.1 (lt_of_mul_lt_mul_left
          (by rw [int.nat_abs_of_nonneg hn_nonneg, ← hn, ← pow_two]; exact hwxyzlt)
          (int.coe_nat_nonneg mp)),
      have hstuv : s^2 + t^2 + u^2 + v^2 = n.nat_abs * p,
        from (domain.mul_left_inj (show (m^2 : ℤ) ≠ 0, from pow_ne_zero 2
            (int.coe_nat_ne_zero_iff_pos.2 hm0))).1 $
          calc (m : ℤ)^2 * (s^2 + t^2 + u^2 + v^2) = ((mp : ℕ) * s)^2 + ((mp : ℕ) * t)^2 +
              ((mp : ℕ) * u)^2 + ((mp : ℕ) * v)^2 :
            by simp [mp]; ring
          ... = (w^2 + x^2 + y^2 + z^2) * (a^2 + b^2 + c^2 + d^2) :
            by simp only [hs.symm, ht.symm, hu.symm, hv.symm]; ring
          ... = _ : by rw [hn, habcd, int.nat_abs_of_nonneg hn_nonneg]; dsimp [mp]; ring,
      false.elim $ nat.find_min hm hnm ⟨lt_trans hnm hmp, hn0, s, t, u, v, hstuv⟩)

open nat

lemma sum_four_squares : ∀ n : ℕ, ∃ a b c d : ℕ, a^2 + b^2 + c^2 + d^2 = n
| 0 := ⟨0, 0, 0, 0, rfl⟩
| 1 := ⟨1, 0, 0, 0, rfl⟩
| n@(k+2) :=
have hm : (min_fac n).prime := min_fac_prime dec_trivial,
have n / min_fac n < n := factors_lemma,
let ⟨a, b, c, d, h₁⟩ := show ∃ a b c d : ℤ, a^2 + b^2 + c^2 + d^2 = min_fac n,
  from or.cases_on hm.eq_two_or_odd
    (λ h2, h2.symm ▸ ⟨1, 1, 0, 0, rfl⟩)
    (odd_prime_sum_four_squares hm) in
let ⟨w, x, y, z, h₂⟩ := sum_four_squares (n / min_fac n) in
⟨(a * x - w * b + (d * y - z * c)).nat_abs,
 (a * y - w * c + (b * z - x * d)).nat_abs,
 (a * z - w * d + (c * x - y * b)).nat_abs,
 (a * w + b * x +  c * y + d * z).nat_abs,
  begin
    rw [← int.coe_nat_inj', ← nat.mul_div_cancel' (min_fac_dvd (k+2)), int.coe_nat_mul, ← h₁, ← h₂],
    simp [nat.pow_two, int.coe_nat_add, int.nat_abs_mul_self'],
    ring,
  end⟩

#print sum_four_squares
