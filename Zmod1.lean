import .lagrange_four_square tactic.ring data.set.finite .int_gcd data.int.modeq data.int.basic data.nat.modeq data.equiv data.fintype data.nat.prime data.nat.gcd tactic.norm_num group_theory.order_of_element
universe u
local attribute [instance, priority 0] classical.prop_decidable

open int int.modeq
@[reducible]
def Z_aux (n : ℤ) : Type := ℤ

instance Zmod_setoid {n : ℤ} : setoid (Z_aux n) :=
{ r := int.modeq n,
  iseqv := ⟨int.modeq.refl, @int.modeq.symm n, @int.modeq.trans n⟩ }

def Zmod (n : ℤ) : Type := quotient (@Zmod_setoid n)

lemma setoid_eq {α : Type*} : ∀ {a b : setoid α}, a.r = b.r → a = b
| ⟨ar, ha⟩ ⟨br, hb⟩ rfl := rfl

lemma Zmod_eq_Zmod_neg (n : ℤ) : Zmod n = (Zmod (-n)) :=
by unfold Zmod Zmod_setoid; exact 
congr rfl (setoid_eq (begin 
  funext,
  unfold setoid.r int.modeq,
  rw [← int.mod_abs _ (- _), ← int.mod_abs _ (- _), abs_neg, ← int.mod_abs _ n, ← int.mod_abs _ n],
end))

namespace Zmod

private def add_aux {n : ℤ} (a b : Zmod n) : Zmod n :=
quotient.lift_on₂ a b (λ a b, ⟦a + b⟧) (λ a b c d hac hbd, quotient.sound (modeq_add hac hbd))

private def mul_aux {n : ℤ} (a b : Zmod n) : Zmod n :=
quotient.lift_on₂ a b (λ a b, ⟦a * b⟧) (λ a b c d hac hbd, quotient.sound (modeq_mul hac hbd))

private def neg_aux {n : ℤ} (a : Zmod n) : Zmod n :=
quotient.lift_on a (λ a, ⟦-a⟧) (λ a b hab, quotient.sound (modeq_neg hab))

instance (n : ℤ) : comm_ring (Zmod n) :=
{ add := add_aux,
  add_assoc := λ a b c, quotient.induction_on₃ a b c (λ a b c, quotient.sound (by rw add_assoc)),
  zero := ⟦0⟧,
  zero_add := λ a, quotient.induction_on a (λ a, quotient.sound (by rw zero_add)),
  add_zero := λ a, quotient.induction_on a (λ a, quotient.sound (by rw add_zero)),
  neg := neg_aux,
  add_left_neg := λ a, quotient.induction_on a (λ a, quotient.sound (by rw add_left_neg)),
  add_comm := λ a b, quotient.induction_on₂ a b (λ a b, quotient.sound (by rw add_comm)),
  mul := mul_aux,
  mul_assoc := λ a b c, quotient.induction_on₃ a b c (λ a b c, quotient.sound (by rw mul_assoc)),
  one := ⟦1⟧,
  one_mul := λ a, quotient.induction_on a (λ a, quotient.sound (by rw one_mul)),
  mul_one := λ a, quotient.induction_on a (λ a, quotient.sound (by rw mul_one)),
  left_distrib := λ a b c, quotient.induction_on₃ a b c (λ a b c, quotient.sound (by rw left_distrib)),
  right_distrib := λ a b c, quotient.induction_on₃ a b c (λ a b c, quotient.sound (by rw right_distrib)),
  mul_comm := λ a b, quotient.induction_on₂ a b (λ a b, quotient.sound (by rw mul_comm)) }

instance (n : ℤ) : has_coe ℤ (Zmod n) := ⟨quotient.mk⟩

instance Zmod_coe_nat (n : ℤ) : has_coe ℕ (Zmod n) := ⟨quotient.mk ∘ coe⟩

@[simp] lemma coe_nat_coe_int (n : ℤ) (a : ℕ) : (((a : ℕ) : ℤ) : Zmod n) = (a : Zmod n) := rfl

@[simp] lemma mk_eq_coe (n a : ℤ) : (⟦a⟧ : Zmod n) = (a : Zmod n) := rfl

@[simp] lemma coe_int_zero (n : ℤ) : ((0 : ℤ) : Zmod n) = 0 := rfl

@[simp] lemma coe_int_one (n : ℤ) :  ((1 : ℤ) : Zmod n) = 1 := rfl

@[simp] lemma coe_int_bit0 (n a : ℤ) : ((bit0 a : ℤ) : Zmod n) = bit0 (a : Zmod n) := rfl

@[simp] lemma coe_int_bit1 (n a : ℤ) : ((bit1 a : ℤ) : Zmod n) = bit1 (a : Zmod n) := rfl

lemma coe_int_add (a b n : ℤ) : ((a + b : ℤ) : Zmod n) = a + b := rfl

lemma coe_int_mul (a b n : ℤ) : ((a * b : ℤ) : Zmod n) = a * b := rfl

lemma coe_int_neg (a n : ℤ) : ((-a : ℤ) : Zmod n) = -a := rfl

@[simp] lemma coe_int_mod (a n : ℤ) : ((a % n : ℤ) : Zmod n) = a := quotient.sound (int.mod_mod _ _)

lemma coe_int_pow (a n : ℤ) (k : ℕ) : ((a ^ k : ℤ) : Zmod n) = a ^ k := 
by induction k; simp [pow_succ, *, coe_int_mul]

lemma coe_int_sub (a b n : ℤ) : ((a - b : ℤ) : Zmod n) = a - b := rfl

@[simp] lemma coe_nat_zero (n : ℤ) : ((0 : ℕ) : Zmod n) = 0 := rfl

@[simp] lemma coe_nat_one (n : ℤ) :  ((1 : ℕ) : Zmod n) = 1 := rfl

@[simp] lemma coe_nat_bit0 (n : ℤ) (a : ℕ) : ((bit0 a : ℕ) : Zmod n) = bit0 (a : Zmod n) := rfl

@[simp] lemma coe_nat_bit1 (n : ℤ) (a : ℕ) : ((bit1 a : ℕ) : Zmod n) = bit1 (a : Zmod n) := rfl

lemma coe_nat_add (a b : ℕ) (n : ℤ) : ((a + b : ℕ) : Zmod n) = a + b := rfl

lemma coe_nat_mul (a b : ℕ) (n : ℤ) : ((a * b : ℕ) : Zmod n) = a * b := rfl

lemma eq_iff_modeq_nat {n : ℤ} {a b : ℕ} : a ≡ b [MOD n.nat_abs] ↔ (a : Zmod n) = (b : Zmod n) :=
⟨λ h, quotient.sound (int.modeq.modeq_iff_dvd.2 (int.nat_abs_dvd.1 (nat.modeq.modeq_iff_dvd.1 h))),
λ h, nat.modeq.modeq_iff_dvd.2 (int.nat_abs_dvd.2 (int.modeq.modeq_iff_dvd.1 (quotient.exact h)))⟩

lemma eq_iff_modeq_int {n a b : ℤ} : a ≡ b [ZMOD n] ↔ (a : Zmod n) = b :=
⟨λ h, quotient.sound h, λ h, quotient.exact h⟩

@[simp] lemma coe_nat_mod (a n : ℕ) : ((a % n : ℕ) : Zmod n) = a := eq_iff_modeq_nat.1 (nat.mod_mod _ _)

lemma coe_nat_sub {a b : ℕ} (n : ℤ) (h : b ≤ a) : ((a - b : ℕ) : Zmod n) = a - b :=
show (((a - b : ℕ) : ℤ) : Zmod n) = a - b, by rw int.coe_nat_sub h; refl

def to_nat {n : ℤ} (a : Zmod n) : ℕ :=
quotient.lift_on a (λ a, nat_abs (a % n)) 
  (λ a b (hab : _ = _), or.cases_on (classical.em (n = 0)) 
    (λ hn, by simp * at *)
    (λ hn, int.coe_nat_inj 
      (by simpa [int.nat_abs_of_nonneg (mod_nonneg a hn), 
        int.nat_abs_of_nonneg (mod_nonneg b hn)])))

lemma to_nat_lt {n : ℤ} (hn : n ≠ 0) (a : Zmod n) : a.to_nat < n.nat_abs :=
quotient.induction_on a (λ a, show (a % n).nat_abs < n.nat_abs, 
    from int.coe_nat_lt.1 
      (by rw [int.nat_abs_of_nonneg (mod_nonneg a hn), ← abs_eq_nat_abs];
        exact mod_lt _ hn))

@[simp] lemma coe_to_nat {n : ℤ} (hn : n ≠ 0) (a : Zmod n) : (a.to_nat : Zmod n) = a :=
quotient.induction_on a (λ a : ℤ, show (((a % n).nat_abs : ℤ) : Zmod n) = a, 
  by rw [nat_abs_of_nonneg (mod_nonneg _ hn), coe_int_mod])

def equiv_fin {n : ℤ} (hn : n ≠ 0) : Zmod n ≃ fin (nat_abs n) :=
{ to_fun := λ a, ⟨a.to_nat, to_nat_lt hn a⟩,
  inv_fun := λ a, ⟦a.1⟧,
  left_inv := λ a, quotient.induction_on a (λ a, quotient.sound 
    (show ↑(a % n).nat_abs % n = _, 
      by rw nat_abs_of_nonneg (mod_nonneg a hn);
        exact int.mod_mod _ _)),
  right_inv := λ ⟨a, ha⟩,
    have ha' : (a : ℤ) < abs n := (abs_eq_nat_abs n).symm ▸ int.coe_nat_lt.2 ha,
    fin.eq_of_veq (show ((a : ℤ) % n).to_nat = a, 
      from int.coe_nat_inj 
        (by rw [to_nat_of_nonneg (mod_nonneg a hn), ← mod_abs];
          exact mod_eq_of_lt (int.coe_nat_le.2 (nat.zero_le a)) ha')) }

def Zmod_fintype {n : ℤ} (hn : n ≠ 0) : fintype (Zmod n) :=
fintype.of_equiv _ (equiv_fin hn).symm

lemma card_Zmod {n : ℤ} (hn : n ≠ 0) : @fintype.card (Zmod n) (Zmod_fintype hn) = n.nat_abs :=
fintype.card_fin n.nat_abs ▸ @fintype.card_congr _ _ (Zmod_fintype hn) _ (equiv_fin hn)

private def inv_aux {n : ℤ} (a : Zmod n) : Zmod n := 
quotient.lift_on a (λ a, (⟦(nat.gcd_a (a % n).nat_abs n.nat_abs : ℤ)⟧ : Zmod n)) 
  (λ a b (hab : _ = _),
     by unfold nat_mod; rw hab)

instance (n : ℤ) : has_inv (Zmod n) := ⟨inv_aux⟩

@[simp] lemma int.gcd_neg (a b : ℤ) : gcd (-a) b = gcd a b :=
by unfold gcd; rw nat_abs_neg

lemma gcd_a_modeq (a b : ℕ) : (a : ℤ) * nat.gcd_a a b ≡ nat.gcd a b [ZMOD b] :=
by rw [← add_zero ((a : ℤ) * _), nat.gcd_eq_gcd_ab];
  exact int.modeq.modeq_add rfl (int.modeq.modeq_zero_iff.2 (dvd_mul_right _ _)).symm

lemma mul_inv_eq_gcd_nat (n a : ℕ) : (a : Zmod n) * a⁻¹ = nat.gcd a n :=
show (a :  Zmod n) * (nat.gcd_a (a % n) n) = nat.gcd a n, from
by rw [nat.gcd_comm, nat.gcd_rec, ← coe_nat_coe_int _ (nat.gcd _ _), ← eq_iff_modeq_int.1 (gcd_a_modeq _ _),
    coe_int_mul, coe_nat_coe_int, coe_nat_mod]
 
lemma mul_inv_eq_gcd_int (n a : ℤ) (hn : n ≠ 0) : (a : Zmod n) * a⁻¹ = int.gcd a n :=
have ha : (a : Zmod n) = (a % n.nat_abs).nat_abs :=
  by rw [← coe_nat_coe_int, ← abs_eq_nat_abs n, mod_abs,
    int.nat_abs_of_nonneg (int.mod_nonneg _ hn), coe_int_mod],
have h : ∀ a : ℕ, (a : ℤ) * nat.gcd_a a n.nat_abs ≡ nat.gcd a n.nat_abs [ZMOD n] :=λ a,
begin 
  unfold int.modeq,
  rw [← mod_abs _ n, ← mod_abs _ n, abs_eq_nat_abs],
  exact gcd_a_modeq _ _,
end,
show (a :  Zmod n) * (nat.gcd_a (a % n).nat_abs n.nat_abs) = int.gcd a n,
begin 
  rw [ha, gcd_comm, ← int.gcd_mod, int.gcd, ← mod_abs _ n, abs_eq_nat_abs, ← coe_nat_coe_int _ (nat.gcd _ _),
    ← eq_iff_modeq_int.1 (h _)],
  refl,
end

private lemma mul_inv_cancel_aux {p : ℕ} (hp : nat.prime p) {a : Zmod p} : a ≠ 0 →
    a * a⁻¹ = (1 : Zmod p) := 
quotient.induction_on a (λ (a : ℤ) ha, begin
  rw [mk_eq_coe, ne.def, ← coe_int_zero, ← eq_iff_modeq_int, modeq_zero_iff, 
    ← dvd_nat_abs, ← nat_abs_dvd, int.coe_nat_dvd] at ha,
  have : gcd p a = 1 := hp.coprime_iff_not_dvd.2 ha,
  rw [mk_eq_coe, mul_inv_eq_gcd_int _ _ (ne_of_lt (int.coe_nat_lt.2 hp.pos)).symm, gcd_comm, this, coe_nat_one],
end)

def Zmod_prime_field {p : ℕ} (hp : nat.prime p) : discrete_field (Zmod p) :=
{ inv := has_inv.inv,
  zero_ne_one := λ h, 
    let h : (0 : ℤ) % p = 1 % p := quotient.exact h in
    begin 
      rw mod_eq_of_lt (le_refl (0 : ℤ)) (int.coe_nat_lt.2 hp.pos) at h, 
      rw mod_eq_of_lt (show (0 : ℤ) ≤ 1, by norm_num) (int.coe_nat_lt.2 hp.gt_one) at h,
      exact absurd h dec_trivial,
    end,
  mul_inv_cancel := λ a ha, mul_inv_cancel_aux hp ha,
  inv_mul_cancel := λ a ha, by rw mul_comm; exact mul_inv_cancel_aux hp ha,
  has_decidable_eq := by apply_instance,
  inv_zero := 
    show ((nat.xgcd_aux (nat_abs (0 % p)) 1 0 p 0 1).2.1 : Zmod p) = 0,
    begin
      rw zero_mod,
      change nat_abs 0 with 0,
      rw nat.xgcd_zero_left,
      refl,
    end,
  ..Zmod.comm_ring p }

instance (p : {p // nat.prime p}) : discrete_field (Zmod p) := Zmod_prime_field p.2

instance (p : {p // nat.prime p}) : fintype (Zmod p) := Zmod_fintype (ne_of_lt (int.coe_nat_lt.2 p.2.pos)).symm

noncomputable lemma fintype.of_injective {α β : Type*} [fintype α] (f : β → α) 
  (hf : function.injective f) : fintype β :=
by haveI := classical.dec_eq β; exact
classical.choice (or.cases_on (classical.em (nonempty β))
(λ h, by haveI : inhabited β := ⟨classical.choice h⟩; exact
⟨fintype.of_surjective (function.inv_fun f) (function.inv_fun_surjective hf)⟩) 
(λ h, ⟨⟨∅, λ x, false.elim (h ⟨x⟩)⟩⟩))

noncomputable instance fintype_units {α : Type*} [fintype α] [monoid α] : fintype (units α) :=
fintype.of_injective units.val (λ x y h, units.ext h)

lemma fintype.card_pos {α : Type*} [fintype α] (a : α) : 0 < fintype.card α := 
nat.pos_of_ne_zero (λ h, begin 
  have : α ≃ fin 0 := eq.rec_on h (trunc.out (fintype.equiv_fin α)),
  exact fin.elim0 (this.1 a),
end)

def units_equiv_ne_zero (p : {p // nat.prime p}) : units (Zmod p) ≃ {a : Zmod p // a ≠ 0} :=
{ to_fun := λ ⟨a, b, h₁, h₂⟩, ⟨a, λ h, by rw [h, zero_mul] at h₁; exact zero_ne_one h₁⟩,
  inv_fun := λ ⟨a, ha⟩, ⟨a, a⁻¹, mul_inv_cancel ha, inv_mul_cancel ha⟩,
  left_inv := λ ⟨a, b, h₁, h₂⟩, 
    have ha : a ≠ 0 := λ h, by rw [h, zero_mul] at h₁; exact zero_ne_one h₁,
    suffices h : a⁻¹ = b, by simp! [h],
      by rw [← one_mul (a⁻¹), ← h₂, mul_assoc, mul_inv_cancel ha, mul_one],
  right_inv := λ ⟨a, ha⟩, rfl }

def equiv_univ (α : Type*) : α ≃ @set.univ α := ⟨λ x, ⟨x, trivial⟩, λ x, x.1, λ _, rfl, λ ⟨_, _⟩, rfl⟩

lemma fintype.card_ne {α : Type u} [fintype α] [decidable_eq α] (a : α) : 
  @fintype.card {b | b ≠ a} (set_fintype {b | b ≠ a}) = fintype.card α - 1 :=
begin
  haveI := set_fintype {b | b ≠ a},
  haveI := set_fintype (@set.univ α),
  haveI := classical.prop_decidable,
  have ha : a ∉ {b : α | b ≠ a} := by simp [set.mem_def],
  have h2 : 1 ≤ fintype.card (@set.univ α) := fintype.card_pos ⟨a, trivial⟩,
  rw [fintype.card_congr  (equiv_univ α), eq_comm,
    nat.sub_eq_iff_eq_add, ← @set.card_insert _ _ a],
  simp [set.insert, classical.em],
  congr,
  assumption,
  assumption,
end

lemma card_units_prime {p : {p // nat.prime p}} : @fintype.card (units (Zmod p)) 
  (@Zmod.fintype_units _ (Zmod_fintype (ne_of_lt (int.coe_nat_lt.2 p.2.pos)).symm) _) = p - 1 :=
begin
  change (p : ℕ) with ((p : ℤ).nat_abs),
  rw [← card_Zmod (show (p : ℤ) ≠ 0, from (ne_of_lt (int.coe_nat_lt.2 p.2.pos)).symm), 
    fintype.card_congr (units_equiv_ne_zero _), ← fintype.card_ne (0 : Zmod p)],
  refl,
end

lemma units.pow_coe {α : Type*} [monoid α] {a : units α} {n : ℕ} : ((a ^ n : units α ) : α) = (a : α) ^ n :=
by induction n; simp [pow_succ, *]

lemma fermat_little {p : {p // nat.prime p}} {a : Zmod p}
  (ha : a ≠ 0) : a ^ ((p : ℕ) - 1) = 1 :=
begin
  have := units.val_coe (units.mk0 _ ha),
  change (a : Zmod p) with ((units.mk0 _ ha).1 : Zmod p),
  rw [← units.val_coe, ← units.pow_coe, ← card_units_prime, pow_eq_mod_order_of,
    nat.mod_eq_zero_of_dvd (order_of_dvd_card_univ )],
  simp
end

lemma odd_sub_one_even {n : ℕ} (ho : n % 2 = 1) : 2 ∣ n - 1 := 
begin
  rw [← nat.mod_add_div n 2, ho, nat.add_sub_cancel_left],
  exact dvd_mul_right _ _
end

lemma pow_half_prime_sub_one_eq_one_or_neg_one {p : {p // nat.prime p}} (hpo : (p : ℕ) % 2 = 1) {a : Zmod p}
  (ha : a ≠ 0) : a ^ (((p : ℕ) - 1) / 2) = 1 ∨ a ^ (((p : ℕ) - 1) / 2) = -1 :=
begin
  have := fermat_little ha, 
  rw [← nat.mul_div_cancel' (odd_sub_one_even hpo), pow_mul, pow_two, mul_pow] at this,
  exact (mul_self_eq_one_iff _).1 this
end

instance units_comm (α : Type*) [comm_monoid α] : comm_group (units α) :=
{ mul_comm := λ a b, units.ext 
    (show ((a * b : units α) : α) = ((b * a : units α) : α), 
      by simp [units.mul_coe, mul_comm]),
  ..units.group }

open finset

lemma int.coe_nat_ne_zero_of_pos {n : ℕ} : 0 < n → (n : ℤ) ≠ 0 :=
ne.symm ∘ ne_of_lt ∘ int.coe_nat_lt.2

lemma prod_finset_distinct_inv {α : Type*} [discrete_field α] {s : finset α} :
  (∀ x ∈ s, x⁻¹ ∈ s) → (∀ x ∈ s, x⁻¹ ≠ x) → s.prod id = 1 :=
finset.strong_induction_on s $ λ s ih h₁ h₂, or.cases_on (classical.em (s = ∅))
  (λ h, by simp [h])
  (λ h, have h0 : ∀ (y : α), y ∈ s → y ≠ 0 := λ y hy h,
    (show (0 : α)⁻¹ ≠ 0, from h ▸ (h₂ y hy)) (by simp),
  let ⟨x, hx⟩ := exists_mem_of_ne_empty h in
  have hxi : x⁻¹ ∈ s.erase x := mem_erase.2 ⟨h₂ x hx, h₁ x hx⟩,
  have ht : erase (erase s x) x⁻¹ ⊂ s := lt_iff_ssubset.1 (lt.trans (erase_ssubset hxi) (erase_ssubset hx)),
  have ht₁ : ∀ y ∈ erase (erase s x) x⁻¹, y⁻¹ ∈ erase (erase s x) x⁻¹ := 
    λ y hy, by rw [mem_erase, mem_erase] at *;
      exact ⟨λ h, hy.2.1 (begin 
        rw [inv_eq_one_div, inv_eq_one_div, div_eq_div_iff (h0 y hy.2.2) (h0 x hx), one_mul, one_mul] at h,
        exact h.symm,
      end), λ h, hy.1 (by rw[← h, inv_eq_one_div, inv_eq_one_div, one_div_div, div_one]), h₁ y hy.2.2⟩,
  have ht₂ : ∀ y ∈ erase (erase s x) x⁻¹, y⁻¹ ≠ y := λ y hy, 
    by rw [mem_erase, mem_erase] at hy;
    exact h₂ y hy.2.2,
  begin
    rw [← insert_erase hx, prod_insert (not_mem_erase _ _), ← insert_erase hxi,
      prod_insert (not_mem_erase _ _), ih _ ht ht₁ ht₂],
    simp [mul_inv_cancel (h0 x hx)],
  end)

lemma ne_neg {n : ℕ} (ho : n % 2 = 1) {a : Zmod n} (ha : a ≠ 0) : a ≠ -a :=
have hn : (n : ℤ) ≠ 0 := λ h, by rw int.coe_nat_inj h at ho; contradiction,
begin
  rw [← coe_to_nat hn a, ne.def, eq_neg_iff_add_eq_zero, ← coe_nat_add, ← coe_nat_zero,
    ← eq_iff_modeq_nat, nat.modeq.modeq_zero_iff, nat_abs_of_nat],
  refine not_exists.2 (λ x h, _),
  rw ← mul_two at h,
  have : to_nat a * 2 < n * 2 := (mul_lt_mul_right (show 2 > 0, from dec_trivial)).2 
    (to_nat_lt hn _),
  rw h at this,
  cases x,
  { rw mul_zero at h,
    have := or.resolve_right (nat.eq_zero_of_mul_eq_zero h) dec_trivial,
    rw [← coe_to_nat hn a, this] at ha,
    contradiction },
  { cases x,
    { rw mul_one at h,
      rw [← h, nat.mul_mod_left] at ho,
      contradiction },
    { exact absurd (lt_of_mul_lt_mul_left this (nat.zero_le _)) dec_trivial } }
end

lemma wilson_lemma {p : {p // nat.prime p}} (hpo : (p : ℕ) % 2 = 1) : 
  ((univ : finset (Zmod p)).erase 0).prod id = -1 :=
have h10 : (1 : Zmod p) ≠ 0 := by rw [← coe_nat_one, ← coe_nat_zero, ne.def, 
      ← eq_iff_modeq_nat, nat.modeq.modeq_zero_iff]; exact p.2.not_dvd_one,
have h₁ : (1 : Zmod p) ∈ univ.erase (0 : Zmod p) := mem_erase.2 ⟨h10, mem_univ _⟩,
have h₂ : (-1 : Zmod p) ∈ (erase (erase univ (0 : Zmod p)) 1) :=
  mem_erase.2 ⟨ne.symm (ne_neg hpo h10), 
    mem_erase.2 ⟨(by rw [ne.def, neg_eq_iff_neg_eq, neg_zero]; exact h10.symm),
      mem_univ _⟩⟩,
have h₃ : ∀ (x : Zmod ↑p), x ∈ erase (erase (erase univ (0 : Zmod p)) 1) (-1) → 
    x⁻¹ ∈ erase (erase (erase univ (0 : Zmod p)) 1) (-1) := λ x hx, begin
  rw [mem_erase, mem_erase, mem_erase] at *,
  rw [ne.def, ne.def, ne.def, inv_eq_one_div, div_eq_iff_mul_eq hx.2.2.1, div_eq_iff_mul_eq hx.2.2.1, 
    div_eq_iff_mul_eq hx.2.2.1, neg_mul_comm, one_mul, one_mul, zero_mul, neg_eq_iff_neg_eq],
  exact ⟨hx.1.symm, hx.2.1, h₁.1.symm, mem_univ _⟩,
end,
have h₄ : ∀ (x : Zmod ↑p), x ∈ erase (erase (erase univ (0 : Zmod p)) 1) (-1) → x⁻¹ ≠ x := λ x hx, begin
  rw [mem_erase, mem_erase, mem_erase] at hx,
  rw [ne.def, inv_eq_one_div, div_eq_iff_mul_eq hx.2.2.1, mul_self_eq_one_iff, not_or_distrib],
  exact ⟨hx.2.1, hx.1⟩
end,
begin
  rw [← insert_erase h₁, prod_insert (not_mem_erase _ _), ← insert_erase h₂, 
    prod_insert (not_mem_erase _ _), prod_finset_distinct_inv h₃ h₄],
  simp,
end

lemma euler_criterion {p : {p // nat.prime p}} (hpo : (p : ℕ) % 2 = 1) {a : units (Zmod p)}
  : (∃ x, x * x = a) ↔ a ^ (((p : ℕ) - 1) / 2) = 1 :=
have h₁ : {b : units (Zmod p) | ∃ x, x * x = b} ⊆ {b | b ^ (((p : ℕ) - 1) / 2) = 1} :=
λ b ⟨x, hx⟩,
show b ^ (((p : ℕ) - 1) / 2) = 1,
begin
  rw [← hx, ← pow_two, ← pow_mul, nat.mul_div_cancel' (odd_sub_one_even hpo)],
  exact fermat_little hx0,
end,
begin



end

#eval ((12345 : Zmod 145975)⁻¹).to_nat
#eval 12345 * 3169 % 145975
end Zmod
