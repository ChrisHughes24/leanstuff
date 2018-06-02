import data.int.modeq data.int.basic data.nat.modeq data.equiv data.fintype data.nat.prime data.nat.gcd data.pnat .int_gcd data.nat.prime

@[simp] lemma int.mod_mod (a b : ℤ) : a % b % b = a % b :=
by conv {to_rhs, rw [← int.mod_add_div a b, int.add_mul_mod_self_left]}

@[simp] lemma int.mod_neg_mod (a b : ℤ) : (-(a % b) % b) = (-a % b) :=
by conv {to_rhs, rw [← int.mod_add_div a b, neg_add, neg_mul_eq_mul_neg, int.add_mul_mod_self_left]}

open nat nat.modeq int

def Zmod := fin

namespace Zmod

--Copied from core, but marked as private in core
lemma mlt {n b : nat} : ∀ {a}, n > a → b % n < n
| 0     h := nat.mod_lt _ h
| (a+1) h :=
  have n > 0, from lt.trans (nat.zero_lt_succ _) h,
  nat.mod_lt _ this

class pos (n : ℕ) := (pos : 0 < n)

attribute [class] nat.prime

instance pos_of_prime (p : ℕ) [hp : nat.prime p] : pos p := ⟨hp.pos⟩

instance succ_pos (n : ℕ) : pos (nat.succ n) := ⟨succ_pos _⟩

def add_aux {n : ℕ} (a b : Zmod n) : Zmod n :=
⟨(a.1 + b.1) % n, mlt a.2⟩ 

def mul_aux {n : ℕ} (a b : Zmod n) : Zmod n :=
⟨(a.1 * b.1) % n, mlt a.2⟩

def neg_aux {n : ℕ} (a : Zmod n) : Zmod n :=
⟨nat_mod (-(a.1 : ℤ)) n, 
begin
  cases n with n,
  { exact (nat.not_lt_zero _ a.2).elim },
  { have h : (nat.succ n : ℤ) ≠ 0 := dec_trivial,
    rw [← int.coe_nat_lt, nat_mod, to_nat_of_nonneg (int.mod_nonneg _ h)],
    exact int.mod_lt _ h }
end⟩

instance (n : ℕ) : add_comm_semigroup (Zmod n) :=
{ add := add_aux,
  add_assoc := λ ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩, fin.eq_of_veq 
    (show ((a + b) % n + c) ≡ (a + (b + c) % n) [MOD n], 
    from calc ((a + b) % n + c) ≡ a + b + c [MOD n] : modeq_add (nat.mod_mod _ _) rfl
      ... ≡ a + (b + c) [MOD n] : by rw add_assoc
      ... ≡ (a + (b + c) % n) [MOD n] : modeq_add rfl (nat.mod_mod _ _).symm),
  add_comm := λ a b, fin.eq_of_veq (show (a.1 + b.1) % n = (b.1 + a.1) % n, by rw add_comm) }

instance (n : ℕ) : comm_semigroup (Zmod n) :=
{ mul := mul_aux,
  mul_assoc := λ ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩, fin.eq_of_veq
    (calc ((a * b) % n * c) ≡ a * b * c [MOD n] : modeq_mul (nat.mod_mod _ _) rfl
      ... ≡ a * (b * c) [MOD n] : by rw mul_assoc
      ... ≡ a * (b * c % n) [MOD n] : modeq_mul rfl (nat.mod_mod _ _).symm),
  mul_comm := λ a b, fin.eq_of_veq (show (a.1 * b.1) % n = (b.1 * a.1) % n, by rw mul_comm) }

def one_aux (n : ℕ) [h0 : pos n] : Zmod n := ⟨1 % n, nat.mod_lt _ h0.pos⟩

lemma one_mul_aux (n : ℕ) [h0 : pos n] : ∀ a : Zmod n, one_aux n * a = a := 
λ ⟨a, ha⟩, fin.eq_of_veq (show (1 % n * a) % n = a, 
begin
  resetI,
  clear _fun_match,
  cases n with n,
  { simp },
  { cases n with n,
    { rw [nat.mod_self, zero_mul];
      exact (nat.eq_zero_of_le_zero (le_of_lt_succ ha)).symm },
    { have h : 1 < n + 2 := dec_trivial,
      have ha : a < succ (succ n) := ha,
      rw [nat.mod_eq_of_lt h, one_mul, nat.mod_eq_of_lt ha] } }
end)

lemma left_distrib_aux (n : ℕ) : ∀ a b c : Zmod n, a * (b + c) = a * b + a * c :=
λ ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩, fin.eq_of_veq
(calc a * ((b + c) % n) ≡ a * (b + c) [MOD n] : modeq_mul rfl (nat.mod_mod _ _)
  ... ≡ a * b + a * c [MOD n] : by rw mul_add
  ... ≡ (a * b) % n + (a * c) % n [MOD n] : modeq_add (nat.mod_mod _ _).symm (nat.mod_mod _ _).symm)

instance (n : ℕ) : has_neg (Zmod n) := ⟨neg_aux⟩

instance (n : ℕ) : distrib (Zmod n) :=
{ left_distrib := left_distrib_aux n,
  right_distrib := λ a b c, by rw [mul_comm, left_distrib_aux, mul_comm _ b, mul_comm]; refl,
  ..Zmod.add_comm_semigroup n,
  ..Zmod.comm_semigroup n }

instance (n : ℕ) [h0 : pos n] : comm_ring (Zmod n) :=
{ zero := ⟨0, h0.pos⟩,
  zero_add := λ ⟨a, ha⟩, fin.eq_of_veq (show (0 + a) % n = a, by rw zero_add; exact nat.mod_eq_of_lt ha),
  add_zero := λ ⟨a, ha⟩, fin.eq_of_veq (nat.mod_eq_of_lt ha),
  neg := has_neg.neg,
  add_left_neg := 
    λ ⟨a, ha⟩, fin.eq_of_veq (show (((-a : ℤ) % n).to_nat + a) % n = 0,
      from int.coe_nat_inj
      begin
        have hn : (n : ℤ) ≠ 0 := (ne_of_lt (int.coe_nat_lt.2 h0.pos)).symm,
        rw [int.coe_nat_mod, int.coe_nat_add, to_nat_of_nonneg (int.mod_nonneg _ hn), add_comm],
        simp,
      end),
  one := ⟨1 % n, nat.mod_lt _ h0.pos⟩,
  one_mul := one_mul_aux n,
  mul_one := λ a, by rw mul_comm; exact one_mul_aux n a,
  ..Zmod.distrib n,
  ..Zmod.add_comm_semigroup n,
  ..Zmod.comm_semigroup n }

-- instance {n : ℕ+} : has_coe ℤ (Zmod n) := ⟨of_int n⟩

-- instance Zmod_coe_nat (n : ℕ+) : has_coe ℕ (Zmod n) := ⟨of_nat n⟩

-- @[simp] lemma coe_nat_coe_int (n : ℕ+) (a : ℕ) : (((a : ℕ) : ℤ) : Zmod n) = a :=
-- subtype.eq $ int.coe_nat_inj $ (show (nat_mod a n : ℤ)= a % n, by simp)

-- lemma coe_eq_of_nat {n : ℕ+} (a : ℕ) : (a : Zmod n) = of_nat n a := rfl

-- lemma coe_int_add (n : ℕ+) (a b : ℤ) : ((a + b : ℤ) : Zmod n) = a + b := 
-- subtype.eq (show nat_mod (a + b) n = (nat_mod a n + nat_mod b n) % n, 
--   from int.coe_nat_inj (by simp [int.coe_nat_add]))

-- lemma coe_int_mul (n : ℕ+) (a b : ℤ) : ((a * b : ℤ) : Zmod n) = a * b := 
-- subtype.eq (show nat_mod (a * b) n = (nat_mod a n * nat_mod b n) % n, 
--   from int.coe_nat_inj (begin
--     rw [coe_coe, nat_mod_coe_pnat, int.coe_nat_mod, int.coe_nat_mul, nat_mod_coe_pnat, nat_mod_coe_pnat],
--     exact int.modeq.modeq_mul (int.mod_mod _ _).symm (int.mod_mod _ _).symm
--   end))

-- lemma coe_int_neg (n : ℕ+) (a : ℤ) : ((-a : ℤ) : Zmod n) = -a := 
-- subtype.eq (show nat_mod (-a) n = nat_mod (-↑(nat_mod a n)) n,
-- from int.coe_nat_inj (by simp))

-- lemma coe_int_sub (n : ℕ+) (a b : ℤ) : ((a - b : ℤ) : Zmod n) = a - b := 
-- by rw [sub_eq_add_neg, coe_int_add, coe_int_neg, sub_eq_add_neg]

-- lemma coe_nat_add (n : ℕ+) (a b : ℕ) : ((a + b : ℕ) : Zmod n) = a + b := 
-- subtype.eq (modeq_add (nat.mod_mod _ _).symm (nat.mod_mod _ _).symm)

-- lemma coe_nat_mul (n : ℕ+) (a b : ℕ) : ((a * b : ℕ) : Zmod n) = a * b := 
-- subtype.eq (modeq_mul (nat.mod_mod _ _).symm (nat.mod_mod _ _).symm)

-- lemma coe_nat_sub (n : ℕ+) {a b : ℕ} (h : b ≤ a) : ((a - b : ℕ) : Zmod n) = a - b :=
-- by rw [← coe_nat_coe_int, int.coe_nat_sub h, coe_int_sub]; simp

-- @[simp] lemma coe_eq_zero' (n : ℕ+) : ((n : ℕ) : Zmod n) = 0 := 
-- subtype.eq (nat.mod_self _)

-- lemma eq_iff_modeq_nat {n : ℕ+} {a b : ℕ} : (a : Zmod n) = b ↔ a ≡ b [MOD n] := 
-- ⟨subtype.mk.inj, λ h, subtype.eq h⟩

-- @[simp] lemma val_coe {n : ℕ+} (a : Zmod n) : (a.val : Zmod n) = a := 
-- subtype.eq (nat.mod_eq_of_lt a.2)

-- lemma eq_iff_modeq_int {n : ℕ+} {a b : ℤ} : (a : Zmod n) = b ↔ a ≡ b [ZMOD n] :=
-- ⟨λ h, begin 
--   have := (int.coe_nat_eq_coe_nat_iff _ _).2 (subtype.mk.inj h),
--   rw [coe_coe, nat_mod_coe_pnat, nat_mod_coe_pnat] at this,
--   exact this
-- end,
-- λ h, subtype.eq (show nat_mod a n = nat_mod b n, from 
--   int.coe_nat_inj begin 
--   rw [coe_coe, nat_mod_coe_pnat, nat_mod_coe_pnat],
--   exact h
-- end)⟩

-- @[simp] lemma coe_int_mod (n : ℕ+) (a : ℤ) : ((a % ((n : ℕ) : ℤ) : ℤ) : Zmod n) = a :=
-- eq_iff_modeq_int.2 (int.mod_mod _ _)

-- @[simp] lemma coe_nat_mod (n : ℕ+) (a : ℕ) : ((a % n : ℕ) : Zmod n) = a :=
-- eq_iff_modeq_nat.2 (nat.mod_mod _ _)

-- @[simp] lemma coe_nat_zero (n : ℕ+) : ((0 : ℕ) : Zmod n) = 0 := 
-- subtype.eq (nat.zero_mod _)

-- @[simp] lemma coe_int_zero (n : ℕ+) : ((0 : ℤ) : Zmod n) = 0 :=
-- by rw [← int.coe_nat_zero, coe_nat_coe_int, coe_nat_zero]

-- @[simp] lemma coe_nat_one (n : ℕ+) : ((1 : ℕ) : Zmod n) = 1 := rfl

-- @[simp] lemma coe_int_one (n : ℕ+) : ((1 : ℤ) : Zmod n) = 1 := rfl 

-- @[simp] lemma coe_nat_bit0 (n : ℕ+) (a : ℕ) : ((bit0 a : ℕ) : Zmod n) = bit0 (a : Zmod n) := coe_nat_add _ _ _

-- @[simp] lemma coe_nat_bit1 (n : ℕ+) (a : ℕ) : ((bit1 a : ℕ) : Zmod n) = bit1 (a : Zmod n) :=
-- by rw [bit1, bit1, coe_nat_add, coe_nat_bit0, coe_nat_one]

-- @[simp] lemma coe_int_bit0 (n : ℕ+) (a : ℤ) : ((bit0 a : ℤ) : Zmod n) = bit0 (a : Zmod n) := coe_int_add _ _ _

-- @[simp] lemma coe_int_bit1 (n : ℕ+) (a : ℤ) : ((bit1 a : ℤ) : Zmod n) = bit1 (a : Zmod n) :=
-- by rw [bit1, bit1, coe_int_add, coe_int_bit0, coe_int_one]

@[simp] lemma val_zero (n : ℕ) [h0 : pos n] : (0 : Zmod n).val = 0 := rfl

@[simp] lemma cast_val {n : ℕ} [h0 : pos n] (a : ℕ) : (a : Zmod n).val = a % n :=
begin
  induction a with a ih,
  { rw [nat.zero_mod]; refl },
  { show ((a : Zmod n).val + 1 % n) % n = (a + 1) % n, 
    rw ih,
    exact nat.modeq.modeq_add (nat.mod_mod _ _) (nat.mod_mod _ _) }
end 

@[simp] lemma eq_zero (n : ℕ) [h0 : pos n] : (n : Zmod n) = 0 :=
fin.eq_of_veq (show (n : Zmod n).val = 0, by simp [cast_val])

@[simp] lemma cast_nat_mod (n : ℕ) [h0 : pos n] (a : ℕ) : ((a % n : ℕ) : Zmod n) = a :=
fin.eq_of_veq (show ((a % n : ℕ) : Zmod n).val = (a : Zmod n).val, by simp)

instance (n : ℕ) : fintype (Zmod n) := fin.fintype _

lemma card_Zmod : ∀ n, fintype.card (Zmod n) = n := fintype.card_fin

-- @[simp] lemma cast_int_mod (n : ℕ) [h0 : pos n] (a : ℤ) : ((a % n : ℤ) : Zmod n) = a :=
-- begin
  
-- end

-- lemma eq_zero_iff_dvd_nat (n : ℕ) [h0 : pos n] (a : ℕ) : (a : Zmod n) = 0 ↔ (n : ℕ) ∣ a := 
-- ⟨begin end, sorry⟩

-- lemma eq_zero_iff_dvd_int (n : ℕ) [h0 : pos n] (a : ℤ) : (a : Zmod n) = 0 ↔ (n : ℤ) ∣ a :=
-- ⟨λ h, int.modeq.modeq_zero_iff.1 (eq_iff_modeq_int.1 (by  rw [h, coe_int_zero])),
-- λ h, by rwa [← int.modeq.modeq_zero_iff, ← eq_iff_modeq_int, coe_int_zero] at h⟩


-- def equiv_fin (n : ℕ) : Zmod n ≃ fin (nat_abs n) :=
-- { to_fun := λ ⟨a, h⟩, ⟨a, h⟩,
--   inv_fun := λ ⟨a, h⟩, ⟨a, h⟩,
--   left_inv := λ ⟨_, _⟩, rfl,
--   right_inv := λ ⟨_, _⟩, rfl }

-- instance (n : ℕ) : fintype (Zmod n) :=
-- fintype.of_equiv _ (equiv_fin n).symm

-- lemma card_Zmod {n : ℕ} : fintype.card (Zmod n) = n :=
-- eq.trans (fintype.card_congr (equiv_fin n)) (fintype.card_fin _)

-- private def inv_aux {n : ℕ+} (a : Zmod n) : Zmod n := gcd_a a.1 n

-- instance (n : ℕ+) : has_inv (Zmod n) := ⟨inv_aux⟩

-- @[simp] lemma int.gcd_neg (a b : ℤ) : int.gcd (-a) b = int.gcd a b :=
-- by unfold int.gcd; rw nat_abs_neg

-- lemma gcd_a_modeq (a b : ℕ) : (a : ℤ) * gcd_a a b ≡ nat.gcd a b [ZMOD b] :=
-- by rw [← add_zero ((a : ℤ) * _), gcd_eq_gcd_ab];
--   exact int.modeq.modeq_add rfl (int.modeq.modeq_zero_iff.2 (dvd_mul_right _ _)).symm

-- lemma mul_inv_eq_gcd_nat (n : ℕ+) (a : ℕ) : (a : Zmod n) * a⁻¹ = nat.gcd a n :=
-- eq_iff_modeq_nat.2 $ int.modeq.coe_nat_modeq_iff.1
--   (calc ((a % n * nat_mod (gcd_a (a % n) n) ↑n : ℕ) : ℤ) ≡ (a % n : ℕ) * gcd_a (a % n) n [ZMOD n] : 
--     by rw [coe_coe, int.coe_nat_mul, nat_mod_coe_pnat]; exact int.modeq.modeq_mul rfl (int.mod_mod _ _)
--   ... ≡ nat.gcd (a % n) n [ZMOD n] : gcd_a_modeq _ _
--   ... = (nat.gcd a n : ℤ) : by rw [← gcd_rec, nat.gcd_comm])

-- lemma mul_inv_eq_gcd_int (n : ℕ+) (a : ℤ) : (a : Zmod n) * a⁻¹ = int.gcd a n :=
-- have h : ((n : ℕ) : ℤ) ≠ 0 := (ne_of_lt (int.coe_nat_lt.2 n.2)).symm,
-- begin
--   rw [int.gcd_comm, ← int.gcd_mod, int.gcd, coe_coe, nat_abs_of_nat, ← mul_inv_eq_gcd_nat,
--     ← coe_nat_coe_int _ (nat_abs _), nat_abs_of_nonneg (mod_nonneg _ h)],
--   simp,
-- end

-- private lemma mul_inv_cancel_aux {p : {n : ℕ+ // nat.prime n.1}} (a : Zmod (p : ℕ+)) (ha : a ≠ 0) : a * a⁻¹ = 1 := 
-- begin
--   rw [← val_coe a, ne.def, eq_zero_iff_dvd_nat] at ha,
--   have : coprime ((p : ℕ+) : ℕ) a.val := p.2.coprime_iff_not_dvd.2 ha,
--   rw [← val_coe a, mul_inv_eq_gcd_nat, nat.gcd_comm, coprime.gcd_eq_one this],
--   refl,
-- end

-- instance Zmod_prime_field (p : {n : ℕ+ // nat.prime n.1}) : field (Zmod (p : ℕ+)) :=
-- { inv := has_inv.inv,
--   zero_ne_one := λ h, begin 
--     have : 0 = 1 % p.1.1 := subtype.mk.inj h,
--     rw nat.mod_eq_of_lt (p.2.gt_one) at this,
--     exact nat.no_confusion this,
--   end,
--   mul_inv_cancel := mul_inv_cancel_aux,
--   inv_mul_cancel := λ a ha, by rw mul_comm; exact mul_inv_cancel_aux a ha,
--   ..Zmod.comm_ring p.1 }

end Zmod
