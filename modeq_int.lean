/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import data.int.basic data.nat.modeq

namespace int

def modeq (n a b : ℤ) := a % n = b % n

notation a ` ≡ `:50 b ` [ZMOD `:50 n `]`:0 := modeq n a b

namespace modeq
variables {n m a b c d : ℤ}

@[refl] protected theorem refl (a : ℤ) : a ≡ a [ZMOD n] := @rfl _ _

@[symm] protected theorem symm : a ≡ b [ZMOD n] → b ≡ a [ZMOD n] := eq.symm

@[trans] protected theorem trans : a ≡ b [ZMOD n] → b ≡ c [ZMOD n] → a ≡ c [ZMOD n] := eq.trans

lemma coe_nat_modeq_iff (a b n : ℕ) : a ≡ b [ZMOD n] ↔ a ≡ b [MOD n] :=
by unfold modeq nat.modeq; rw ← int.coe_nat_eq_coe_nat_iff; simp [int.coe_nat_mod]

instance : decidable (a ≡ b [ZMOD n]) := by unfold modeq; apply_instance

theorem modeq_zero_iff : a ≡ 0 [ZMOD n] ↔ n ∣ a :=
by rw [modeq, zero_mod, dvd_iff_mod_eq_zero]

theorem modeq_iff_dvd : a ≡ b [ZMOD n] ↔ (n:ℤ) ∣ b - a :=
by rw [modeq, eq_comm];
   simp [int.mod_eq_mod_iff_mod_sub_eq_zero, int.dvd_iff_mod_eq_zero]

theorem modeq_of_dvd_of_modeq (d : m ∣ n) (h : a ≡ b [ZMOD n]) : a ≡ b [ZMOD m] :=
modeq_iff_dvd.2 $ dvd_trans d (modeq_iff_dvd.1 h)

theorem modeq_mul_left' (hc : 0 ≤ c) (h : a ≡ b [ZMOD n]) : c * a ≡ c * b [ZMOD (c * n)] :=
or.cases_on (lt_or_eq_of_le hc) (λ hc, 
  by unfold modeq;
  simp [mul_mod_mul_of_pos _ _ hc, (show _ = _, from h)] ) 
(λ hc, by simp [hc.symm])

theorem modeq_mul_right' (hc : 0 ≤ c) (h : a ≡ b [ZMOD n]) : a * c ≡ b * c [ZMOD (n * c)] :=
by rw [mul_comm a, mul_comm b, mul_comm n]; exact modeq_mul_left' hc h

theorem modeq_add (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) : a + c ≡ b + d [ZMOD n] :=
modeq_iff_dvd.2 $ by simpa using dvd_add (modeq_iff_dvd.1 h₁) (modeq_iff_dvd.1 h₂)

theorem modeq_add_cancel_left (h₁ : a ≡ b [ZMOD n]) (h₂ : a + c ≡ b + d [ZMOD n]) : c ≡ d [ZMOD n] :=
have (n:ℤ) ∣ a + (-a + (d + -c)),
by simpa using dvd_sub (modeq_iff_dvd.1 h₂) (modeq_iff_dvd.1 h₁),
modeq_iff_dvd.2 $ by rwa add_neg_cancel_left at this

theorem modeq_add_cancel_right (h₁ : c ≡ d [ZMOD n]) (h₂ : a + c ≡ b + d [ZMOD n]) : a ≡ b [ZMOD n] :=
by rw [add_comm a, add_comm b] at h₂; exact modeq_add_cancel_left h₁ h₂

theorem modeq_neg (h : a ≡ b [ZMOD n]) : -a ≡ -b [ZMOD n] := 
modeq_add_cancel_left h (by simp)

theorem modeq_sub (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) : a - c ≡ b - d [ZMOD n] :=
by rw [sub_eq_add_neg, sub_eq_add_neg]; exact modeq_add h₁ (modeq_neg h₂)

theorem modeq_mul_left (c : ℤ) (h : a ≡ b [ZMOD n]) : c * a ≡ c * b [ZMOD n] :=
or.cases_on (le_total 0 c) 
(λ hc, modeq_of_dvd_of_modeq (dvd_mul_left _ _) (modeq_mul_left' hc h))
(λ hc, by rw [← neg_neg c, ← neg_mul_eq_neg_mul, ← neg_mul_eq_neg_mul _ b];
    exact modeq_neg (modeq_of_dvd_of_modeq (dvd_mul_left _ _) 
    (modeq_mul_left' (neg_nonneg.2 hc) h)))

theorem modeq_mul_right (c : ℤ) (h : a ≡ b [ZMOD n]) : a * c ≡ b * c [ZMOD n] :=
by rw [mul_comm a, mul_comm b]; exact modeq_mul_left c h

theorem modeq_mul (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) : a * c ≡ b * d [ZMOD n] :=
(modeq_mul_left _ h₂).trans (modeq_mul_right _ h₁)

end modeq
end int
