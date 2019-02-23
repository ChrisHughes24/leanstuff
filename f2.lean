import tactic.ring data.int.modeq data.fintype group_theory.sylow
universe u
local attribute [instance, priority 0] classical.prop_decidable

open fintype finset nat

private def S (p : ℕ) : finset (ℕ × ℕ × ℕ) :=
((range p).product ((range p).product (range p))).filter
  (λ v, v.1 ^ 2 + 4 * v.2.1 * v.2.2 = p)

lemma mem_S (p : ℕ) (v : ℕ × ℕ × ℕ) : v.1 ^ 2 + 4 * v.2.1 * v.2.2 = p → v ∈ S p :=
begin
  rcases v with ⟨x, y, z⟩,
  suffices : x ^ 2 + 4 * y * z = p → (x < p ∧ y < p ∧ z < p),
  { simp [S], tauto },
  assume h,
  refine ⟨_, _, _⟩,
  { calc x ≤ x ^ 2 : by rw pow_two; exact le_mul_self x
    ... ≤ x ^ 2 + 4 * y * z : _
    ... < _ : sorry },

end

lemma nat.not_prime_mul_self (n : ℕ) : ¬prime (n * n) :=
λ h, or.by_cases (h.2 _ $ dvd_mul_right n n)
  (λ h₁, (dec_trivial : ¬ 1 ≥ 2) (h₁ ▸ h : prime (1 * 1)).1)
  (λ h₁,
    have h₂ : n * 1 = n * n := by rwa mul_one,
    have h₃ : 1 = n := (@nat.mul_left_inj n 1 n (prime.pos (h₁.symm ▸ h))).1 h₂,
    (dec_trivial : ¬ 1 ≥ 2) (h₃.symm ▸ h : prime (1 * 1)).1)

@[reducible] private def f₁ (v : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (v.1, v.2.2, v.2.1)

@[reducible] private def f₂ (v : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
if v.1 + v.2.2 < v.2.1
  then (v.1 + 2 * v.2.2, v.2.2, v.2.1 - v.1 - v.2.2)
  else if 2 * v.2.1 < v.1
    then (v.1 - 2 * v.2.1, v.1 - v.2.1 + v.2.2, v.2.1)
    else (2 * v.2.1 - v.1, v.2.1, v.1 - v.2.1 + v.2.2)

variables {p : ℕ} (hp : prime p) (hp₁ : p % 4 = 1)
include hp hp₁

private lemma f₁_mem_S : ∀ v : ℕ × ℕ × ℕ, v ∈ S p → f₁ v ∈ S p :=
λ ⟨x, y, z⟩, by simp [S, mul_comm, *, mul_assoc, mul_left_comm, *, f₁] {contextual := tt}

private lemma f₁_involution : ∀ v : ℕ × ℕ × ℕ, f₁ (f₁ v) = v := λ ⟨x, y, z⟩, rfl

private lemma f₂_mem_S₁ {x y z : ℕ} (hxp : x < p) (hyp : y < p) (hzp : z < p)
  (hxyz : x + z < y) :

∀ v : ℕ × ℕ × ℕ, v ∈ S p → f₂ v ∈ S p

private lemma f₂_S : ∀ v : ℕ × ℕ × ℕ, v ∈ S p → f₂ v ∈ S p :=
λ ⟨x, y, z⟩, begin
  clear_aux_decl,
  simp [S, f₂] at *,
  split_ifs; simp *,
end

private lemma f₂_invo_on_S : ∀ v : ℤ × ℤ × ℤ, v ∈ S p → f₂ (f₂ v) = v :=
λ ⟨x, y, z⟩ hv,
have xp : 0 < x := x_pos hp hp₁ (x, y, z) hv,
have yzp : 0 < y ∧ 0 < z :=  yz_pos hp hp₁ (x, y, z) hv,
 or.by_cases (decidable.em (x + z < y)) (λ h,
have h₁ : ¬ x + (y + (2 * z + (-x + -z))) < z :=
  have h₁ : x + (y + (2 * z + (-x + -z))) = y + z := by ring,
  not_lt_of_ge (h₁.symm ▸ le_add_of_nonneg_left hv.2.2.1),
by simp[f₂, h, h₁, xp]; ring) $
λ h, or.by_cases (decidable.em (2 * y < x))
(λ h₁, have h₂ : y + -(2 * y) < z + -y :=
  have h₂ : y + -(2 * y) = -y := by ring,
  h₂.symm ▸ lt_add_of_pos_left _ yzp.2,
by simp[f₂, h, h₁, h₂]; ring) $
λ h₁, have h₂ : ¬ x + (z + (2 * y + (-x + -y))) < y :=
  have h₁ : x + (z + (2 * y + (-x + -y))) = z + y := by ring,
  not_lt_of_ge (h₁.symm ▸ le_add_of_nonneg_left hv.2.2.2),
have h₃ : ¬ 0 < -x := not_lt_of_ge $ le_of_lt $ neg_neg_of_pos xp,
by simp [f₂, h, h₁, h₂, h₃]; ring

private lemma f₂_fixed_point : ∃! v : S p, f₂ v = v :=
have hp4 : (0 : ℤ) ≤ p / 4 := int.div_nonneg (int.coe_nat_nonneg _) dec_trivial,
have h : ¬ (1 : ℤ) + p / 4 < 1 := not_lt_of_ge $ le_add_of_nonneg_right hp4,
⟨⟨(1, 1, (p / 4 : ℤ)),
⟨show (1 : ℤ) + 4 * (p / 4) = p,
from have h : (p : ℤ) % 4 = 1 := (int.coe_nat_eq_coe_nat_iff _ _).2 hp₁,
have h₁ : (p : ℤ) = p % 4 + 4 * (p / 4) := (int.mod_add_div _ _).symm,
by rw [h₁] {occs := occurrences.pos [2]}; rw h,
dec_trivial, dec_trivial, hp4 ⟩⟩,
⟨by simp [f₂, h, (dec_trivial : ¬ (2 : ℤ) < 1)]; refl,
λ ⟨⟨x, y, z⟩, ⟨hv, hx, hy, hz⟩ ⟩ hf,
have xp : 0 < x := x_pos hp hp₁ (x, y, z) ⟨hv, hx, hy, hz⟩,
have yzp : 0 < y ∧ 0 < z := yz_pos hp hp₁ (x, y, z) ⟨hv, hx, hy, hz⟩,
or.by_cases (decidable.em (x + z < y))
(λ h₁,
have h₂ : x + 2 * z ≠ x := λ h₃,
  have h₄ : x + 2 * z = x + 0 := by rwa add_zero,
  not_or dec_trivial (ne_of_lt yzp.2).symm (mul_eq_zero.1 ((add_left_inj _).1 h₄)),
by simpa [f₂, h₁, h₂] using hf) $ λ h₁,
or.by_cases (decidable.em (2 * y < x))
(λ h₂,
have h₃ : x + -(2 * y) ≠ x := λ h₄,
  have h₅ : x + -2 * y = x + 0 := by rwa [← neg_mul_eq_neg_mul, add_zero],
  not_or dec_trivial (ne_of_lt yzp.1).symm (mul_eq_zero.1 ((add_left_inj _).1 h₅)),
by simp [f₂, h₁, h₂, h₃] at hf; trivial) $ λ h₂,
have hf₁ : 2 * y - x = x ∧ x + (z + -y) = z := by simp [f₂, h₁, h₂] at hf; assumption,
have hxy : y = x := by rw [sub_eq_iff_eq_add, ← two_mul] at hf₁;
  exact eq_of_mul_eq_mul_left dec_trivial hf₁.1,
subtype.eq $ show (x, y, z) = (1, 1, p / 4), from
begin
  rw [hxy, mul_comm (4 : ℤ), mul_assoc] at hv,
  have hxp : int.nat_abs x ∣ p := int.coe_nat_dvd.1 (int.nat_abs_dvd.2 (hv ▸ dvd_add (dvd_mul_right _ _) (dvd_mul_right _ _))),
  have h4 : ((4 : ℕ) : ℤ) = 4 := rfl,
  cases hp.2 _ (hxp) with h₃ h₃,
  { have h₄ : x = 1 := by rwa [← int.coe_nat_eq_coe_nat_iff, int.nat_abs_of_nonneg hx] at h₃,
    rw [← mod_add_div p 4, hp₁, h₄, int.coe_nat_add, int.coe_nat_one, mul_one, one_mul, add_left_cancel_iff,
        int.coe_nat_mul] at hv,
    have : z = p / 4 := eq_of_mul_eq_mul_left_of_ne_zero dec_trivial hv,
    rw [hxy, h₄, this] },
  { have h4 : ((4 : ℕ) : ℤ) = 4 := rfl,
    rw [← int.nat_abs_of_nonneg hx, ← int.nat_abs_of_nonneg hz, h₃, ← mul_add] at hv,
    have := int.eq_one_of_mul_eq_self_right (int.coe_nat_ne_zero.2 (ne_of_lt (prime.pos hp)).symm) hv,
    rw [← h4, ← int.coe_nat_mul, ← int.coe_nat_add, ← int.coe_nat_one, int.coe_nat_eq_coe_nat_iff] at this,
    have : p ≤ 1 := this ▸ (le_add_right p (4 * int.nat_abs z)),
    exact absurd (prime.gt_one hp) (not_lt_of_ge this) }
end ⟩ ⟩

theorem fermat_sum_two_squares : ∃ a b : ℕ, a^2 + b^2 = p :=
have fS : fintype (S p) := fintype_S hp hp₁,
let f₁' : S p → S p := λ ⟨v, hv⟩, ⟨f₁ v, f₁_S hp hp₁ _ hv⟩ in
let f₂' : S p → S p := λ ⟨v, hv⟩, ⟨f₂ v, f₂_S hp hp₁ _ hv⟩ in
have hf₁ : ∀ v, f₁' (f₁' v) = v := λ ⟨v, hv⟩, subtype.eq $ f₁_invo_on_S hp hp₁ v,
have hf₂ : ∀ v, f₂' (f₂' v) = v := λ ⟨v, hv⟩, subtype.eq $ f₂_invo_on_S hp hp₁ v hv,
have hf₂u : ∃! v : S p, f₂' v = v :=
  let ⟨⟨v, vS⟩, ⟨hv₁, hv₂⟩⟩ := f₂_fixed_point hp hp₁ in
  ⟨⟨v, vS⟩, ⟨subtype.eq hv₁, λ ⟨w, wS⟩ hw, hv₂ ⟨w, wS⟩ (subtype.mk.inj hw) ⟩ ⟩,
let h := @odd_card_of_involution_of_unique_fixed_point _ _ fS hf₂ hf₂u in
let ⟨⟨⟨x, y, z⟩, hvp, ⟨hx, hy, hz⟩⟩, h⟩ := @exists_fixed_point_of_involution_of_odd_card _ _ fS h hf₁ in
have h : y = z := (prod.eq_iff_fst_eq_snd_eq.1 (prod.eq_iff_fst_eq_snd_eq.1 (subtype.mk.inj h)).2).2,
⟨int.nat_abs x, 2 * int.nat_abs y,
begin
  simp only [nat.pow_succ, nat.pow_zero, one_mul],
  rw [mul_right_comm 2, mul_assoc, mul_assoc, ← int.coe_nat_eq_coe_nat_iff, int.coe_nat_add,
      int.nat_abs_mul_self, int.coe_nat_mul, int.coe_nat_mul, int.nat_abs_mul_self, ← hvp, h],
  simp,
  ring,
end⟩
#print axioms fermat_sum_two_squares
