import data.complex.basic
open cau_seq

namespace real

lemma eq_lim_of_const_equiv {f : cau_seq ℝ abs} {x : ℝ} (h : cau_seq.const abs x ≈ f) : x = lim f :=
const_equiv.mp (setoid.trans h (equiv_lim f))

lemma lim_eq_of_equiv_const {f : cau_seq ℝ abs} {x : ℝ} (h : f ≈ cau_seq.const abs x) : lim f = x :=
(eq_lim_of_const_equiv (setoid.symm h)).symm

lemma lim_eq_lim_of_equiv {f g : cau_seq ℝ abs} (h : f ≈ g) : lim f = lim g := 
lim_eq_of_equiv_const (setoid.trans h (equiv_lim g))

@[simp] lemma lim_const (x : ℝ) : lim (const abs x) = x := 
lim_eq_of_equiv_const (setoid.refl _)

lemma lim_add (f g : cau_seq ℝ abs) : lim f + lim g = lim ⇑(f + g) := 
eq_lim_of_const_equiv (show lim_zero (const abs (lim ⇑f + lim ⇑g) - (f + g)),
  from by rw [const_add, add_sub_comm];
  exact add_lim_zero (setoid.symm (equiv_lim f)) (setoid.symm (equiv_lim g)))

lemma lim_mul_lim (f g : cau_seq ℝ abs) : lim f * lim g = lim ⇑(f * g) := 
eq_lim_of_const_equiv (show lim_zero (const abs (lim ⇑f * lim ⇑g) - f * g),
  from have h : const abs (lim ⇑f * lim ⇑g) - f * g = g * (const abs (lim f) - f) 
      + const abs (lim f) * (const abs (lim g) - g) := 
    by simp [mul_sub, mul_comm, const_mul, mul_add],
  by rw h; exact add_lim_zero (mul_lim_zero _ (setoid.symm (equiv_lim f))) 
      (mul_lim_zero _ (setoid.symm (equiv_lim g))))

lemma lim_mul (f : cau_seq ℝ abs) (x : ℝ) : lim f * x = lim ⇑(f * const abs x) :=
by rw [← lim_mul_lim, lim_const]

lemma lim_neg (f : cau_seq ℝ abs) : lim ⇑(-f) = -lim f :=
lim_eq_of_equiv_const (show lim_zero (-f - const abs (-lim ⇑f)),
  from by rw [const_neg, sub_neg_eq_add, add_comm];
  exact setoid.symm (equiv_lim f))

lemma lim_eq_zero_iff (f : cau_seq ℝ abs) : lim f = 0 ↔ lim_zero f :=
⟨assume h,
  by have hf := equiv_lim f;
  rw h at hf;
  exact (lim_zero_congr hf).mpr (const_lim_zero.mpr rfl),
assume h, 
  have h₁ : f = (f - const abs 0) := ext (λ n, by simp [sub_apply, const_apply]),
  by rw h₁ at h; exact lim_eq_of_equiv_const h ⟩

end real

namespace complex

local notation `abs'` := _root_.abs

open cau_seq

lemma is_cau_seq_coe (f : cau_seq ℝ abs') : is_cau_seq abs (λ n, f n) :=
  show ∀ ε > 0, ∃ (i : ℕ), ∀ (j : ℕ), j ≥ i → abs (↑(f j) - ↑(f i)) < ε,  
  from by simp only [(of_real_sub _ _).symm, abs_of_real]; exact f.2 

lemma is_cau_seq_of_im_re {f : ℕ → ℂ} (hre : is_cau_seq abs' (λ n, (f n).re)) (him : is_cau_seq abs' (λ n, (f n).im)) : 
    is_cau_seq abs f := 
have h : f = (λ n, (f n).re + (f n).im * I) := funext (λ n, (re_add_im (f n)).symm),
let g : cau_seq ℂ abs := ⟨_, is_cau_seq_coe ⟨_, hre⟩⟩ + ⟨_, is_cau_seq_coe ⟨_, him⟩⟩ * cau_seq.const abs I in
by rw h; exact g.2

namespace cau_seq

noncomputable def conj (f : cau_seq ℂ abs) : cau_seq ℂ abs := ⟨λ n, complex.conj (f n), is_cau_seq_of_im_re (is_cau_seq_re f) (is_cau_seq_im (-f))⟩ 

end cau_seq

open cau_seq 

theorem const_equiv1 {α β : Type*} [discrete_linear_ordered_field α] [ring β] {abv : β → α} [is_absolute_value abv] {x y : β} : const abv x ≈ const abv y ↔ x = y :=
show lim_zero _ ↔ _, by rw [← const_sub, const_lim_zero, sub_eq_zero]

@[simp] lemma conj_apply (f : cau_seq ℂ abs) (n : ℕ) : (cau_seq.conj f) n = conj (f n) := rfl

lemma eq_lim_of_const_equiv {f : cau_seq ℂ abs} {x : ℂ} (h : cau_seq.const abs x ≈ f) : x = lim f :=
const_equiv1.mp (setoid.trans h (equiv_lim f))

lemma lim_eq_of_equiv_const {f : cau_seq ℂ abs} {x : ℂ} (h : f ≈ cau_seq.const abs x) : lim f = x :=
(eq_lim_of_const_equiv (setoid.symm h)).symm

lemma lim_eq_lim_of_equiv {f g : cau_seq ℂ abs} (h : f ≈ g) : lim f = lim g := 
lim_eq_of_equiv_const (setoid.trans h (equiv_lim g))

@[simp] lemma lim_const (x : ℂ) : lim (const abs x) = x := 
lim_eq_of_equiv_const (setoid.refl _)

lemma lim_add (f g : cau_seq ℂ abs) : lim f + lim g = lim ⇑(f + g) := 
eq_lim_of_const_equiv (show lim_zero (const abs (lim ⇑f + lim ⇑g) - (f + g)),
  from by rw [const_add, add_sub_comm];
  exact add_lim_zero (setoid.symm (equiv_lim f)) (setoid.symm (equiv_lim g)))

lemma lim_mul_lim (f g : cau_seq ℂ abs) : lim f * lim g = lim ⇑(f * g) := 
eq_lim_of_const_equiv (show lim_zero (const abs (lim ⇑f * lim ⇑g) - f * g),
  from have h : const abs (lim ⇑f * lim ⇑g) - f * g = g * (const abs (lim f) - f) 
      + const abs (lim f) * (const abs (lim g) - g) := 
    by simp [mul_sub, mul_comm, const_mul, mul_add],
  by rw h; exact add_lim_zero (mul_lim_zero _ (setoid.symm (equiv_lim f))) 
      (mul_lim_zero _ (setoid.symm (equiv_lim g))))

lemma lim_mul (f : cau_seq ℂ abs) (x : ℝ) : lim f * x = lim ⇑(f * const abs x) :=
by rw [← lim_mul_lim, lim_const]

lemma lim_neg (f : cau_seq ℂ abs) : lim ⇑(-f) = -lim f :=
lim_eq_of_equiv_const (show lim_zero (-f - const abs (-lim ⇑f)),
  from by rw [const_neg, sub_neg_eq_add, add_comm];
  exact setoid.symm (equiv_lim f))

lemma lim_conj (f : cau_seq ℂ abs) : lim (cau_seq.conj f) = conj (lim f) :=
begin
  unfold lim,
  apply ext,
  { simp }, 
  { simp,
  have := real.lim_neg ⟨_, is_cau_seq_im f⟩,
    exact this }
end
-- f : cau_seq ℝ abs, -f = (λ n, -f n)
lemma lim_eq_zero_iff (f : cau_seq ℂ abs) : lim f = 0 ↔ lim_zero f :=
⟨assume h,
  by have hf := equiv_lim f;
  rw h at hf;
  exact (lim_zero_congr hf).mpr (const_lim_zero.mpr rfl),
assume h, 
  have h₁ : f = (f - const abs 0) := cau_seq.ext (λ n, by simp [sub_apply, const_apply]),
  by rw h₁ at h; exact lim_eq_of_equiv_const h ⟩

end complex