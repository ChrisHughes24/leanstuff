import data.equiv algebra.group_power data.fintype data.pnat data.set.finite

local attribute [instance] classical.prop_decidable
noncomputable theory

--------------------------------------------
section
variable {α : Type*}
open function set finset

lemma infinite_univ_nat : infinite (univ : set ℕ) :=
 assume (h : finite (univ : set ℕ)),
 let ⟨n, hn⟩ := finset.exists_nat_subset_range h.to_finset in
 have n ∈ finset.range n, from finset.subset_iff.mpr hn $ by simp,
 by simp * at *

lemma not_injective_nat_fintype [fintype α] [decidable_eq α] {f : ℕ → α} : ¬ injective f :=
 assume (h : injective f),
 have finite (f '' univ),
   from finite_subset (finset.finite_to_set $ fintype.elems α) (assume a h, fintype.complete a),
 have finite (univ : set ℕ), from finite_of_finite_image h this,
 infinite_univ_nat this

end

section ord
local infix `^` := monoid.pow
variables {α : Type*} 
open nat

variable [group α]

def has_ord (a : α) : Prop := ∃ n : ℕ, 0 < n ∧ a^n = 1

lemma has_ord_of_fintype [fintype α] (b : α) : has_ord b := begin
  apply by_contradiction,
  assume h,
  replace h := not_exists.mp h,
  have : ∀ m n : ℕ, succ m ≤ succ n → b^(succ m) = b^(succ n) → m = n,
    assume m n hmn hbmn,
    rw [← nat.sub_add_cancel hmn, _root_.pow_add,
    ← one_mul (b^(succ m)), ← mul_assoc, mul_right_inj, mul_one] at hbmn,
    have : succ n ≤ succ m := 
      nat.sub_eq_zero_iff_le.mp (nat.eq_zero_of_le_zero (le_of_not_gt ((not_and'.mp (h (succ n - succ m))) hbmn.symm))),
    exact succ_inj (le_antisymm hmn this),
  have : ∀ m n : ℕ, b^(succ m) = b^(succ n) → m = n := 
  λ m n, or.by_cases (le_total (succ m) (succ n)) (λ h, this _ _ h) (λ h h₁,(this _ _ h h₁.symm).symm),
  exact not_injective_nat_fintype this,
end

def ord (a : α) : ℕ := dite (has_ord a) (λ h, nat.find h) (λ h, 0)

variables {a : α} (ha : has_ord a)
include ha

lemma pow_ord : a^ord a = 1 := by simp [ha, ord]; exact (nat.find_spec ha).right

@[simp] lemma fintype_pow_ord [fintype α] : a^ord a = 1 := pow_ord (has_ord_of_fintype _)

lemma ord_pos : 0 < ord a := by simp [ha, ord]; exact (nat.find_spec ha).left

lemma ord_le {n : ℕ} (ha0 : 0 < n) (han : a^n = 1) : ord a ≤ n :=
by simp [ha, ord]; exact nat.find_min' ha ⟨ha0, han⟩

lemma lt_ord {n : ℕ} (hn : n < ord a) : n = 0 ∨ a^n ≠ 1 :=
begin
  simp [ha, ord] at ⊢ hn,
  have h : ¬0 < n ∨ ¬a^n = 1 := (decidable.not_and_iff_or_not _ _).mp (nat.find_min ha hn),
  rwa [nat.pos_iff_ne_zero', not_not] at h
end

lemma order_dvd_iff (i : ℤ) : (ord a : ℤ) ∣ i ↔ gpow a i = 1 :=
⟨λ h₁, let ⟨k, hk⟩ := exists_eq_mul_right_of_dvd h₁ in by simp [hk, gpow_mul, pow_ord ha],
λ h₁, by_contradiction $ λ h₂, 
begin 
  rw int.dvd_iff_mod_eq_zero at h₂,
  have h₃ : gpow a (i % ↑(ord a)) = 1,
  { rw ← int.mod_add_div i (ord a) at h₁,
    simp [gpow_add, gpow_mul, pow_ord ha] at h₁,
    exact h₁ },
  have hzc := int.coe_nat_ne_zero.mpr (ne_of_lt (ord_pos ha)).symm,
  have h₄ : (int.nat_abs (i % ord a) : ℤ)  = (i % ord a) := 
    int.nat_abs_of_nonneg (int.mod_nonneg _ hzc),
  have h₅ : a^int.nat_abs (i % ↑(ord a)) = 1 := by rwa [← gpow_coe_nat, h₄],
  have h₆ : (ord a : ℤ) ≤ (i % ↑(ord a)) := by rw [← h₄, int.coe_nat_le];
    exact ord_le ha (int.nat_abs_pos_of_ne_zero h₂) h₅,
  have h₇ := int.mod_lt i hzc,
  rw abs_of_nonneg (int.coe_nat_le.mpr (nat.zero_le _)) at h₇,
  exact not_le_of_gt h₇ h₆,
end⟩

end ord

class subgroup {α : Type*} [group α] (s : set α) : Prop :=
(one_mem : (1 : α) ∈ s)
(mul_mem : ∀ {x y}, x ∈ s → y ∈ s → x * y ∈ s)
(inv_mem : ∀ {x}, x ∈ s → x⁻¹ ∈ s)

namespace subgroup

instance group {α : Type*} [group α] (s : set α) [subgroup s] : group s :=
{ mul := λ ⟨x, hx⟩ ⟨y, hy⟩, ⟨x * y, mul_mem hx hy⟩,
  mul_assoc := λ ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩, subtype.eq $ mul_assoc _ _ _,
  one := ⟨1, one_mem s⟩,
  one_mul := λ ⟨x, hx⟩, subtype.eq $ one_mul _,
  mul_one := λ ⟨x, hx⟩, subtype.eq $ mul_one _,
  inv := λ ⟨x, hx⟩, ⟨x⁻¹, inv_mem hx⟩,
  mul_left_inv := λ ⟨x, hx⟩, subtype.eq $ mul_left_inv _ }

end subgroup

class cyclic_group (α : Type*) extends group α :=
(cyclic : ∃ a, ∀ b : α, ∃ i : ℤ, b = gpow a i)

instance comm_of_cyclic {α : Type*} [cyclic_group α] : comm_group α := 
{ mul := (*),
  mul_assoc := mul_assoc,
  one := 1,
  one_mul := one_mul,
  mul_one := mul_one,
  inv := has_inv.inv,
  mul_left_inv := mul_left_inv,
  mul_comm := λ x y, let ⟨a, ha⟩ := cyclic_group.cyclic α in
    let ⟨i, hi⟩ := ha x in
    let ⟨j, hj⟩ := ha y in
    by rw [hi, hj]; exact gpow_mul_comm _ _ _ }


-- section cyclic
-- variables {α : Type*}

-- open equiv

-- def is_cycle (f : perm α) : Prop := ∀ a b : α, f a ≠ a → f b ≠ b → ∃ i : ℤ, (f^i) a = b

-- lemma exists_length (f : perm α) (h : is_cycle f) : ∃ n : ℕ, ((∀ a : α, (f^n) a = a) ∧ ∀ m : ℕ, (∀ a : α, (f^m) a = a) → n ∣ m) :=
-- begin
  


-- end
-- def length (f : perm α) (hf : is_cycle f) := 


-- end cyclic


-- open function



-- end Sym