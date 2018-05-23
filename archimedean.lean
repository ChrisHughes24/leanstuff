/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Archimedean groups and fields.
-/
import algebra.group_power data.rat data.int.order

local infix ` • `:73 := add_monoid.smul

variables {α : Type*}

class floor_ring (α) extends linear_ordered_ring α :=
(floor : α → ℤ)
(le_floor : ∀ (z : ℤ) (x : α), z ≤ floor x ↔ (z : α) ≤ x)

instance : floor_ring ℤ :=
{ floor := id, le_floor := by simp,
  ..linear_ordered_comm_ring.to_linear_ordered_ring ℤ }

instance : floor_ring ℚ :=
{ floor := rat.floor, le_floor := @rat.le_floor,
  ..linear_ordered_comm_ring.to_linear_ordered_ring ℚ }

section
variable [floor_ring α]

def floor : α → ℤ := floor_ring.floor

notation `⌊` x `⌋` := floor x

theorem le_floor : ∀ {z : ℤ} {x : α}, z ≤ ⌊x⌋ ↔ (z : α) ≤ x :=
floor_ring.le_floor

theorem floor_lt {x : α} {z : ℤ} : ⌊x⌋ < z ↔ x < z :=
le_iff_le_iff_lt_iff_lt.1 le_floor

theorem floor_le (x : α) : (⌊x⌋ : α) ≤ x :=
le_floor.1 (le_refl _)

theorem floor_nonneg {x : α} : 0 ≤ ⌊x⌋ ↔ 0 ≤ x :=
by simpa using @le_floor _ _ 0 x

theorem lt_succ_floor (x : α) : x < ⌊x⌋.succ :=
floor_lt.1 $ int.lt_succ_self _

theorem lt_floor_add_one (x : α) : x < ⌊x⌋ + 1 :=
by simpa [int.succ] using lt_succ_floor x

theorem sub_one_lt_floor (x : α) : x - 1 < ⌊x⌋ :=
sub_lt_iff_lt_add.2 (lt_floor_add_one x)

@[simp] theorem floor_coe (z : ℤ) : ⌊(z:α)⌋ = z :=
eq_of_forall_le_iff $ λ a, by rw [le_floor, int.cast_le]

theorem floor_mono {a b : α} (h : a ≤ b) : ⌊a⌋ ≤ ⌊b⌋ :=
le_floor.2 (le_trans (floor_le _) h)

@[simp] theorem floor_add_int (x : α) (z : ℤ) : ⌊x + z⌋ = ⌊x⌋ + z :=
eq_of_forall_le_iff $ λ a, by rw [le_floor,
  ← sub_le_iff_le_add, ← sub_le_iff_le_add, le_floor, int.cast_sub]

theorem floor_sub_int (x : α) (z : ℤ) : ⌊x - z⌋ = ⌊x⌋ - z :=
eq.trans (by rw [int.cast_neg]; refl) (floor_add_int _ _)

/-- `ceil x` is the smallest integer `z` such that `x ≤ z` -/
def ceil (x : α) : ℤ := -⌊-x⌋

notation `⌈` x `⌉` := ceil x

theorem ceil_le {z : ℤ} {x : α} : ⌈x⌉ ≤ z ↔ x ≤ z :=
by rw [ceil, neg_le, le_floor, int.cast_neg, neg_le_neg_iff]

theorem lt_ceil {x : α} {z : ℤ} : z < ⌈x⌉ ↔ (z:α) < x :=
le_iff_le_iff_lt_iff_lt.1 ceil_le

theorem le_ceil (x : α) : x ≤ ⌈x⌉ :=
ceil_le.1 (le_refl _)

@[simp] theorem ceil_coe (z : ℤ) : ⌈(z:α)⌉ = z :=
by rw [ceil, ← int.cast_neg, floor_coe, neg_neg]

theorem ceil_mono {a b : α} (h : a ≤ b) : ⌈a⌉ ≤ ⌈b⌉ :=
ceil_le.2 (le_trans h (le_ceil _))

@[simp] theorem ceil_add_int (x : α) (z : ℤ) : ⌈x + z⌉ = ⌈x⌉ + z :=
by rw [ceil, neg_add', floor_sub_int, neg_sub, sub_eq_neg_add]; refl

theorem ceil_sub_int (x : α) (z : ℤ) : ⌈x - z⌉ = ⌈x⌉ - z :=
eq.trans (by rw [int.cast_neg]; refl) (ceil_add_int _ _)

theorem ceil_lt_add_one (x : α) : (⌈x⌉ : α) < x + 1 :=
by rw [← lt_ceil, ← int.cast_one, ceil_add_int]; apply lt_add_one

end

class archimedean (α) [ordered_comm_monoid α] : Prop :=
(arch : ∀ (x : α) {y}, 0 < y → ∃ n, x ≤ y • n)

theorem exists_nat_gt [linear_ordered_semiring α] [archimedean α]
  (x : α) : ∃ n : ℕ, x < n :=
let ⟨n, h⟩ := archimedean.arch x zero_lt_one in
⟨n+1, lt_of_le_of_lt (by simpa using h)
  (nat.cast_lt.2 (nat.lt_succ_self _))⟩

lemma pow_unbounded_of_gt_one [linear_ordered_ring α] [archimedean α] (x : α) {y : α} 
    (hy1 : 1 < y) : ∃ n : ℕ, x < monoid.pow y n :=
have hy0 : 0 <  y - 1 := sub_pos_of_lt hy1,
let ⟨n, h⟩ := archimedean.arch x hy0 in
⟨n, calc x ≤ (y - 1) • n     : h
       ... < 1 + (y - 1) • n : by rw add_comm; exact lt_add_one _
       ... ≤ monoid.pow y n  : pow_ge_one_add_sub_mul (le_of_lt hy1) _⟩

section linear_ordered_ring
variables [linear_ordered_ring α] [archimedean α]

theorem exists_int_gt (x : α) : ∃ n : ℤ, x < n :=
let ⟨n, h⟩ := exists_nat_gt x in ⟨n, by simp [h]⟩

theorem exists_int_lt (x : α) : ∃ n : ℤ, (n : α) < x :=
let ⟨n, h⟩ := exists_int_gt (-x) in ⟨-n, by simp [neg_lt.1 h]⟩

theorem exists_floor (x : α) :
  ∃ (fl : ℤ), ∀ (z : ℤ), z ≤ fl ↔ (z : α) ≤ x :=
begin
  haveI := classical.prop_decidable,
  have : ∃ (ub : ℤ), (ub:α) ≤ x ∧ ∀ (z : ℤ), (z:α) ≤ x → z ≤ ub :=
  int.exists_greatest_of_bdd
    (let ⟨n, hn⟩ := exists_int_gt x in ⟨n, λ z h',
      int.cast_le.1 $ le_trans h' $ le_of_lt hn⟩)
    (let ⟨n, hn⟩ := exists_int_lt x in ⟨n, le_of_lt hn⟩),
  refine this.imp (λ fl h z, _),
  cases h with h₁ h₂,
  exact ⟨λ h, le_trans (int.cast_le.2 h) h₁, h₂ z⟩,
end

end linear_ordered_ring

instance : archimedean ℕ :=
⟨λ n m m0, ⟨n, by simpa using nat.mul_le_mul_right n m0⟩⟩

instance : archimedean ℤ :=
⟨λ n m m0, ⟨n.to_nat, begin
  simp [add_monoid.smul_eq_mul],
  refine le_trans (int.le_to_nat _) _,
  simpa using mul_le_mul_of_nonneg_right
    (int.add_one_le_iff.2 m0) (int.coe_zero_le n.to_nat),
end⟩⟩

noncomputable def archimedean.floor_ring (α)
  [R : linear_ordered_ring α] [archimedean α] : floor_ring α :=
{ floor := λ x, classical.some (exists_floor x),
  le_floor := λ z x, classical.some_spec (exists_floor x) z,
  ..R }

section linear_ordered_field
variables [linear_ordered_field α]

theorem archimedean_iff_nat_lt :
  archimedean α ↔ ∀ x : α, ∃ n : ℕ, x < n :=
⟨@exists_nat_gt α _, λ H, ⟨λ x y y0,
  (H (x / y)).imp $ λ n h, le_of_lt $
  by rwa [div_lt_iff y0, ← add_monoid.smul_eq_mul'] at h⟩⟩

theorem archimedean_iff_nat_le :
  archimedean α ↔ ∀ x : α, ∃ n : ℕ, x ≤ n :=
archimedean_iff_nat_lt.trans
⟨λ H x, (H x).imp $ λ _, le_of_lt,
 λ H x, let ⟨n, h⟩ := H x in ⟨n+1,
   lt_of_le_of_lt h (nat.cast_lt.2 (lt_add_one _))⟩⟩

theorem exists_rat_gt [archimedean α] (x : α) : ∃ q : ℚ, x < q :=
let ⟨n, h⟩ := exists_nat_gt x in ⟨n, by simp [h]⟩

theorem archimedean_iff_rat_lt :
  archimedean α ↔ ∀ x : α, ∃ q : ℚ, x < q :=
⟨@exists_rat_gt α _,
  λ H, archimedean_iff_nat_lt.2 $ λ x,
  let ⟨q, h⟩ := H x in
  ⟨rat.nat_ceil q, lt_of_lt_of_le h $ 
    by simpa using (@rat.cast_le α _ _ _).2 (rat.le_nat_ceil _)⟩⟩

theorem archimedean_iff_rat_le :
  archimedean α ↔ ∀ x : α, ∃ q : ℚ, x ≤ q :=
archimedean_iff_rat_lt.trans
⟨λ H x, (H x).imp $ λ _, le_of_lt,
 λ H x, let ⟨n, h⟩ := H x in ⟨n+1,
   lt_of_le_of_lt h (rat.cast_lt.2 (lt_add_one _))⟩⟩

variable [archimedean α]

theorem exists_rat_lt (x : α) : ∃ q : ℚ, (q : α) < x :=
let ⟨n, h⟩ := exists_int_lt x in ⟨n, by simp [h]⟩

theorem exists_pos_rat_lt {x : α} (x0 : 0 < x) : ∃ q : ℚ, 0 < q ∧ (q : α) < x :=
let ⟨n, h⟩ := exists_nat_gt x⁻¹ in begin
  have n0 := nat.cast_pos.1 (lt_trans (inv_pos x0) h),
  refine ⟨n⁻¹, inv_pos (nat.cast_pos.2 n0), _⟩,
  simpa [rat.cast_inv_of_ne_zero, ne_of_gt n0] using
    (inv_lt x0 (nat.cast_pos.2 n0)).1 h
end

theorem exists_rat_btwn {x y : α} (h : x < y) : ∃ q : ℚ, x < q ∧ (q:α) < y :=
begin
  cases exists_nat_gt (y - x)⁻¹ with n nh,
  cases exists_floor (x * n) with z zh,
  refine ⟨(z + 1 : ℤ) / n, _⟩,
  have n0 := nat.cast_pos.1 (lt_trans (inv_pos (sub_pos.2 h)) nh),
  simp [rat.cast_div_of_ne_zero, -int.cast_add, ne_of_gt n0],
  have n0' := (@nat.cast_pos α _ _).2 n0,
  refine ⟨(lt_div_iff n0').2 $
    (le_iff_le_iff_lt_iff_lt.1 (zh _)).1 (lt_add_one _), _⟩,
  simp [div_lt_iff n0', -add_comm],
  refine lt_of_le_of_lt (add_le_add_right ((zh _).1 (le_refl _)) _) _,
  rwa [← lt_sub_iff_add_lt', ← sub_mul,
       ← div_lt_iff' (sub_pos.2 h), one_div_eq_inv]
end

end linear_ordered_field

section
variables [discrete_linear_ordered_field α] [archimedean α]

theorem exists_rat_near (x : α) {ε : α} (ε0 : ε > 0) :
  ∃ q : ℚ, abs (x - q) < ε :=
let ⟨q, h₁, h₂⟩ := exists_rat_btwn $
  lt_trans ((sub_lt_self_iff x).2 ε0) ((lt_add_iff_pos_left x).2 ε0) in
⟨q, abs_sub_lt_iff.2 ⟨sub_lt.1 h₁, sub_lt_iff_lt_add.2 h₂⟩⟩

end

instance : archimedean ℚ :=
archimedean_iff_rat_le.2 $ λ q, ⟨q, by simp⟩
