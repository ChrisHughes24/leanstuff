import tactic.find data.equiv algebra.group_power data.fintype data.set.finite set_theory.cardinal data.set.lattice

noncomputable theory
local attribute [instance, priority 0] classical.prop_decidable classical.dec_pred
local attribute [instance] set_fintype
open fintype
local infix `^` := gpow
universe u


instance {α : Type*} (p : α → Prop) [fintype α] : fintype {a // p a} :=
set_fintype p

instance {α : Type*} [fintype α] (r : α → α → Prop) : fintype (quot r) :=
of_surjective (quot.mk r) (λ x, quot.exists_rep _)

lemma finset.sum_const {α β : Type*} [decidable_eq α] [add_comm_monoid β] 
    (s : finset α) (b : β) : finset.sum s (λ a, b) = add_monoid.smul b (finset.card s) :=
finset.induction_on s (by simp) $ λ a s h hi,
by simp [finset.sum_insert h, finset.card_insert_of_not_mem h, hi, smul_succ]

theorem card_quot {α : Type*} [fintype α] (r : α → α → Prop) : 
    card α = (finset.univ : finset (quot r)).sum (λ x, card {a // quot.mk r a = x}) :=
card_sigma (λ x, {a // quot.mk r a = x}) ▸
card_congr ⟨λ x, ⟨quot.mk r x, ⟨x, rfl⟩⟩, λ x, x.2, λ _, rfl, λ ⟨_, _, ⟨_⟩⟩, rfl⟩

instance {α : Type*} [fintype α] (s : setoid α) : fintype (quotient s) := quot.fintype s.r

theorem card_quotient {α : Type*} [fintype α] (s : setoid α) :
    card α = (finset.univ : finset (quotient s)).sum (λ x, card {a // ⟦a⟧ = x}) := card_quot s.r

instance {α : Type*} [fintype α] : fintype (set α) := pi.fintype

section
variable {α : Type*}
open function set finset

set_option pp.implicit true
#print eq.drec_on
lemma set.card_eq_zero {α : Type*} {s : set α} [hf : fintype s] : card s = 0 ↔ s = ∅ :=
⟨λ h, by_contradiction $ λ h₁, let ⟨x, hx⟩ := set.exists_mem_of_ne_empty h₁ in
finset.not_mem_empty (⟨x, hx⟩ : s) $ finset.card_eq_zero.1 h ▸ finset.mem_univ (⟨x, hx⟩ : s),
λ h, by rw ← set.empty_card; congr; assumption⟩ 

lemma set.to_finset_union_distrib {α : Type*} (s t : set α) [hs : fintype s] [ht : fintype t] :
@set.to_finset α (s ∪ t) (classical.choice $ set.finite_union ⟨hs⟩ ⟨ht⟩) = set.to_finset s ∪ set.to_finset t :=
finset.ext.2 $ λ x, by simp [set.mem_to_finset, finset.mem_union]

lemma set.card_disjoint_union {α : Type*} {s t : set α} (hs : fintype s) (ht : fintype t) (hst : disjoint s t) :
    @finset.card (s ∪ t : set α) (classical.choice $ set.finite_union ⟨hs⟩ ⟨ht⟩) = card s + card t :=
begin
  have h := set.card_fintype_of_finset _ (@set.mem_to_finset _ s hs),
  have h₁ : ∀ {s : set α} (hs : fintype s), @card s hs =  @card ↥s (@set.fintype_of_finset α s (@set.to_finset α s hs) (@set.mem_to_finset _ s hs)) := λ s hs, by congr,
  have h₃ := set.card_fintype_of_finset _ (@set.mem_to_finset _ t ht),
  have h₄ := set.card_fintype_of_finset _ (@set.mem_to_finset _ _ (classical.choice $ set.finite_union ⟨hs⟩ ⟨ht⟩)),
  rw [h₁ hs, h₁ ht, h₁ (classical.choice $ set.finite_union ⟨hs⟩ ⟨ht⟩), h, h₃, h₄, set.to_finset_union_distrib],
  rw finset.card_disjoint_union,
  simp [finset.disjoint],
  exact hst,

end

lemma blah {p q : Prop} (hp : p) (hq : q) : hp == hq := 
@eq.drec_on _ _ (λ r h₁, hp == (h₁ ▸ hp : r)) _
(propext ⟨λ h, hq, λ h, hp⟩) (heq.refl _)

class subgroup {α : Type*} [group α] (s : set α) : Prop :=
(one_mem : (1 : α) ∈ s)
(mul_mem : ∀ {x y}, x ∈ s → y ∈ s → x * y ∈ s)
(inv_mem : ∀ {x}, x ∈ s → x⁻¹ ∈ s)
end
namespace subgroup
variables {α : Type*} [g : group α]
include g

instance group (s : set α) [subgroup s] : group s :=
{ mul := λ ⟨x, hx⟩ ⟨y, hy⟩, ⟨x * y, mul_mem hx hy⟩,
  mul_assoc := λ ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩, subtype.eq $ mul_assoc _ _ _,
  one := ⟨1, one_mem s⟩,
  one_mul := λ ⟨x, hx⟩, subtype.eq $ one_mul _,
  mul_one := λ ⟨x, hx⟩, subtype.eq $ mul_one _,
  inv := λ ⟨x, hx⟩, ⟨x⁻¹, inv_mem hx⟩,
  mul_left_inv := λ ⟨x, hx⟩, subtype.eq $ mul_left_inv _ }

@[simp] lemma coe_one (S : set α) [subgroup S] : ((1 : S) : α) = 1 := rfl

@[simp] lemma coe_mul {S : set α} [subgroup S] : ∀ a b : S, ((a * b : S) : α) = (a : α) * (b : α) :=
λ ⟨a, ha⟩ ⟨b, hb⟩, rfl

@[simp] lemma coe_inv {S : set α} [subgroup S] : ∀ a : S, ((a⁻¹ : S) : α) = (a : α)⁻¹ := 
λ ⟨a, ha⟩, rfl

@[simp] lemma coe_pow {S : set α} [subgroup S] (a : S) (n : ℕ) : ((monoid.pow a n : S) : α) = monoid.pow a n := 
by induction n; simp[pow_succ, *]

@[simp] lemma coe_gpow {S : set α} [subgroup S] (a : S) (i : ℤ) : ((gpow a i : S) : α) = gpow a i :=
by cases i; simp

end subgroup

section cyclic 

class cyclic_group (α : Type*) extends group α :=
(cyclic : ∃ a, ∀ b : α, ∃ i : ℤ, a^i = b)

instance cyclic_group.comm_group {α : Type*} [h : cyclic_group α] : comm_group α := 
{ mul_comm :=
  λ x y, let ⟨a, ha⟩ := cyclic_group.cyclic α in
         let ⟨i, hi⟩ := ha x in
         let ⟨j, hj⟩ := ha y in
         hi ▸ hj ▸ gpow_mul_comm a i j,
  ..h }

variables {α : Type*} [group α]

def cycle (a : α) := {b : α | ∃ i : ℤ, a^i = b}

instance [fintype α] (a : α) : fintype (cycle a) := set_fintype _

instance (a : α) : subgroup (cycle a) := 
{ one_mem := ⟨0, by simp⟩,
  inv_mem := λ b ⟨i, hi⟩, ⟨-i, hi ▸ gpow_neg _ _⟩,
  mul_mem := λ b c ⟨i, hi⟩ ⟨j, hj⟩, ⟨i + j, hi ▸ (hj ▸ (gpow_add _ _ _))⟩ }

instance (a : α) : cyclic_group (cycle a) :=
{ cyclic := ⟨⟨a, 1, pow_one _⟩, λ ⟨b, ⟨i, hi⟩⟩, 
⟨i, subtype.eq ((subgroup.coe_gpow (⟨a, _⟩ : cycle a) i).trans hi)⟩ ⟩ }

lemma mem_cycle_self (a : α) [fintype (cycle a)] : a ∈ cycle a := ⟨1, by simp⟩

lemma exists_int_pow_eq_one_of_finite_cycle (a : α) [fintype (cycle a)] : ∃ i : ℤ, i ≠ 0 ∧ a^i = 1 :=
by_contradiction $ λ h, @not_injective_nat_fintype _ _ _ 
(λ n, (⟨a^(nat.succ n), ⟨int.nat_abs (nat.succ n), by rw [int.nat_abs_of_nat] ⟩ ⟩ : cycle a)) $
have h : ∀ i : ℤ, ¬(i ≠ 0 ∧ a^i = 1) := not_exists.mp h,
have h₁ : ∀ (i : ℤ), a^i = 1 → ¬i ≠ 0 := λ i, not_and'.mp (h i),
λ m n hmn, have hmn' : a^(nat.succ m) =a^(nat.succ n) := subtype.mk.inj hmn,
begin 
  rw [← sub_add_cancel ((nat.succ m) : ℤ) (nat.succ n), gpow_add, ← mul_right_inj (a^nat.succ n)⁻¹,
      mul_inv_self, mul_assoc, mul_inv_self, mul_one] at hmn',
  exact nat.succ_inj (int.coe_nat_inj $ eq_of_sub_eq_zero $ not_not.mp $ h₁ _ hmn') 
end

lemma exists_nat_pow_eq_one_of_finite_cycle (a : α) [fintype (cycle a)] :
    ∃ n : ℕ, 0 < n ∧ monoid.pow a n = 1 :=
let ⟨i, hi⟩ := exists_int_pow_eq_one_of_finite_cycle a in
⟨int.nat_abs i, ⟨int.nat_abs_pos_of_ne_zero hi.1,
or.by_cases (int.nat_abs_eq i) 
(λ h, by rw h at hi; exact (gpow_coe_nat _ _).symm.trans hi.2) 
(λ h, by rw [h, gpow_neg] at hi; exact (gpow_coe_nat _ _).symm.trans (inv_eq_one.1 hi.2)) ⟩ ⟩

def ord (a : α) [fintype (cycle a)] := nat.find $ exists_nat_pow_eq_one_of_finite_cycle a

variables (a : α) [fintype (cycle a)]

@[simp] lemma pow_ord : monoid.pow a (ord a) = 1 := (nat.find_spec $ exists_nat_pow_eq_one_of_finite_cycle a).2

lemma ord_pos : 0 < ord a := (nat.find_spec $ exists_nat_pow_eq_one_of_finite_cycle a).1

lemma ord_le {a : α} [fintype (cycle a)] {n : ℕ} (ha0 : 0 < n) (han : monoid.pow a n = 1) : ord a ≤ n :=
nat.find_min' (exists_nat_pow_eq_one_of_finite_cycle a) ⟨ha0, han⟩

lemma lt_ord {a : α} [fintype (cycle a)] {n : ℕ} (hn : n < ord a) : n = 0 ∨ monoid.pow a n ≠ 1 :=
have h : ¬0 < n ∨ ¬ monoid.pow a n = 1 := (decidable.not_and_iff_or_not _ _).1 (nat.find_min
(exists_nat_pow_eq_one_of_finite_cycle a) hn), by rwa [nat.pos_iff_ne_zero', not_not] at h

lemma ord_dvd_int_iff (i : ℤ) : (ord a : ℤ) ∣ i ↔ a^i = 1 :=
⟨λ h₁, let ⟨k, hk⟩ := exists_eq_mul_right_of_dvd h₁ in by simp [hk, gpow_mul, pow_ord],
λ h₁, by_contradiction $ λ h₂,
begin 
  rw int.dvd_iff_mod_eq_zero at h₂,
  have h₃ : gpow a (i % ↑(ord a)) = 1,
  { rw ← int.mod_add_div i (ord a) at h₁,
    simp [gpow_add, gpow_mul] at h₁,
    exact h₁ },
  have hzc := int.coe_nat_ne_zero.2 (ne_of_lt (ord_pos a)).symm,
  have h₄ : (int.nat_abs (i % ord a) : ℤ) = (i % ord a) := 
    int.nat_abs_of_nonneg (int.mod_nonneg _ hzc),
  have h₅ : monoid.pow a (int.nat_abs (i % ↑(ord a))) = 1 := by rwa [← gpow_coe_nat, h₄],
  have h₆ : (ord a : ℤ) ≤ (i % ↑(ord a)) := by rw [← h₄, int.coe_nat_le];
    exact ord_le (int.nat_abs_pos_of_ne_zero h₂) h₅,
  have h₇ := int.mod_lt i hzc,
  rw abs_of_nonneg (int.coe_nat_le.2 (nat.zero_le _)) at h₇,
  exact not_le_of_gt h₇ h₆,
end⟩

lemma ord_dvd_nat_iff (n : ℕ) : ord a ∣ n ↔ monoid.pow a n = 1 :=
let h := ord_dvd_int_iff a n in by simp [int.coe_nat_dvd] at h; assumption

lemma fintype_cycle_of_pow_eq_one (i : ℤ) (a : α) (hi : i ≠ 0) (h : a^i = 1) : fintype (cycle a) :=
fintype.of_surjective
(λ n : fin (int.nat_abs i), (⟨monoid.pow a n.val, n.val, by simp⟩ : cycle a)) $
λ ⟨b, j, hj⟩, have hji : 0 ≤ j % i := int.mod_nonneg _ hi,
⟨⟨int.nat_abs (j % i), 
by rw [← int.coe_nat_lt, int.nat_abs_of_nonneg hji, ← int.abs_eq_nat_abs];
exact int.mod_lt _ hi⟩, 
subtype.eq $ show monoid.pow a (int.nat_abs (j % i)) = b,
by rw [← gpow_coe_nat, int.nat_abs_of_nonneg hji, int.mod_def, sub_eq_add_neg, 
    gpow_add, gpow_neg, gpow_mul, h, hj]; simp⟩

-- lemma ord_eq_cycle_card (a : α) [fintype (cycle a)] : ord a = card (cycle a) :=
-- card_fin (ord a) ▸ card_congr
-- ⟨λ (n : fin (ord a)), (⟨monoid.pow a n.val, ⟨n.val, by simp⟩⟩ : cycle a),
-- λ ⟨b, hb⟩, have ho : (0 : ℤ) < ord a := int.coe_nat_lt.2 (ord_pos a),
-- have h₁ : classical.some hb % ↑(ord a) ≥ 0 := int.mod_nonneg _ (ne_of_lt ho).symm,
-- ⟨int.nat_abs (classical.some hb % (ord a : ℤ)),
-- int.coe_nat_lt.1 ((int.nat_abs_of_nonneg h₁).symm ▸ int.mod_lt_of_pos _ ho)⟩,
-- λ ⟨n, hn⟩, begin cases lt_ord hn with h h,
-- simp [h],
--  end,sorry⟩

-- too long

lemma ord_eq_cycle_card (a : α) [fintype (cycle a)] : ord a = fintype.card (cycle a) :=
fintype.card_fin (ord a) ▸ (fintype.card_congr $ equiv.of_bijective $ 
show function.bijective (λ (n : fin (ord a)), (⟨monoid.pow a n.val, ⟨n.val, by simp⟩⟩ : cycle a)), from
⟨λ n m h, fin.eq_of_veq $ --injective proof
begin
  cases n with n hn,
  cases m with m hm,
  wlog h : m ≤ n using m n,
  { exact (this hm hn h_1.symm).symm },
  replace h_1 : monoid.pow a n = monoid.pow a m := subtype.mk.inj h_1,
  rw [← nat.sub_add_cancel h, ← one_mul (monoid.pow a m), pow_add, mul_right_inj] at h_1,
  have h₁ := or.neg_resolve_right (lt_ord (lt_of_le_of_lt (nat.sub_le n m) hn)) h_1,
  exact le_antisymm (nat.sub_eq_zero_iff_le.1 (or.neg_resolve_right (lt_ord 
    (lt_of_le_of_lt (nat.sub_le n m) hn)) h_1)) h,
end, λ ⟨x, ⟨i, hi⟩ ⟩, -- surjective proof
have ho : (ord a : ℤ) ≠ 0 := int.coe_nat_ne_zero.2 (ne_of_lt (ord_pos _)).symm,
have hio : (int.to_nat (i % ↑(ord a)) : ℤ) = i % ord a := int.to_nat_of_nonneg (int.mod_nonneg _ ho),
⟨⟨int.to_nat (i % (ord a : ℤ)), int.coe_nat_lt.1 $ 
by rw [hio, ← abs_of_nonneg (int.coe_nat_le.2 (nat.zero_le (ord a))), int.mod_abs];
exact int.mod_lt _ ho⟩,
begin
  simp,
  rw [← gpow_coe_nat, hio, int.mod_def],
  simp [gpow_add, gpow_mul, gpow_neg, hi]
end⟩⟩)
#print ord_eq_cycle_card
end cyclic

section coset

open subgroup

variables {α : Type*} [group α] (S : set α) [subgroup S]

def lcoset (b : α) := {a : α | ∃ s ∈ S, b * s = a}

def rcoset (b : α) := {a : α | ∃ s ∈ S, s * b = a}

lemma lcoset_eq {S : set α} [subgroup S] {a b : α} : b ∈ lcoset S a → lcoset S a = lcoset S b :=
λ ⟨sa, hSsa, hsa⟩, set.ext $ λ x, 
⟨λ ⟨sb, hSsb, hsb⟩, ⟨sa⁻¹ * sb, ⟨mul_mem (inv_mem hSsa) hSsb, hsa ▸ by simpa [mul_assoc] ⟩ ⟩,
λ ⟨sb, hSsb, hsb⟩, ⟨sa * sb, ⟨mul_mem hSsa hSsb, mul_assoc a sa sb ▸ hsa.symm ▸ hsb ⟩ ⟩ ⟩ 

lemma rcoset_eq {S : set α} [subgroup S] {a b : α} : b ∈ rcoset S a → rcoset S a = rcoset S b :=
λ ⟨sa, hSsa, hsa⟩, set.ext $ λ x, 
⟨λ ⟨sb, hSsb, hsb⟩, ⟨sb * sa⁻¹, ⟨mul_mem hSsb (inv_mem hSsa), hsa ▸ by simpa [mul_assoc] ⟩ ⟩,
λ ⟨sb, hSsb, hsb⟩, ⟨sb * sa, ⟨mul_mem hSsb hSsa, (mul_assoc sb sa a).symm ▸ hsa.symm ▸ hsb ⟩ ⟩ ⟩ 

@[simp] lemma mem_lcoset_self (a : α) : a ∈ lcoset S a := ⟨1, one_mem _, mul_one _⟩

@[simp] lemma mem_rcoset_self (a : α) : a ∈ rcoset S a := ⟨1, one_mem _, one_mul _⟩

lemma lcoset_card [fintype α] (a : α) : card (lcoset S a) = fintype.card S :=
fintype.card_congr $ @equiv.of_bijective (lcoset S a) S 
(λ x, ⟨a⁻¹ * x, let ⟨y, hyS, (hy : a * y = x)⟩ := x.2 in by rwa ← hy; simpa⟩) 
⟨λ x y h, by simp at h; exact subtype.eq h, λ x, ⟨ ⟨a * x, ⟨x, ⟨x.2, rfl⟩ ⟩ ⟩, by simp ⟩ ⟩

lemma rcoset_card [fintype α] (a : α) : card (rcoset S a) = fintype.card S :=
fintype.card_congr $ @equiv.of_bijective (rcoset S a) S 
(λ x, ⟨x * a⁻¹, let ⟨y, hyS, (hy : y *  a = x)⟩ := x.2 in by rwa ← hy; simpa⟩) 
⟨λ x y h, by simp at h; exact subtype.eq h, λ x, ⟨ ⟨x * a, ⟨x, ⟨x.2, rfl⟩ ⟩ ⟩, by simp ⟩ ⟩

instance lcoset_setoid : setoid α := 
{ r := λ a b, b ∈ lcoset S a,
  iseqv := ⟨mem_lcoset_self S,
  λ a b h, by rw ← lcoset_eq h; exact mem_lcoset_self S a,
  λ a b c hab hbc, by rwa lcoset_eq hab⟩ }

def index [fintype α] := card (quotient (lcoset_setoid S))

theorem lagrange [fintype α] : card α = card S * index S :=
have h : (λ x : quotient (lcoset_setoid S), card {a // ⟦a⟧ = x}) = (λ x, card S) := 
  funext (λ x, begin
    simp only [@eq_comm _ _ x],
    rw [← quot.out_eq x, ← lcoset_card S (quot.out x)],
    congr,
    exact set.ext (λ y, quotient.eq)
  end),
by rw [card_quotient (lcoset_setoid S), h, finset.sum_const, nat.smul_eq_mul]; refl

end coset

lemma card_eq_ord_mul_index {α : Type*} [group α] [fintype α] (a : α) : card α = ord a * index (cycle a) :=
(ord_eq_cycle_card a).symm ▸ lagrange _

@[simp] lemma pow_card {α : Type*} [group α] [fintype α] (a : α) : monoid.pow a (card α) = 1 :=
(ord_dvd_nat_iff _ _).1 $ (card_eq_ord_mul_index a).symm ▸ dvd_mul_right _ _

open equiv

namespace perm
variables {α : Type*}

lemma mul_apply (a b : perm α) (x : α) : (a * b) x = (a (b x)) := rfl

@[simp] lemma one_apply (x : α) : (1 : perm α) x = x := rfl

instance [decidable_eq α] (h : fintype α): fintype (perm α) := 
fintype.of_equiv {y : (α → α) × (α → α) // function.left_inverse y.2 y.1 ∧ function.right_inverse y.2 y.1}
⟨λ x, ⟨x.1.1, x.1.2, x.2.1, x.2.2⟩, λ x, ⟨⟨x.1, x.2⟩, ⟨x.3, x.4⟩⟩, λ ⟨⟨_, _⟩, _, _⟩, rfl, λ ⟨_, _, _, _⟩, rfl⟩

instance perm.cycle.fintype [h : fintype α] (a : perm α) : fintype (cycle a) := @cycle.fintype (perm α) _ (perm.fintype h) a

def support (a : perm α) : set α := {x : α | a x ≠ x}

example (f g : perm α) : support (g * f * g⁻¹) = set.image g (support f) :=
set.ext $ λ y, ⟨λ h : _ ≠ _, ⟨g⁻¹ y, λ h₁, by
  rw [mul_apply, mul_apply, h₁, ← mul_apply, mul_inv_self] at h;
  exact h rfl,
show (g * g⁻¹) y = y,by rw mul_inv_self; refl⟩, 
λ ⟨x, (hx : _ ≠ _ ∧ _)⟩, show _ ≠ _, from
begin 
  rw [mul_apply, ← hx.2, ← mul_apply, ← mul_apply, mul_assoc, inv_mul_self, mul_one, mul_apply], 
  assume h,
  rw (equiv.bijective g).1 h at hx,
  exact hx.1 rfl
end⟩

def disjoint (a b : perm α) := _root_.disjoint (support a) (support b)

lemma disjoint_or {a b : perm α} : disjoint a b ↔ ∀ x : α, a x = x ∨ b x = x :=
have h : disjoint a b ↔ ∀ x : α, ¬ (a x ≠ x ∧ b x ≠ x) := 
  ⟨λ (h : (λ x, a x ≠ x ∧ b x ≠ x : set α) = ∅) x, 
  show x ∉ {x : α | a x ≠ x ∧ b x ≠ x}, by rw h; simp, 
λ h, set.ext $ λ x, ⟨λ h₁, absurd h₁ (h x), λ h₁, absurd h₁ (set.not_mem_empty _)⟩⟩,
by rw h; simp only [or_iff_not_and_not]

lemma disjoint_comm {a b : perm α} (hd : disjoint a b) : a * b = b * a := 
equiv.ext _ _ $ λ x, show a (b x) = b (a x), from or.by_cases (disjoint_or.1 hd x) 
(λ h, h.symm ▸ or.by_cases (disjoint_or.1 hd $ b x) (λ h₁, h₁) (λ h₁, ((equiv.bijective b).1 h₁).symm ▸ h))
(λ h, h.symm ▸ or.by_cases (disjoint_or.1 hd $ a x) (λ h₁, ((equiv.bijective a).1 h₁.symm) ▸ h.symm) (λ h₁, h₁.symm))

lemma eq_one_of_support_eq_empty {a : perm α} [fintype (support a)] (h : support a = ∅) : a = 1 :=
ext _ _ $ λ x, have hx : x ∉ support a := h.symm ▸ set.not_mem_empty x, not_not.1 hx

lemma exists_mem_support_of_ne_one {a : perm α} (h : a ≠ 1) : ∃ x : α, x ∈ support a :=
by_contradiction $ λ h₁, h $ ext _ _ $ by simp [support, *] at *

def same_cycle (a : perm α) (x y : α) := ∃ i : ℤ, (a^i) x = y

@[refl] lemma same_cycle.refl {a : perm α} (x : α) : same_cycle a x x := ⟨0, by rw gpow_zero; refl⟩

@[symm] lemma same_cycle.symm {a : perm α} {x y : α} (h : same_cycle a x y) : same_cycle a y x :=
let ⟨i, hi⟩ := h in ⟨-i, by rw [← hi, ←mul_apply, ← gpow_add, neg_add_self, gpow_zero, one_apply] ⟩ 

@[trans] lemma same_cycle.trans {a : perm α} {x y z : α} (hxy : same_cycle a x y) (hyz : same_cycle a y z)
    : same_cycle a x z :=
let ⟨i, hi⟩ := hxy in let ⟨j, hj⟩ := hyz in ⟨j + i, begin rw [gpow_add, mul_apply, hi], simp [hi, hj] end⟩

lemma same_cycle_apply {a : perm α} {x y : α} (h : same_cycle a x y) (i : ℤ) : same_cycle a ((a^i) x) y :=
same_cycle.trans (same_cycle.symm (⟨i, rfl⟩ : same_cycle a x ((a^i) x))) h

def cycle_of (a : perm α) (x : α) : perm α :=
{ to_fun   := λ y, ite (same_cycle a x y) (a y) y,
  inv_fun  := λ y, ite (same_cycle a x y) (a⁻¹ y) y,
  left_inv := λ y, dite (same_cycle a x y)
  (λ h, have h₁ : same_cycle a x (a y) := same_cycle.symm (same_cycle_apply (same_cycle.symm h) 1), 
    by simp [h, h₁]; rw [← mul_apply, inv_mul_self, one_apply]) 
  (λ h, by simp [h]),
  right_inv := λ y, dite (same_cycle a x y) 
  (λ h, have h₁ : same_cycle a x (a⁻¹ y) := same_cycle.symm (same_cycle_apply (same_cycle.symm h) (-1)),
    by simp [h, h₁]; rw [← mul_apply, mul_inv_self, one_apply]) 
  (λ h, by simp [h]) }

def is_cycle (a : perm α) := a ≠ 1 ∧ ∀ x y : α, x ∈ support a → y ∈ support a → same_cycle a x y

lemma support_disjoint_mul {a b : perm α} (h : disjoint a b) : support (a * b) = support a ∪ support b :=
set.ext $ λ x, or.by_cases (disjoint_or.1 h x) 
(λ h₁, ⟨λ h₂, or.inr (have h₂ : b (a x) ≠ x := by rw disjoint_comm h at h₂; exact h₂, by rw h₁ at h₂; exact h₂),
λ h₂, by rw disjoint_comm h; exact show b (a x) ≠ x, by rw h₁; exact or.resolve_left h₂ (not_not.2 h₁)⟩) 
(λ h₁, ⟨λ (h₂ : a (b x) ≠ x), or.inl $ by rw h₁ at h₂; exact h₂,
λ h₂, show a (b x) ≠ x, by rw h₁; exact or.resolve_right h₂ (not_not.2 h₁)⟩)

lemma exists_disjoint_factors [fintype α] (a : perm α) (h : ¬ is_cycle a) (h₁ : a ≠ 1) :
    ∃ b c : perm α, disjoint b c ∧ b * c = a ∧ card (support b) < card (support a) ∧ 
    card (support c) < card (support a) :=
begin
  suffices : ∀ (n : ℕ) (a : perm α), ¬ is_cycle a → a ≠ 1 → card (support a) ≤ n → 
      ∃ b c : perm α, disjoint b c ∧ b * c = a ∧ card (support b) < card (support a) ∧ 
      card (support c) < card (support a),
  exact this (card (support a)) a h h₁ (le_refl _),
  assume n,
  induction n with n hi,
  { assume a h h₁ h₂,
    exact absurd (eq_one_of_support_eq_empty (set.card_eq_zero.1 (nat.eq_zero_of_le_zero h₂))) h₁ },
  { assume a h h₁ h₂,
    cases exists_mem_support_of_ne_one h₁ with x hx,
    
     }
end

-- lemma product_disjoint [fintype α] (a : perm α) : ∃ l : list (perm α), (∀ b ∈ l, is_cycle b ∧ b ≠ 1) ∧ (∀ b c ∈ l, disjoint b c) ∧ list.prod l = a :=
-- begin
--   suffices : ∀ (n : ℕ) (a : perm α), ord a ≤ n → ∃ l : list (perm α), (∀ b ∈ l, is_cycle b ∧ b ≠ 1) ∧ (∀ b c ∈ l, disjoint b c) ∧ list.prod l = a,
--   { exact this (ord a) a (le_refl _) },
--   assume n,
--   induction n with n hi,
--   { exact λ a ha, absurd (lt_of_lt_of_le (ord_pos a) ha) dec_trivial },
--   assume a ha,


-- end

end perm