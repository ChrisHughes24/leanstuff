import group_theory.order_of_element data.fintype data.nat.prime data.nat.modeq
open equiv fintype finset
universes u v w
variables {G : Type u} {α : Type v} {β : Type w} [group G]

def fin_list (n : ℕ) : list (fin n) := 
  (list.range n).pmap (λ m hm, ⟨m, hm⟩) (λ m hm, list.mem_range.1 hm)

namespace finset

lemma filter_insert_of_pos [decidable_eq α] (s : finset α) {P : α → Prop} 
  [decidable_pred P] (a : α) (h : P a) : (insert a s).filter P = insert a (s.filter P) :=
ext.2 (λ x, by rw [mem_filter, mem_insert, mem_insert, mem_filter, eq_comm];
  exact ⟨λ h₁, by cases h₁.1; simp * at *, λ h₁, by cases h₁; simp * at *⟩)

lemma filter_insert_of_neg [decidable_eq α] (s : finset α) {P : α → Prop} 
  [decidable_pred P] (a : α) (h : ¬P a) : (insert a s).filter P = s.filter P :=
ext.2 (λ x, by rw [mem_filter, mem_insert, mem_filter, eq_comm];
  exact ⟨λ h₁, by cases h₁.1; simp * at *, by finish⟩)

lemma prod_const [comm_monoid β] (s : finset α) (b : β) 
  [decidable_eq α] : s.prod (λ x, b) = b ^ s.card :=
finset.induction_on s rfl (by simp [pow_add, mul_comm] {contextual := tt})

lemma sum_const [add_comm_monoid β] (s : finset α) (b : β) 
  [decidable_eq α] : s.sum (λ x, b) = add_monoid.smul s.card b :=
finset.induction_on s rfl (by simp [add_monoid.add_smul] {contextual := tt})

lemma card_pi {δ : α → Type*} [decidable_eq α] [Π (a : α), decidable_eq (δ a)]
  (s : finset α) (t : Π (a : α), finset (δ a)) : (s.pi t).card = s.prod (λ a, card (t a)) :=
multiset.card_pi _ _

end finset

lemma nat.sum_mod [decidable_eq α] (s : finset α) (f : α → ℕ) (n : ℕ) : 
  s.sum f ≡ (s.filter (λ x, f x % n ≠ 0)).sum f [MOD n] :=
finset.induction_on s rfl begin 
  assume a s has ih,
  by_cases ha : f a % n ≠ 0,
  { rw [finset.sum_insert has, finset.filter_insert_of_pos s a ha, finset.sum_insert],
    exact nat.modeq.modeq_add rfl ih,
    { finish [finset.mem_filter] } },
  { rw [finset.sum_insert has, finset.filter_insert_of_neg s a ha, 
      ← zero_add (finset.sum (finset.filter _ _) _)],
    rw [ne.def, ← nat.zero_mod n] at ha,
    exact nat.modeq.modeq_add (not_not.1 ha) ih }  
end 

namespace perm 

@[simp] lemma one_apply (a : α) : (1 : perm α) a = a := rfl

@[simp] lemma mul_apply (x y : perm α) (a : α) : (x * y) a = x (y a) := rfl

end perm

namespace fintype

instance quotient_fintype {α : Type*} [fintype α] (s : setoid α)
  [decidable_eq (quotient s)] : fintype (quotient s) :=
fintype.of_surjective quotient.mk (λ x, quotient.induction_on x (λ x, ⟨x, rfl⟩))

instance finset_fintype [fintype α] : fintype (finset α) :=
⟨finset.univ.powerset, λ x, finset.mem_powerset.2 (finset.subset_univ _)⟩

instance set.fintype (α : Type u) [fintype α] [decidable_eq α] : fintype (set α) := 
fintype.of_bijective finset.to_set
⟨λ _ _, finset.coe_eq_coe.1, 
λ x, by haveI := classical.prop_decidable;
  exact ⟨set.finite.to_finset ⟨set_fintype _⟩, finset.coe_to_finset⟩⟩

def subtype_fintype [fintype α] (p : α → Prop) [decidable_pred p] : fintype {x // p x} :=
set_fintype _

lemma card_eq_one_iff [fintype α] : card α = 1 ↔ (∃ x : α, ∀ y : α, y = x) :=
by rw [← card_unit, card_eq]; exact
⟨λ h, ⟨(classical.choice h).symm unit.star, λ y, (classical.choice h).bijective.1 
    (subsingleton.elim _ _)⟩, 
λ ⟨x, hx⟩, ⟨⟨λ _, unit.star, λ _, x, λ _, (hx _).trans (hx _).symm, 
    λ _, subsingleton.elim _ _⟩⟩⟩

open finset

lemma card_pi {β : α → Type*} [fintype α] [decidable_eq α]
  [f : Π a, fintype (β a)] [Π a, decidable_eq (β a)] : 
  card (Π a, β a) = univ.prod (λ a, card (β a)) :=
by letI f : fintype (Πa∈univ, β a) :=
  ⟨(univ.pi $ λa, univ), assume f, finset.mem_pi.2 $ assume a ha, mem_univ _⟩;
exact calc card (Π a, β a) = card (Π a ∈ univ, β a) : card_congr 
  ⟨λ f a ha, f a, λ f a, f a (mem_univ a), λ _, rfl, λ _, rfl⟩ 
... = univ.prod (λ a, card (β a)) : finset.card_pi _ _

lemma card_fun [fintype α] [decidable_eq α] [fintype β] [decidable_eq β] :
  card (α → β) = card β ^ card α :=
by rw [card_pi, prod_const, nat.pow_eq_pow]; refl

end fintype

namespace set

lemma card_eq_of_eq {s t : set α} [fintype s] [fintype t] (h : s = t) :
  card s = card t := 
by congr; assumption

end set

local attribute [instance, priority 0] 
  classical.prop_decidable fintype.subtype_fintype set_fintype

section should_be_in_group_theory

noncomputable instance [fintype G] (H : set G) [is_subgroup H] : 
fintype (left_cosets H) := fintype.quotient_fintype (left_rel H)

lemma card_eq_card_cosets_mul_card_subgroup [fintype G] (H : set G) [is_subgroup H] : 
  card G = card (left_cosets H) * card H :=
by rw ← card_prod;
  exact card_congr (is_subgroup.group_equiv_left_cosets_times_subgroup _)

end should_be_in_group_theory


def group_action (G : Type u) (α : Type v) [group G] :=
{f : G → perm α // is_group_hom f}

instance : has_coe_to_fun (group_action G α) :=
{ F := λ _, G → perm α,
  coe := λ x, x.val }

instance group_action.is_group_hom (f : group_action G α) : is_group_hom f := f.2

def orbit (f : group_action G α) (a : α) := (λ x : G, f x a) '' set.univ

lemma mem_orbit_iff {f : group_action G α} {a b : α} : 
  b ∈ orbit f a ↔ ∃ x : G, f x a = b :=
by finish [orbit, set.image]

def orbit_rel (f : group_action G α) (a b : α) := orbit f a = orbit f b

@[simp] lemma mem_orbit (f : group_action G α) (a : α) (x : G) :
  f x a ∈ orbit f a :=
⟨x, set.mem_univ _, rfl⟩

lemma mem_orbit_self (f : group_action G α) (a : α) :
  a ∈ orbit f a :=
⟨1, set.mem_univ _, show f 1 a = a, by rw [is_group_hom.one f, perm.one_apply]⟩

lemma orbit_eq {f : group_action G α} {a b : α} : a ∈ orbit f b → orbit f a = orbit f b :=
λ ⟨x, _, (hx : f x b = a)⟩, set.ext (λ c, ⟨λ ⟨y, _, (hy : f y a = c)⟩, ⟨y * x, set.mem_univ _,
  show f (y * x) b = c, by rw [is_group_hom.mul f, perm.mul_apply, hx, hy]⟩,     
λ ⟨y, _, (hy : f y b = c)⟩, ⟨y * x⁻¹, set.mem_univ _ , 
  show f (y * x⁻¹) a = c, by 
    conv {to_rhs, rw [← hy, ← mul_one y, ← inv_mul_self x, ← mul_assoc,
      is_group_hom.mul f, perm.mul_apply, hx]}⟩⟩)

noncomputable def orbit_fintype (f : group_action G α) (a : α) [fintype G] : 
fintype (orbit f a) := set.fintype_image _ _

def stabilizer (f : group_action G α) (a : α) : set G := 
{ x : G | f x a = a }

lemma mem_stabilizer_iff {f : group_action G α} {a : α} {x : G} : 
  x ∈ stabilizer f a ↔ f x a = a := 
iff.rfl

instance (f : group_action G α) (a : α) : is_subgroup (stabilizer f a) :=
{ one_mem := show f 1 a = a, by rw [is_group_hom.one f, perm.one_apply],
  mul_mem := λ x y (hx : f x a = a) (hy : f y a = a),
    show f (x * y) a = a, by rw is_group_hom.mul f; simp *,
  inv_mem := λ x (hx : f x a = a), show f x⁻¹ a = a, 
    by rw [← hx, ← perm.mul_apply, ← is_group_hom.mul f, 
    inv_mul_self, is_group_hom.one f, perm.one_apply, hx] }

noncomputable lemma orbit_equiv_left_cosets (a : α) (f : group_action G α) : 
  orbit f a ≃ left_cosets (stabilizer f a) :=
let I := left_rel (stabilizer f a) in
{ to_fun := λ b, @quotient.mk _ I (classical.some (mem_orbit_iff.1 b.2)),
  inv_fun := λ x, ⟨f (@quotient.out _ I x) a, mem_orbit _ _ _⟩,
  left_inv := λ b, subtype.eq 
    (let x := classical.some (mem_orbit_iff.1 b.2) in
    let y := @quotient.out _ I (@quotient.mk _ I x) in
    show f y a = b.1, begin
      have : f (x⁻¹ * y) a = a := 
        @setoid.symm _ I _ _ (@quotient.mk_out _ I x),
      rw [← one_mul y, ← mul_inv_self x, mul_assoc, is_group_hom.mul f, perm.mul_apply, this],
      exact classical.some_spec (mem_orbit_iff.1 b.2)
    end),
  right_inv := λ x, 
    let hx := mem_orbit_iff.1 (mem_orbit f a (@quotient.out _ I x)) in
    let y := classical.some hx in
    have hy : f y a = f (@quotient.out _ I x) a := classical.some_spec hx,
    show @quotient.mk _ I y = _,
    begin
      rw ← @quotient.out_eq _ I x,
      refine @quotient.sound _ I _  _ _,
      show y⁻¹ * _ ∈ _,
      rw [mem_stabilizer_iff, is_group_hom.mul f, perm.mul_apply, ← hy, ← perm.mul_apply,
        ← is_group_hom.mul f, inv_mul_self, is_group_hom.one f, perm.one_apply]
    end }

def fixed_points (f : group_action G α) : set α := {a : α | ∀ x, x ∈ stabilizer f a}

lemma mem_fixed_points {f : group_action G α} {x : α} : x ∈ fixed_points f ↔ 
  (∀ {y}, y ∈ orbit f x → y = x) := 
⟨λ h y h₁, let ⟨a, ha⟩ := mem_orbit_iff.1 h₁ in ha ▸ h a, 
λ h x, mem_stabilizer_iff.2 (h (mem_orbit _ _ _))⟩

lemma card_orbit_of_mem_fixed_point {f : group_action G α} {x : α} [fintype (orbit f x)] : 
  x ∈ fixed_points f ↔ card (orbit f x) = 1 := 
begin
  rw [fintype.card_eq_one_iff, mem_fixed_points],
  split,
  { exact λ h, ⟨⟨x, mem_orbit_self _ _⟩, λ ⟨y, hy⟩, subtype.eq (h hy)⟩ }, 
  { assume h y hy,
    rcases h with ⟨⟨z, hz⟩, hz₁⟩,
    exact calc y = z : subtype.mk.inj (hz₁ ⟨y, hy⟩)
      ... = x : (subtype.mk.inj (hz₁ ⟨x, mem_orbit_self _ _⟩)).symm }
end

lemma mpl [fintype α] [fintype G] {p n : ℕ} (hp : nat.prime p) (h : card G = p ^ n)
  (f : group_action G α) : card α ≡ card (fixed_points f) [MOD p] :=
have hcard : ∀ s : set α, card ↥{x : α | orbit f x = s} % p ≠ 0
    ↔ card ↥{x : α | orbit f x = s} = 1 := 
  λ s, ⟨λ hs, begin
    have h : ∃ y, orbit f y = s := by_contradiction (λ h, begin
      rw not_exists at h,
      have : {x | orbit f x = s} = ∅ := set.eq_empty_iff_forall_not_mem.2 h,
      rw [set.card_eq_of_eq this, set.empty_card', nat.zero_mod] at hs,
      contradiction
    end),
    cases h with y hy,
    have hseq : {x | orbit f x = s} = orbit f y := set.ext (λ z, 
      ⟨λ h : orbit f z = s, hy.symm ▸ h ▸ mem_orbit_self _ _, 
      λ h, show orbit f z = s, by rwa orbit_eq h⟩),
    rw [card_eq_card_cosets_mul_card_subgroup (stabilizer f y), 
      ← card_congr (orbit_equiv_left_cosets y f)] at h,
    have : ∃ k ≤ n, card (orbit f y) = p ^ k := (nat.dvd_prime_pow hp).1 
      (h ▸ dvd_mul_right _ _),
    rcases this with ⟨k, hk₁, hk₂⟩,
    rw [set.card_eq_of_eq hseq, hk₂] at hs ⊢,
    have : ¬p ∣ p ^ k := mt nat.mod_eq_zero_of_dvd hs,
    cases k,
    { refl },
    { simpa [nat.pow_succ] using this }
  end, 
  λ hs, hs.symm ▸ (nat.mod_eq_of_lt hp.gt_one).symm ▸ λ h, nat.no_confusion h⟩,
have h : (finset.univ.filter (λ a, card {x | orbit f x = a} % p ≠ 0)).sum 
  (λ a : set α, card {x | orbit f x = a}) = card (fixed_points f),
  from calc _ = (finset.univ.filter (λ a, card {x | orbit f x = a} % p ≠ 0)).sum 
    (λ a : set α, 1) : finset.sum_congr rfl (λ s hs, (hcard s).1 (finset.mem_filter.1 hs).2)
  ... = card {a : set α | card ↥{x : α | orbit f x = a} % p ≠ 0} :
  begin
    rw [finset.sum_const, nat.smul_eq_mul, mul_one],
    refine eq.symm (set.card_fintype_of_finset' _ _),
    simp [finset.mem_filter],
  end
  ... = card (fixed_points f) : fintype.card_congr 
    (@equiv.of_bijective _ _ (show fixed_points f → {a : set α // card ↥{x : α | orbit f x = a} % p ≠ 0},
      from λ x, ⟨orbit f x.1, begin 
          rw [hcard, fintype.card_eq_one_iff],
          exact ⟨⟨x, rfl⟩, λ ⟨y, hy⟩, 
            have hy : y ∈ orbit f x := (show orbit f y = orbit f x, from hy) ▸ mem_orbit_self _ _,
            subtype.eq (mem_fixed_points.1 x.2 hy)⟩
        end⟩) 
      ⟨λ x y hxy, 
        have hxy : orbit f x.1 = orbit f y.1 := subtype.mk.inj hxy,
        have hxo : x.1 ∈ orbit f y.1 := hxy ▸ mem_orbit_self _ _,
        subtype.eq (mem_fixed_points.1 y.2 hxo), 
      λ ⟨s, hs⟩, begin
        rw [hcard, fintype.card_eq_one_iff] at hs,
        rcases hs with ⟨⟨x, hx₁⟩, hx₂⟩,
        exact ⟨⟨x, mem_fixed_points.2 (λ y hy, 
          subtype.mk.inj (hx₂ ⟨y, by have := orbit_eq hy; simpa [this, hx₁] using hx₁⟩))⟩,
            by simpa using hx₁⟩
      end⟩).symm,
calc card α % p = finset.sum finset.univ (λ a : set α, card {x // orbit f x = a}) % p : 
  by rw [card_congr (equiv_fib (orbit f)), fintype.card_sigma] 
... = _ : nat.sum_mod _ _ _
... = fintype.card ↥(fixed_points f) % p : by rw ← h; congr

def F (n : ℕ) (x : fin n → G) : fin (n+1) → G := 
λ m, if h : m.1 < n then x ⟨m, h⟩ else ((fin_list n).map x).prod

lemma F_injective {p : ℕ} (hp : 0 < p) : function.injective (@F G _ p) := 
λ x y hxy, funext (λ ⟨a, ha⟩, begin
  have := congr_fun hxy (fin.raise ⟨a, ha⟩),
  have h : (fin.raise ⟨a, ha⟩).1 < p := ha,
  unfold F at this,
  split_ifs at this,
  exact this,
end)

def H_star (n : ℕ) (H : set G) [is_subgroup H] := 
F n '' (set.univ : set (fin n → H))