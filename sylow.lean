import group_theory.order_of_element data.fintype data.nat.prime data.nat.modeq .zmod_as_fin2 algebra.pi_instances
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

lemma card_pi {δ : α → Type*} [decidable_eq α] [Π a, decidable_eq (δ a)]
  (s : finset α) (t : Π a, finset (δ a)) : (s.pi t).card = s.prod (λ a, card (t a)) :=
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

lemma card_eq_zero_iff [fintype α] : card α = 0 ↔ (α → false) :=
⟨λ h a, have e : α ≃ empty := classical.choice (card_eq.1 (by simp [h])),
  (e a).elim, 
λ h, have e : α ≃ empty := ⟨λ a, (h a).elim, λ a, a.elim, λ a, (h a).elim, λ a, a.elim⟩, 
  by simp [card_congr e]⟩

lemma card_pos [fintype α] (a : α) : 0 < card α :=
nat.pos_of_ne_zero (mt card_eq_zero_iff.1 (λ h, h a))

lemma card_le_of_injective [fintype α] [fintype β] (f : α → β) 
  (hf : function.injective f) : card α ≤ card β :=
by haveI := classical.prop_decidable; exact
finset.card_le_card_of_inj_on f (λ _ _, finset.mem_univ _) (λ _ _ _ _ h, hf h)

lemma card_le_one_iff [fintype α] : card α ≤ 1 ↔ (∀ a b : α, a = b) :=
let n := card α in
have hn : n = card α := rfl,
match n, hn with
| 0 := λ ha, ⟨λ h, λ a, (card_eq_zero_iff.1 ha.symm a).elim, λ _, ha ▸ nat.le_succ _⟩
| 1 := λ ha, ⟨λ h, λ a b, let ⟨x, hx⟩ := card_eq_one_iff.1 ha.symm in
  by rw [hx a, hx b],
    λ _, ha ▸ le_refl _⟩
| (n+2) := λ ha, ⟨λ h, by rw ← ha at h; exact absurd h dec_trivial, 
  (λ h, card_unit ▸ card_le_of_injective (λ _, ())
    (λ _ _ _, h _ _))⟩
end

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

lemma card_image_of_inj_on {s : set α} [fintype s]
  {f : α → β} [fintype (f '' s)] (H : ∀x∈s, ∀y∈s, f x = f y → x = y) : 
  fintype.card (f '' s) = fintype.card s :=
by haveI := classical.prop_decidable; exact
calc fintype.card (f '' s) = (s.to_finset.image f).card : card_fintype_of_finset' _ (by simp)
... = s.to_finset.card : card_image_of_inj_on 
    (λ x hx y hy hxy, H x (mem_to_finset.1 hx) y (mem_to_finset.1 hy) hxy)
... = card s : (card_fintype_of_finset' _ (λ a, mem_to_finset)).symm

lemma card_image_of_injective (s : set α) [fintype s]
  {f : α → β} [fintype (f '' s)] (H : function.injective f) : 
  fintype.card (f '' s) = fintype.card s :=
card_image_of_inj_on $ λ x _ y _ h, H h

def equiv_univ (α : Type u) : α ≃ (set.univ : set α) :=
{ to_fun := λ a, ⟨a, mem_univ _⟩,
  inv_fun := λ a, a.1,
  left_inv := λ a, rfl,
  right_inv := λ ⟨a, ha⟩, rfl }

@[simp] lemma card_univ (α : Type u) [fintype α] [fintype.{u} (set.univ : set α)] : 
  fintype.card (set.univ : set α) = fintype.card α := 
eq.symm (card_congr (equiv_univ α))

end set

namespace pi
variable {I : Type u}     -- The indexing type
variable {f : I → Type v} -- The family of types already equiped with instances

lemma mul_apply [∀ i, has_mul $ f i] (a b : Π i, f i) (i : I) : (a * b) i = a i * b i := rfl

lemma one_apply [∀ i, has_one $ f i] (i : I) : (1 : Π i, f i) i = 1 := rfl

end pi

local attribute [instance, priority 0] 
  classical.prop_decidable fintype.subtype_fintype set_fintype set.fintype_image

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
    (@equiv.of_bijective _ _ 
      (show fixed_points f → {a : set α // card ↥{x : α | orbit f x = a} % p ≠ 0},
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

namespace sylow

def F₁ (n : ℕ) [Zmod.pos n] (v : Zmod n → G) : Zmod (n+1) → G := 
λ m, if h : m.1 < n then v ⟨m.1, h⟩ else ((fin_list n).map v).prod⁻¹

lemma F₁_injective {p : ℕ} [Zmod.pos p] : function.injective (@F₁ G _ p _) := 
λ x y hxy, funext (λ ⟨a, ha⟩, begin
  have := congr_fun hxy (fin.raise ⟨a, ha⟩),
  have h : (fin.raise ⟨a, ha⟩).1 < p := ha,
  unfold F₁ at this,
  split_ifs at this,
  exact this
end)

def Gstar (G : Type*) [group G] (n : ℕ) [Zmod.pos n] : set (Zmod (n + 1) → G) := 
F₁ n '' (set.univ : set (Zmod n → G))

lemma mem_Gstar (n : ℕ) [Zmod.pos n] (v : Zmod (n + 1) → G) (hv : v ∈ Gstar G n) :
((fin_list (n + 1)).map x).prod = 1 := begin


end


def F₂ (α : Type*) (n : ℕ) [h0 : Zmod.pos n] : 
  group_action (multiplicative (Zmod (n + 1))) (Gstar G n) :=
⟨λ a : Zmod (n + 1), 
  { to_fun := λ v, begin end ,
    inv_fun := λ (v : Zmod n → α) (m : Zmod n), v (m - a),
    left_inv := λ v, by simp,
    right_inv := λ v : Zmod n → α, show (λ (m : Zmod n), v (m + a - a)) = v, 
      from funext (λ m, by rw add_sub_cancel) }, 
⟨λ a b : Zmod n, equiv.ext _ _ (λ x : Zmod n → α, 
  funext (λ m : Zmod n, show x (m + (a + b)) = x (m + a + b),
    by rw add_assoc))⟩⟩

lemma fixed_points_F₂_eq_const {n : ℕ} [h0 : Zmod.pos n] {v : Zmod n → G}
  (h : v ∈ fixed_points (F₂ G n)) (i j : Zmod n) : v i = v j :=
calc v i = v (j + i) : add_comm i j ▸ (congr_fun ((mem_fixed_points.1 h) (mem_orbit (F₂ G n) v j)) i).symm
... = v j : congr_fun ((mem_fixed_points.1 h) (mem_orbit (F₂ G n) v i)) j

lemma fixed_points_F₂_pow_n [fintype G] {n : ℕ} (hn : nat.prime (n + 1))
  [h0 : Zmod.pos n]
  {v : Zmod (n+1) → G} (hv : v ∈ Gstar G n)
  (h : v ∈ fixed_points (F₂ G (n + 1))) : v 0 ^ (n + 1) = 1 :=
let ⟨w, hw⟩ := hv in
begin
  have h₁ : dite _ _ _ = _ := congr_fun hw.2 ⟨n, nat.lt_succ_self n⟩,
  rw dif_neg (lt_irrefl _) at h₁,
  have h₂ : dite (0 < n) _ _ = _ := congr_fun hw.2 0,
  have h₂ : w 0 = v 0 := by rwa dif_pos h0.pos at h₂,
  refine (@mul_left_inj _ _ (w 0 ^ (-n : ℤ)) _ _).1 _,
  conv { to_rhs, rw [h₁, fixed_points_F₂_eq_const h _ 0] },
  rw [← h₂, ← gpow_coe_nat, ← gpow_add],
  simp
end

lemma one_mem_fixed_points_F₂ [fintype G] {n : ℕ} [h0 : Zmod.pos n] :
  (1 : Zmod n → G) ∈ fixed_points (F₂ G n) :=
mem_fixed_points.2 (λ y hy, funext (λ j,
  let ⟨i, hi⟩ := mem_orbit_iff.1 hy in
  have hj : (1 : G) = y j := congr_fun hi j,
    hj ▸ rfl))

attribute [trans] dvd.trans

lemma exists_prime_order_of_dvd_card [fintype G] {p : ℕ} (hp : nat.prime p)
  (hdvd : p ∣ card G) : ∃ x : G, order_of x = p :=
let n := p - 1 in
have hn : p = n + 1 := nat.succ_sub hp.pos,
have hnp : nat.prime (n + 1) := hn ▸ hp,
by haveI hn0 : Zmod.pos n := ⟨nat.lt_of_succ_lt_succ hnp.gt_one⟩; exact
have hlt : ¬(n : Zmod (n + 1)).val < n :=
  not_lt_of_ge (by rw [Zmod.cast_val, nat.mod_eq_of_lt (nat.lt_succ_self _)]; 
    exact le_refl _),
have hcard1 : card (Gstar G n) = card (Zmod n → G) := 
  set.card_univ (Zmod n → G) ▸ set.card_image_of_injective 
    _ F_injective,
have hcard : card (Gstar G n) = card G ^ n :=
  by conv { rw hcard1, to_rhs, rw ← card_fin n };
    exact fintype.card_fun,
have hZmod : @fintype.card (multiplicative (Zmod (n+1))) (fin.fintype _) = 
  (n+1) ^ 1 := (nat.pow_one (n + 1)).symm ▸ card_fin _,
have hmodeq : _ = _ := mpl hnp hZmod (F₂ (Gstar G n) (n + 1)),
have hdvdcard : (n + 1) ∣ card (Zmod (n + 1) → (Gstar G n)) :=
  calc (n + 1) = p : hn.symm
  ... ∣ card G ^ 1 : by rwa nat.pow_one
  ... ∣ card G ^ n : nat.pow_dvd_pow _ hn0.pos
  ... = card (Gstar G n) : hcard.symm
  ... ∣ card (Zmod (n + 1) → (Gstar G n)) : 
    by rw [fintype.card_fun, Zmod.card_Zmod, nat.pow_add, nat.pow_one];
      exact dvd_mul_left _ _,
have hdvdcard₂ : (n + 1) ∣ card (fixed_points (F₂ (Gstar G n) (n + 1))) :=
  nat.dvd_of_mod_eq_zero (hmodeq ▸ (nat.mod_eq_zero_of_dvd hdvdcard)),
have hcard_pos : 0 < card (fixed_points (F₂ (Gstar G n) (n + 1))) :=
  fintype.card_pos ⟨1, one_mem_fixed_points_F₂⟩,
have hle : 1 < card (fixed_points (F₂ (Gstar G n) (n + 1))) :=
  calc 1 < n + 1 : hnp.gt_one
  ... ≤ _ : nat.le_of_dvd hcard_pos hdvdcard₂,
let ⟨⟨x, hx⟩, hx₁⟩ := classical.not_forall.1 (mt fintype.card_le_one_iff.2 (not_le_of_gt hle)) in
let ⟨⟨y, hy⟩, hy₁⟩ := classical.not_forall.1 hx₁ in
have hxy : x ≠ 1 ∨ y ≠ 1 := or_iff_not_imp_left.2 
  (λ hx1 hy1, hy₁ (by simp [hy1, not_not.1 hx1])),
begin
  clear _let_match hx₁ hy₁,
  rw hn,
  wlog h : x ≠ 1 using x y,
  { exact hxy },
  { existsi (x 0).1,
    refine le_antisymm (nat.find_min' _ ⟨dec_trivial, _⟩) _,
     }
end


-- lemma exists_prime_order_of_dvd_card [fintype G] {p : ℕ} (hp : nat.prime p)
--   (hdvd : p ∣ card G) : ∃ x : G, order_of x = p :=
-- let n := p - 1 in
-- have hn : p = n + 1 := nat.succ_sub hp.pos,
-- have hnp : nat.prime (n + 1) := hn ▸ hp,
-- by haveI : Zmod.pos n := ⟨nat.lt_of_succ_lt_succ hnp.gt_one⟩; exact
-- have hlt : ¬(n : Zmod (n + 1)).val < n :=
--   not_lt_of_ge (by rw [Zmod.cast_val, nat.mod_eq_of_lt (nat.lt_succ_self _)]; 
--     exact le_refl _),
-- have hcard1 : card (Gstar G n) = card (Zmod n → G) := 
--   set.card_univ (Zmod n → G) ▸ set.card_image_of_injective 
--     _ F_injective,
-- have hcard : card (Gstar G n) = card G ^ n :=
--   by conv { rw hcard1, to_rhs, rw ← card_fin n };
--     exact fintype.card_fun,
-- have hZmod : @fintype.card (multiplicative (Zmod (n+1))) (fin.fintype _) = 
--   (n+1) ^ 1 := (nat.pow_one (n + 1)).symm ▸ card_fin _,
-- have hmodeq : _ = _ := mpl hnp hZmod (F₂ G (n + 1)),
-- have hdvdcard : (n + 1) ∣ card (Zmod (n + 1) → G) :=
--   calc (n + 1) = p : hn.symm
--   ... ∣ card G : hdvd
--   ... ∣ card G * card G ^ n : dvd_mul_right _ _
--   ... = card (Zmod (n + 1) → G) :
--     by simp [fintype.card_fun, Zmod.card_Zmod, mul_comm, nat.pow_add],
-- have hdvdcard₂ : (n + 1) ∣ card (fixed_points (F₂ G (n + 1))) :=
--   nat.dvd_of_mod_eq_zero (hmodeq ▸ (nat.mod_eq_zero_of_dvd hdvdcard)),
-- have hcard_pos : 0 < card (fixed_points (F₂ G (n + 1))) :=
--   fintype.card_pos ⟨1, one_mem_fixed_points_F₂⟩,
-- have hle : 1 < card (fixed_points (F₂ G (n + 1))) :=
--   calc 1 < n + 1 : hnp.gt_one
--   ... ≤ _ : nat.le_of_dvd hcard_pos hdvdcard₂,
-- let ⟨⟨x, hx⟩, hx₁⟩ := classical.not_forall.1 (mt fintype.card_le_one_iff.2 (not_le_of_gt hle)) in
-- let ⟨⟨y, hy⟩, hy₁⟩ := classical.not_forall.1 hx₁ in
-- have hxy : x ≠ 1 ∨ y ≠ 1 := or_iff_not_imp_left.2 
--   (λ hx1 hy1, hy₁ (by simp [hy1, not_not.1 hx1])),
-- begin
--   clear _let_match hx₁ hy₁,
--   rw hn,
--   wlog h : x ≠ 1 using x y,
--   { exact hxy },
--   { existsi x 0,
--     refine le_antisymm (nat.find_min' _ ⟨dec_trivial, _⟩) _,
--      }
-- end
-- #print subsingleton
end sylow