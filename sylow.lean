import group_theory.order_of_element data.fintype data.nat.prime data.nat.modeq .zmod_as_fin2 algebra.pi_instances group_theory.subgroup
open equiv fintype finset
universes u v w
variables {G : Type u} {α : Type v} {β : Type w} [group G]

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

lemma coe_to_finset' [decidable_eq α] (s : set α) [fintype s] : (↑s.to_finset : set α) = s :=
set.ext (by simp)

lemma ssubset_iff_subset_not_subset {s t : set α} : s ⊂ t ↔ s ⊆ t ∧ ¬ t ⊆ s :=
by split; simp [set.ssubset_def, ne.def, set.subset.antisymm_iff] {contextual := tt}

lemma coe_ssubset [decidable_eq α] {s t : finset α} : (↑s : set α) ⊂ ↑t ↔ s ⊂ t :=
show ↑s ⊆ ↑t ∧ ↑s ≠ ↑t ↔ s ⊆ t ∧ ¬t ⊆ s,
  by split; simp [set.ssubset_def, ne.def, set.subset.antisymm_iff] {contextual := tt}

lemma card_lt_card [decidable_eq α] {s t : set α} [fintype s] [fintype t] (h : s ⊂ t) : card s < card t :=
begin
  rw [card_fintype_of_finset' _ (λ x, mem_to_finset), card_fintype_of_finset' _ (λ x, mem_to_finset)],
  rw [← coe_to_finset' s, ← coe_to_finset' t, coe_ssubset] at h,
  exact finset.card_lt_card h,
end

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
  classical.prop_decidable fintype.subtype_fintype set_fintype

section should_be_in_group_theory

noncomputable instance [fintype G] (H : set G) [is_subgroup H] : 
fintype (left_cosets H) := fintype.quotient_fintype (left_rel H)

lemma card_eq_card_cosets_mul_card_subgroup [fintype G] (H : set G) [is_subgroup H] : 
  card G = card (left_cosets H) * card H :=
by rw ← card_prod;
  exact card_congr (is_subgroup.group_equiv_left_cosets_times_subgroup _)

lemma order_of_dvd_of_pow_eq_one [fintype G] {a : G} {n : ℕ} (h : a ^ n = 1) :
  order_of a ∣ n :=
by_contradiction
(λ h₁, nat.find_min _ (show n % order_of a < order_of a, 
  from nat.mod_lt _ (nat.pos_of_ne_zero (order_of_ne_zero _))) 
    ⟨mt nat.dvd_of_mod_eq_zero h₁, by rwa ← pow_eq_mod_order_of⟩)

lemma eq_one_of_order_of_eq_one [fintype G] {a : G} (h : order_of a = 1) : a = 1 :=
by conv { to_lhs, rw [← pow_one a, ← h, pow_order_of_eq_one] }

lemma order_eq_card_gpowers [fintype G] {a : G} : order_of a = card (gpowers a) :=
begin
  refine (finset.card_eq_of_bijective _ _ _ _).symm,
  { exact λn hn, ⟨gpow a n, ⟨n, rfl⟩⟩ },
  { exact assume ⟨_, i, rfl⟩ _,
      have pos: (0:int) < order_of a,
        from int.coe_nat_lt.mpr $ nat.pos_iff_ne_zero.mpr $ order_of_ne_zero a,
      have 0 ≤ i % (order_of a),
        from int.mod_nonneg _ $ ne_of_gt pos,
      ⟨int.to_nat (i % order_of a),
        by rw [← int.coe_nat_lt, int.to_nat_of_nonneg this];
          exact ⟨int.mod_lt_of_pos _ pos, subtype.eq gpow_eq_mod_order_of.symm⟩⟩ },
  { intros, exact finset.mem_univ _ },
  { exact assume i j hi hj eq, pow_injective_of_lt_order_of a hi hj $ by simpa using eq }
end

@[simp] lemma card_trivial [fintype (is_subgroup.trivial G)] :
  fintype.card (is_subgroup.trivial G) = 1 := fintype.card_eq_one_iff.2
  ⟨⟨(1 : G), by simp⟩, λ ⟨y, hy⟩, subtype.eq $ is_subgroup.mem_trivial.1 hy⟩

local attribute [instance] left_rel normal_subgroup.to_is_subgroup

instance (H : set G) [normal_subgroup H] : group (left_cosets H) :=
{ one := ⟦1⟧,
  mul := λ a b, quotient.lift_on₂ a b
  (λ a b, ⟦a * b⟧)
  (λ a₁ a₂ b₁ b₂ (hab₁ : a₁⁻¹ * b₁ ∈ H) (hab₂ : a₂⁻¹ * b₂ ∈ H),
    quotient.sound
    ((is_subgroup.mul_mem_cancel_left H (is_subgroup.inv_mem hab₂)).1
        (by rw [mul_inv_rev, mul_inv_rev, ← mul_assoc (a₂⁻¹ * a₁⁻¹),
          mul_assoc _ b₂, ← mul_assoc b₂, mul_inv_self, one_mul, mul_assoc (a₂⁻¹)];
          exact normal_subgroup.normal _ hab₁ _))),
  mul_assoc := λ a b c, quotient.induction_on₃
    a b c (λ a b c, show ⟦_⟧ = ⟦_⟧, by rw mul_assoc),
  one_mul := λ a, quotient.induction_on a
    (λ a, show ⟦_⟧ = ⟦_⟧, by rw one_mul),
  mul_one := λ a, quotient.induction_on a
    (λ a, show ⟦_⟧ = ⟦_⟧, by rw mul_one),
  inv := λ a, quotient.lift_on a (λ a, ⟦a⁻¹⟧)
    (λ a b hab, quotient.sound begin
      show a⁻¹⁻¹ * b⁻¹ ∈ H,
      rw ← mul_inv_rev,
      exact is_subgroup.inv_mem (is_subgroup.mem_norm_comm hab)
    end),
  mul_left_inv := λ a, quotient.induction_on a
    (λ a, show ⟦_⟧ = ⟦_⟧, by rw inv_mul_self) }

def normalizer (H : set G) : set G :=
{ g : G | ∀ n, n ∈ H ↔ g * n * g⁻¹ ∈ H }

instance (H : set G) [is_subgroup H] : is_subgroup (normalizer H) :=
{ one_mem := by simp [normalizer],
  mul_mem := λ a b (ha : ∀ n, n ∈ H ↔ a * n * a⁻¹ ∈ H)
    (hb : ∀ n, n ∈ H ↔ b * n * b⁻¹ ∈ H) n,
    by rw [mul_inv_rev, ← mul_assoc, mul_assoc a, mul_assoc a, ← ha, ← hb],
  inv_mem := λ a (ha : ∀ n, n ∈ H ↔ a * n * a⁻¹ ∈ H) n,
    by rw [ha (a⁻¹ * n * a⁻¹⁻¹)];
    simp [mul_assoc] }

lemma subset_normalizer (H : set G) [is_subgroup H] : H ⊆ normalizer H :=
λ g hg n, by rw [is_subgroup.mul_mem_cancel_left _ ((is_subgroup.inv_mem_iff _).2 hg),
  is_subgroup.mul_mem_cancel_right _ hg]

instance (H : set G) [is_subgroup H] : normal_subgroup { x : normalizer H | ↑x ∈ H } :=
{ one_mem := show (1 : G) ∈ H, from is_submonoid.one_mem _,
  mul_mem := λ a b ha hb, show (a * b : G) ∈ H, from is_submonoid.mul_mem ha hb,
  inv_mem := λ a ha, show (a⁻¹ : G) ∈ H, from is_subgroup.inv_mem ha, 
  normal := λ a ha ⟨m, hm⟩, (hm a).1 ha }

lemma mem_normalizer_fintype_iff {H : set G} [fintype H] {x : G} : 
  x ∈ normalizer H ↔ ∀ n, n ∈ H → x * n * x⁻¹ ∈ H :=
⟨λ h n, (h n).1,
λ h n, ⟨h n, λ h₁,
have hsubs₁ : (λ n, x * n * x⁻¹) '' H ⊆ H := λ n ⟨y, hy⟩, hy.2 ▸ h y hy.1,
have hcard : card ((λ (n : G), x * n * x⁻¹) '' H) = card H :=
  set.card_image_of_injective H (λ a₁ a₂ ha, (mul_left_inj x).1 ((mul_right_inj (x⁻¹)).1 ha)),
have hsubs₂ : H ⊆ (λ n, x * n * x⁻¹) '' H := by_contradiction 
  (λ h, by have := set.card_lt_card (set.ssubset_iff_subset_not_subset.2 ⟨hsubs₁, h⟩);
    exact lt_irrefl (card H) (by rwa hcard at this)),
begin
  rw set.subset.antisymm hsubs₂ hsubs₁ at h₁,
  cases h₁ with m hm,
  have : m = n, from (mul_left_inj x).1 ((mul_right_inj (x⁻¹)).1 hm.2),
  exact this ▸ hm.1  
end⟩ ⟩

end should_be_in_group_theory

structure group_action (G : Type u) [group G] (α : Type v) :=
( to_fun : G → α → α) 
( one : ∀ a : α, to_fun (1 : G) a = a )
( mul : ∀ (x y : G) (a : α), to_fun (x * y) a = to_fun x (to_fun y a))

instance : has_coe_to_fun (group_action G α) :=
{ F := λ _, G → α → α,
  coe := λ x, x.to_fun }

namespace group_action

@[simp] lemma one_apply (f : group_action G α) (a : α) : f 1 a = a := group_action.one f a

lemma mul_apply (f : group_action G α) (x y : G) (a : α) : f (x * y) a = f x (f y a) := group_action.mul _ _ _ _

lemma bijective (f : group_action G α) (x : G) : function.bijective (f x) :=
function.bijective_iff_has_inverse.2 ⟨f (x⁻¹), 
  λ a, by rw [← mul_apply, inv_mul_self, one_apply],
  λ a, by rw [← mul_apply, mul_inv_self, one_apply]⟩ 

/-- restriction of a group action on a Type α to s, a set α -/
def restriction {f : group_action G α} {s : set α}
  (h : ∀ a ∈ s, ∀ x : G, f x a ∈ s) :
  group_action G s :=
{ to_fun := λ x a, ⟨f x a, h a.1 a.2 x⟩,
  mul := λ x y a, subtype.eq (group_action.mul f x y a),
  one := λ a, subtype.eq (group_action.one f a) } 

lemma restriction_apply {f : group_action G α} {s : set α}
  (h : ∀ a ∈ s, ∀ x : G, f x a ∈ s) (x : G) (a : s) :
  f x a = (restriction h) x a := rfl

def orbit (f : group_action G α) (a : α) := set.range (λ x : G, f x a)

lemma mem_orbit_iff {f : group_action G α} {a b : α} :
  b ∈ orbit f a ↔ ∃ x : G, f x a = b :=
by finish [orbit]

def orbit_rel (f : group_action G α) (a b : α) := orbit f a = orbit f b

@[simp] lemma mem_orbit (f : group_action G α) (a : α) (x : G) :
  f x a ∈ orbit f a :=
⟨x, rfl⟩

lemma mem_orbit_self (f : group_action G α) (a : α) :
  a ∈ orbit f a :=
⟨1, show f 1 a = a, by simp⟩

lemma orbit_eq {f : group_action G α} {a b : α} : a ∈ orbit f b → orbit f a = orbit f b :=
λ ⟨x, (hx : f x b = a)⟩, set.ext (λ c, ⟨λ ⟨y, (hy : f y a = c)⟩, ⟨y * x,
  show f (y * x) b = c, by rwa [mul_apply, hx]⟩,
λ ⟨y, (hy : f y b = c)⟩, ⟨y * x⁻¹,
  show f (y * x⁻¹) a = c, by
    conv {to_rhs, rw [← hy, ← mul_one y, ← inv_mul_self x, ← mul_assoc,
      mul_apply, hx]}⟩⟩)

noncomputable def orbit_fintype (f : group_action G α) (a : α) [fintype G] :
fintype (orbit f a) := set.fintype_range _

def stabilizer (f : group_action G α) (a : α) : set G :=
{ x : G | f x a = a }

lemma mem_stabilizer_iff {f : group_action G α} {a : α} {x : G} :
  x ∈ stabilizer f a ↔ f x a = a :=
iff.rfl

lemma orbit_restriction {f : group_action G α} {s : set α} {a : s}
  {h : ∀ a ∈ s, ∀ x, f x a ∈ s} {b : s} :
  b ∈ orbit (restriction h) a ↔ (b : α) ∈ orbit f a :=
⟨λ h, let ⟨x, hx⟩ := mem_orbit_iff.1 h in
  mem_orbit_iff.2 ⟨x, hx ▸ rfl⟩,
λ h, let ⟨x, hx⟩ := mem_orbit_iff.1 h in
  mem_orbit_iff.2 ⟨x, subtype.eq hx⟩⟩

lemma stabilizer_restriction {f : group_action G α} {s : set α} {a : s}
  (h : ∀ a ∈ s, ∀ x, f x a ∈ s) :
stabilizer (restriction h) a = stabilizer f a :=
set.ext (λ x,by rw [mem_stabilizer_iff, mem_stabilizer_iff];
  exact ⟨λ h, by conv {to_rhs, rw ← h}; refl,
  λ h, subtype.eq h⟩)

instance (f : group_action G α) (a : α) : is_subgroup (stabilizer f a) :=
{ one_mem := one_apply _ _,
  mul_mem := λ x y (hx : f x a = a) (hy : f y a = a),
    show f (x * y) a = a, by rw mul_apply; simp *,
  inv_mem := λ x (hx : f x a = a), show f x⁻¹ a = a,
    by rw [← hx, ← mul_apply, inv_mul_self, one_apply, hx] }

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
      rw [← one_mul y, ← mul_inv_self x, mul_assoc, mul_apply, this],
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
      rw [mem_stabilizer_iff, mul_apply, ← hy, ← mul_apply, inv_mul_self, one_apply]
    end }

def fixed_points (f : group_action G α) : set α := {a : α | ∀ x, x ∈ stabilizer f a}

lemma mem_fixed_points {f : group_action G α} {x : α} : x ∈ fixed_points f ↔
  (∀ {y}, y ∈ orbit f x → y = x) :=
⟨λ h y h₁, let ⟨a, ha⟩ := mem_orbit_iff.1 h₁ in ha ▸ h a,
λ h x, mem_stabilizer_iff.2 (h (mem_orbit _ _ _))⟩

lemma fixed_points_restriction {f : group_action G α} {s : set α}
  (h : ∀ a ∈ s, ∀ x, f x a ∈ s) {a : s} :
  a ∈ fixed_points (restriction h) ↔ (a : α) ∈ fixed_points f :=
show (∀ x, x ∈ stabilizer (restriction h) a) ↔
  (∀ x, x ∈ stabilizer f a),
by rw stabilizer_restriction h; refl

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

end group_action

namespace sylow
open group_action

def F₁ (n : ℕ) [Zmod.pos n] (v : Zmod n → G) : Zmod (n+1) → G := 
λ m, if h : m.1 < n then v m.1 else ((list.range n).map (λ m : ℕ, v (m : Zmod n))).prod⁻¹

lemma F₁_injective {p : ℕ} [h0 : Zmod.pos p] : function.injective (@F₁ G _ p _) := 
λ x y hxy, funext (λ ⟨a, ha⟩, begin
  have : dite _ _ _ = dite _ _ _ := congr_fun hxy a,
  rw [Zmod.cast_val, nat.mod_eq_of_lt (nat.lt_succ_of_lt ha), 
    dif_pos ha, dif_pos ha] at this,
  rwa Zmod.mk_eq_cast
end)

/-- set of elements of G^n such that the product of the 
  list of elements of the vector is one -/
def Gstar (G : Type*) [group G] (n : ℕ) [Zmod.pos n] : set (Zmod n → G) := 
{v | ((list.range n).map (λ m : ℕ, v (↑m : Zmod n))).prod = 1 }

lemma prod_lemma (n : ℕ) [Zmod.pos n] (v : Zmod (n + 1) → G) :
  ((list.range (n + 1)).map (λ m : ℕ, v (m : Zmod (n + 1)))).prod =
  list.prod (list.map (λ (m : ℕ), v ↑m) (list.range n)) * v ↑n :=
by rw [list.range_concat, list.map_append, list.prod_append,
  list.map_singleton, list.prod_cons, list.prod_nil, mul_one]

lemma mem_Gstar_iff {n : ℕ} [Zmod.pos n] (v : Zmod (n + 1) → G) :
  v ∈ Gstar G (n + 1) ↔ v ∈ F₁ n '' (set.univ : set (Zmod n → G)) :=
⟨λ h : list.prod (list.map (λ (m : ℕ), v ↑m) (list.range (n + 1))) = 1, 
  have h₁ : list.map (λ (m : ℕ), v ((m : Zmod n).val : Zmod (n+1))) (list.range n)
    = list.map (λ (m : ℕ), v m) (list.range n) := list.map_congr (λ m hm, 
  have hm' : m < n := list.mem_range.1 hm,  
    by simp[nat.mod_eq_of_lt hm']),
⟨λ m, v m.val, set.mem_univ _, funext (λ i, show dite _ _ _ = _, begin
  split_ifs,
  { refine congr_arg _ (fin.eq_of_veq _), 
    simp [nat.mod_eq_of_lt h_1, nat.mod_eq_of_lt (nat.lt_succ_of_lt h_1)] },
  { have hi : i = n := fin.eq_of_veq begin 
      rw [Zmod.cast_val, nat.mod_eq_of_lt (nat.lt_succ_self _)],
      exact le_antisymm (nat.le_of_lt_succ i.2) (le_of_not_gt h_1),
    end,
    rw [h₁, hi, inv_eq_iff_mul_eq_one, ← prod_lemma, h] }
end)⟩,
λ ⟨w, hw⟩, 
have h : list.map (λ m : ℕ, w m) (list.range n) = list.map (λ m : ℕ, v m) (list.range n) :=
list.map_congr (λ k hk, 
  have hk' : k < n := list.mem_range.1 hk,
  hw.2 ▸ (show _ = dite _ _ _, 
    by rw [Zmod.cast_val, nat.mod_eq_of_lt (nat.lt_succ_of_lt hk'), dif_pos hk'])),
begin
  show list.prod (list.map (λ (m : ℕ), v ↑m) (list.range (n + 1))) = 1,
  rw [prod_lemma, ← h, ← hw.2],
  show _ * dite _ _ _ = (1 : G),
  rw [Zmod.cast_val, nat.mod_eq_of_lt (nat.lt_succ_self _), dif_neg (lt_irrefl _),
    mul_inv_self],
end⟩

def F₂ (α : Type*) (n : ℕ) [h0 : Zmod.pos n] : 
  group_action (multiplicative (Zmod n)) (Zmod n → α) :=
{ to_fun := λ i v m, v (m + i),
  mul := λ (i j : Zmod n) (v : Zmod n → α), 
    funext (λ m, congr_arg v (add_assoc _ _ _).symm),
  one := λ (v : Zmod n → α), funext (λ m, congr_arg v (add_zero m)) }

lemma fixed_points_F₂_eq_const {n : ℕ} [h0 : Zmod.pos n] {v : Zmod n → G}
  (h : v ∈ fixed_points (F₂ G n)) (i j : Zmod n) : v i = v j :=
calc v i = v (j + i) : add_comm i j ▸ (congr_fun ((mem_fixed_points.1 h) (mem_orbit (F₂ G n) v j)) i).symm
... = v j : congr_fun ((mem_fixed_points.1 h) (mem_orbit (F₂ G n) v i)) j

lemma map_succ_range : ∀ n : ℕ, list.range (nat.succ n) = 0 :: (list.range n).map nat.succ
| 0 := rfl
| (n+1) := by rw [list.range_concat, list.range_concat, list.map_append,
  ← list.cons_append, ← map_succ_range, list.range_concat, list.map_singleton]

open nat

lemma list.prod_const [monoid α] : ∀ {l : list α} {a : α}, (∀ b ∈ l, b = a) → l.prod = a ^ l.length
| [] := λ _ _, rfl
| (b::l) := λ a ha,
have h : ∀ b ∈ l, b = a := λ b hb, ha b (list.mem_cons_of_mem _ hb),
have hb : b = a := ha b (list.mem_cons_self _ _),
by simp [_root_.pow_add, list.prod_const h, hb]

lemma F₂_on_Gstar {n : ℕ} [h0 : Zmod.pos n] {v : Zmod (succ n) → G}
  (hv : v ∈ Gstar G (succ n)) (i : Zmod (succ n)) :
  (F₂ G (succ n)) (i : Zmod (succ n)) v ∈ Gstar G (succ n) :=
begin
  cases i with i hi,
  rw Zmod.mk_eq_cast,
  clear hi,
  induction i with i ih,
  { show list.prod (list.map (λ (m : ℕ), v (m + 0)) (list.range (succ n))) = 1,
    simpa },
  { show list.prod (list.map (λ (m : ℕ), v (m + (i + 1))) (list.range (succ n))) = 1,
    replace ih : list.prod (list.map (λ (m : ℕ), v (m + i)) (list.range (succ n))) = 1 := ih, 
    rw [list.range_concat, list.map_append, list.prod_append, list.map_singleton, 
      list.prod_cons, list.prod_nil, mul_one] at ⊢ ih,
    have h : list.map (λ m : ℕ, v (↑m + (i + 1))) (list.range n) =
      list.map (λ m : ℕ, v (m + i)) (list.map (λ m : ℕ, m + 1) (list.range n)),
    { simp [list.map_map, function.comp] },
    resetI,
    cases n,
    { exact (lt_irrefl 0 h0.pos).elim },
    { have h : list.map (λ m : ℕ, v (↑m + (i + 1))) (list.range n) =
        list.map (λ m : ℕ, v (m + i)) (list.map succ (list.range n)),
      { simp [list.map_map, function.comp] },
      have h₁ : (succ n : Zmod (succ (succ n))) + (↑i + 1) = i,
      { rw [add_left_comm, ← nat.cast_one, ← nat.cast_add, Zmod.cast_self_eq_zero, add_zero] },
      have h₂ : (n : Zmod (succ (succ n))) + i + 1 = succ n + i := by simp [succ_eq_add_one],
      rw [map_succ_range, list.map_cons, list.prod_cons, ← h, nat.cast_zero, zero_add] at ih,
      have := eq_inv_mul_of_mul_eq ih,
      rw [list.range_concat, list.map_append, list.map_singleton, list.prod_append,
        list.prod_cons, list.prod_nil, mul_one, ← add_assoc, h₁, h₂, this],
      simp } }
end

def F₂Gstar (G : Type u) [group G] (n : ℕ) [Zmod.pos n] : 
  group_action (multiplicative (Zmod (succ n))) (Gstar G (succ n)) :=
restriction (λ v, F₂_on_Gstar)

lemma fixed_points_F₂_pow_n [fintype G] {n : ℕ} (hn : nat.prime (succ n))
  [h0 : Zmod.pos n]
  {v : Gstar G (succ n)}
  (hv : v ∈ fixed_points (F₂Gstar G n)) : (v : Zmod (succ n) → G) 0 ^ (n + 1) = 1 :=
let ⟨w, hw⟩ := (mem_Gstar_iff _).1 v.2 in
have hv' : (v : Zmod (succ n) → G) ∈ _ := ((fixed_points_restriction _).1 hv),
begin
  have h₁ : dite _ _ _ = (v : Zmod (succ n) → G) _ := congr_fun hw.2 ⟨n, nat.lt_succ_self n⟩,
  rw dif_neg (lt_irrefl _) at h₁,
  have h₂ : ∀ b, b < n → w b = (v : Zmod (succ n) → G) b := λ b hb, begin
    have : dite _ _ _ = _ := congr_fun hw.2 b,
    rwa [Zmod.cast_val_of_lt (lt_succ_of_lt hb), dif_pos hb] at this,
  end,
  have hb : ∀ (b : G), b ∈ list.map (λ (m : ℕ), w ↑m) (list.range n) → b = w 0 := λ b hb,
    let ⟨i, hi⟩ := list.mem_map.1 hb in
    by rw [← hi.2, h₂ _ (list.mem_range.1 hi.1), fixed_points_F₂_eq_const 
      ((fixed_points_restriction _).1 hv) _ 0];
      exact (h₂ 0 h0.pos).symm,
  refine (@mul_left_inj _ _ (w 0 ^ (-n : ℤ)) _ _).1 _,
  rw [@list.prod_const _ _ _ (w 0) hb, list.length_map, list.length_range, ← gpow_coe_nat, ← gpow_neg] at h₁,
  conv { to_rhs, rw [h₁, fixed_points_F₂_eq_const hv' _ 0] },
  rw [← nat.cast_zero, h₂ 0 h0.pos, nat.cast_zero, ← gpow_coe_nat, ← gpow_add, int.coe_nat_add],
  simp,
end

lemma one_mem_fixed_points_F₂ [fintype G] {n : ℕ} [h0 : Zmod.pos n] :
  (1 : Zmod n → G) ∈ fixed_points (F₂ G n) :=
mem_fixed_points.2 (λ y hy, funext (λ j,
  let ⟨i, hi⟩ := mem_orbit_iff.1 hy in
  have hj : (1 : G) = y j := congr_fun hi j,
    hj ▸ rfl))

lemma one_mem_Gstar (n : ℕ) [Zmod.pos n] : (1 : Zmod n → G) ∈ Gstar G n :=
show list.prod (list.map (λ (m : ℕ), (1 : G)) (list.range n)) = 1,
from have h : ∀ b : G, b ∈ list.map (λ (m : ℕ), (1 : G)) (list.range n) → b = 1 :=
λ b hb, let ⟨_, h⟩ := list.mem_map.1 hb in h.2.symm,
by simp [list.prod_const h]

attribute [trans] dvd.trans

lemma exists_prime_order_of_dvd_card [fintype G] {p : ℕ} (hp : nat.prime p)
  (hdvd : p ∣ card G) : ∃ x : G, order_of x = p :=
let n := p - 1 in
have hn : p = n + 1 := nat.succ_sub hp.pos,
have hnp : nat.prime (n + 1) := hn ▸ hp,
have hn0 : Zmod.pos n := ⟨nat.lt_of_succ_lt_succ hnp.gt_one⟩,
have hlt : ¬(n : Zmod (n + 1)).val < n :=
  not_lt_of_ge (by rw [Zmod.cast_val, nat.mod_eq_of_lt (nat.lt_succ_self _)]; 
    exact le_refl _),
have hcard1 : card (Gstar G (n + 1)) = card (Zmod n → G) := 
  by rw [← set.card_univ (Zmod n → G), set.ext (@mem_Gstar_iff _ _ _ hn0), 
    set.card_image_of_injective _ F₁_injective],
have hcard : card (Gstar G (n + 1)) = card G ^ n :=
  by conv { rw hcard1, to_rhs, rw ← card_fin n };
    exact fintype.card_fun,
have hZmod : @fintype.card (multiplicative (Zmod (n+1))) (fin.fintype _) = 
  (n+1) ^ 1 := (nat.pow_one (n + 1)).symm ▸ card_fin _,
have hmodeq : _ = _ := mpl hnp hZmod (@F₂Gstar G _ n hn0),
have hdvdcard : (n + 1) ∣ card (Gstar G (n + 1)) :=
  calc (n + 1) = p : hn.symm
  ... ∣ card G ^ 1 : by rwa nat.pow_one
  ... ∣ card G ^ n : nat.pow_dvd_pow _ hn0.pos
  ... = card (Gstar G (n + 1)) : hcard.symm,
have hdvdcard₂ : (n + 1) ∣ card (fixed_points (@F₂Gstar G _ n hn0)) :=
  nat.dvd_of_mod_eq_zero (hmodeq ▸ (nat.mod_eq_zero_of_dvd hdvdcard)),
have hcard_pos : 0 < card (fixed_points (@F₂Gstar G _ n hn0)) :=
  fintype.card_pos ⟨⟨(1 : Zmod (succ n) → G), one_mem_Gstar _⟩, 
    (fixed_points_restriction _).2 (one_mem_fixed_points_F₂)⟩,
have hle : 1 < card (fixed_points (@F₂Gstar G _ n hn0)) :=
  calc 1 < n + 1 : hnp.gt_one
  ... ≤ _ : nat.le_of_dvd hcard_pos hdvdcard₂,
let ⟨⟨x, hx₁⟩, hx₂⟩ := classical.not_forall.1 (mt fintype.card_le_one_iff.2 (not_le_of_gt hle)) in
let ⟨⟨y, hy₁⟩, hy₂⟩ := classical.not_forall.1 hx₂ in
have hxy : (x : Zmod (succ n) → G) 0 ≠ 1 ∨ (y : Zmod (succ n) → G) 0 ≠ 1 := 
  or_iff_not_imp_left.2 
  (λ hx1 hy1, hy₂ (subtype.eq (subtype.eq (funext (λ i, 
  show (x : Zmod (succ n) → G) i = (y : Zmod (succ n) → G) i,
  by rw [fixed_points_F₂_eq_const ((fixed_points_restriction _).1 hy₁) i 0, hy1,
        fixed_points_F₂_eq_const ((fixed_points_restriction _).1 hx₁) i 0, not_not.1 hx1]))))),
have hxp : (x : Zmod (succ n) → G) 0 ^ (n + 1) = 1 := @fixed_points_F₂_pow_n _ _ _ _ hnp hn0 _ hx₁,
have hyp : (y : Zmod (succ n) → G) 0 ^ (n + 1) = 1 := @fixed_points_F₂_pow_n _ _ _ _ hnp hn0 _ hy₁,
begin
  rw hn,
  cases hxy with hx hy,
  { existsi (x : Zmod (succ n) → G) 0,
    exact or.resolve_left (hnp.2 _ (order_of_dvd_of_pow_eq_one hxp)) 
      (λ h, hx (eq_one_of_order_of_eq_one h)) },
  { existsi (y : Zmod (succ n) → G) 0,
    exact or.resolve_left (hnp.2 _ (order_of_dvd_of_pow_eq_one hyp)) 
      (λ h, hy (eq_one_of_order_of_eq_one h)) }
end

local attribute [instance] left_rel
open is_subgroup is_submonoid
def thing (H : set G) [is_subgroup H] : group_action H (left_cosets H) :=
{ to_fun := λ x y, quotient.lift_on y (λ y, ⟦(x : G) * y⟧) 
  (λ a b (hab : _ ∈ H), quotient.sound 
    (show _ ∈ H, by rwa [mul_inv_rev, ← mul_assoc, mul_assoc (a⁻¹), inv_mul_self, mul_one])),
  one := λ a, quotient.induction_on a (λ a, quotient.sound (show (1 : G) * a ≈ a, by simp)),
  mul := λ x y a, quotient.induction_on a (λ a, quotient.sound (by rw ← mul_assoc; refl)) }

lemma fixed_points_thing (H : set G) [is_subgroup H] [fintype H] : 
  fixed_points (thing H) ≃ left_cosets { x : normalizer H | ↑x ∈ H } :=
equiv.symm (@equiv.of_bijective _ _ 
(show left_cosets {x : normalizer H | ↑x ∈ H} → fixed_points (thing H), from λ x,
⟨@quotient.lift_on _ _ (left_rel {x : normalizer H | ↑x ∈ H}) x 
  (λ ⟨x, (hx : ∀ (n : G), n ∈ H ↔ x * n * x⁻¹ ∈ H)⟩, show fixed_points (thing H), from 
    ⟨⟦x⟧, mem_fixed_points.2 (λ y, quotient.induction_on y (λ y ⟨⟨b, hb₁⟩, hb⟩, 
    have hb : x * (x⁻¹ * b⁻¹ * y) * x⁻¹ ∈ H := (hx _).1 (by rw ← mul_inv_rev; exact quotient.exact hb),
    quotient.sound ((hx _).2 $ (inv_mem_iff H).1 $ 
    (mul_mem_cancel_right H (inv_mem hb₁)).1
    begin
      simpa [mul_inv_rev, mul_assoc] using hb,
    end)))⟩) 
    (λ ⟨x, hx⟩ ⟨y, hy⟩ (hxy : x⁻¹ * y ∈ H), @quotient.sound _ (left_rel {x : normalizer H | ↑x ∈ H}) _ _ begin  
      
    end), sorry⟩) sorry)

lemma fixed_points_thing (H : set G) [is_subgroup H] [fintype H] : 
  fixed_points (thing H) ≃ left_cosets { x : normalizer H | ↑x ∈ H } :=
have h : ∀ a : G, ⟦a⟧ ∈ fixed_points (thing H) → a ∈ normalizer H := λ a ha, 
  have ha : ∀ {y : left_cosets H}, y ∈ orbit (thing H) ⟦a⟧ → y = ⟦a⟧ := λ _, 
    (mem_fixed_points.1 ha),
  (is_subgroup.inv_mem_iff _).1 (mem_normalizer_fintype_iff.2 (λ n hn,
    have (n⁻¹ * a)⁻¹ * a ∈ H := quotient.exact (ha (mem_orbit (thing H) _ 
      ⟨n⁻¹, is_subgroup.inv_mem hn⟩)),
    by simpa only [mul_inv_rev, inv_inv] using this)),
{ to_fun := λ ⟨a, ha⟩, quotient.hrec_on a (λ a ha, @quotient.mk _ 
  (left_rel {x : normalizer H | ↑x ∈ H}) ⟨a, h a ha⟩) 
    (λ x y hxy, function.hfunext (by rw quotient.sound hxy) 
      (λ hx hy _, heq_of_eq (@quotient.sound _ (left_rel {x : normalizer H | ↑x ∈ H}) 
        _ _ (by exact hxy)))) ha


}

lemma fixed_points_thing (H : set G) [is_subgroup H] : 
  fixed_points (thing H) ≃ left_cosets (normalizer H) :=
{ to_fun := λ ⟨a, ha⟩, quotient.lift_on a 
  (λ a, (@quotient.mk _ (left_rel (normalizer H)) a : 
    left_cosets (normalizer H))) 
      (λ a b (hab : _ ∈ _), 
        @quotient.sound _ (left_rel (normalizer H)) _ _ 
        (subset_normalizer _ hab)),
  inv_fun := λ a, ⟨⟦@quotient.out _ (left_rel (normalizer H)) a⟧, 
    mem_fixed_points.2 (λ y hy, let ⟨⟨b, hb₁⟩, hb₂⟩ := hy in begin
      dsimp [thing, coe_fn, has_coe_to_fun.coe] at hb₂,
      rw ← hb₂,
      refine quotient.sound _,
      show _ ∈ H,
      rw mul_inv_rev,
    end)⟩  ,  
    left_in :=    }

lemma fixed_points_thing (H : set G) [is_subgroup H] : 
  fixed_points (thing H) ≃ normalizer H :=
{ to_fun := λ ⟨a, ha⟩, ⟨quotient.out a, begin rw [mem_fixed_points] at ha,
  unfold normalizer,simp, end⟩}

lemma sylow1 [fintype G] {p n : ℕ} : ∀ {i : ℕ} (hp : nat.prime p)
  (hdvd : p ^ n ∣ card G) (hin : i ≤ n), ∃ H : set G, is_subgroup H ∧ card H = p ^ i
| 0 := λ _ _ _, ⟨is_subgroup.trivial G, by apply_instance, by rw [card_trivial, nat.pow_zero]⟩
| 1 := λ hp hdvd hin, 
let ⟨x, hx⟩ := exists_prime_order_of_dvd_card hp 
  (dvd.trans (by have := nat.pow_dvd_pow p hin; rwa nat.pow_one at this) hdvd) in
  ⟨gpowers x, by apply_instance, begin rw [nat.pow_one, ← hx], exact order_eq_card_gpowers.symm, end⟩
| (i+2) := λ hp hdvd hin, 
let ⟨H, ⟨hH1, hH2⟩⟩ := sylow1 hp hdvd (nat.le_of_succ_le hin) in
let ⟨s, hs⟩ := exists_eq_mul_left_of_dvd hdvd in
by exactI
have hcard : card (left_cosets H) = s * p ^ (n - (i + 1)) := 
  (nat.mul_right_inj (show card H > 0, from fintype.card_pos ⟨1, is_submonoid.one_mem H⟩)).1 
    (by rwa [← card_eq_card_cosets_mul_card_subgroup, hH2, mul_assoc, 
      ← nat.pow_add, nat.sub_add_cancel (nat.le_of_succ_le hin)]),
have hm : s * p ^ (n - (i + 1)) ≡ card ↥(fixed_points (thing H)) [MOD p] := 
  hcard ▸ mpl hp hH2 (thing H),
begin


end

end sylow